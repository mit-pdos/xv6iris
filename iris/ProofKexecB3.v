(* ProofKexecB3.v -- PHASE B of kexec, THIRD CHUNK: the phdr loop itself,
   the two paths that close the inode, and the whole of phase B2 as one
   lemma.

   It is a separate file from ProofKexecB2.v for the build reason
   ProofKexecTail.v's header records -- B2 is already 2200 lines and 2
   minutes, and every iteration on this loop would pay for [kxc_ls] again.
   The two do NOT meet through a module application of ProofKexecB2.v: this
   file does not require ProofKexecB2.v at all, only SpecKexecB2.v (fast, no
   [Qed] in it), and takes [B2] as an ABSTRACT functor argument of that
   file's [KEXECB2] signature -- [kxc_ls] and [kxc_bad324] at the same nine
   callee proofs, but without ever forcing ProofKexecB2.v to compile before
   this file does. See SpecKexecB2.v's header and
   claude-notes/design/spec-modules.md.

   ---- THE LOOP'S SHAPE, AND WHY THE HEAD IS +0x12c -------------------

   Read off the instructions, not the C: the [c.j] at +0x0cc enters the
   BODY at +0x12c, and +0x11a..+0x128 (increment, reload [off], add 56,
   reload [elf.phnum], test) is the BACK EDGE.  Three paths reach that back
   edge -- the not-PT_LOAD test at +0x148, the empty-segment test at
   +0x18c (through +0x19c), and the loadseg loop's own exit at +0x116 --
   so it is factored out as [kxc_incr] rather than written three times.

   [kxc_incr]'s single output carries a DISJUNCTION (the next body entry, or
   the +0x1a4 exit) rather than two [wp_next]s, and that is forced: both
   downstream paths need kexec's own exit continuation, which is linear, so
   two output wands could not both be built.  The same reason makes
   [kxc_ph_step] -- one whole iteration, +0x12c through +0x128 -- the unit
   the induction is over: its one non-[bad:] output is that disjunction, and
   the induction is then twenty lines.

   ---- THE MEASURE ----------------------------------------------------

   [eh_phnum ef - i], and the [W = 0] case is not vacuous by arithmetic but
   by the BRANCH: the back-edge disjunct carries [S i <= eh_phnum ef], which
   contradicts [eh_phnum ef - i <= 0].  (Contrast the loadseg loop, whose
   measure is [2^32 - off] and whose base case dies on the range alone.)

   ---- WHAT THE ITERATION DOES TO THE INVARIANT ------------------------

   Only uvmalloc moves it, and [ProofKexecSeam.kxc_grow_inv] is that step for
   both of its success arms at once.  Every other instruction in the body
   either tests an untrusted ELF field -- in which case the proof takes a
   BLIND split and neither branch needs the field's meaning -- or moves a
   value the invariant does not mention.  That is why a loop over an
   attacker-controlled program header table needs no premise about it. *)
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
Require Import CalleeSaved.
Require Import KernelRvcDecode.
Require Import InstrBytes.
Require Import KernelText.
Require Import WpSconfAlu WpSconfMem WpSconfCtl WpSconfBtype.
Require Import WpSmodeHalf.
Require Import WpSmodeIntr.
Require Import IntrDefs.
Require Import CpuOwn.
Require Import WpLock.
Require Import FdSlots.
Require Export SwtchCtx.
Require Import WpUart.
Require Import IcacheEscrow.
Require Import W32Arith.
Require Import ElfEnc.
Require Import PageGeom.
Require Import ProcGeom.
Require Import ProcInv.
Require Import DiskPtsto.
Require Import BioDefs.
Require Import FsBlocks LogInv.
Require Import BitmapInv.
Require Import InodeInv.
Require Import IcacheRef.
Require Import IcacheInv.
Require Import KvmSpec.
Require Import DinodeEnc.
Require Import IrefSlots.
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
Require Import SpecDirlink.
Require Import SpecNamei.
Require Import SpecProcFreepagetable.
Require Import SpecWalkaddr.
Require Import SpecFlags2perm.
Require Import SpecUvmalloc.
Require Import ProofKexecTail.
Require Import ProofKexecSeam.
Require Import SpecKexecB2.
Require Import SpecKexecB3.
Require Import CodeKexec.
From Kernel Require KernelSyms.
Require Import ProcAvail.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Local Open Scope Z_scope.

(* A syscall-altitude goal carries [ProcInv.tf_page]'s 4096-conjunct big-op;
   printing one takes tens of minutes, so a one-line mistake reads as a hang.
   durable-notes.md's rule. *)
Set Printing Depth 40.

Notation KXB := KernelSyms.kexec (only parsing).

(* ===================================================================== *)
(*  THE [ph] BUFFER'S FIVE FIELD OFFSETS, off its base slot 61.            *)
(* ===================================================================== *)
(* [struct proghdr] sits at [s0-488] = [pa_stk sp0 61], and the loop reads
   type@0, flags@4, off@8, vaddr@16, filesz@32 and memsz@40 out of it.  Every
   one of those but [flags] lands on a slot boundary; [flags] is the upper
   half of slot 61, which is what [InstrBytes.aligned8_aligned4_hi] is for. *)
Lemma kxc_ph_o0 (X : mword 64) : pa_add (pa_stk X 61) 0 = pa_stk X 61.
Proof. unfold pa_add, pa_stk. rewrite avi_assoc. f_equal; lia. Qed.

(* ...and the one field that is NOT slot-aligned: [flags] is the upper half
   of slot 61, so its address is stated against [pa_add] directly. *)
Lemma kxc_ph_o4 (X : mword 64) :
  add_vec X (sign_extend' 64 (mword_of_int 3612 : mword 12))
  = pa_add (pa_stk X 61) 4.
Proof.
  assert (Hv : (sign_extend' 64 (mword_of_int 3612 : mword 12) : mword 64)
               = mword_of_int (- (8 * Z.of_nat 61) + Z.of_nat 4))
    by (apply bv_eq; vm_compute; reflexivity).
  rewrite Hv. unfold pa_add, pa_stk. rewrite avi_assoc. reflexivity.
Qed.

Lemma kxc_ph_o8 (X : mword 64) : pa_add (pa_stk X 61) 8 = pa_stk X 60.
Proof. unfold pa_add, pa_stk. rewrite avi_assoc. f_equal; lia. Qed.

Lemma kxc_ph_o16 (X : mword 64) : pa_add (pa_stk X 61) 16 = pa_stk X 59.
Proof. unfold pa_add, pa_stk. rewrite avi_assoc. f_equal; lia. Qed.

Lemma kxc_ph_o32 (X : mword 64) : pa_add (pa_stk X 61) 32 = pa_stk X 57.
Proof. unfold pa_add, pa_stk. rewrite avi_assoc. f_equal; lia. Qed.

Lemma kxc_ph_o40 (X : mword 64) : pa_add (pa_stk X 61) 40 = pa_stk X 56.
Proof. unfold pa_add, pa_stk. rewrite avi_assoc. f_equal; lia. Qed.

(* [w32_uarg] at zero -- the loadseg loop's entry guard is stated over it. *)
Lemma kxc_uarg0 : w32_uarg 0 = 0.
Proof.
  unfold w32_uarg. case_decide as Hd; [reflexivity |].
  exfalso. change (2 ^ 31)%Z with 2147483648%Z in Hd. lia.
Qed.

(* ===================================================================== *)
(*  THE MIDDLE [stack_own] AT EIGHT SLOTS.                                *)
(* ===================================================================== *)
(* [kxc_frameBpin] holds slots 55..62 as [stack_own (pa_stk sp0 54) 8] (slot
   63 having been split out and pinned).  The body carves the seven [ph]
   slots out of it for readi's destination and puts them back before the
   back edge; [ProofKexecB2]'s pair does the same at nine slots. *)
Section KexecB3Ph.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Lemma kxc_ph8_of_stack (sp0 : mword 64) :
    stack_own (KTR := KT1) (pa_stk sp0 54) 8 ⊢
    ([∗ list] i ∈ seq 0 7,
       ∃ w : mword 64, word_pointsto (KTR := KT1) (pa_stk sp0 (61 - i)) (DfracOwn 1) w) ∗
    (∃ w : mword 64, word_pointsto (KTR := KT1) (pa_stk sp0 62) (DfracOwn 1) w).
  Proof.
    rewrite (kxc_slots_asc sp0 8 54). cbn [seq big_opL].
    iIntros "(H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & _)".
    cbn [Nat.add Nat.sub].
    iSplitR "H8"; [| iExact "H8"].
    iFrame "H7 H6 H5 H4 H3 H2 H1".
  Qed.

  Lemma kxc_stack8_of_ph (sp0 : mword 64) (w62 : mword 64) :
    ([∗ list] i ∈ seq 0 7,
       ∃ w : mword 64, word_pointsto (KTR := KT1) (pa_stk sp0 (61 - i)) (DfracOwn 1) w) -∗
    word_pointsto (KTR := KT1) (pa_stk sp0 62) (DfracOwn 1) w62 -∗
    stack_own (KTR := KT1) (pa_stk sp0 54) 8.
  Proof.
    iIntros "H A".
    rewrite (kxc_slots_asc sp0 8 54). cbn [seq big_opL Nat.add Nat.sub].
    iDestruct "H" as "(H1 & H2 & H3 & H4 & H5 & H6 & H7 & _)".
    iFrame "H7 H6 H5 H4 H3 H2 H1". iSplitL "A"; [by iExists w62 | done].
  Qed.

  (* the pinned frame, out of its twenty-one pieces.  Written once because
     the five [bad:] exits each need it and each holds the pieces under the
     same names. *)
  Lemma kxc_pin_intro (sp0 ra0 s00 s10 s20 pv av : mword 64)
      (w5 w6 w7 w8 w9 w10 w11 w12 w13 w63 w65 w67 w68 : mword 64) :
    word_pointsto (KTR := KT1) (pa_stk sp0 1) (DfracOwn 1) ra0 -∗
    word_pointsto (KTR := KT1) (pa_stk sp0 2) (DfracOwn 1) s00 -∗
    word_pointsto (KTR := KT1) (pa_stk sp0 3) (DfracOwn 1) s10 -∗
    word_pointsto (KTR := KT1) (pa_stk sp0 4) (DfracOwn 1) s20 -∗
    word_pointsto (KTR := KT1) (pa_stk sp0 5) (DfracOwn 1) w5 -∗
    word_pointsto (KTR := KT1) (pa_stk sp0 6) (DfracOwn 1) w6 -∗
    word_pointsto (KTR := KT1) (pa_stk sp0 7) (DfracOwn 1) w7 -∗
    word_pointsto (KTR := KT1) (pa_stk sp0 8) (DfracOwn 1) w8 -∗
    word_pointsto (KTR := KT1) (pa_stk sp0 9) (DfracOwn 1) w9 -∗
    word_pointsto (KTR := KT1) (pa_stk sp0 10) (DfracOwn 1) w10 -∗
    word_pointsto (KTR := KT1) (pa_stk sp0 11) (DfracOwn 1) w11 -∗
    word_pointsto (KTR := KT1) (pa_stk sp0 12) (DfracOwn 1) w12 -∗
    word_pointsto (KTR := KT1) (pa_stk sp0 13) (DfracOwn 1) w13 -∗
    stack_own (KTR := KT1) (pa_stk sp0 13) 33 -∗
    stack_own (KTR := KT1) (pa_stk sp0 54) 8 -∗
    word_pointsto (KTR := KT1) (pa_stk sp0 63) (DfracOwn 1) w63 -∗
    word_pointsto (KTR := KT1) (pa_stk sp0 64) (DfracOwn 1) av -∗
    word_pointsto (KTR := KT1) (pa_stk sp0 65) (DfracOwn 1) w65 -∗
    word_pointsto (KTR := KT1) (pa_stk sp0 66) (DfracOwn 1) pv -∗
    word_pointsto (KTR := KT1) (pa_stk sp0 67) (DfracOwn 1) w67 -∗
    word_pointsto (KTR := KT1) (pa_stk sp0 68) (DfracOwn 1) w68 -∗
    kxc_frameBpin sp0 ra0 s00 s10 s20 pv av
                  w5 w6 w7 w8 w9 w10 w11 w12 w13 w63 w65 w67.
  Proof.
    rewrite /kxc_frameBpin.
    iIntros "A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 Aust Aph A63 A64 A65
             A66 A67 A68".
    iSplitL "A1"; [iExact "A1" |]. iSplitL "A2"; [iExact "A2" |].
    iSplitL "A3"; [iExact "A3" |]. iSplitL "A4"; [iExact "A4" |].
    iSplitL "A5"; [iExact "A5" |]. iSplitL "A6"; [iExact "A6" |].
    iSplitL "A7"; [iExact "A7" |]. iSplitL "A8"; [iExact "A8" |].
    iSplitL "A9"; [iExact "A9" |]. iSplitL "A10"; [iExact "A10" |].
    iSplitL "A11"; [iExact "A11" |]. iSplitL "A12"; [iExact "A12" |].
    iSplitL "A13"; [iExact "A13" |]. iSplitL "Aust"; [iExact "Aust" |].
    iSplitL "Aph"; [iExact "Aph" |]. iSplitL "A63"; [iExact "A63" |].
    iSplitL "A64"; [iExact "A64" |]. iSplitL "A65"; [iExact "A65" |].
    iSplitL "A66"; [iExact "A66" |]. iSplitL "A67"; [iExact "A67" |].
    by iExists w68.
  Qed.

End KexecB3Ph.

(* ===================================================================== *)
(*  +0x11a -- THE BACK EDGE'S ENTRY STATE.                                *)
(* ===================================================================== *)
(* Three paths reach it and they agree about everything the five
   instructions there read: [s10 = i], slot 63 = [off], and the named elf
   run (for [elf.phnum]).  [s2] carries whatever size that path settled on,
   which is the loop variable. *)
Section KexecB3Seam.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ, !irefslotG Σ, !pavG Σ}.
  Context `{GEN : GenId} `{CID0 : CpuId}.

  Notation Rs0 := (mword_of_int 8 : mword 5).
  Notation Rs2 := (mword_of_int 18 : mword 5).
  Notation Rs4 := (mword_of_int 20 : mword 5).
  Notation Rs5 := (mword_of_int 21 : mword 5).
  Notation Rs6 := (mword_of_int 22 : mword 5).
  Notation Rs9 := (mword_of_int 25 : mword 5).
  Notation Rs10 := (mword_of_int 26 : mword 5).
  Notation Rs11 := (mword_of_int 27 : mword 5).

  Definition kxc_at_11a
      (jp : nat)
      (bn : bio_names) (g : log_names) (gfs : fs_names) (gi : gname)
      (cn : ic_names) (ga gf : gname)
      (cov : gset Z) (logstart bmapstart inodestart : Z) (nib : nat)
      (size : Z) (dev : mword 32)
      (kf : nat) (qf sf : Qp) (gyf : gname) (inumf : mword 32)
      (dnf : dinode) (bmf : blkmap)
      (gilf gislf : gname) (n2 : nat)
      (plen : nat) (pfun : nat -> bv 8)
      (na : nat) (avf : nat -> mword 64) (aslen : nat -> nat)
      (afun : nat -> nat -> bv 8)
      (pidv : mword 32) (V : pprivate) (eb : bool) (dqb dqs dqa dqpv dqas : dfrac)
      (M : regfile) (K : nat)
      (sp0 ra0 s00 s10 s20 pv av : mword 64)
      (w5 w6 w7 w8 w9 w10 w11 w12 w13 w65 w67 : mword 64)
      (ef : nat -> bv 8) (P : uptd) (i : nat) (szv : mword 64) : iProp Σ :=
    (⌜ M !!! Regidx csp_rs1 = pa_stk sp0 68 /\
       M !!! Regidx Rs0 = sp0 /\
       M !!! Regidx Rs2 = szv /\
       M !!! Regidx Rs4 = ientry kf /\
       M !!! Regidx Rs5 = (mword_of_int 4096 : mword 64) /\
       M !!! Regidx Rs6 = page_base P.(ud_root) /\
       M !!! Regidx Rs9 = (mword_of_int 4096 : mword 64) /\
       M !!! Regidx Rs10 = (mword_of_int (Z.of_nat i) : mword 64) /\
       M !!! Regidx Rs11 = (mword_of_int 56 : mword 64) ⌝ ∗
     ⌜ (kf < NINODE)%nat /\
       bv_unsigned inumf < 16 * Z.of_nat nib /\
       (iput_units <= n2)%nat /\
       (forall j, (j < 8)%nat ->
          is_aligned_paddr (Physaddr (pa_stk sp0 (54 - j))) 8 = true) ⌝ ∗
     ⌜ (Z.of_nat i <= eh_phnum ef)%Z /\
       ud_tfp P = ud_tfp (pv_upt V) /\
       um_below szv P.(ud_um) /\
       um_covered szv P.(ud_um) ⌝ ∗
     pc_is (mword_of_int (KXB + 0x11a) : mword 64) ∗
     sie_cap_gpr KT1 M (K - 68)%nat eb (proc_addr jp) ∗
     cpu_own 0 eb (proc_addr jp) eb ∅ ∗
     trap_csrs_ext KT1 eb ∗
     cpu_claim_ext eb (proc_addr jp) ∗
     kalloc_env ga None ∗
     kxc_res jp bn g gfs gi cn gf cov logstart bmapstart inodestart size dev
             kf qf sf gyf inumf dnf bmf gilf gislf n2 plen pfun na avf
             aslen afun pidv V dqb dqs dqa dqpv dqas sp0 ra0 s00 s10 s20 pv av
             w5 w6 w7 w8 w9 w10 w11 w12 w13 (kxc_off ef i) w65 w67 ef P)%I.

End KexecB3Seam.

(* ===================================================================== *)
(*  THE PROOF.                                                            *)
(* ===================================================================== *)
(* [B2] is now taken ABSTRACTLY, as a module of SpecKexecB2's [KEXECB2]
   signature, rather than built here by applying
   [ProofKexecB2.KexecB2Proof] -- so this file no longer requires
   ProofKexecB2.v (~2200 lines / ~2 min) at all, and the two phases compile
   in parallel.  See SpecKexecB2.v's header and
   claude-notes/design/spec-modules.md.  [A] is built the same way B2 built
   it (a direct application of [ProofKexecTail.KexecTailProof]), not
   fetched via [B2.A] -- [KEXECB2] does not re-export it, and there is no
   reason to route through B2 for something both phases build identically
   from the same seven arguments. *)
Module KexecB3Proof (Myproc : MYPROC) (BeginOp : BEGIN_OP) (Namei : NAMEI)
                    (Ilock : ILOCK) (Readi : READI) (Iunlockput : IUNLOCKPUT)
                    (EndOp : END_OP) (PFP : PROC_FREEPAGETABLE)
                    (Walkaddr : WALKADDR) (Flags2perm : FLAGS2PERM)
                    (Uvmalloc : UVMALLOC) (B2 : KEXECB2) : KEXECB3.

Module A := ProofKexecTail.KexecTailProof Myproc BeginOp Namei Ilock Readi
                                          Iunlockput EndOp.

(* ===================================================================== *)
(*  +0x11a .. +0x128 -- THE BACK EDGE.                                    *)
(* ===================================================================== *)
(*    c.addiw s10,s10,1     i++                                            *)
(*    ld      a5,-504(s0)   off  (slot 63, written at +0x12c)              *)
(*    addiw   a3,a5,56      off += sizeof(struct proghdr)                  *)
(*    lhu     a5,-376(s0)   elf.phnum                                      *)
(*    bge     s10,a5,+0x1a4                                                *)
(*                                                                         *)
(*  ONE OUTPUT CARRYING A DISJUNCTION, not two [wp_next]s: both downstream  *)
(*  paths need kexec's exit continuation, which is linear, so two output    *)
(*  wands could not both be constructed by the caller.                      *)
(* ===================================================================== *)
Section KexecB3Incr.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ, !irefslotG Σ, !pavG Σ}.
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
  Notation Rs8 := (mword_of_int 24 : mword 5).
  Notation Rs9 := (mword_of_int 25 : mword 5).
  Notation Rs10 := (mword_of_int 26 : mword 5).
  Notation Rs11 := (mword_of_int 27 : mword 5).
  Notation Ra0 := (mword_of_int 10 : mword 5).
  Notation Ra1 := (mword_of_int 11 : mword 5).
  Notation Ra2 := (mword_of_int 12 : mword 5).
  Notation Ra3 := (mword_of_int 13 : mword 5).
  Notation Ra4 := (mword_of_int 14 : mword 5).
  Notation Ra5 := (mword_of_int 15 : mword 5).

  Local Ltac inz := vm_compute; discriminate.
  Local Ltac ipcw := apply bv_eq; vm_compute; reflexivity.
  Local Ltac is0slot := apply stk_push; apply bv_eq; vm_compute; reflexivity.

  Lemma kxc_incr `{CID0 : CpuId}
      (jp : nat) (bn : bio_names) (g : log_names) (gfs : fs_names) (gi : gname)
      (cn : ic_names) (ga gf : gname)
      (cov : gset Z) (logstart bmapstart inodestart : Z) (nib : nat)
      (size : Z) (dev : mword 32)
      (kf : nat) (qf sf : Qp) (gyf : gname) (inumf : mword 32)
      (dnf : dinode) (bmf : blkmap) (gilf gislf : gname) (n2 : nat)
      (plen : nat) (pfun : nat -> bv 8)
      (na : nat) (avf : nat -> mword 64) (aslen : nat -> nat)
      (afun : nat -> nat -> bv 8)
      (pidv : mword 32) (V : pprivate) (eb : bool) (dqb dqs dqa dqpv dqas : dfrac)
      (m M : regfile) (K : nat)
      (sp0 ra0 s00 s10 s20 pv av : mword 64)
      (w5 w6 w7 w8 w9 w10 w11 w12 w13 w65 w67 : mword 64)
      (ef : nat -> bv 8) (P : uptd) (i : nat) (szv : mword 64) :
    kernel_text -∗
    kxc_at_11a jp bn g gfs gi cn ga gf cov logstart bmapstart inodestart nib
               size dev kf qf sf gyf inumf dnf bmf gilf gislf n2
               plen pfun na avf aslen afun pidv V eb dqb dqs dqa dqpv dqas M K
               sp0 ra0 s00 s10 s20 pv av
               w5 w6 w7 w8 w9 w10 w11 w12 w13 w65 w67 ef P i szv -∗
    wp_next true (proc_addr jp) (fun (CID : CpuId) =>
      ∀ (M' : regfile),
        ( kxc_at_12c jp bn g gfs gi cn ga gf cov logstart bmapstart inodestart
                     nib size dev kf qf sf gyf inumf dnf bmf
                     gilf gislf n2 plen pfun na avf aslen afun pidv V eb
                     dqb dqs dqa dqpv dqas m M' K sp0 ra0 s00 s10 s20 pv av
                     w5 w6 w7 w8 w9 w10 w11 w12 w13 w67 ef P (S i) szv
          ∨ kxc_at_1a4 jp bn g gfs gi cn ga gf cov logstart bmapstart inodestart
                       nib size dev kf qf sf gyf inumf dnf bmf
                       gilf gislf n2 plen pfun na avf aslen afun pidv V eb
                       dqb dqs dqa dqpv dqas M' K sp0 ra0 s00 s10 s20 pv av
                       w5 w6 w7 w8 w9 w10 w11 w12 w13 w67 ef P szv ) -∗
        WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    iIntros "#Htext Hst Hout".
    rewrite /kxc_at_11a.
    iDestruct "Hst" as "((%HMsp & %HMs0 & %HMs2 & %HMs4 & %HMs5 & %HMs6 &
                          %HMs9 & %HMs10 & %HMs11) &
                         (%Hk & %Hib & %Hn2 & %Hal) &
                         (%Hiphn & %HPtfp & %Hbelow & %Hcov) &
                         Hpc & Hcg & Hcnt & Hextc & Hclmc & #Hka & Hres)".
    rewrite /kxc_res.
    iDestruct "Hres" as "(Hopen & Hlog & Hirs & Hbm & Hins & Hbits & Hbs & Hpt &
                          Hpriv & Hpath & Hargv & Hargs & Helf & Hframe)".
    rewrite /kxc_frameBpin.
    iDestruct "Hframe" as "(Hf1 & Hf2 & Hf3 & Hf4 & Hf5 & Hf6 & Hf7 & Hf8 &
                            Hf9 & Hf10 & Hf11 & Hf12 & Hf13 & Hust & Hph &
                            Hf63 & Hf64 & Hf65 & Hf66 & Hf67 & Hf68)".
    pose proof (eh_phnum_bound ef) as Hphb.
    (* ---- +0x11a: c.addiw s10,s10,1 ---- *)
    assert (Hv11a : (sign_extend' 64 (subrange_vec_dec
                       (add_vec (rget M Rs10)
                          (sign_extend' 64 (sign_extend' 12
                             (mword_of_int 1 : mword 6)))) 31 0 : mword 32)
                     : mword 64)
                    = (mword_of_int (Z.of_nat i + 1) : mword 64)).
    { rewrite (rget_ne M Rs10 ltac:(inz)) HMs10.
      apply w32_caddiw_moi;
        [ apply bv_eq; vm_compute; reflexivity
        | change (2 ^ 31)%Z with 2147483648%Z; lia ]. }
    iApply (wp_caddiw_s_sconf (mword_of_int (KXB + 0x11a)) Rs10
              (mword_of_int 1 : mword 6) M (K - 68)%nat eb
              ltac:(inz) ltac:(rdok) with "Hcg Hpc []").
    { iApply (kxc_11a with "Htext"). }
    iIntros (CID1 Hsq1) "Hcg Hpc". iEval (rewrite Hv11a) in "Hcg".
    set (T1 := <[Regidx Rs10 := regval_into_reg
                  (mword_of_int (Z.of_nat i + 1) : mword 64)]> M).
    assert (HT1s10 : T1 !!! Regidx Rs10
                     = (mword_of_int (Z.of_nat i + 1) : mword 64))
      by (rewrite /T1; apply upd_eq).
    assert (HT1sp : T1 !!! Regidx csp_rs1 = pa_stk sp0 68)
      by (rewrite /T1 upd_ne; [exact HMsp | inz]).
    assert (HT1s0 : T1 !!! Regidx Rs0 = sp0)
      by (rewrite /T1 upd_ne; [exact HMs0 | inz]).
    assert (HT1s2 : T1 !!! Regidx Rs2 = szv)
      by (rewrite /T1 upd_ne; [exact HMs2 | inz]).
    assert (HT1s4 : T1 !!! Regidx Rs4 = ientry kf)
      by (rewrite /T1 upd_ne; [exact HMs4 | inz]).
    assert (HT1s5 : T1 !!! Regidx Rs5 = (mword_of_int 4096 : mword 64))
      by (rewrite /T1 upd_ne; [exact HMs5 | inz]).
    assert (HT1s6 : T1 !!! Regidx Rs6 = page_base P.(ud_root))
      by (rewrite /T1 upd_ne; [exact HMs6 | inz]).
    assert (HT1s9 : T1 !!! Regidx Rs9 = (mword_of_int 4096 : mword 64))
      by (rewrite /T1 upd_ne; [exact HMs9 | inz]).
    assert (HT1s11 : T1 !!! Regidx Rs11 = (mword_of_int 56 : mword 64))
      by (rewrite /T1 upd_ne; [exact HMs11 | inz]).
    assert (Hpp11c : add_vec_int (mword_of_int (KXB + 0x11a) : mword 64) 2
                     = mword_of_int (KXB + 0x11c)) by ipcw.
    iEval (rewrite Hpp11c) in "Hpc".
    (* ---- +0x11c: ld a5,-504(s0) -- [off] back out of slot 63 ---- *)
    assert (Hpa63 : add_vec (rget T1 Rs0)
                      (sign_extend' 64 (mword_of_int 3592 : mword 12))
                    = pa_stk sp0 63).
    { rewrite (rget_ne T1 Rs0 ltac:(inz)) HT1s0. is0slot. }
    iEval (rewrite -Hpa63) in "Hf63".
    iApply (wp_ld_s_sconf (mword_of_int (KXB + 0x11c)) Ra5 Rs0
              (mword_of_int 3592 : mword 12) T1 (K - 68)%nat (kxc_off ef i) eb
              (dqm := DfracOwn 1) ltac:(inz) ltac:(rdok)
              with "Hcg Hpc [] Hf63").
    { iApply (kxc_11c with "Htext"). }
    iIntros (CID2 Hsq2) "Hcg Hpc Hf63". iEval (rewrite Hpa63) in "Hf63".
    set (T2 := <[Regidx Ra5 := regval_into_reg (kxc_off ef i)]> T1).
    assert (HT2a5 : T2 !!! Regidx Ra5 = kxc_off ef i)
      by (rewrite /T2; apply upd_eq).
    assert (Hpp120 : add_vec_int (mword_of_int (KXB + 0x11c) : mword 64) 4
                     = mword_of_int (KXB + 0x120)) by ipcw.
    iEval (rewrite Hpp120) in "Hpc".
    (* ---- +0x120: addiw a3,a5,56 -- the next header's file offset ---- *)
    assert (Hv120 : (sign_extend' 64 (subrange_vec_dec
                       (add_vec (rget T2 Ra5)
                          (sign_extend' 64 (mword_of_int 56 : mword 12)))
                       31 0 : mword 32) : mword 64)
                    = kxc_off ef (S i)).
    { rewrite (rget_ne T2 Ra5 ltac:(inz)) HT2a5. apply kxc_off_step. }
    iApply (wp_addiw_s_sconf (mword_of_int (KXB + 0x120)) Ra3 Ra5
              (mword_of_int 56 : mword 12) T2 (K - 68)%nat eb
              ltac:(inz) ltac:(rdok) with "Hcg Hpc []").
    { iApply (kxc_120 with "Htext"). }
    iIntros (CID3 Hsq3) "Hcg Hpc". iEval (rewrite Hv120) in "Hcg".
    set (T3 := <[Regidx Ra3 := regval_into_reg (kxc_off ef (S i))]> T2).
    assert (HT3a3 : T3 !!! Regidx Ra3 = kxc_off ef (S i))
      by (rewrite /T3; apply upd_eq).
    assert (HT3s0 : T3 !!! Regidx Rs0 = sp0).
    { rewrite /T3 upd_ne; [| inz]. rewrite /T2 upd_ne; [exact HT1s0 | inz]. }
    assert (Hpp124 : add_vec_int (mword_of_int (KXB + 0x120) : mword 64) 4
                     = mword_of_int (KXB + 0x124)) by ipcw.
    iEval (rewrite Hpp124) in "Hpc".
    (* ---- +0x124: lhu a5,-376(s0) -- elf.phnum, out of the named run ---- *)
    assert (Hal47 : is_aligned_paddr (Physaddr (pa_stk sp0 47)) 8 = true)
      by (pose proof (Hal 7%nat ltac:(lia)) as Hx; cbn in Hx; exact Hx).
    assert (Hal2 : is_aligned_paddr
                     (Physaddr (pa_add (pa_stk sp0 54) 56)) 2 = true).
    { rewrite kxc_elf_off56. apply kxc_aligned8_aligned2. exact Hal47. }
    iDestruct (kxc_win2 (pa_stk sp0 54) ef 56 6 64 ltac:(lia) Hal2
                 with "Helf") as "[Hw2 Hbk2]".
    assert (Hpa47 : add_vec (rget T3 Rs0)
                      (sign_extend' 64 (mword_of_int 3720 : mword 12))
                    = pa_add (pa_stk sp0 54) 56).
    { rewrite (rget_ne T3 Rs0 ltac:(inz)) HT3s0 kxc_elf_off56.
      apply kxc_phnum_slot. }
    iEval (rewrite -Hpa47) in "Hw2".
    iApply (wp_lhu_s_sconf (kt := KT1) (ktd := KT1) (mword_of_int (KXB + 0x124)) Ra5 Rs0
              (mword_of_int 3720 : mword 12) T3 (K - 68)%nat
              (Z_to_bv 16 (le_at ef 56 2) : mword 16) eb
              (dqm := DfracOwn 1) ltac:(inz) ltac:(rdok)
              with "Hcg Hpc [] Hw2").
    { iApply (kxc_124 with "Htext"). }
    iIntros (CID4 Hsq4) "Hcg Hpc Hw2". iEval (rewrite Hpa47) in "Hw2".
    iDestruct ("Hbk2" with "Hw2") as "Helf".
    set (T4 := <[Regidx Ra5 := regval_into_reg
                  (zero_extend' 64 (Z_to_bv 16 (le_at ef 56 2)
                                    : mword 16))]> T3).
    assert (HT4a5 : T4 !!! Regidx Ra5 = (mword_of_int (eh_phnum ef) : mword 64)).
    { rewrite /T4 upd_eq. apply kxc_phnum_moi. }
    assert (HT4a3 : T4 !!! Regidx Ra3 = kxc_off ef (S i))
      by (rewrite /T4 upd_ne; [exact HT3a3 | inz]).
    assert (HT4s10 : T4 !!! Regidx Rs10
                     = (mword_of_int (Z.of_nat i + 1) : mword 64)).
    { rewrite /T4 upd_ne; [| inz]. rewrite /T3 upd_ne; [| inz].
      rewrite /T2 upd_ne; [exact HT1s10 | inz]. }
    assert (HT4sp : T4 !!! Regidx csp_rs1 = pa_stk sp0 68).
    { rewrite /T4 upd_ne; [| inz]. rewrite /T3 upd_ne; [| inz].
      rewrite /T2 upd_ne; [exact HT1sp | inz]. }
    assert (HT4s0 : T4 !!! Regidx Rs0 = sp0)
      by (rewrite /T4 upd_ne; [exact HT3s0 | inz]).
    assert (HT4s2 : T4 !!! Regidx Rs2 = szv).
    { rewrite /T4 upd_ne; [| inz]. rewrite /T3 upd_ne; [| inz].
      rewrite /T2 upd_ne; [exact HT1s2 | inz]. }
    assert (HT4s4 : T4 !!! Regidx Rs4 = ientry kf).
    { rewrite /T4 upd_ne; [| inz]. rewrite /T3 upd_ne; [| inz].
      rewrite /T2 upd_ne; [exact HT1s4 | inz]. }
    assert (HT4s5 : T4 !!! Regidx Rs5 = (mword_of_int 4096 : mword 64)).
    { rewrite /T4 upd_ne; [| inz]. rewrite /T3 upd_ne; [| inz].
      rewrite /T2 upd_ne; [exact HT1s5 | inz]. }
    assert (HT4s6 : T4 !!! Regidx Rs6 = page_base P.(ud_root)).
    { rewrite /T4 upd_ne; [| inz]. rewrite /T3 upd_ne; [| inz].
      rewrite /T2 upd_ne; [exact HT1s6 | inz]. }
    assert (HT4s9 : T4 !!! Regidx Rs9 = (mword_of_int 4096 : mword 64)).
    { rewrite /T4 upd_ne; [| inz]. rewrite /T3 upd_ne; [| inz].
      rewrite /T2 upd_ne; [exact HT1s9 | inz]. }
    assert (HT4s11 : T4 !!! Regidx Rs11 = (mword_of_int 56 : mword 64)).
    { rewrite /T4 upd_ne; [| inz]. rewrite /T3 upd_ne; [| inz].
      rewrite /T2 upd_ne; [exact HT1s11 | inz]. }
    assert (Hpp128 : add_vec_int (mword_of_int (KXB + 0x124) : mword 64) 4
                     = mword_of_int (KXB + 0x128)) by ipcw.
    iEval (rewrite Hpp128) in "Hpc".
    (* ---- the frame, back as one chunk (slot 63 still holds [off]) ---- *)
    iAssert (kxc_frameB sp0 ra0 s00 s10 s20 pv av
               w5 w6 w7 w8 w9 w10 w11 w12 w13 w67)
      with "[Hf1 Hf2 Hf3 Hf4 Hf5 Hf6 Hf7 Hf8 Hf9 Hf10 Hf11 Hf12 Hf13 Hust Hph
             Hf63 Hf64 Hf65 Hf66 Hf67 Hf68]" as "Hfr".
    { iApply (kxc_frameB_of_Bpin sp0 ra0 s00 s10 s20 pv av
                w5 w6 w7 w8 w9 w10 w11 w12 w13 (kxc_off ef i) w65 w67).
      rewrite /kxc_frameBpin.
      iSplitL "Hf1"; [iExact "Hf1" |]. iSplitL "Hf2"; [iExact "Hf2" |].
      iSplitL "Hf3"; [iExact "Hf3" |]. iSplitL "Hf4"; [iExact "Hf4" |].
      iSplitL "Hf5"; [iExact "Hf5" |]. iSplitL "Hf6"; [iExact "Hf6" |].
      iSplitL "Hf7"; [iExact "Hf7" |]. iSplitL "Hf8"; [iExact "Hf8" |].
      iSplitL "Hf9"; [iExact "Hf9" |]. iSplitL "Hf10"; [iExact "Hf10" |].
      iSplitL "Hf11"; [iExact "Hf11" |]. iSplitL "Hf12"; [iExact "Hf12" |].
      iSplitL "Hf13"; [iExact "Hf13" |]. iSplitL "Hust"; [iExact "Hust" |].
      iSplitL "Hph"; [iExact "Hph" |]. iSplitL "Hf63"; [iExact "Hf63" |].
      iSplitL "Hf64"; [iExact "Hf64" |]. iSplitL "Hf65"; [iExact "Hf65" |].
      iSplitL "Hf66"; [iExact "Hf66" |]. iSplitL "Hf67"; [iExact "Hf67" |].
      iExact "Hf68". }
    (* ---- +0x128: bge s10,a5 -- the loop test ---- *)
    assert (Hcmp : zopz0zKzJ_s (rget T4 Rs10) (rget T4 Ra5)
                   = Z.geb (Z.of_nat i + 1) (eh_phnum ef)).
    { rewrite (rget_ne T4 Rs10 ltac:(inz)) (rget_ne T4 Ra5 ltac:(inz))
              HT4s10 HT4a5.
      apply w32_bge_moi; change (2 ^ 63)%Z with 9223372036854775808%Z; lia. }
    assert (Htgt1a4 : add_vec (mword_of_int (KXB + 0x128) : mword 64)
                        (sign_extend' 64 (mword_of_int 124 : mword 13))
                      = mword_of_int (KXB + 0x1a4)) by ipcw.
    destruct (Z.geb (Z.of_nat i + 1) (eh_phnum ef)) eqn:Egeb.
    - (* ---- DONE: on to +0x1a4 ---- *)
      iApply (wp_bge_taken_s_sconf (mword_of_int (KXB + 0x128))
                (mword_of_int 124 : mword 13) Ra5 Rs10 T4 (K - 68)%nat eb
                ltac:(inz) ltac:(inz) ltac:(exact Hcmp)
                ltac:(rewrite Htgt1a4; vm_compute; reflexivity)
                with "Hcg Hpc []").
      { iApply (kxc_128 with "Htext"). }
      iIntros (CID5 Hsq5). iNext. iIntros "Hcg Hpc".
      iEval (rewrite Htgt1a4) in "Hpc".
      iDestruct (cpu_own_transport CID0 CID5 0%nat eb (proc_addr jp) eb
                   ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
      iDestruct (trap_csrs_ext_transport CID0 CID5 eb (proc_addr jp)
                   ltac:(try rewrite Hebb; wp_next_chain) with "Hextc") as "Hextc".
      iDestruct (cpu_claim_ext_transport CID0 CID5 eb (proc_addr jp)
                   ltac:(try rewrite Hebb; wp_next_chain) with "Hclmc") as "Hclmc".
      iSpecialize ("Hout" $! CID5 with "[%]"); [wp_next_chain |].
      iApply ("Hout" $! T4). iRight. rewrite /kxc_at_1a4.
      iSplitR.
      { iPureIntro. split_and!;
          [exact HT4sp | exact HT4s0 | exact HT4s2 | exact HT4s4 | exact HT4s6]. }
      iSplitR.
      { iPureIntro. split_and!;
          [exact Hk | exact Hib | exact Hn2 | exact Hal]. }
      iSplitR.
      { iPureIntro. split_and!; [exact HPtfp | exact Hbelow | exact Hcov]. }
      (* NEVER [iFrame] HERE.  At this altitude the goal carries
         [ProcInv.tf_page]'s 4096-conjunct big-op inside [proc_priv], and
         [iFrame]'s search does not terminate on it (durable-notes.md).  The
         eighteen conjuncts go one at a time. *)
      iSplitL "Hpc"; [iExact "Hpc" |]. iSplitL "Hcg"; [iExact "Hcg" |].
      iSplitL "Hcnt"; [iExact "Hcnt" |].
      iSplitL "Hextc"; [iExact "Hextc" |]. iSplitL "Hclmc"; [iExact "Hclmc" |]. iSplitL "Hopen"; [iExact "Hopen" |].
      iSplitL "Hlog"; [iExact "Hlog" |]. iSplitL "Hirs"; [iExact "Hirs" |].
      iSplitL "Hbm"; [iExact "Hbm" |]. iSplitL "Hins"; [iExact "Hins" |].
      iSplitL "Hbits"; [iExact "Hbits" |]. iSplitL "Hbs"; [iExact "Hbs" |].
      iSplitR; [iExact "Hka" |]. iSplitL "Hpt"; [iExact "Hpt" |].
      iSplitL "Hpriv"; [iExact "Hpriv" |]. iSplitL "Hpath"; [iExact "Hpath" |].
      iSplitL "Hargv"; [iExact "Hargv" |]. iSplitL "Hargs"; [iExact "Hargs" |].
      iSplitL "Helf"; [iExact "Helf" | iExact "Hfr"].
    - (* ---- ANOTHER HEADER: back to the body at +0x12c ---- *)
      iApply (wp_bge_fall_s_sconf (mword_of_int (KXB + 0x128))
                (mword_of_int 124 : mword 13) Ra5 Rs10 T4 (K - 68)%nat eb
                ltac:(inz) ltac:(inz) ltac:(exact Hcmp)
                with "Hcg Hpc []").
      { iApply (kxc_128 with "Htext"). }
      iIntros (CID5 Hsq5) "Hcg Hpc".
      assert (Hpp12c : add_vec_int (mword_of_int (KXB + 0x128) : mword 64) 4
                       = mword_of_int (KXB + 0x12c)) by ipcw.
      iEval (rewrite Hpp12c) in "Hpc".
      iDestruct (cpu_own_transport CID0 CID5 0%nat eb (proc_addr jp) eb
                   ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
      iDestruct (trap_csrs_ext_transport CID0 CID5 eb (proc_addr jp)
                   ltac:(try rewrite Hebb; wp_next_chain) with "Hextc") as "Hextc".
      iDestruct (cpu_claim_ext_transport CID0 CID5 eb (proc_addr jp)
                   ltac:(try rewrite Hebb; wp_next_chain) with "Hclmc") as "Hclmc".
      assert (HSi : (Z.of_nat (S i) <= eh_phnum ef)%Z)
        by (rewrite Nat2Z.inj_succ; rewrite Z.geb_leb in Egeb;
            apply Z.leb_gt in Egeb; lia).
      assert (HT4s10' : T4 !!! Regidx Rs10
                        = (mword_of_int (Z.of_nat (S i)) : mword 64))
        by (rewrite HT4s10 Nat2Z.inj_succ; f_equal; lia).
      iSpecialize ("Hout" $! CID5 with "[%]"); [wp_next_chain |].
      iApply ("Hout" $! T4). iLeft. rewrite /kxc_at_12c.
      iSplitR.
      { iPureIntro. split_and!;
          [exact HT4sp | exact HT4s0 | exact HT4s2 | exact HT4s4 | exact HT4s5
          | exact HT4s6 | exact HT4s9 | exact HT4s10' | exact HT4s11
          | exact HT4a3]. }
      iSplitR.
      { iPureIntro. split_and!;
          [exact Hk | exact Hib | exact Hn2 | exact Hal]. }
      iSplitR.
      { iPureIntro. split_and!;
          [exact HSi | exact HPtfp | exact Hbelow | exact Hcov]. }
      (* NEVER [iFrame] HERE.  At this altitude the goal carries
         [ProcInv.tf_page]'s 4096-conjunct big-op inside [proc_priv], and
         [iFrame]'s search does not terminate on it (durable-notes.md).  The
         eighteen conjuncts go one at a time. *)
      iSplitL "Hpc"; [iExact "Hpc" |]. iSplitL "Hcg"; [iExact "Hcg" |].
      iSplitL "Hcnt"; [iExact "Hcnt" |].
      iSplitL "Hextc"; [iExact "Hextc" |]. iSplitL "Hclmc"; [iExact "Hclmc" |]. iSplitL "Hopen"; [iExact "Hopen" |].
      iSplitL "Hlog"; [iExact "Hlog" |]. iSplitL "Hirs"; [iExact "Hirs" |].
      iSplitL "Hbm"; [iExact "Hbm" |]. iSplitL "Hins"; [iExact "Hins" |].
      iSplitL "Hbits"; [iExact "Hbits" |]. iSplitL "Hbs"; [iExact "Hbs" |].
      iSplitR; [iExact "Hka" |]. iSplitL "Hpt"; [iExact "Hpt" |].
      iSplitL "Hpriv"; [iExact "Hpriv" |]. iSplitL "Hpath"; [iExact "Hpath" |].
      iSplitL "Hargv"; [iExact "Hargv" |]. iSplitL "Hargs"; [iExact "Hargs" |].
      iSplitL "Helf"; [iExact "Helf" | iExact "Hfr"].
  Qed.

End KexecB3Incr.

(* ===================================================================== *)
(*  +0x12c .. +0x128 -- ONE WHOLE ITERATION.                              *)
(* ===================================================================== *)
(*    sd   a3,-504(s0)     off -> slot 63                                  *)
(*    mv   a4,s11 ; addi a2,s0,-488 ; li a1,0 ; mv a0,s4                   *)
(*    jal  readi           the 56-byte program header                      *)
(*    bne  a0,s11,+0x320   short read -> bad:                              *)
(*    lw   a5,-488(s0) ; li a4,1 ; bne a5,a4,+0x11a   not PT_LOAD          *)
(*    ld   s1,-448(s0) ; ld a5,-456(s0) ; bltu s1,a5,+0x340  memsz<filesz  *)
(*    ld   a5,-472(s0) ; add s1,s1,a5 ; bltu s1,a5,+0x346    wrap          *)
(*    ld   a4,-536(s0) ; and a5,a5,a4 ; bnez a5,+0x34c       misaligned    *)
(*    lw   a0,-484(s0) ; jal flags2perm                                    *)
(*    mv a3,a0 ; mv a2,s1 ; mv a1,s2 ; mv a0,s6 ; jal uvmalloc             *)
(*    sd   a0,-520(s0) ; beqz a0,+0x352                      out of memory *)
(*    lw   s3,-456(s0) ; beqz s3,+0x19c                      empty segment *)
(*    ld   s8,-472(s0) ; lw s7,-480(s0) ; li s1,0 ; j +0xf6   loadseg      *)
(*                                                                         *)
(*  FOUR OF THE SIX BRANCHES ARE BLIND SPLITS.  memsz<filesz, the wrap     *)
(*  test, the page-alignment test and the PT_LOAD test all compare fields  *)
(*  read out of an untrusted file, and NEITHER arm of any of them needs to *)
(*  know which way it went: the [bad:] arm frees the table and returns -1, *)
(*  the other carries on.  That is why this loop has no premise about the  *)
(*  program header table at all.                                          *)
(* ===================================================================== *)
Section KexecB3Body.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ, !irefslotG Σ, !pavG Σ}.
  Context `{GEN : GenId}.

  Notation Rra := (mword_of_int 1 : mword 5).
  Notation Rtp := (mword_of_int 4 : mword 5).
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
  Notation Ra2 := (mword_of_int 12 : mword 5).
  Notation Ra3 := (mword_of_int 13 : mword 5).
  Notation Ra4 := (mword_of_int 14 : mword 5).
  Notation Ra5 := (mword_of_int 15 : mword 5).

  Local Ltac bnz := vm_compute; discriminate.
  Local Ltac bpcw := apply bv_eq; vm_compute; reflexivity.
  Local Ltac bs0slot := apply stk_push; apply bv_eq; vm_compute; reflexivity.


  Lemma kxc_ph_step `{CID0 : CpuId}
      (Q : mword 64 -> Prop)
      (gs : list gname) (jp : nat) (gl : gname)
      (gu : uart_names) (gd : disk_names) (gk : gname) (pd pav pu : mword 64)
      (bn : bio_names) (g : log_names) (gfs : fs_names) (gi : gname)
      (cn : ic_names) (gtl : gname) (gilf gislf : gname) (ga gf : gname)
      (cov : gset Z) (logstart bmapstart inodestart : Z) (nib : nat)
      (size : Z) (dev : mword 32)
      (kf : nat) (qf sf : Qp) (gyf : gname) (inumf : mword 32)
      (dnf : dinode) (bmf : blkmap) (n2 : nat)
      (plen : nat) (pfun : nat -> bv 8)
      (na : nat) (avf : nat -> mword 64) (alen aslen : nat -> nat)
      (afun : nat -> nat -> bv 8)
      (pidv : mword 32) (V : pprivate) (eb : bool) (dqb dqs dqa dqpv dqas : dfrac)
      (m M : regfile) (K : nat)
      (sp0 ra0 s00 s10 s20 pv av w67 : mword 64)
      (ef : nat -> bv 8) (P : uptd) (i : nat) (szv : mword 64) :
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
    (jp < NPROC)%nat ->
    gs !! jp = Some gl ->
    dev = icfg_dev ->
    m !!! Regidx csp_rs1 = sp0 ->
    m !!! Regidx Rra = ra0 ->
    m !!! Regidx Rs0 = s00 ->
    m !!! Regidx Rs1 = s10 ->
    m !!! Regidx Rs2 = s20 ->
    kernel_text -∗
    fs_fabric gs gu gd gk pd pav pu bn g gfs gi cn gtl
              cov logstart inodestart nib dev -∗
    kxc_at_12c jp bn g gfs gi cn ga gf cov logstart bmapstart inodestart nib
               size dev kf qf sf gyf inumf dnf bmf gilf gislf n2
               plen pfun na avf aslen afun pidv V eb dqb dqs dqa dqpv dqas m M K
               sp0 ra0 s00 s10 s20 pv av
               (m !!! Regidx Rs3) (m !!! Regidx Rs4) (m !!! Regidx Rs5)
               (m !!! Regidx Rs6) (m !!! Regidx Rs7) (m !!! Regidx Rs8)
               (m !!! Regidx Rs9) (m !!! Regidx Rs10) (m !!! Regidx Rs11)
               w67 ef P i szv -∗
    (* ---- kexec's OWN continuation: the five [bad:] exits close it ---- *)
    wp_next true (proc_addr jp) (fun (CID : CpuId) =>
      ∀ (mf : regfile) (V' : pprivate)
        (entry spv szv' : mword 64),
          ⌜callee_saved m mf⌝ -∗
          ⌜kexec_ok_q Q V V' (mf !!! Regidx Ra0) entry spv szv' na alen⌝ -∗
          sie_cap_gpr KT1 mf K eb (proc_addr jp) -∗
          cpu_own 0 eb (proc_addr jp) eb ∅ -∗
          trap_csrs_ext KT1 eb -∗
          cpu_claim_ext eb (proc_addr jp) -∗
          pc_is (ret_pc ra0) -∗
          sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
          sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
          kalloc_env ga None -∗
          proc_priv gf (proc_addr jp) pidv V' -∗
          ([∗ list] k ∈ seq 0 (S plen), pa_add pv k ↦ₘ[KT1]{dqpv} pfun k) -∗
          ([∗ list] k ∈ seq 0 (S na), pa_add av (8 * k) ↦₈[KT1]{dqa} avf k) -∗
          ([∗ list] k ∈ seq 0 na,
             [∗ list] j ∈ seq 0 (aslen k), pa_add (avf k) j ↦ₘ{dqas} afun k j) -∗
          bslots 3 -∗
          iref_slots 2 -∗
          WP (Loop : expr riscv_lang)) -∗
    (* ---- THE ONE OUTPUT: the back edge's verdict, and the exit back ---- *)
    wp_next true (proc_addr jp) (fun (CID : CpuId) =>
      ∀ (M' : regfile) (P' : uptd) (szv' : mword 64),
        ( kxc_at_12c jp bn g gfs gi cn ga gf cov logstart bmapstart inodestart
                     nib size dev kf qf sf gyf inumf dnf bmf
                     gilf gislf n2 plen pfun na avf aslen afun pidv V eb
                     dqb dqs dqa dqpv dqas m M' K sp0 ra0 s00 s10 s20 pv av
                     (m !!! Regidx Rs3) (m !!! Regidx Rs4) (m !!! Regidx Rs5)
                     (m !!! Regidx Rs6) (m !!! Regidx Rs7) (m !!! Regidx Rs8)
                     (m !!! Regidx Rs9) (m !!! Regidx Rs10) (m !!! Regidx Rs11)
                     w67 ef P' (S i) szv'
          ∨ kxc_at_1a4 jp bn g gfs gi cn ga gf cov logstart bmapstart inodestart
                       nib size dev kf qf sf gyf inumf dnf bmf
                       gilf gislf n2 plen pfun na avf aslen afun pidv V eb
                       dqb dqs dqa dqpv dqas M' K sp0 ra0 s00 s10 s20 pv av
                       (m !!! Regidx Rs3) (m !!! Regidx Rs4) (m !!! Regidx Rs5)
                       (m !!! Regidx Rs6) (m !!! Regidx Rs7) (m !!! Regidx Rs8)
                       (m !!! Regidx Rs9) (m !!! Regidx Rs10)
                       (m !!! Regidx Rs11) w67 ef P' szv' ) -∗
        wp_next (CID0 := CID) true (proc_addr jp) (fun (CIDy : CpuId) =>
          ∀ (mf : regfile) (V' : pprivate)
            (entry spv szv2 : mword 64),
              ⌜callee_saved m mf⌝ -∗
              ⌜kexec_ok_q Q V V' (mf !!! Regidx Ra0) entry spv szv2 na alen⌝ -∗
              sie_cap_gpr KT1 mf K eb (proc_addr jp) -∗
              cpu_own 0 eb (proc_addr jp) eb ∅ -∗
              trap_csrs_ext KT1 eb -∗
              cpu_claim_ext eb (proc_addr jp) -∗
              pc_is (ret_pc ra0) -∗
              sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
              sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
              kalloc_env ga None -∗
              proc_priv gf (proc_addr jp) pidv V' -∗
              ([∗ list] k ∈ seq 0 (S plen), pa_add pv k ↦ₘ[KT1]{dqpv} pfun k) -∗
              ([∗ list] k ∈ seq 0 (S na), pa_add av (8 * k) ↦₈[KT1]{dqa} avf k) -∗
              ([∗ list] k ∈ seq 0 na,
                 [∗ list] j ∈ seq 0 (aslen k), pa_add (avf k) j ↦ₘ{dqas} afun k j) -∗
              bslots 3 -∗
              iref_slots 2 -∗
              WP (Loop : expr riscv_lang)) -∗
        WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros HK Hk Hlg Hsz Hbm0 Hbmc Hbml Hins0 Hcovb Hiregb Hjp Hgs Hdevc
           Hsp Hra Hs0 Hs1 Hs2.
    pose proof HK as HK'. 
    assert (Hmb : (Z.of_nat MAXFILE * Z.of_nat BSIZE = 274432)%Z)
      by (vm_compute; reflexivity).
    iIntros "#Htext #Hfab Hst Hcont Hout".
    rewrite /kxc_at_12c.
    iDestruct "Hst" as "((%HMsp & %HMs0 & %HMs2 & %HMs4 & %HMs5 & %HMs6 &
                          %HMs9 & %HMs10 & %HMs11 & %HMa3) &
                         (%Hk2 & %Hib & %Hn2 & %Hal) &
                         (%Hiphn & %HPtfp & %Hbelow & %Hcov) &
                         Hpc & Hcg & Hcnt & Hextc & Hclmc & Hopen & Hlog & Hirs & Hbm & Hins &
                         Hbits & Hbs & #Hka & Hpt & Hpriv & Hpath & Hargv &
                         Hargs & Helf & Hframe)".
    destruct (Hiregb inumf Hib) as [Hibc Hibl].
    iDestruct "Hfab" as "(#Hkd & #Hpenv & #Hbio & #Hlogc & #Hcrash & #Hcert & #Hitab & #Hitinv &
                          #Hesc & #Hslks & #Hireg & #Hropen & #Hprocs & #Hdevi & #Hdgeom &
                          #Hdlock)".
    iDestruct (proc_pt_wf_get with "Hpt") as %Hwf.
    pose proof (proc_pt_covered_maxsz P szv Hwf Hcov) as Hmax.
    rewrite /kxc_frameB.
    iDestruct "Hframe" as "(Hf1 & Hf2 & Hf3 & Hf4 & Hf5 & Hf6 & Hf7 & Hf8 &
                            Hf9 & Hf10 & Hf11 & Hf12 & Hf13 & Hust & Hmid &
                            Hf64 & Hf65e & Hf66 & Hf67 & Hf68e)".
    iDestruct "Hf65e" as (w65) "Hf65".
    iDestruct "Hf68e" as (w68) "Hf68".
    iEval (rewrite kxc_slot63_split) in "Hmid".
    iDestruct "Hmid" as "(Hph8 & Hf63e)". iDestruct "Hf63e" as (w63) "Hf63".
    iDestruct (kxc_ph8_of_stack sp0 with "Hph8") as "(Hph7 & Hf62e)".
    iDestruct "Hf62e" as (w62) "Hf62".
    iDestruct (kxc_ph_take sp0 with "Hph7") as "[%Hphal Hphbe]".
    iDestruct "Hphbe" as (phb) "Hphb".
    (* the [ph] buffer's per-field alignment, once *)
    assert (Hpa0 : is_aligned_paddr (Physaddr (pa_add (pa_stk sp0 61) 0)) 4 = true).
    { rewrite kxc_ph_o0. apply aligned8_aligned4.
      pose proof (Hphal 0%nat ltac:(lia)) as Hx; cbn in Hx; exact Hx. }
    assert (Hpa4 : is_aligned_paddr (Physaddr (pa_add (pa_stk sp0 61) 4)) 4 = true).
    { apply aligned8_aligned4_hi.
      pose proof (Hphal 0%nat ltac:(lia)) as Hx; cbn in Hx; exact Hx. }
    assert (Hpa8 : is_aligned_paddr (Physaddr (pa_add (pa_stk sp0 61) 8)) 4 = true).
    { rewrite kxc_ph_o8. apply aligned8_aligned4.
      pose proof (Hphal 1%nat ltac:(lia)) as Hx; cbn in Hx; exact Hx. }
    assert (Hpa16 : is_aligned_paddr (Physaddr (pa_add (pa_stk sp0 61) 16)) 8 = true).
    { rewrite kxc_ph_o16.
      pose proof (Hphal 2%nat ltac:(lia)) as Hx; cbn in Hx; exact Hx. }
    assert (Hpa32 : is_aligned_paddr (Physaddr (pa_add (pa_stk sp0 61) 32)) 8 = true).
    { rewrite kxc_ph_o32.
      pose proof (Hphal 4%nat ltac:(lia)) as Hx; cbn in Hx; exact Hx. }
    assert (Hpa32w : is_aligned_paddr (Physaddr (pa_add (pa_stk sp0 61) 32)) 4 = true)
      by (apply aligned8_aligned4; exact Hpa32).
    assert (Hpa40 : is_aligned_paddr (Physaddr (pa_add (pa_stk sp0 61) 40)) 8 = true).
    { rewrite kxc_ph_o40.
      pose proof (Hphal 5%nat ltac:(lia)) as Hx; cbn in Hx; exact Hx. }
    (* ---- +0x12c: sd a3,-504(s0) -- [off] into slot 63 ---- *)
    assert (Hpa63 : add_vec (rget M Rs0)
                      (sign_extend' 64 (mword_of_int 3592 : mword 12))
                    = pa_stk sp0 63).
    { rewrite (rget_ne M Rs0 ltac:(bnz)) HMs0. bs0slot. }
    assert (Hsta3 : rget M Ra3 = kxc_off ef i)
      by (rewrite (rget_ne M Ra3 ltac:(bnz)); exact HMa3).
    iEval (rewrite -Hpa63) in "Hf63".
    iApply (wp_sd_s_sconf (mword_of_int (KXB + 0x12c)) Ra3 Rs0
              (mword_of_int 3592 : mword 12) M (K - 68)%nat w63 eb
              with "Hcg Hpc [] Hf63").
    { iApply (kxc_12c with "Htext"). }
    iIntros (CIDa Hsqa) "Hcg Hpc Hf63".
    iEval (rewrite Hpa63 Hsta3) in "Hf63".
    assert (Hpp130 : add_vec_int (mword_of_int (KXB + 0x12c) : mword 64) 4
                     = mword_of_int (KXB + 0x130)) by bpcw.
    iEval (rewrite Hpp130) in "Hpc".
    (* ---- +0x130: c.mv a4,s11 -- n = sizeof(struct proghdr) ---- *)
    iApply (wp_cmv_s_sconf (mword_of_int (KXB + 0x130)) Ra4 Rs11
              M (K - 68)%nat eb ltac:(bnz) ltac:(rdok) with "Hcg Hpc []").
    { iApply (kxc_130 with "Htext"). }
    iIntros (CIDb Hsqb) "Hcg Hpc". iEval (rgne) in "Hcg".
    set (U1 := <[Regidx Ra4 := regval_into_reg
                  (add_vec zero_reg (M !!! Regidx Rs11))]> M).
    assert (HU1a4 : U1 !!! Regidx Ra4 = (mword_of_int 56 : mword 64)).
    { rewrite /U1 upd_eq HMs11. apply w32_zero_add. }
    assert (HU1s0 : U1 !!! Regidx Rs0 = sp0)
      by (rewrite /U1 upd_ne; [exact HMs0 | bnz]).
    assert (HU1s4 : U1 !!! Regidx Rs4 = ientry kf)
      by (rewrite /U1 upd_ne; [exact HMs4 | bnz]).
    assert (Hpp132 : add_vec_int (mword_of_int (KXB + 0x130) : mword 64) 2
                     = mword_of_int (KXB + 0x132)) by bpcw.
    iEval (rewrite Hpp132) in "Hpc".
    (* ---- +0x132: addi a2,s0,-488 -- &ph ---- *)
    assert (Hphbase : add_vec (rget U1 Rs0)
                        (sign_extend' 64 (mword_of_int 3608 : mword 12))
                      = pa_stk sp0 61).
    { rewrite (rget_ne U1 Rs0 ltac:(bnz)) HU1s0. bs0slot. }
    iApply (wp_addi4_s_sconf (mword_of_int (KXB + 0x132)) Ra2 Rs0
              (mword_of_int 3608 : mword 12) U1 (K - 68)%nat eb
              ltac:(bnz) ltac:(rdok) with "Hcg Hpc []").
    { iApply (kxc_132 with "Htext"). }
    iIntros (CIDc Hsqc) "Hcg Hpc". iEval (rewrite Hphbase) in "Hcg".
    set (U2 := <[Regidx Ra2 := regval_into_reg (pa_stk sp0 61)]> U1).
    assert (HU2a2 : U2 !!! Regidx Ra2 = pa_stk sp0 61)
      by (rewrite /U2; apply upd_eq).
    assert (HU2a4 : U2 !!! Regidx Ra4 = (mword_of_int 56 : mword 64))
      by (rewrite /U2 upd_ne; [exact HU1a4 | bnz]).
    assert (HU2s4 : U2 !!! Regidx Rs4 = ientry kf)
      by (rewrite /U2 upd_ne; [exact HU1s4 | bnz]).
    assert (Hpp136 : add_vec_int (mword_of_int (KXB + 0x132) : mword 64) 4
                     = mword_of_int (KXB + 0x136)) by bpcw.
    iEval (rewrite Hpp136) in "Hpc".
    (* ---- +0x136: c.li a1,0 -- THE KERNEL ARM of readi ---- *)
    iApply (wp_cli_s_sconf (mword_of_int (KXB + 0x136)) Ra1
              (mword_of_int 0 : mword 6) (mword_of_int 0 : mword 64)
              U2 (K - 68)%nat eb ltac:(bnz) ltac:(rdok)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc []").
    { iApply (kxc_136 with "Htext"). }
    iIntros (CIDd Hsqd) "Hcg Hpc".
    set (U3 := <[Regidx Ra1 := regval_into_reg (mword_of_int 0 : mword 64)]> U2).
    assert (HU3a1 : U3 !!! Regidx Ra1 = (mword_of_int 0 : mword 64))
      by (rewrite /U3; apply upd_eq).
    assert (HU3a2 : U3 !!! Regidx Ra2 = pa_stk sp0 61)
      by (rewrite /U3 upd_ne; [exact HU2a2 | bnz]).
    assert (HU3a4 : U3 !!! Regidx Ra4 = (mword_of_int 56 : mword 64))
      by (rewrite /U3 upd_ne; [exact HU2a4 | bnz]).
    assert (HU3s4 : U3 !!! Regidx Rs4 = ientry kf)
      by (rewrite /U3 upd_ne; [exact HU2s4 | bnz]).
    assert (Hpp138 : add_vec_int (mword_of_int (KXB + 0x136) : mword 64) 2
                     = mword_of_int (KXB + 0x138)) by bpcw.
    iEval (rewrite Hpp138) in "Hpc".
    (* ---- +0x138: c.mv a0,s4 ---- *)
    iApply (wp_cmv_s_sconf (mword_of_int (KXB + 0x138)) Ra0 Rs4
              U3 (K - 68)%nat eb ltac:(bnz) ltac:(rdok) with "Hcg Hpc []").
    { iApply (kxc_138 with "Htext"). }
    iIntros (CIDe Hsqe) "Hcg Hpc". iEval (rgne) in "Hcg".
    set (U4 := <[Regidx Ra0 := regval_into_reg
                  (add_vec zero_reg (U3 !!! Regidx Rs4))]> U3).
    assert (Hpp13a : add_vec_int (mword_of_int (KXB + 0x138) : mword 64) 2
                     = mword_of_int (KXB + 0x13a)) by bpcw.
    iEval (rewrite Hpp13a) in "Hpc".
    (* ---- +0x13a: jal ra,readi ---- *)
    assert (Htrd : add_vec (mword_of_int (KXB + 0x13a) : mword 64)
                     (sign_extend' 64 (mword_of_int 2092258 : mword 21))
                   = mword_of_int KernelSyms.readi) by bpcw.
    iApply (wp_jal_s_sconf (mword_of_int (KXB + 0x13a)) Rra
              (mword_of_int 2092258 : mword 21) U4 (K - 68)%nat eb
              ltac:(bnz) ltac:(rdok)
              ltac:(rewrite Htrd; vm_compute; reflexivity)
              with "Hcg Hpc []").
    { iApply (kxc_13a with "Htext"). }
    iIntros (CIDf Hsqf) "Hcg Hpc". iEval (rewrite Htrd) in "Hpc".
    set (U5 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (KXB + 0x13a) : mword 64) 4)]> U4).
    change (<[Regidx Rra := regval_into_reg
              (add_vec_int (mword_of_int (KXB + 0x13a) : mword 64) 4)]> U4)
      with U5.
    assert (HU5ra : U5 !!! Regidx Rra
              = add_vec_int (mword_of_int (KXB + 0x13a) : mword 64) 4)
      by (rewrite /U5; apply upd_eq).
    assert (HU5a0 : U5 !!! Regidx Ra0 = ientry kf).
    { rewrite /U5 upd_ne; [| bnz]. rewrite /U4 upd_eq HU3s4.
      apply w32_zero_add. }
    assert (HU5a1 : U5 !!! Regidx Ra1 = (mword_of_int 0 : mword 64)).
    { rewrite /U5 upd_ne; [| bnz]. rewrite /U4 upd_ne; [exact HU3a1 | bnz]. }
    assert (HU5a2 : U5 !!! Regidx Ra2 = pa_stk sp0 61).
    { rewrite /U5 upd_ne; [| bnz]. rewrite /U4 upd_ne; [exact HU3a2 | bnz]. }
    assert (HU5a4 : U5 !!! Regidx Ra4 = (mword_of_int 56 : mword 64)).
    { rewrite /U5 upd_ne; [| bnz]. rewrite /U4 upd_ne; [exact HU3a4 | bnz]. }
    assert (HU5get : forall r : mword 5, is_cs_idx r = true ->
              U5 !!! Regidx r = M !!! Regidx r).
    { intros r Hr. rewrite /U5 upd_ne; [| reg_ne_side].
      rewrite /U4 upd_ne; [| reg_ne_side]. rewrite /U3 upd_ne; [| reg_ne_side].
      rewrite /U2 upd_ne; [| reg_ne_side]. rewrite /U1 upd_ne; [| reg_ne_side].
      reflexivity. }
    (* ---- the [off] argument, as [SpecReadi]'s ABI uint ---- *)
    set (offz := ((ph_at ef i) `mod` 2 ^ 32)%Z).
    assert (Hphat0 : (0 <= ph_at ef i)%Z).
    { unfold ph_at. pose proof (eh_phoff_bound ef). lia. }
    assert (Hoffr : (0 <= offz < 2 ^ 32)%Z)
      by (rewrite /offz; apply Z.mod_pos_bound; lia).
    set (offn := Z.to_nat offz).
    assert (HoffnZ : Z.of_nat offn = offz) by (rewrite /offn Z2Nat.id; lia).
    assert (HU5a3 : U5 !!! Regidx Ra3
              = sign_extend' 64 (mword_of_int (Z.of_nat offn) : mword 32)).
    { rewrite /U5 upd_ne; [| bnz]. rewrite /U4 upd_ne; [| bnz].
      rewrite /U3 upd_ne; [| bnz]. rewrite /U2 upd_ne; [| bnz].
      rewrite /U1 upd_ne; [| bnz]. rewrite HMa3 kxc_off_alt HoffnZ /offz.
      symmetry. apply w32_arg_mod. }
    assert (HU5a4' : U5 !!! Regidx Ra4
              = sign_extend' 64 (mword_of_int (Z.of_nat 56%nat) : mword 32)).
    { rewrite HU5a4. change (Z.of_nat 56%nat) with 56%Z.
      apply (w32_moi_arg 56); lia. }
    (* ---- what readi borrows ---- *)
    iDestruct "Hopen" as "(#Hslkk & Hslkd & Hdep & Hidev & Hiinum &
                           Hivalid & Hload & #Hity & Hfrz & Hkeep & Hru)".
    iDestruct (kxc_load_peel with "Hload") as
      (datl) "(%Hiok & %Hdok & %Hddix & %Hdoc & %Hduq & Hdlk & Hdiat & Hmeta & Hmap
               & Hblocks & Hdview & Hfview)".
    pose proof Hiok as Hiok'.
    destruct Hiok' as (Hbmwf & Hbmcov & Hdaddr & Hdty & Hszb & Hholes & Hsized).
    iDestruct (proc_priv_bare_acc gf (proc_addr jp) pidv V with "Hpriv")
      as "[Hppid Hpvbk]".
    iDestruct (A.kxa_bs3_split with "Hbs") as "[Hbs1 Hbs2]".
    iDestruct (cpu_own_transport CID0 CIDf 0%nat eb (proc_addr jp) eb
                 ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
    iDestruct (trap_csrs_ext_transport CID0 CIDf eb (proc_addr jp)
                 ltac:(try rewrite Hebb; wp_next_chain) with "Hextc") as "Hextc".
    iDestruct (cpu_claim_ext_transport CID0 CIDf eb (proc_addr jp)
                 ltac:(try rewrite Hebb; wp_next_chain) with "Hclmc") as "Hclmc".
    iEval (rewrite -HU5a2) in "Hphb".
    iApply (Readi.wp_readi_sconf KT1 gs jp gl gu gd gk pd pav pu bn gfs ga gf
              cov logstart dev (ientry kf) bmf datl dnf false offn 56%nat phb V
              pidv (DfracOwn (1/4)) (DfracOwn (1/2)) U5 (K - 68)%nat eb
              eb ∅ ltac:(lia) Hlg Hbmwf Hbmcov Hszb
              ltac:(rewrite HoffnZ; lia)
              ltac:(intros Hg; rewrite HoffnZ in Hg |- *;
                    pose proof Hszb as Hs; rewrite Hmb in Hs;
                    change (Z.of_nat 56%nat) with 56%Z;
                    change (2 ^ 32)%Z with 4294967296%Z; lia)
              Hjp Hgs HU5a0
              ltac:(rewrite HU5a1; vm_compute; reflexivity) HU5a3 HU5a4'
              with "Hcg Hcnt Hextc Hclmc Htext Hkd Hpc Hpenv Hbio Hka Hidev Hmeta Hmap
                    Hblocks [Hphb Hppid] Hprocs Hdevi Hdgeom Hdlock Hbs1").
    all: try lkbelow.
    { iSplitL "Hphb"; [iExact "Hphb" | iExact "Hppid"]. }
    iIntros (CIDrd Hsrd M2 tot Pr) "%Hcsrd %Huptr %Htotb %Hret Hcg Hcnt Hextc Hclmc Hpc
             Hidev Hmeta Hmap Hblocks [Hphb Hppid] Hbs1".
    assert (Hpc13e : ret_pc (U5 !!! Regidx Rra) = mword_of_int (KXB + 0x13e))
      by (rewrite HU5ra; bpcw).
    iEval (rewrite Hpc13e) in "Hpc".
    iEval (rewrite HU5a2) in "Hphb".
    iDestruct ("Hpvbk" with "Hppid") as "Hpriv".
    iDestruct (kxc_load_seal gfs gi cov logstart kf inumf dnf bmf datl
                 Hiok Hdok Hddix Hdoc Hduq
                 with "Hdlk Hdiat Hmeta Hmap Hblocks Hdview Hfview") as "Hload".
    iDestruct (A.kxa_bs3_join with "Hbs1 Hbs2") as "Hbs".
    iDestruct (kxc_open_intro gfs gi cn cov logstart dev pidv kf qf sf gyf
                 inumf dnf bmf gilf gislf
                 with "Hslkk Hslkd Hdep Hidev Hiinum Hivalid Hload
                       Hity Hfrz Hkeep Hru") as "Hopen".
    set (pf := rd_delivered datl phb offn tot).
    assert (HM2get : forall r : mword 5, is_cs_idx r = true ->
              M2 !!! Regidx r = M !!! Regidx r).
    { intros r Hr. rewrite (callee_saved_lookup Hcsrd r Hr).
      exact (HU5get r Hr). }
    assert (HM2sp : M2 !!! Regidx csp_rs1 = pa_stk sp0 68)
      by (rewrite (HM2get csp_rs1 ltac:(vm_compute; reflexivity)); exact HMsp).
    assert (HM2s0 : M2 !!! Regidx Rs0 = sp0)
      by (rewrite (HM2get Rs0 ltac:(vm_compute; reflexivity)); exact HMs0).
    assert (HM2s2 : M2 !!! Regidx Rs2 = szv)
      by (rewrite (HM2get Rs2 ltac:(vm_compute; reflexivity)); exact HMs2).
    assert (HM2s4 : M2 !!! Regidx Rs4 = ientry kf)
      by (rewrite (HM2get Rs4 ltac:(vm_compute; reflexivity)); exact HMs4).
    assert (HM2s5 : M2 !!! Regidx Rs5 = (mword_of_int 4096 : mword 64))
      by (rewrite (HM2get Rs5 ltac:(vm_compute; reflexivity)); exact HMs5).
    assert (HM2s6 : M2 !!! Regidx Rs6 = page_base P.(ud_root))
      by (rewrite (HM2get Rs6 ltac:(vm_compute; reflexivity)); exact HMs6).
    assert (HM2s9 : M2 !!! Regidx Rs9 = (mword_of_int 4096 : mword 64))
      by (rewrite (HM2get Rs9 ltac:(vm_compute; reflexivity)); exact HMs9).
    assert (HM2s10 : M2 !!! Regidx Rs10 = (mword_of_int (Z.of_nat i) : mword 64))
      by (rewrite (HM2get Rs10 ltac:(vm_compute; reflexivity)); exact HMs10).
    assert (HM2s11 : M2 !!! Regidx Rs11 = (mword_of_int 56 : mword 64))
      by (rewrite (HM2get Rs11 ltac:(vm_compute; reflexivity)); exact HMs11).
    assert (HM2a0 : M2 !!! Regidx Ra0 = (mword_of_int (Z.of_nat tot) : mword 64)).
    { destruct Hret as [(_ & Hbad) | (Hv & _)]; [discriminate Hbad | exact Hv]. }
    assert (Htotle : (Z.of_nat tot <= 274432)%Z).
    { rewrite /rd_clamp in Htotb.
      pose proof (bv_unsigned_in_range 32 (di_size dnf)) as [Hsz0 _].
      assert (Hszn : (Z.of_nat (Z.to_nat (bv_unsigned (di_size dnf)))
                      <= 274432)%Z)
        by (rewrite Z2Nat.id; [rewrite -Hmb; exact Hszb | exact Hsz0]).
      destruct (decide (Z.to_nat (bv_unsigned (di_size dnf))
                        < offn + 56)%nat); lia. }
    (* ---- +0x13e: bne a0,s11 -- a short read is a malformed file ---- *)
    assert (Hcmp13e : neq_vec (rget M2 Ra0) (rget M2 Rs11)
                      = negb (Z.eqb (Z.of_nat tot) 56)).
    { rewrite (rget_ne M2 Ra0 ltac:(bnz)) (rget_ne M2 Rs11 ltac:(bnz))
              HM2a0 HM2s11.
      apply w32_neq_moi; change (2 ^ 64)%Z with 18446744073709551616%Z; lia. }
    assert (Htgt320 : add_vec (mword_of_int (KXB + 0x13e) : mword 64)
                        (sign_extend' 64 (mword_of_int 482 : mword 13))
                      = mword_of_int (KXB + 0x320)) by bpcw.
    destruct (decide (tot = 56%nat)) as [Htot56 | Htot56].
    - (* ================ THE HEADER ARRIVED ======================== *)
      iApply (wp_bne_fall_s_sconf (mword_of_int (KXB + 0x13e))
                (mword_of_int 482 : mword 13) Rs11 Ra0 M2 (K - 68)%nat eb
                ltac:(bnz) ltac:(bnz)
                ltac:(rewrite Hcmp13e Htot56; reflexivity)
                with "Hcg Hpc []").
      { iApply (kxc_13e with "Htext"). }
      iIntros (CIDg1 Hsg1) "Hcg Hpc".
      assert (Hpp142 : add_vec_int (mword_of_int (KXB + 0x13e) : mword 64) 4
                       = mword_of_int (KXB + 0x142)) by bpcw.
      iEval (rewrite Hpp142) in "Hpc".
      (* ---- +0x142: lw a5,-488(s0) -- ph.type ---- *)
      assert (Hph61 : add_vec (rget M2 Rs0)
                        (sign_extend' 64 (mword_of_int 3608 : mword 12))
                      = pa_add (pa_stk sp0 61) 0).
      { rewrite (rget_ne M2 Rs0 ltac:(bnz)) HM2s0 kxc_ph_o0. bs0slot. }
      iDestruct (kxc_win4 (pa_stk sp0 61) pf 0 52 56 ltac:(lia) Hpa0
                   with "Hphb") as "[Hw Hbk]".
      iEval (rewrite -Hph61) in "Hw".
      iApply (wp_lw_s_sconf (mword_of_int (KXB + 0x142)) Ra5 Rs0
                (mword_of_int 3608 : mword 12) M2 (K - 68)%nat
                (Z_to_bv 32 (le_at pf 0 4) : mword 32) eb
                (dqm := DfracOwn 1) ltac:(bnz) ltac:(rdok)
                with "Hcg Hpc [] Hw").
      { iApply (kxc_142 with "Htext"). }
      iIntros (CIDg2 Hsg2) "Hcg Hpc Hw". iEval (rewrite Hph61) in "Hw".
      iDestruct ("Hbk" with "Hw") as "Hphb".
      set (U6 := <[Regidx Ra5 := regval_into_reg
                    (sign_extend' 64 (Z_to_bv 32 (le_at pf 0 4)
                                      : mword 32))]> M2).
      assert (Hpp146 : add_vec_int (mword_of_int (KXB + 0x142) : mword 64) 4
                       = mword_of_int (KXB + 0x146)) by bpcw.
      iEval (rewrite Hpp146) in "Hpc".
      (* ---- +0x146: c.li a4,1 -- ELF_PROG_LOAD ---- *)
      iApply (wp_cli_s_sconf (mword_of_int (KXB + 0x146)) Ra4
                (mword_of_int 1 : mword 6) (mword_of_int 1 : mword 64)
                U6 (K - 68)%nat eb ltac:(bnz) ltac:(rdok)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                with "Hcg Hpc []").
      { iApply (kxc_146 with "Htext"). }
      iIntros (CIDg3 Hsg3) "Hcg Hpc".
      set (U7 := <[Regidx Ra4 := regval_into_reg
                    (mword_of_int 1 : mword 64)]> U6).
      assert (HU7get : forall r : mword 5, is_cs_idx r = true ->
                U7 !!! Regidx r = M2 !!! Regidx r).
      { intros r Hr. rewrite /U7 upd_ne; [| reg_ne_side].
        rewrite /U6 upd_ne; [| reg_ne_side]. reflexivity. }
      assert (HU7sp : U7 !!! Regidx csp_rs1 = pa_stk sp0 68)
        by (rewrite (HU7get csp_rs1 ltac:(vm_compute; reflexivity)); exact HM2sp).
      assert (HU7s0 : U7 !!! Regidx Rs0 = sp0)
        by (rewrite (HU7get Rs0 ltac:(vm_compute; reflexivity)); exact HM2s0).
      assert (HU7s2 : U7 !!! Regidx Rs2 = szv)
        by (rewrite (HU7get Rs2 ltac:(vm_compute; reflexivity)); exact HM2s2).
      assert (HU7s4 : U7 !!! Regidx Rs4 = ientry kf)
        by (rewrite (HU7get Rs4 ltac:(vm_compute; reflexivity)); exact HM2s4).
      assert (HU7s5 : U7 !!! Regidx Rs5 = (mword_of_int 4096 : mword 64))
        by (rewrite (HU7get Rs5 ltac:(vm_compute; reflexivity)); exact HM2s5).
      assert (HU7s6 : U7 !!! Regidx Rs6 = page_base P.(ud_root))
        by (rewrite (HU7get Rs6 ltac:(vm_compute; reflexivity)); exact HM2s6).
      assert (HU7s9 : U7 !!! Regidx Rs9 = (mword_of_int 4096 : mword 64))
        by (rewrite (HU7get Rs9 ltac:(vm_compute; reflexivity)); exact HM2s9).
      assert (HU7s10 : U7 !!! Regidx Rs10
                       = (mword_of_int (Z.of_nat i) : mword 64))
        by (rewrite (HU7get Rs10 ltac:(vm_compute; reflexivity)); exact HM2s10).
      assert (HU7s11 : U7 !!! Regidx Rs11 = (mword_of_int 56 : mword 64))
        by (rewrite (HU7get Rs11 ltac:(vm_compute; reflexivity)); exact HM2s11).
      assert (Hpp148 : add_vec_int (mword_of_int (KXB + 0x146) : mword 64) 2
                       = mword_of_int (KXB + 0x148)) by bpcw.
      iEval (rewrite Hpp148) in "Hpc".
      (* ---- +0x148: bne a5,a4 -- a BLIND split on [ph.type] ---- *)
      assert (Htgt11a : add_vec (mword_of_int (KXB + 0x148) : mword 64)
                          (sign_extend' 64 (mword_of_int 8146 : mword 13))
                        = mword_of_int (KXB + 0x11a)) by bpcw.
      destruct (neq_vec (rget U7 Ra5) (rget U7 Ra4)) eqn:Ety.
      + (* ---- NOT PT_LOAD: nothing to do, take the back edge ---- *)
        iApply (wp_bne_taken_s_sconf (mword_of_int (KXB + 0x148))
                  (mword_of_int 8146 : mword 13) Ra4 Ra5 U7 (K - 68)%nat eb
                  ltac:(bnz) ltac:(bnz) ltac:(exact Ety)
                  ltac:(rewrite Htgt11a; vm_compute; reflexivity)
                  with "Hcg Hpc []").
        { iApply (kxc_148 with "Htext"). }
        iIntros (CIDg4 Hsg4). iNext. iIntros "Hcg Hpc".
        iEval (rewrite Htgt11a) in "Hpc".
        iDestruct (kxc_ph_give sp0 pf Hphal with "Hphb") as "Hph7".
        iDestruct (kxc_stack8_of_ph sp0 w62 with "Hph7 Hf62") as "Hph8".
        iDestruct (kxc_pin_intro sp0 ra0 s00 s10 s20 pv av
                     (m !!! Regidx Rs3) (m !!! Regidx Rs4) (m !!! Regidx Rs5)
                     (m !!! Regidx Rs6) (m !!! Regidx Rs7) (m !!! Regidx Rs8)
                     (m !!! Regidx Rs9) (m !!! Regidx Rs10) (m !!! Regidx Rs11)
                     (kxc_off ef i) w65 w67 w68
                     with "Hf1 Hf2 Hf3 Hf4 Hf5 Hf6 Hf7 Hf8 Hf9 Hf10 Hf11 Hf12
                           Hf13 Hust Hph8 Hf63 Hf64 Hf65 Hf66 Hf67 Hf68")
          as "Hframe".
        iDestruct (cpu_own_transport CIDrd CIDg4 0%nat eb (proc_addr jp)
                     eb ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
        iDestruct (trap_csrs_ext_transport CIDrd CIDg4 eb (proc_addr jp)
                     ltac:(try rewrite Hebb; wp_next_chain) with "Hextc") as "Hextc".
        iDestruct (cpu_claim_ext_transport CIDrd CIDg4 eb (proc_addr jp)
                     ltac:(try rewrite Hebb; wp_next_chain) with "Hclmc") as "Hclmc".
        iApply (kxc_incr (CID0 := CIDg4) jp bn g gfs gi cn ga gf cov logstart
                  bmapstart inodestart nib size dev kf qf sf gyf
                  inumf dnf bmf gilf gislf n2 plen pfun na avf aslen afun
                  pidv V eb dqb dqs dqa dqpv dqas m U7 K sp0 ra0 s00 s10 s20 pv av
                  (m !!! Regidx Rs3) (m !!! Regidx Rs4) (m !!! Regidx Rs5)
                  (m !!! Regidx Rs6) (m !!! Regidx Rs7) (m !!! Regidx Rs8)
                  (m !!! Regidx Rs9) (m !!! Regidx Rs10) (m !!! Regidx Rs11)
                  w65 w67 ef P i szv
                  with "Htext [-Hout Hcont] [Hout Hcont]").
        { rewrite /kxc_at_11a /kxc_res.
          iSplitR.
          { iPureIntro. split_and!;
              [exact HU7sp | exact HU7s0 | exact HU7s2 | exact HU7s4
              | exact HU7s5 | exact HU7s6 | exact HU7s9 | exact HU7s10
              | exact HU7s11]. }
          iSplitR.
          { iPureIntro. split_and!;
              [exact Hk2 | exact Hib | exact Hn2 | exact Hal]. }
          iSplitR.
          { iPureIntro. split_and!;
              [exact Hiphn | exact HPtfp | exact Hbelow | exact Hcov]. }
          iSplitL "Hpc"; [iExact "Hpc" |]. iSplitL "Hcg"; [iExact "Hcg" |].
          iSplitL "Hcnt"; [iExact "Hcnt" |].
          iSplitL "Hextc"; [iExact "Hextc" |]. iSplitL "Hclmc"; [iExact "Hclmc" |]. iSplitR; [iExact "Hka" |].
          iSplitL "Hopen"; [iExact "Hopen" |].
          iSplitL "Hlog"; [iExact "Hlog" |]. iSplitL "Hirs"; [iExact "Hirs" |].
          iSplitL "Hbm"; [iExact "Hbm" |]. iSplitL "Hins"; [iExact "Hins" |].
          iSplitL "Hbits"; [iExact "Hbits" |]. iSplitL "Hbs"; [iExact "Hbs" |].
          iSplitL "Hpt"; [iExact "Hpt" |]. iSplitL "Hpriv"; [iExact "Hpriv" |].
          iSplitL "Hpath"; [iExact "Hpath" |].
          iSplitL "Hargv"; [iExact "Hargv" |].
          iSplitL "Hargs"; [iExact "Hargs" |].
          iSplitL "Helf"; [iExact "Helf" | iExact "Hframe"]. }
        iIntros (CIDh Hsh M') "Hdisj".
        assert (Hcrh : true = false \/ proc_addr jp = zero_reg ->
                  (CIDh : CPU) = (CID0 : CPU)) by wp_next_chain.
        iDestruct (wp_next_retarget CID0 CIDh true (proc_addr jp) _ Hcrh
                     with "Hcont") as "Hcont".
        iSpecialize ("Hout" $! CIDh with "[%]"); [wp_next_chain |].
        iApply ("Hout" $! M' P szv with "Hdisj Hcont").
      + (* ================ PT_LOAD: load the segment ================ *)
        iApply (wp_bne_fall_s_sconf (mword_of_int (KXB + 0x148))
                  (mword_of_int 8146 : mword 13) Ra4 Ra5 U7 (K - 68)%nat eb
                  ltac:(bnz) ltac:(bnz) ltac:(exact Ety)
                  with "Hcg Hpc []").
        { iApply (kxc_148 with "Htext"). }
        iIntros (CIDg4 Hsg4) "Hcg Hpc".
        assert (Hpp14c : add_vec_int (mword_of_int (KXB + 0x148) : mword 64) 4
                         = mword_of_int (KXB + 0x14c)) by bpcw.
        iEval (rewrite Hpp14c) in "Hpc".
        (* ---- +0x14c: ld s1,-448(s0) -- ph.memsz ---- *)
        assert (Hph40 : add_vec (rget U7 Rs0)
                          (sign_extend' 64 (mword_of_int 3648 : mword 12))
                        = pa_add (pa_stk sp0 61) 40).
        { rewrite (rget_ne U7 Rs0 ltac:(bnz)) HU7s0 kxc_ph_o40. bs0slot. }
        iDestruct (kxc_win8 (pa_stk sp0 61) pf 40 8 56 ltac:(lia) Hpa40
                     with "Hphb") as "[Hw Hbk]".
        iEval (rewrite -Hph40) in "Hw".
        iApply (wp_ld_s_sconf (mword_of_int (KXB + 0x14c)) Rs1 Rs0
                  (mword_of_int 3648 : mword 12) U7 (K - 68)%nat
                  (Z_to_bv 64 (le_at pf 40 8) : mword 64) eb
                  (dqm := DfracOwn 1) ltac:(bnz) ltac:(rdok)
                  with "Hcg Hpc [] Hw").
        { iApply (kxc_14c with "Htext"). }
        iIntros (CIDg5 Hsg5) "Hcg Hpc Hw". iEval (rewrite Hph40) in "Hw".
        iDestruct ("Hbk" with "Hw") as "Hphb".
        set (U8 := <[Regidx Rs1 := regval_into_reg
                      (Z_to_bv 64 (le_at pf 40 8) : mword 64)]> U7).
        assert (HU8s0 : U8 !!! Regidx Rs0 = sp0)
          by (rewrite /U8 upd_ne; [exact HU7s0 | bnz]).
        assert (Hpp150 : add_vec_int (mword_of_int (KXB + 0x14c) : mword 64) 4
                         = mword_of_int (KXB + 0x150)) by bpcw.
        iEval (rewrite Hpp150) in "Hpc".
        (* ---- +0x150: ld a5,-456(s0) -- ph.filesz ---- *)
        assert (Hph32 : add_vec (rget U8 Rs0)
                          (sign_extend' 64 (mword_of_int 3640 : mword 12))
                        = pa_add (pa_stk sp0 61) 32).
        { rewrite (rget_ne U8 Rs0 ltac:(bnz)) HU8s0 kxc_ph_o32. bs0slot. }
        iDestruct (kxc_win8 (pa_stk sp0 61) pf 32 16 56 ltac:(lia) Hpa32
                     with "Hphb") as "[Hw Hbk]".
        iEval (rewrite -Hph32) in "Hw".
        iApply (wp_ld_s_sconf (mword_of_int (KXB + 0x150)) Ra5 Rs0
                  (mword_of_int 3640 : mword 12) U8 (K - 68)%nat
                  (Z_to_bv 64 (le_at pf 32 8) : mword 64) eb
                  (dqm := DfracOwn 1) ltac:(bnz) ltac:(rdok)
                  with "Hcg Hpc [] Hw").
        { iApply (kxc_150 with "Htext"). }
        iIntros (CIDg6 Hsg6) "Hcg Hpc Hw". iEval (rewrite Hph32) in "Hw".
        iDestruct ("Hbk" with "Hw") as "Hphb".
        set (U9 := <[Regidx Ra5 := regval_into_reg
                      (Z_to_bv 64 (le_at pf 32 8) : mword 64)]> U8).
        assert (HU9get : forall r : mword 5, is_cs_idx r = true -> r <> Rs1 ->
                  U9 !!! Regidx r = U7 !!! Regidx r).
        { intros r Hr Hne. rewrite /U9 upd_ne; [| reg_ne_side].
          rewrite /U8 upd_ne; [reflexivity | congruence]. }
        assert (HU9s0 : U9 !!! Regidx Rs0 = sp0)
          by (rewrite (HU9get Rs0 ltac:(vm_compute; reflexivity) ltac:(bnz));
              exact HU7s0).
        assert (Hpp154 : add_vec_int (mword_of_int (KXB + 0x150) : mword 64) 4
                         = mword_of_int (KXB + 0x154)) by bpcw.
        iEval (rewrite Hpp154) in "Hpc".
        (* ---- +0x154: bltu s1,a5 -- a BLIND split on memsz < filesz ---- *)
        assert (Htgt340 : add_vec (mword_of_int (KXB + 0x154) : mword 64)
                            (sign_extend' 64 (mword_of_int 492 : mword 13))
                          = mword_of_int (KXB + 0x340)) by bpcw.
        destruct (zopz0zI_u (rget U9 Rs1) (rget U9 Ra5)) eqn:Emf.
        * (* memsz < filesz -- malformed *)
          iApply (wp_bltu_taken_s_sconf (mword_of_int (KXB + 0x154))
                    (mword_of_int 492 : mword 13) Ra5 Rs1 U9 (K - 68)%nat eb
                    ltac:(bnz) ltac:(bnz) ltac:(exact Emf)
                    ltac:(rewrite Htgt340; vm_compute; reflexivity)
                    with "Hcg Hpc []").
          { iApply (kxc_154 with "Htext"). }
          iIntros (CIDx1 Hsx1). iNext. iIntros "Hcg Hpc".
          iEval (rewrite Htgt340) in "Hpc".
          (* ---- 0x340: sd s2,-520(s0) ; 0x344: c.j +0x324 ---- *)
          assert (Hbsp : U9 !!! Regidx csp_rs1 = pa_stk sp0 68)
            by (rewrite (HU9get csp_rs1 ltac:(vm_compute; reflexivity) ltac:(bnz));
                exact HU7sp).
          assert (Hbs0 : U9 !!! Regidx Rs0 = sp0)
            by (rewrite (HU9get Rs0 ltac:(vm_compute; reflexivity) ltac:(bnz));
                exact HU7s0).
          assert (Hbs2 : U9 !!! Regidx Rs2 = szv)
            by (rewrite (HU9get Rs2 ltac:(vm_compute; reflexivity) ltac:(bnz));
                exact HU7s2).
          assert (Hbs4 : U9 !!! Regidx Rs4 = ientry kf)
            by (rewrite (HU9get Rs4 ltac:(vm_compute; reflexivity) ltac:(bnz));
                exact HU7s4).
          assert (Hbs6 : U9 !!! Regidx Rs6 = page_base (ud_root P))
            by (rewrite (HU9get Rs6 ltac:(vm_compute; reflexivity) ltac:(bnz));
                exact HU7s6).
          assert (Hbpa : add_vec (rget U9 Rs0)
                           (sign_extend' 64 (mword_of_int 3576 : mword 12))
                         = pa_stk sp0 65)
            by (rewrite (rget_ne U9 Rs0 ltac:(bnz)) Hbs0; bs0slot).
          assert (Hbsv : rget U9 Rs2 = szv)
            by (rewrite (rget_ne U9 Rs2 ltac:(bnz)); exact Hbs2).
          iEval (rewrite -Hbpa) in "Hf65".
          iApply (wp_sd_s_sconf (mword_of_int (KXB + 0x340)) Rs2 Rs0
                    (mword_of_int 3576 : mword 12) U9 (K - 68)%nat w65 eb
                    with "Hcg Hpc [] Hf65").
          { iApply (kxc_340 with "Htext"). }
          iIntros (CIDy1 Hsy1) "Hcg Hpc Hf65".
          iEval (rewrite Hbpa Hbsv) in "Hf65".
          assert (Hbppj : add_vec_int (mword_of_int (KXB + 0x340) : mword 64) 4
                          = mword_of_int (KXB + 0x344)) by bpcw.
          iEval (rewrite Hbppj) in "Hpc".
          assert (Hbtgt : add_vec (mword_of_int (KXB + 0x344) : mword 64)
                            (sign_extend' 64 (sign_extend' 21
                               (concat_vec (mword_of_int 2032 : mword 11) ('b"0"))))
                          = mword_of_int (KXB + 0x324)) by bpcw.
          iApply (wp_cj_s_sconf (mword_of_int (KXB + 0x344))
                    (sign_extend' 21 (concat_vec (mword_of_int 2032 : mword 11) ('b"0")))
                    U9 (K - 68)%nat eb
                    ltac:(rewrite Hbtgt; vm_compute; reflexivity)
                    with "Hcg Hpc []").
          { iApply (kxc_344 with "Htext"). }
          iIntros (CIDy2 Hsy2). iNext. iIntros "Hcg Hpc".
          iEval (rewrite Hbtgt) in "Hpc".
          iDestruct (kxc_ph_give sp0 pf Hphal with "Hphb") as "Hph7".
          iDestruct (kxc_stack8_of_ph sp0 w62 with "Hph7 Hf62") as "Hph8".
          iDestruct (kxc_pin_intro sp0 ra0 s00 s10 s20 pv av
                       (m !!! Regidx Rs3) (m !!! Regidx Rs4) (m !!! Regidx Rs5)
                       (m !!! Regidx Rs6) (m !!! Regidx Rs7) (m !!! Regidx Rs8)
                       (m !!! Regidx Rs9) (m !!! Regidx Rs10) (m !!! Regidx Rs11)
                       (kxc_off ef i) szv w67 w68
                       with "Hf1 Hf2 Hf3 Hf4 Hf5 Hf6 Hf7 Hf8 Hf9 Hf10 Hf11 Hf12
                             Hf13 Hust Hph8 Hf63 Hf64 Hf65 Hf66 Hf67 Hf68")
            as "Hframe".
          iDestruct (cpu_own_transport CIDrd CIDy2 0%nat eb (proc_addr jp) eb
                       ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
          iDestruct (trap_csrs_ext_transport CIDrd CIDy2 eb (proc_addr jp)
                       ltac:(try rewrite Hebb; wp_next_chain) with "Hextc") as "Hextc".
          iDestruct (cpu_claim_ext_transport CIDrd CIDy2 eb (proc_addr jp)
                       ltac:(try rewrite Hebb; wp_next_chain) with "Hclmc") as "Hclmc".
          assert (Hbcr : true = false \/ proc_addr jp = zero_reg ->
                    (CIDy2 : CPU) = (CID0 : CPU)) by wp_next_chain.
          iDestruct (wp_next_retarget CID0 CIDy2 true (proc_addr jp) _ Hbcr
                       with "Hcont") as "Hcont".
          iApply (B2.kxc_bad324 (CID0 := CIDy2) Q gs jp gl gu gd gk pd pav pu bn g
                    gfs gi cn gtl gilf gislf ga gf cov logstart bmapstart
                    inodestart nib size dev kf qf sf gyf inumf dnf bmf
                    n2 plen pfun na avf alen aslen afun pidv V dqb dqs dqa dqpv dqas m U9
                    K sp0 ra0 s00 s10 s20 pv av (kxc_off ef i) w67 ef P szv eb ∅
                    HK Hk Hlg Hsz Hbm0 Hbmc Hbml Hins0 Hcovb Hiregb Hib Hn2 Hjp
                    Hgs Hsp Hra Hs0 Hs1 Hs2 Hbsp Hbs0 Hbs4 Hbs6
                    Hal Hbelow Hcov
                    with "Hcg Hcnt Hextc Hclmc Htext Hpc [] Hopen Hbm Hins Hbits Hka
                          Hpt Hpriv Hpath Hargv Hargs Helf Hbs Hirs Hlog Hframe
                          Hcont").
          { iApply (A.fs_fabric_mk with "Hkd Hpenv Hbio Hlogc Hcrash Hcert Hitab Hitinv
                                         Hesc Hslks Hireg Hropen Hprocs Hdevi Hdgeom
                                         Hdlock"). }
        * (* well-formed so far *)
          iApply (wp_bltu_fall_s_sconf (mword_of_int (KXB + 0x154))
                    (mword_of_int 492 : mword 13) Ra5 Rs1 U9 (K - 68)%nat eb
                    ltac:(bnz) ltac:(bnz) ltac:(exact Emf)
                    with "Hcg Hpc []").
          { iApply (kxc_154 with "Htext"). }
          iIntros (CIDx1 Hsx1) "Hcg Hpc".
          assert (Hpp158 : add_vec_int (mword_of_int (KXB + 0x154) : mword 64) 4
                           = mword_of_int (KXB + 0x158)) by bpcw.
          iEval (rewrite Hpp158) in "Hpc".
          (* ---- +0x158: ld a5,-472(s0) -- ph.vaddr ---- *)
          assert (Hph16 : add_vec (rget U9 Rs0)
                            (sign_extend' 64 (mword_of_int 3624 : mword 12))
                          = pa_add (pa_stk sp0 61) 16).
          { rewrite (rget_ne U9 Rs0 ltac:(bnz)) HU9s0 kxc_ph_o16. bs0slot. }
          iDestruct (kxc_win8 (pa_stk sp0 61) pf 16 32 56 ltac:(lia) Hpa16
                       with "Hphb") as "[Hw Hbk]".
          iEval (rewrite -Hph16) in "Hw".
          iApply (wp_ld_s_sconf (mword_of_int (KXB + 0x158)) Ra5 Rs0
                    (mword_of_int 3624 : mword 12) U9 (K - 68)%nat
                    (Z_to_bv 64 (le_at pf 16 8) : mword 64) eb
                    (dqm := DfracOwn 1) ltac:(bnz) ltac:(rdok)
                    with "Hcg Hpc [] Hw").
          { iApply (kxc_158 with "Htext"). }
          iIntros (CIDx2 Hsx2) "Hcg Hpc Hw". iEval (rewrite Hph16) in "Hw".
          iDestruct ("Hbk" with "Hw") as "Hphb".
          set (U10 := <[Regidx Ra5 := regval_into_reg
                        (Z_to_bv 64 (le_at pf 16 8) : mword 64)]> U9).
          assert (Hpp15c : add_vec_int (mword_of_int (KXB + 0x158) : mword 64) 4
                           = mword_of_int (KXB + 0x15c)) by bpcw.
          iEval (rewrite Hpp15c) in "Hpc".
          (* ---- +0x15c: c.add s1,s1,a5 -- vaddr + memsz ---- *)
          iApply (wp_cadd_s_sconf (mword_of_int (KXB + 0x15c)) Rs1 Ra5
                    U10 (K - 68)%nat eb ltac:(bnz) ltac:(rdok)
                    with "Hcg Hpc []").
          { iApply (kxc_15c with "Htext"). }
          iIntros (CIDx3 Hsx3) "Hcg Hpc". iEval (rgne) in "Hcg".
          iEval (rgne) in "Hcg".
          set (nsz := add_vec (U10 !!! Regidx Rs1) (U10 !!! Regidx Ra5)).
          set (U11 := <[Regidx Rs1 := regval_into_reg nsz]> U10).
          assert (HU11s1 : U11 !!! Regidx Rs1 = nsz)
            by (rewrite /U11; apply upd_eq).
          assert (HU11get : forall r : mword 5, is_cs_idx r = true -> r <> Rs1 ->
                    U11 !!! Regidx r = U7 !!! Regidx r).
          { intros r Hr Hne. rewrite /U11 upd_ne; [| congruence].
            rewrite /U10 upd_ne; [| reg_ne_side]. exact (HU9get r Hr Hne). }
          assert (HU11s0 : U11 !!! Regidx Rs0 = sp0)
            by (rewrite (HU11get Rs0 ltac:(vm_compute; reflexivity) ltac:(bnz));
                exact HU7s0).
          assert (Hpp15e : add_vec_int (mword_of_int (KXB + 0x15c) : mword 64) 2
                           = mword_of_int (KXB + 0x15e)) by bpcw.
          iEval (rewrite Hpp15e) in "Hpc".
          (* ---- +0x15e: bltu s1,a5 -- the wrap test, BLIND ---- *)
          assert (Htgt346 : add_vec (mword_of_int (KXB + 0x15e) : mword 64)
                              (sign_extend' 64 (mword_of_int 488 : mword 13))
                            = mword_of_int (KXB + 0x346)) by bpcw.
          destruct (zopz0zI_u (rget U11 Rs1) (rget U11 Ra5)) eqn:Ewr.
          -- iApply (wp_bltu_taken_s_sconf (mword_of_int (KXB + 0x15e))
                       (mword_of_int 488 : mword 13) Ra5 Rs1 U11 (K - 68)%nat
                       eb ltac:(bnz) ltac:(bnz) ltac:(exact Ewr)
                       ltac:(rewrite Htgt346; vm_compute; reflexivity)
                       with "Hcg Hpc []").
          { iApply (kxc_15e with "Htext"). }
             iIntros (CIDx4 Hsx4). iNext. iIntros "Hcg Hpc".
             iEval (rewrite Htgt346) in "Hpc".
             (* ---- 0x346: sd s2,-520(s0) ; 0x34a: c.j +0x324 ---- *)
             assert (Hbsp : U11 !!! Regidx csp_rs1 = pa_stk sp0 68)
               by (rewrite (HU11get csp_rs1 ltac:(vm_compute; reflexivity) ltac:(bnz));
                   exact HU7sp).
             assert (Hbs0 : U11 !!! Regidx Rs0 = sp0)
               by (rewrite (HU11get Rs0 ltac:(vm_compute; reflexivity) ltac:(bnz));
                   exact HU7s0).
             assert (Hbs2 : U11 !!! Regidx Rs2 = szv)
               by (rewrite (HU11get Rs2 ltac:(vm_compute; reflexivity) ltac:(bnz));
                   exact HU7s2).
             assert (Hbs4 : U11 !!! Regidx Rs4 = ientry kf)
               by (rewrite (HU11get Rs4 ltac:(vm_compute; reflexivity) ltac:(bnz));
                   exact HU7s4).
             assert (Hbs6 : U11 !!! Regidx Rs6 = page_base (ud_root P))
               by (rewrite (HU11get Rs6 ltac:(vm_compute; reflexivity) ltac:(bnz));
                   exact HU7s6).
             assert (Hbpa : add_vec (rget U11 Rs0)
                              (sign_extend' 64 (mword_of_int 3576 : mword 12))
                            = pa_stk sp0 65)
               by (rewrite (rget_ne U11 Rs0 ltac:(bnz)) Hbs0; bs0slot).
             assert (Hbsv : rget U11 Rs2 = szv)
               by (rewrite (rget_ne U11 Rs2 ltac:(bnz)); exact Hbs2).
             iEval (rewrite -Hbpa) in "Hf65".
             iApply (wp_sd_s_sconf (mword_of_int (KXB + 0x346)) Rs2 Rs0
                       (mword_of_int 3576 : mword 12) U11 (K - 68)%nat w65 eb
                       with "Hcg Hpc [] Hf65").
             { iApply (kxc_346 with "Htext"). }
             iIntros (CIDy1 Hsy1) "Hcg Hpc Hf65".
             iEval (rewrite Hbpa Hbsv) in "Hf65".
             assert (Hbppj : add_vec_int (mword_of_int (KXB + 0x346) : mword 64) 4
                             = mword_of_int (KXB + 0x34a)) by bpcw.
             iEval (rewrite Hbppj) in "Hpc".
             assert (Hbtgt : add_vec (mword_of_int (KXB + 0x34a) : mword 64)
                               (sign_extend' 64 (sign_extend' 21
                                  (concat_vec (mword_of_int 2029 : mword 11) ('b"0"))))
                             = mword_of_int (KXB + 0x324)) by bpcw.
             iApply (wp_cj_s_sconf (mword_of_int (KXB + 0x34a))
                       (sign_extend' 21 (concat_vec (mword_of_int 2029 : mword 11) ('b"0")))
                       U11 (K - 68)%nat eb
                       ltac:(rewrite Hbtgt; vm_compute; reflexivity)
                       with "Hcg Hpc []").
             { iApply (kxc_34a with "Htext"). }
             iIntros (CIDy2 Hsy2). iNext. iIntros "Hcg Hpc".
             iEval (rewrite Hbtgt) in "Hpc".
             iDestruct (kxc_ph_give sp0 pf Hphal with "Hphb") as "Hph7".
             iDestruct (kxc_stack8_of_ph sp0 w62 with "Hph7 Hf62") as "Hph8".
             iDestruct (kxc_pin_intro sp0 ra0 s00 s10 s20 pv av
                          (m !!! Regidx Rs3) (m !!! Regidx Rs4) (m !!! Regidx Rs5)
                          (m !!! Regidx Rs6) (m !!! Regidx Rs7) (m !!! Regidx Rs8)
                          (m !!! Regidx Rs9) (m !!! Regidx Rs10) (m !!! Regidx Rs11)
                          (kxc_off ef i) szv w67 w68
                          with "Hf1 Hf2 Hf3 Hf4 Hf5 Hf6 Hf7 Hf8 Hf9 Hf10 Hf11 Hf12
                                Hf13 Hust Hph8 Hf63 Hf64 Hf65 Hf66 Hf67 Hf68")
               as "Hframe".
             iDestruct (cpu_own_transport CIDrd CIDy2 0%nat eb (proc_addr jp) eb
                          ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
             iDestruct (trap_csrs_ext_transport CIDrd CIDy2 eb (proc_addr jp)
                          ltac:(try rewrite Hebb; wp_next_chain) with "Hextc") as "Hextc".
             iDestruct (cpu_claim_ext_transport CIDrd CIDy2 eb (proc_addr jp)
                          ltac:(try rewrite Hebb; wp_next_chain) with "Hclmc") as "Hclmc".
             assert (Hbcr : true = false \/ proc_addr jp = zero_reg ->
                       (CIDy2 : CPU) = (CID0 : CPU)) by wp_next_chain.
             iDestruct (wp_next_retarget CID0 CIDy2 true (proc_addr jp) _ Hbcr
                          with "Hcont") as "Hcont".
             iApply (B2.kxc_bad324 (CID0 := CIDy2) Q gs jp gl gu gd gk pd pav pu bn g
                       gfs gi cn gtl gilf gislf ga gf cov logstart bmapstart
                       inodestart nib size dev kf qf sf gyf inumf dnf bmf
                       n2 plen pfun na avf alen aslen afun pidv V dqb dqs dqa dqpv dqas m U11
                       K sp0 ra0 s00 s10 s20 pv av (kxc_off ef i) w67 ef P szv eb ∅
                       HK Hk Hlg Hsz Hbm0 Hbmc Hbml Hins0 Hcovb Hiregb Hib Hn2 Hjp
                       Hgs Hsp Hra Hs0 Hs1 Hs2 Hbsp Hbs0 Hbs4 Hbs6
                       Hal Hbelow Hcov
                       with "Hcg Hcnt Hextc Hclmc Htext Hpc [] Hopen Hbm Hins Hbits Hka
                             Hpt Hpriv Hpath Hargv Hargs Helf Hbs Hirs Hlog Hframe
                             Hcont").
             { iApply (A.fs_fabric_mk with "Hkd Hpenv Hbio Hlogc Hcrash Hcert Hitab Hitinv
                                            Hesc Hslks Hireg Hropen Hprocs Hdevi Hdgeom
                                            Hdlock"). }
          -- iApply (wp_bltu_fall_s_sconf (mword_of_int (KXB + 0x15e))
                       (mword_of_int 488 : mword 13) Ra5 Rs1 U11 (K - 68)%nat
                       eb ltac:(bnz) ltac:(bnz) ltac:(exact Ewr)
                       with "Hcg Hpc []").
             { iApply (kxc_15e with "Htext"). }
             iIntros (CIDx4 Hsx4) "Hcg Hpc".
             assert (Hpp162 : add_vec_int
                                (mword_of_int (KXB + 0x15e) : mword 64) 4
                              = mword_of_int (KXB + 0x162)) by bpcw.
             iEval (rewrite Hpp162) in "Hpc".
             (* ---- +0x162: ld a4,-536(s0) -- the PGSIZE-1 mask ---- *)
             assert (Hpa67 : add_vec (rget U11 Rs0)
                               (sign_extend' 64 (mword_of_int 3560 : mword 12))
                             = pa_stk sp0 67).
             { rewrite (rget_ne U11 Rs0 ltac:(bnz)) HU11s0. bs0slot. }
             iEval (rewrite -Hpa67) in "Hf67".
             iApply (wp_ld_s_sconf (mword_of_int (KXB + 0x162)) Ra4 Rs0
                       (mword_of_int 3560 : mword 12) U11 (K - 68)%nat w67 eb
                       (dqm := DfracOwn 1) ltac:(bnz) ltac:(rdok)
                       with "Hcg Hpc [] Hf67").
             { iApply (kxc_162 with "Htext"). }
             iIntros (CIDx5 Hsx5) "Hcg Hpc Hf67".
             iEval (rewrite Hpa67) in "Hf67".
             set (U12 := <[Regidx Ra4 := regval_into_reg w67]> U11).
             assert (Hpp166 : add_vec_int
                                (mword_of_int (KXB + 0x162) : mword 64) 4
                              = mword_of_int (KXB + 0x166)) by bpcw.
             iEval (rewrite Hpp166) in "Hpc".
             (* ---- +0x166: c.and a5,a5,a4 ---- *)
             iApply (wp_cand_s_sconf (mword_of_int (KXB + 0x166)) Ra5 Ra4
                       U12 (K - 68)%nat eb ltac:(bnz) ltac:(rdok)
                       with "Hcg Hpc []").
             { iApply (kxc_166 with "Htext"). }
             iIntros (CIDx6 Hsx6) "Hcg Hpc". iEval (rgne) in "Hcg".
             iEval (rgne) in "Hcg".
             set (U13 := <[Regidx Ra5 := regval_into_reg
                            (and_vec (U12 !!! Regidx Ra5)
                                     (U12 !!! Regidx Ra4))]> U12).
             assert (HU13get : forall r : mword 5, is_cs_idx r = true ->
                       r <> Rs1 -> U13 !!! Regidx r = U7 !!! Regidx r).
             { intros r Hr Hne. rewrite /U13 upd_ne; [| reg_ne_side].
               rewrite /U12 upd_ne; [| reg_ne_side]. exact (HU11get r Hr Hne). }
             assert (HU13s1 : U13 !!! Regidx Rs1 = nsz).
             { rewrite /U13 upd_ne; [| bnz]. rewrite /U12 upd_ne; [| bnz].
               exact HU11s1. }
             assert (HU13s0 : U13 !!! Regidx Rs0 = sp0)
               by (rewrite (HU13get Rs0 ltac:(vm_compute; reflexivity)
                              ltac:(bnz)); exact HU7s0).
             assert (Hpp168 : add_vec_int
                                (mword_of_int (KXB + 0x166) : mword 64) 2
                              = mword_of_int (KXB + 0x168)) by bpcw.
             iEval (rewrite Hpp168) in "Hpc".
             (* ---- +0x168: bnez a5 -- the alignment test, BLIND ---- *)
             assert (Htgt34c : add_vec (mword_of_int (KXB + 0x168) : mword 64)
                                 (sign_extend' 64 (mword_of_int 484 : mword 13))
                               = mword_of_int (KXB + 0x34c)) by bpcw.
             destruct (neq_vec (rget U13 Ra5) (zero_reg : mword 64)) eqn:Eal.
             ++ iApply (wp_bnez_x0_taken_s_sconf (mword_of_int (KXB + 0x168))
                          (mword_of_int 484 : mword 13) Ra5 U13 (K - 68)%nat
                          eb ltac:(bnz) ltac:(exact Eal)
                          ltac:(rewrite Htgt34c; vm_compute; reflexivity)
                          with "Hcg Hpc []").
             { iApply (kxc_168 with "Htext"). }
                iIntros (CIDx7 Hsx7). iNext. iIntros "Hcg Hpc".
                iEval (rewrite Htgt34c) in "Hpc".
                (* ---- 0x34c: sd s2,-520(s0) ; 0x350: c.j +0x324 ---- *)
                assert (Hbsp : U13 !!! Regidx csp_rs1 = pa_stk sp0 68)
                  by (rewrite (HU13get csp_rs1 ltac:(vm_compute; reflexivity) ltac:(bnz));
                      exact HU7sp).
                assert (Hbs0 : U13 !!! Regidx Rs0 = sp0)
                  by (rewrite (HU13get Rs0 ltac:(vm_compute; reflexivity) ltac:(bnz));
                      exact HU7s0).
                assert (Hbs2 : U13 !!! Regidx Rs2 = szv)
                  by (rewrite (HU13get Rs2 ltac:(vm_compute; reflexivity) ltac:(bnz));
                      exact HU7s2).
                assert (Hbs4 : U13 !!! Regidx Rs4 = ientry kf)
                  by (rewrite (HU13get Rs4 ltac:(vm_compute; reflexivity) ltac:(bnz));
                      exact HU7s4).
                assert (Hbs6 : U13 !!! Regidx Rs6 = page_base (ud_root P))
                  by (rewrite (HU13get Rs6 ltac:(vm_compute; reflexivity) ltac:(bnz));
                      exact HU7s6).
                assert (Hbpa : add_vec (rget U13 Rs0)
                                 (sign_extend' 64 (mword_of_int 3576 : mword 12))
                               = pa_stk sp0 65)
                  by (rewrite (rget_ne U13 Rs0 ltac:(bnz)) Hbs0; bs0slot).
                assert (Hbsv : rget U13 Rs2 = szv)
                  by (rewrite (rget_ne U13 Rs2 ltac:(bnz)); exact Hbs2).
                iEval (rewrite -Hbpa) in "Hf65".
                iApply (wp_sd_s_sconf (mword_of_int (KXB + 0x34c)) Rs2 Rs0
                          (mword_of_int 3576 : mword 12) U13 (K - 68)%nat w65 eb
                          with "Hcg Hpc [] Hf65").
                { iApply (kxc_34c with "Htext"). }
                iIntros (CIDy1 Hsy1) "Hcg Hpc Hf65".
                iEval (rewrite Hbpa Hbsv) in "Hf65".
                assert (Hbppj : add_vec_int (mword_of_int (KXB + 0x34c) : mword 64) 4
                                = mword_of_int (KXB + 0x350)) by bpcw.
                iEval (rewrite Hbppj) in "Hpc".
                assert (Hbtgt : add_vec (mword_of_int (KXB + 0x350) : mword 64)
                                  (sign_extend' 64 (sign_extend' 21
                                     (concat_vec (mword_of_int 2026 : mword 11) ('b"0"))))
                                = mword_of_int (KXB + 0x324)) by bpcw.
                iApply (wp_cj_s_sconf (mword_of_int (KXB + 0x350))
                          (sign_extend' 21 (concat_vec (mword_of_int 2026 : mword 11) ('b"0")))
                          U13 (K - 68)%nat eb
                          ltac:(rewrite Hbtgt; vm_compute; reflexivity)
                          with "Hcg Hpc []").
                { iApply (kxc_350 with "Htext"). }
                iIntros (CIDy2 Hsy2). iNext. iIntros "Hcg Hpc".
                iEval (rewrite Hbtgt) in "Hpc".
                iDestruct (kxc_ph_give sp0 pf Hphal with "Hphb") as "Hph7".
                iDestruct (kxc_stack8_of_ph sp0 w62 with "Hph7 Hf62") as "Hph8".
                iDestruct (kxc_pin_intro sp0 ra0 s00 s10 s20 pv av
                             (m !!! Regidx Rs3) (m !!! Regidx Rs4) (m !!! Regidx Rs5)
                             (m !!! Regidx Rs6) (m !!! Regidx Rs7) (m !!! Regidx Rs8)
                             (m !!! Regidx Rs9) (m !!! Regidx Rs10) (m !!! Regidx Rs11)
                             (kxc_off ef i) szv w67 w68
                             with "Hf1 Hf2 Hf3 Hf4 Hf5 Hf6 Hf7 Hf8 Hf9 Hf10 Hf11 Hf12
                                   Hf13 Hust Hph8 Hf63 Hf64 Hf65 Hf66 Hf67 Hf68")
                  as "Hframe".
                iDestruct (cpu_own_transport CIDrd CIDy2 0%nat eb (proc_addr jp) eb
                             ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
                iDestruct (trap_csrs_ext_transport CIDrd CIDy2 eb (proc_addr jp)
                             ltac:(try rewrite Hebb; wp_next_chain) with "Hextc") as "Hextc".
                iDestruct (cpu_claim_ext_transport CIDrd CIDy2 eb (proc_addr jp)
                             ltac:(try rewrite Hebb; wp_next_chain) with "Hclmc") as "Hclmc".
                assert (Hbcr : true = false \/ proc_addr jp = zero_reg ->
                          (CIDy2 : CPU) = (CID0 : CPU)) by wp_next_chain.
                iDestruct (wp_next_retarget CID0 CIDy2 true (proc_addr jp) _ Hbcr
                             with "Hcont") as "Hcont".
                iApply (B2.kxc_bad324 (CID0 := CIDy2) Q gs jp gl gu gd gk pd pav pu bn g
                          gfs gi cn gtl gilf gislf ga gf cov logstart bmapstart
                          inodestart nib size dev kf qf sf gyf inumf dnf bmf
                          n2 plen pfun na avf alen aslen afun pidv V dqb dqs dqa dqpv dqas m U13
                          K sp0 ra0 s00 s10 s20 pv av (kxc_off ef i) w67 ef P szv eb ∅
                          HK Hk Hlg Hsz Hbm0 Hbmc Hbml Hins0 Hcovb Hiregb Hib Hn2 Hjp
                          Hgs Hsp Hra Hs0 Hs1 Hs2 Hbsp Hbs0 Hbs4 Hbs6
                          Hal Hbelow Hcov
                          with "Hcg Hcnt Hextc Hclmc Htext Hpc [] Hopen Hbm Hins Hbits Hka
                                Hpt Hpriv Hpath Hargv Hargs Helf Hbs Hirs Hlog Hframe
                                Hcont").
                { iApply (A.fs_fabric_mk with "Hkd Hpenv Hbio Hlogc Hcrash Hcert Hitab Hitinv
                                               Hesc Hslks Hireg Hropen Hprocs Hdevi Hdgeom
                                               Hdlock"). }
             ++ iApply (wp_bnez_x0_fall_s_sconf (mword_of_int (KXB + 0x168))
                          (mword_of_int 484 : mword 13) Ra5 U13 (K - 68)%nat
                          eb ltac:(bnz) ltac:(exact Eal)
                          with "Hcg Hpc []").
                { iApply (kxc_168 with "Htext"). }
                iIntros (CIDx7 Hsx7) "Hcg Hpc".
                assert (Hpp16c : add_vec_int
                                   (mword_of_int (KXB + 0x168) : mword 64) 4
                                 = mword_of_int (KXB + 0x16c)) by bpcw.
                iEval (rewrite Hpp16c) in "Hpc".
                (* ---- +0x16c: lw a0,-484(s0) -- ph.flags ---- *)
                assert (HU13sp : U13 !!! Regidx csp_rs1 = pa_stk sp0 68)
                  by (rewrite (HU13get csp_rs1 ltac:(vm_compute; reflexivity)
                                 ltac:(bnz)); exact HU7sp).
                assert (HU13s2 : U13 !!! Regidx Rs2 = szv)
                  by (rewrite (HU13get Rs2 ltac:(vm_compute; reflexivity)
                                 ltac:(bnz)); exact HU7s2).
                assert (HU13s4 : U13 !!! Regidx Rs4 = ientry kf)
                  by (rewrite (HU13get Rs4 ltac:(vm_compute; reflexivity)
                                 ltac:(bnz)); exact HU7s4).
                assert (HU13s5 : U13 !!! Regidx Rs5
                                 = (mword_of_int 4096 : mword 64))
                  by (rewrite (HU13get Rs5 ltac:(vm_compute; reflexivity)
                                 ltac:(bnz)); exact HU7s5).
                assert (HU13s6 : U13 !!! Regidx Rs6 = page_base P.(ud_root))
                  by (rewrite (HU13get Rs6 ltac:(vm_compute; reflexivity)
                                 ltac:(bnz)); exact HU7s6).
                assert (HU13s9 : U13 !!! Regidx Rs9
                                 = (mword_of_int 4096 : mword 64))
                  by (rewrite (HU13get Rs9 ltac:(vm_compute; reflexivity)
                                 ltac:(bnz)); exact HU7s9).
                assert (HU13s10 : U13 !!! Regidx Rs10
                                  = (mword_of_int (Z.of_nat i) : mword 64))
                  by (rewrite (HU13get Rs10 ltac:(vm_compute; reflexivity)
                                 ltac:(bnz)); exact HU7s10).
                assert (HU13s11 : U13 !!! Regidx Rs11
                                  = (mword_of_int 56 : mword 64))
                  by (rewrite (HU13get Rs11 ltac:(vm_compute; reflexivity)
                                 ltac:(bnz)); exact HU7s11).
                assert (Hph4 : add_vec (rget U13 Rs0)
                                 (sign_extend' 64 (mword_of_int 3612 : mword 12))
                               = pa_add (pa_stk sp0 61) 4).
                { rewrite (rget_ne U13 Rs0 ltac:(bnz)) HU13s0. apply kxc_ph_o4. }
                iDestruct (kxc_win4 (pa_stk sp0 61) pf 4 48 56 ltac:(lia) Hpa4
                             with "Hphb") as "[Hw Hbk]".
                iEval (rewrite -Hph4) in "Hw".
                iApply (wp_lw_s_sconf (mword_of_int (KXB + 0x16c)) Ra0 Rs0
                          (mword_of_int 3612 : mword 12) U13 (K - 68)%nat
                          (Z_to_bv 32 (le_at pf 4 4) : mword 32) eb
                          (dqm := DfracOwn 1) ltac:(bnz) ltac:(rdok)
                          with "Hcg Hpc [] Hw").
                { iApply (kxc_16c with "Htext"). }
                iIntros (CIDz0 Hsz0) "Hcg Hpc Hw". iEval (rewrite Hph4) in "Hw".
                iDestruct ("Hbk" with "Hw") as "Hphb".
                set (U14 := <[Regidx Ra0 := regval_into_reg
                              (sign_extend' 64 (Z_to_bv 32 (le_at pf 4 4)
                                                : mword 32))]> U13).
                assert (Hpp170 : add_vec_int
                                   (mword_of_int (KXB + 0x16c) : mword 64) 4
                                 = mword_of_int (KXB + 0x170)) by bpcw.
                iEval (rewrite Hpp170) in "Hpc".
                (* ---- +0x170: jal ra,flags2perm ---- *)
                assert (Htf2p : add_vec (mword_of_int (KXB + 0x170) : mword 64)
                                  (sign_extend' 64 (mword_of_int 2096752
                                                    : mword 21))
                                = mword_of_int KernelSyms.flags2perm) by bpcw.
                iApply (wp_jal_s_sconf (mword_of_int (KXB + 0x170)) Rra
                          (mword_of_int 2096752 : mword 21) U14 (K - 68)%nat eb
                          ltac:(bnz) ltac:(rdok)
                          ltac:(rewrite Htf2p; vm_compute; reflexivity)
                          with "Hcg Hpc []").
                { iApply (kxc_170 with "Htext"). }
                iIntros (CIDz1 Hsz1) "Hcg Hpc". iEval (rewrite Htf2p) in "Hpc".
                set (U15 := <[Regidx Rra := regval_into_reg
                              (add_vec_int (mword_of_int (KXB + 0x170)
                                            : mword 64) 4)]> U14).
                change (<[Regidx Rra := regval_into_reg
                          (add_vec_int (mword_of_int (KXB + 0x170) : mword 64) 4)]>
                          U14) with U15.
                assert (HU15ra : U15 !!! Regidx Rra
                          = add_vec_int (mword_of_int (KXB + 0x170) : mword 64) 4)
                  by (rewrite /U15; apply upd_eq).
                assert (HU15get : forall r : mword 5, is_cs_idx r = true ->
                          r <> Rs1 -> U15 !!! Regidx r = U7 !!! Regidx r).
                { intros r Hr Hne. rewrite /U15 upd_ne; [| reg_ne_side].
                  rewrite /U14 upd_ne; [| reg_ne_side].
                  exact (HU13get r Hr Hne). }
                iApply (Flags2perm.wp_flags2perm_sconf U15 (K - 68)%nat eb
                          (proc_addr jp) ltac:(lia)
                          with "Hcg Htext Hpc").
                iIntros (CIDz2 Hsz2 M3) "Hcg Hpc %Hcsf %Hf2p".
                assert (Hpc174 : ret_pc (U15 !!! Regidx Rra)
                                 = mword_of_int (KXB + 0x174))
                  by (rewrite HU15ra; bpcw).
                iEval (rewrite Hpc174) in "Hpc".
                set (xp := f2p (U15 !!! Regidx Ra0)).
                assert (HM3get : forall r : mword 5, is_cs_idx r = true ->
                          r <> Rs1 -> M3 !!! Regidx r = U7 !!! Regidx r).
                { intros r Hr Hne. rewrite (callee_saved_lookup Hcsf r Hr).
                  exact (HU15get r Hr Hne). }
                assert (HM3s1 : M3 !!! Regidx Rs1 = nsz).
                { rewrite (callee_saved_lookup Hcsf Rs1
                             ltac:(vm_compute; reflexivity)).
                  rewrite /U15 upd_ne; [| bnz]. rewrite /U14 upd_ne; [| bnz].
                  exact HU13s1. }
                (* ---- +0x174: c.mv a3,a0 ---- *)
                iApply (wp_cmv_s_sconf (mword_of_int (KXB + 0x174)) Ra3 Ra0
                          M3 (K - 68)%nat eb ltac:(bnz) ltac:(rdok)
                          with "Hcg Hpc []").
                { iApply (kxc_174 with "Htext"). }
                iIntros (CIDz3 Hsz3) "Hcg Hpc". iEval (rgne) in "Hcg".
                set (U16 := <[Regidx Ra3 := regval_into_reg
                              (add_vec zero_reg (M3 !!! Regidx Ra0))]> M3).
                assert (HU16a3 : U16 !!! Regidx Ra3
                                 = (mword_of_int xp : mword 64)).
                { rewrite /U16 upd_eq Hf2p. apply w32_zero_add. }
                assert (Hpp176 : add_vec_int
                                   (mword_of_int (KXB + 0x174) : mword 64) 2
                                 = mword_of_int (KXB + 0x176)) by bpcw.
                iEval (rewrite Hpp176) in "Hpc".
                (* ---- +0x176: c.mv a2,s1 -- newsz ---- *)
                iApply (wp_cmv_s_sconf (mword_of_int (KXB + 0x176)) Ra2 Rs1
                          U16 (K - 68)%nat eb ltac:(bnz) ltac:(rdok)
                          with "Hcg Hpc []").
                { iApply (kxc_176 with "Htext"). }
                iIntros (CIDz4 Hsz4) "Hcg Hpc". iEval (rgne) in "Hcg".
                set (U17 := <[Regidx Ra2 := regval_into_reg
                              (add_vec zero_reg (U16 !!! Regidx Rs1))]> U16).
                assert (HU16s1 : U16 !!! Regidx Rs1 = nsz)
                  by (rewrite /U16 upd_ne; [exact HM3s1 | bnz]).
                assert (HU17a2 : U17 !!! Regidx Ra2 = nsz).
                { rewrite /U17 upd_eq HU16s1. apply w32_zero_add. }
                assert (HU17a3 : U17 !!! Regidx Ra3
                                 = (mword_of_int xp : mword 64))
                  by (rewrite /U17 upd_ne; [exact HU16a3 | bnz]).
                assert (Hpp178 : add_vec_int
                                   (mword_of_int (KXB + 0x176) : mword 64) 2
                                 = mword_of_int (KXB + 0x178)) by bpcw.
                iEval (rewrite Hpp178) in "Hpc".
                (* ---- +0x178: c.mv a1,s2 -- oldsz ---- *)
                iApply (wp_cmv_s_sconf (mword_of_int (KXB + 0x178)) Ra1 Rs2
                          U17 (K - 68)%nat eb ltac:(bnz) ltac:(rdok)
                          with "Hcg Hpc []").
                { iApply (kxc_178 with "Htext"). }
                iIntros (CIDz5 Hsz5) "Hcg Hpc". iEval (rgne) in "Hcg".
                set (U18 := <[Regidx Ra1 := regval_into_reg
                              (add_vec zero_reg (U17 !!! Regidx Rs2))]> U17).
                assert (HU17s2 : U17 !!! Regidx Rs2 = szv).
                { rewrite /U17 upd_ne; [| bnz]. rewrite /U16 upd_ne; [| bnz].
                  rewrite (HM3get Rs2 ltac:(vm_compute; reflexivity) ltac:(bnz)).
                  exact HU7s2. }
                assert (HU18a1 : U18 !!! Regidx Ra1 = szv).
                { rewrite /U18 upd_eq HU17s2. apply w32_zero_add. }
                assert (HU18a2 : U18 !!! Regidx Ra2 = nsz)
                  by (rewrite /U18 upd_ne; [exact HU17a2 | bnz]).
                assert (HU18a3 : U18 !!! Regidx Ra3
                                 = (mword_of_int xp : mword 64))
                  by (rewrite /U18 upd_ne; [exact HU17a3 | bnz]).
                assert (Hpp17a : add_vec_int
                                   (mword_of_int (KXB + 0x178) : mword 64) 2
                                 = mword_of_int (KXB + 0x17a)) by bpcw.
                iEval (rewrite Hpp17a) in "Hpc".
                (* ---- +0x17a: c.mv a0,s6 -- the new table's root ---- *)
                iApply (wp_cmv_s_sconf (mword_of_int (KXB + 0x17a)) Ra0 Rs6
                          U18 (K - 68)%nat eb ltac:(bnz) ltac:(rdok)
                          with "Hcg Hpc []").
                { iApply (kxc_17a with "Htext"). }
                iIntros (CIDz6 Hsz6) "Hcg Hpc". iEval (rgne) in "Hcg".
                set (U19 := <[Regidx Ra0 := regval_into_reg
                              (add_vec zero_reg (U18 !!! Regidx Rs6))]> U18).
                assert (HU18s6 : U18 !!! Regidx Rs6 = page_base P.(ud_root)).
                { rewrite /U18 upd_ne; [| bnz]. rewrite /U17 upd_ne; [| bnz].
                  rewrite /U16 upd_ne; [| bnz].
                  rewrite (HM3get Rs6 ltac:(vm_compute; reflexivity) ltac:(bnz)).
                  exact HU7s6. }
                assert (HU19a0 : U19 !!! Regidx Ra0 = page_base P.(ud_root)).
                { rewrite /U19 upd_eq HU18s6. apply w32_zero_add. }
                assert (HU19a1 : U19 !!! Regidx Ra1 = szv)
                  by (rewrite /U19 upd_ne; [exact HU18a1 | bnz]).
                assert (HU19a2 : U19 !!! Regidx Ra2 = nsz)
                  by (rewrite /U19 upd_ne; [exact HU18a2 | bnz]).
                assert (HU19a3 : U19 !!! Regidx Ra3
                                 = (mword_of_int xp : mword 64))
                  by (rewrite /U19 upd_ne; [exact HU18a3 | bnz]).
                assert (HU19get : forall r : mword 5, is_cs_idx r = true ->
                          r <> Rs1 -> U19 !!! Regidx r = U7 !!! Regidx r).
                { intros r Hr Hne. rewrite /U19 upd_ne; [| reg_ne_side].
                  rewrite /U18 upd_ne; [| reg_ne_side].
                  rewrite /U17 upd_ne; [| reg_ne_side].
                  rewrite /U16 upd_ne; [| reg_ne_side].
                  exact (HM3get r Hr Hne). }
                assert (HU19s1 : U19 !!! Regidx Rs1 = nsz).
                { rewrite /U19 upd_ne; [| bnz]. rewrite /U18 upd_ne; [| bnz].
                  rewrite /U17 upd_ne; [| bnz]. exact HU16s1. }
                assert (Hpp17c : add_vec_int
                                   (mword_of_int (KXB + 0x17a) : mword 64) 2
                                 = mword_of_int (KXB + 0x17c)) by bpcw.
                iEval (rewrite Hpp17c) in "Hpc".
                (* ---- +0x17c: jal ra,uvmalloc ---- *)
                assert (Htuvm : add_vec (mword_of_int (KXB + 0x17c) : mword 64)
                                  (sign_extend' 64 (mword_of_int 2083152
                                                    : mword 21))
                                = mword_of_int KernelSyms.uvmalloc) by bpcw.
                iApply (wp_jal_s_sconf (mword_of_int (KXB + 0x17c)) Rra
                          (mword_of_int 2083152 : mword 21) U19 (K - 68)%nat eb
                          ltac:(bnz) ltac:(rdok)
                          ltac:(rewrite Htuvm; vm_compute; reflexivity)
                          with "Hcg Hpc []").
                { iApply (kxc_17c with "Htext"). }
                iIntros (CIDz7 Hsz7) "Hcg Hpc". iEval (rewrite Htuvm) in "Hpc".
                set (Z0 := <[Regidx Rra := regval_into_reg
                             (add_vec_int (mword_of_int (KXB + 0x17c)
                                           : mword 64) 4)]> U19).
                change (<[Regidx Rra := regval_into_reg
                          (add_vec_int (mword_of_int (KXB + 0x17c) : mword 64) 4)]>
                          U19) with Z0.
                assert (HZ0ra : Z0 !!! Regidx Rra
                          = add_vec_int (mword_of_int (KXB + 0x17c) : mword 64) 4)
                  by (rewrite /Z0; apply upd_eq).
                assert (HZ0a0 : Z0 !!! Regidx Ra0 = page_base P.(ud_root))
                  by (rewrite /Z0 upd_ne; [exact HU19a0 | bnz]).
                assert (HZ0a1 : Z0 !!! Regidx Ra1 = szv)
                  by (rewrite /Z0 upd_ne; [exact HU19a1 | bnz]).
                assert (HZ0a2 : Z0 !!! Regidx Ra2 = nsz)
                  by (rewrite /Z0 upd_ne; [exact HU19a2 | bnz]).
                assert (HZ0a3 : Z0 !!! Regidx Ra3
                                = (mword_of_int xp : mword 64))
                  by (rewrite /Z0 upd_ne; [exact HU19a3 | bnz]).
                assert (HZ0get : forall r : mword 5, is_cs_idx r = true ->
                          r <> Rs1 -> Z0 !!! Regidx r = U7 !!! Regidx r).
                { intros r Hr Hne. rewrite /Z0 upd_ne; [| reg_ne_side].
                  exact (HU19get r Hr Hne). }
                assert (HZ0s1 : Z0 !!! Regidx Rs1 = nsz)
                  by (rewrite /Z0 upd_ne; [exact HU19s1 | bnz]).
                (* ---- the tp pin uvmalloc's contract still asks for.
                       ProofGrowproc.v's recipe, and it must come AFTER the
                       [jal]: [cid_word] is HART-INDEXED, so a [tp_pin] set up
                       before the crossing means the wrong hart's word and the
                       call fails with two identical-printing [cid_word]s. ---- *)
                set (Y := tp_pin Z0).
                assert (HYid : tp_pin Y = tp_pin Z0)
                  by (rewrite /Y; apply (tp_pin_id (tp_pin Z0) (rget_tp Z0))).
                assert (HYsp0 : Y !!! Regidx csp_rs1 = Z0 !!! Regidx csp_rs1)
                  by (rewrite /Y; exact (tp_pin_sp Z0)).
                assert (Hgpreq : sie_cap_gpr KT1 Z0 (K - 68)%nat eb (proc_addr jp)
                                 = sie_cap_gpr KT1 Y (K - 68)%nat eb (proc_addr jp))
                  by (unfold sie_cap_gpr, sie_cap; rewrite HYsp0 HYid;
                      reflexivity).
                iEval (rewrite Hgpreq) in "Hcg".
                assert (HYne : forall r : mword 5, r <> Rtp ->
                          Y !!! Regidx r = Z0 !!! Regidx r).
                { intros r Hr. rewrite /Y. apply (rget_ne Z0 r).
                  intro He. injection He as He2. congruence. }
                assert (HYtp : Y !!! Regidx Rtp = cid_word)
                  by (rewrite /Y upd_eq; reflexivity).
                assert (HYra : Y !!! Regidx Rra
                          = add_vec_int (mword_of_int (KXB + 0x17c) : mword 64) 4)
                  by (rewrite (HYne Rra ltac:(bnz)); exact HZ0ra).
                assert (HYa0 : Y !!! Regidx Ra0 = page_base P.(ud_root))
                  by (rewrite (HYne Ra0 ltac:(bnz)); exact HZ0a0).
                assert (HYa1 : Y !!! Regidx Ra1 = szv)
                  by (rewrite (HYne Ra1 ltac:(bnz)); exact HZ0a1).
                assert (HYa2 : Y !!! Regidx Ra2 = nsz)
                  by (rewrite (HYne Ra2 ltac:(bnz)); exact HZ0a2).
                assert (HYa3 : Y !!! Regidx Ra3
                               = (mword_of_int xp : mword 64))
                  by (rewrite (HYne Ra3 ltac:(bnz)); exact HZ0a3).
                assert (HYget : forall r : mword 5, is_cs_idx r = true ->
                          r <> Rs1 -> Y !!! Regidx r = U7 !!! Regidx r).
                { intros r Hr Hne.
                  assert (N4 : r <> Rtp)
                    by (intro He; rewrite He in Hr; vm_compute in Hr;
                        discriminate).
                  rewrite (HYne r N4). exact (HZ0get r Hr Hne). }
                assert (HYs1 : Y !!! Regidx Rs1 = nsz)
                  by (rewrite (HYne Rs1 ltac:(bnz)); exact HZ0s1).
                iDestruct (cpu_own_transport CIDrd CIDz7 0%nat eb
                             (proc_addr jp) eb ltac:(wp_next_chain)
                             with "Hcnt") as "Hcnt".
                iApply (Uvmalloc.wp_uvmalloc_sconf ga Y P xp (K - 68)%nat eb
                          (proc_addr jp) eb ∅ ltac:(lia) HYtp HYa0 HYa3
                          ltac:(rewrite /xp; apply f2p_range)
                          ltac:(destruct (f2p_cases (U15 !!! Regidx Ra0))
                                  as [Hq | [Hq | [Hq | Hq]]];
                                rewrite /xp Hq;
                                [ exact uvm_perm_ok_18 | exact uvm_perm_ok_22
                                | exact uvm_perm_ok_26 | exact uvm_perm_ok_30 ])
                          ltac:(rewrite HYa1 uint_unsigned; exact Hmax)
                          ltac:(right; rewrite HYa1; exact Hcov)
                          ltac:(rewrite HYa1 HYa2; intros j Hj Hbnd;
                                apply (um_below_run_fresh szv P.(ud_um)
                                         (S j) j Hbelow Hmax
                                         ltac:(rewrite Nat2Z.inj_succ; lia)
                                         ltac:(lia)))
                          with "Hcg Hcnt Htext Hpc Hpt Hka").
                all: try lkbelow.
                iIntros (CIDz8 Hsz8 M4) "Hcg Hcnt Hpc %Hcsu Hpost".
                assert (Hpc180 : ret_pc (Y !!! Regidx Rra)
                                 = mword_of_int (KXB + 0x180))
                  by (rewrite HYra; bpcw).
                iEval (rewrite Hpc180) in "Hpc".
                assert (HM4get : forall r : mword 5, is_cs_idx r = true ->
                          r <> Rs1 -> M4 !!! Regidx r = U7 !!! Regidx r).
                { intros r Hr Hne. rewrite (callee_saved_lookup Hcsu r Hr).
                  exact (HYget r Hr Hne). }
                assert (HM4sp : M4 !!! Regidx csp_rs1 = pa_stk sp0 68)
                  by (rewrite (HM4get csp_rs1 ltac:(vm_compute; reflexivity)
                                 ltac:(bnz)); exact HU7sp).
                assert (HM4s0 : M4 !!! Regidx Rs0 = sp0)
                  by (rewrite (HM4get Rs0 ltac:(vm_compute; reflexivity)
                                 ltac:(bnz)); exact HU7s0).
                assert (HM4s2 : M4 !!! Regidx Rs2 = szv)
                  by (rewrite (HM4get Rs2 ltac:(vm_compute; reflexivity)
                                 ltac:(bnz)); exact HU7s2).
                assert (HM4s4 : M4 !!! Regidx Rs4 = ientry kf)
                  by (rewrite (HM4get Rs4 ltac:(vm_compute; reflexivity)
                                 ltac:(bnz)); exact HU7s4).
                assert (HM4s5 : M4 !!! Regidx Rs5
                                = (mword_of_int 4096 : mword 64))
                  by (rewrite (HM4get Rs5 ltac:(vm_compute; reflexivity)
                                 ltac:(bnz)); exact HU7s5).
                assert (HM4s6 : M4 !!! Regidx Rs6 = page_base P.(ud_root))
                  by (rewrite (HM4get Rs6 ltac:(vm_compute; reflexivity)
                                 ltac:(bnz)); exact HU7s6).
                assert (HM4s9 : M4 !!! Regidx Rs9
                                = (mword_of_int 4096 : mword 64))
                  by (rewrite (HM4get Rs9 ltac:(vm_compute; reflexivity)
                                 ltac:(bnz)); exact HU7s9).
                assert (HM4s10 : M4 !!! Regidx Rs10
                                 = (mword_of_int (Z.of_nat i) : mword 64))
                  by (rewrite (HM4get Rs10 ltac:(vm_compute; reflexivity)
                                 ltac:(bnz)); exact HU7s10).
                assert (HM4s11 : M4 !!! Regidx Rs11
                                 = (mword_of_int 56 : mword 64))
                  by (rewrite (HM4get Rs11 ltac:(vm_compute; reflexivity)
                                 ltac:(bnz)); exact HU7s11).
                assert (HM4s8 : M4 !!! Regidx Rs1 = nsz)
                  by (rewrite (callee_saved_lookup Hcsu Rs1
                                 ltac:(vm_compute; reflexivity)); exact HYs1).
                (* ---- THE INVARIANT STEP, both uvmalloc arms at once ---- *)
                iAssert (∃ P4 : uptd,
                           ⌜ud_root P4 = ud_root P /\ ud_tfp P4 = ud_tfp P /\
                            (bv_unsigned (M4 !!! Regidx Ra0) <> 0 ->
                               um_below (M4 !!! Regidx Ra0) P4.(ud_um) /\
                               um_covered (M4 !!! Regidx Ra0) P4.(ud_um)) /\
                            (bv_unsigned (M4 !!! Regidx Ra0) = 0 ->
                               um_below szv P4.(ud_um) /\
                               um_covered szv P4.(ud_um))⌝ ∗
                           proc_pt P4)%I
                  with "[Hpost]" as "Hstep".
                { iDestruct "Hpost" as "[[%Hz Hpt] | (%P4 & %Hext & %Hdom &
                                                      %Hleaf & %Harm & Hpt)]".
                  - iExists P. iSplitR; [| iExact "Hpt"]. iPureIntro.
                    split_and!; [reflexivity | reflexivity | | ].
                    + intro Hne. exfalso. apply Hne. rewrite Hz.
                      vm_compute. reflexivity.
                    + intros _. split; [exact Hbelow | exact Hcov].
                  - iDestruct (proc_pt_wf_get with "Hpt") as %Hwf4.
                    rewrite HYa1 HYa2 !uint_unsigned in Harm.
                    pose proof (kxc_grow_inv P P4 szv nsz (M4 !!! Regidx Ra0)
                                  Hwf Hwf4 Hbelow Hcov Hext
                                  ltac:(rewrite HYa1 HYa2 in Hdom; exact Hdom)
                                  Harm) as [Hbel4 Hcov4].
                    iExists P4. iSplitR; [| iExact "Hpt"]. iPureIntro.
                    destruct Hext as (Hrt & Htf & _).
                    split_and!; [exact Hrt | exact Htf | | ].
                    + intros _. split; [exact Hbel4 | exact Hcov4].
                    + intro Hz0.
                      assert (Hsq : szv = M4 !!! Regidx Ra0).
                      { destruct Harm as [[Hlt Hv] | [Hle Hv]].
                        - by rewrite Hv.
                        - rewrite Hv in Hz0. rewrite Hv.
                          pose proof (bv_unsigned_in_range _ szv) as Hrng.
                          destruct Hrng as [Hs0' _].
                          assert (Hszz : bv_unsigned szv = bv_unsigned nsz)
                            by lia.
                          apply bv_eq. exact Hszz. }
                      rewrite Hsq. split; [exact Hbel4 | exact Hcov4]. }
                iDestruct "Hstep" as (P4) "((%HP4rt & %HP4tf & %HP4ne & %HP4z)
                                            & Hpt)".
                (* ---- +0x180: sd a0,-520(s0) -- sz1 ---- *)
                assert (Hpa65b : add_vec (rget M4 Rs0)
                                   (sign_extend' 64 (mword_of_int 3576
                                                     : mword 12))
                                 = pa_stk sp0 65).
                { rewrite (rget_ne M4 Rs0 ltac:(bnz)) HM4s0. bs0slot. }
                assert (Hsta0b : rget M4 Ra0 = M4 !!! Regidx Ra0)
                  by (apply rget_ne; bnz).
                iEval (rewrite -Hpa65b) in "Hf65".
                iApply (wp_sd_s_sconf (mword_of_int (KXB + 0x180)) Ra0 Rs0
                          (mword_of_int 3576 : mword 12) M4 (K - 68)%nat w65 eb
                          with "Hcg Hpc [] Hf65").
                { iApply (kxc_180 with "Htext"). }
                iIntros (CIDz9 Hsz9) "Hcg Hpc Hf65".
                iEval (rewrite Hpa65b Hsta0b) in "Hf65".
                assert (Hpp184 : add_vec_int
                                   (mword_of_int (KXB + 0x180) : mword 64) 4
                                 = mword_of_int (KXB + 0x184)) by bpcw.
                iEval (rewrite Hpp184) in "Hpc".
                (* ---- +0x184: beqz a0 -- out of memory? ---- *)
                assert (Htgt352 : add_vec (mword_of_int (KXB + 0x184) : mword 64)
                                    (sign_extend' 64 (mword_of_int 462
                                                      : mword 13))
                                  = mword_of_int (KXB + 0x352)) by bpcw.
                destruct (eq_vec (rget M4 Ra0) (zero_reg : mword 64)) eqn:Eoom.
                ** (* ---- kalloc failed: [bad:] at +0x352 ---- *)
                   iApply (wp_beqz_x0_taken_s_sconf (mword_of_int (KXB + 0x184))
                             (mword_of_int 462 : mword 13) Ra0 M4 (K - 68)%nat
                             eb ltac:(bnz) ltac:(exact Eoom)
                             ltac:(rewrite Htgt352; vm_compute; reflexivity)
                             with "Hcg Hpc []").
                   { iApply (kxc_184 with "Htext"). }
                   iIntros (CIDw1 Hsw1). iNext. iIntros "Hcg Hpc".
                   iEval (rewrite Htgt352) in "Hpc".
                   assert (Ha00 : bv_unsigned (M4 !!! Regidx Ra0) = 0).
                   { apply eq_vec_true_iff in Eoom.
                     assert (Hq : M4 !!! Regidx Ra0 = zero_reg)
                       by (etransitivity;
                           [symmetry; exact Hsta0b | exact Eoom]).
                     rewrite Hq. vm_compute. reflexivity. }
                   destruct (HP4z Ha00) as [Hbel4z Hcov4z].
                   assert (Hbsv2 : rget M4 Rs2 = szv)
                     by (rewrite (rget_ne M4 Rs2 ltac:(bnz)); exact HM4s2).
                   iEval (rewrite -Hpa65b) in "Hf65".
                   iApply (wp_sd_s_sconf (mword_of_int (KXB + 0x352)) Rs2 Rs0
                             (mword_of_int 3576 : mword 12) M4 (K - 68)%nat
                             (M4 !!! Regidx Ra0) eb
                             with "Hcg Hpc [] Hf65").
                   { iApply (kxc_352 with "Htext"). }
                   iIntros (CIDw2 Hsw2) "Hcg Hpc Hf65".
                   iEval (rewrite Hpa65b Hbsv2) in "Hf65".
                   assert (Hpp356 : add_vec_int
                                      (mword_of_int (KXB + 0x352) : mword 64) 4
                                    = mword_of_int (KXB + 0x356)) by bpcw.
                   iEval (rewrite Hpp356) in "Hpc".
                   assert (Htgt324b : add_vec
                             (mword_of_int (KXB + 0x356) : mword 64)
                             (sign_extend' 64 (sign_extend' 21
                                (concat_vec (mword_of_int 2023 : mword 11)
                                            ('b"0"))))
                           = mword_of_int (KXB + 0x324)) by bpcw.
                   iApply (wp_cj_s_sconf (mword_of_int (KXB + 0x356))
                             (sign_extend' 21 (concat_vec
                                (mword_of_int 2023 : mword 11) ('b"0")))
                             M4 (K - 68)%nat eb
                             ltac:(rewrite Htgt324b; vm_compute; reflexivity)
                             with "Hcg Hpc []").
                   { iApply (kxc_356 with "Htext"). }
                   iIntros (CIDw3 Hsw3). iNext. iIntros "Hcg Hpc".
                   iEval (rewrite Htgt324b) in "Hpc".
                   iDestruct (kxc_ph_give sp0 pf Hphal with "Hphb") as "Hph7".
                   iDestruct (kxc_stack8_of_ph sp0 w62 with "Hph7 Hf62")
                     as "Hph8".
                   iDestruct (kxc_pin_intro sp0 ra0 s00 s10 s20 pv av
                                (m !!! Regidx Rs3) (m !!! Regidx Rs4)
                                (m !!! Regidx Rs5) (m !!! Regidx Rs6)
                                (m !!! Regidx Rs7) (m !!! Regidx Rs8)
                                (m !!! Regidx Rs9) (m !!! Regidx Rs10)
                                (m !!! Regidx Rs11)
                                (kxc_off ef i) szv w67 w68
                                with "Hf1 Hf2 Hf3 Hf4 Hf5 Hf6 Hf7 Hf8 Hf9 Hf10
                                      Hf11 Hf12 Hf13 Hust Hph8 Hf63 Hf64 Hf65
                                      Hf66 Hf67 Hf68") as "Hframe".
                   iDestruct (cpu_own_transport CIDz8 CIDw3 0%nat eb
                                (proc_addr jp) eb ltac:(wp_next_chain)
                                with "Hcnt") as "Hcnt".
                   iDestruct (trap_csrs_ext_transport CIDrd CIDw3 eb (proc_addr jp)
                                ltac:(try rewrite Hebb; wp_next_chain) with "Hextc") as "Hextc".
                   iDestruct (cpu_claim_ext_transport CIDrd CIDw3 eb (proc_addr jp)
                                ltac:(try rewrite Hebb; wp_next_chain) with "Hclmc") as "Hclmc".
                   assert (Hbcr2 : true = false \/ proc_addr jp = zero_reg ->
                             (CIDw3 : CPU) = (CID0 : CPU)) by wp_next_chain.
                   iDestruct (wp_next_retarget CID0 CIDw3 true (proc_addr jp) _
                                Hbcr2 with "Hcont") as "Hcont".
                   assert (HM4s6' : M4 !!! Regidx Rs6 = page_base P4.(ud_root))
                     by (rewrite HM4s6 HP4rt; reflexivity).
                   iApply (B2.kxc_bad324 (CID0 := CIDw3) Q gs jp gl gu gd gk pd
                             pav pu bn g gfs gi cn gtl gilf gislf ga gf cov
                             logstart bmapstart inodestart nib size dev
                             kf qf sf gyf inumf dnf bmf n2 plen pfun na
                             avf alen aslen afun pidv V dqb dqs dqa dqpv dqas m M4 K
                             sp0 ra0 s00 s10 s20 pv av (kxc_off ef i) w67 ef
                             P4 szv eb ∅
                             HK Hk Hlg Hsz Hbm0 Hbmc Hbml Hins0 Hcovb Hiregb
                             Hib Hn2 Hjp Hgs Hsp Hra Hs0 Hs1 Hs2
                             HM4sp HM4s0 HM4s4 HM4s6' Hal Hbel4z Hcov4z
                             with "Hcg Hcnt Hextc Hclmc Htext Hpc [] Hopen Hbm Hins
                                   Hbits Hka Hpt Hpriv Hpath Hargv Hargs Helf
                                   Hbs Hirs Hlog Hframe Hcont").
                   { iApply (A.fs_fabric_mk with "Hkd Hpenv Hbio Hlogc Hcrash Hcert Hitab
                                                  Hitinv Hesc Hslks Hireg Hropen Hprocs
                                                  Hdevi Hdgeom Hdlock"). }
                ** (* ---- the table grew ---- *)
                   iApply (wp_beqz_x0_fall_s_sconf (mword_of_int (KXB + 0x184))
                             (mword_of_int 462 : mword 13) Ra0 M4 (K - 68)%nat
                             eb ltac:(bnz) ltac:(exact Eoom)
                             with "Hcg Hpc []").
                   { iApply (kxc_184 with "Htext"). }
                   iIntros (CIDw1 Hsw1) "Hcg Hpc".
                   assert (Hpp188 : add_vec_int
                                      (mword_of_int (KXB + 0x184) : mword 64) 4
                                    = mword_of_int (KXB + 0x188)) by bpcw.
                   iEval (rewrite Hpp188) in "Hpc".
                   assert (Ha0nz : bv_unsigned (M4 !!! Regidx Ra0) <> 0).
                   { intro Hz0. apply eq_vec_false_iff in Eoom. apply Eoom.
                     etransitivity; [exact Hsta0b |].
                     apply bv_eq. rewrite Hz0. vm_compute. reflexivity. }
                   destruct (HP4ne Ha0nz) as [Hbel4n Hcov4n].
                   (* ---- +0x188: lw s3,-456(s0) -- ph.filesz as an int ---- *)
                   assert (Hph32w : add_vec (rget M4 Rs0)
                                      (sign_extend' 64 (mword_of_int 3640
                                                        : mword 12))
                                    = pa_add (pa_stk sp0 61) 32).
                   { rewrite (rget_ne M4 Rs0 ltac:(bnz)) HM4s0 kxc_ph_o32.
                     bs0slot. }
                   iDestruct (kxc_win4 (pa_stk sp0 61) pf 32 20 56 ltac:(lia)
                                Hpa32w with "Hphb") as "[Hw Hbk]".
                   iEval (rewrite -Hph32w) in "Hw".
                   iApply (wp_lw_s_sconf (mword_of_int (KXB + 0x188)) Rs3 Rs0
                             (mword_of_int 3640 : mword 12) M4 (K - 68)%nat
                             (Z_to_bv 32 (le_at pf 32 4) : mword 32) eb
                             (dqm := DfracOwn 1) ltac:(bnz) ltac:(rdok)
                             with "Hcg Hpc [] Hw").
                   { iApply (kxc_188 with "Htext"). }
                   iIntros (CIDw2 Hsw2) "Hcg Hpc Hw".
                   iEval (rewrite Hph32w) in "Hw".
                   iDestruct ("Hbk" with "Hw") as "Hphb".
                   set (U20 := <[Regidx Rs3 := regval_into_reg
                                 (sign_extend' 64 (Z_to_bv 32 (le_at pf 32 4)
                                                   : mword 32))]> M4).
                   assert (HU20sp : U20 !!! Regidx csp_rs1 = pa_stk sp0 68)
                     by (rewrite /U20 upd_ne; [exact HM4sp | bnz]).
                   assert (HU20s0 : U20 !!! Regidx Rs0 = sp0)
                     by (rewrite /U20 upd_ne; [exact HM4s0 | bnz]).
                   assert (HU20s1 : U20 !!! Regidx Rs1 = nsz)
                     by (rewrite /U20 upd_ne; [exact HM4s8 | bnz]).
                   assert (HU20s2 : U20 !!! Regidx Rs2 = szv)
                     by (rewrite /U20 upd_ne; [exact HM4s2 | bnz]).
                   assert (HU20s4 : U20 !!! Regidx Rs4 = ientry kf)
                     by (rewrite /U20 upd_ne; [exact HM4s4 | bnz]).
                   assert (HU20s5 : U20 !!! Regidx Rs5
                                    = (mword_of_int 4096 : mword 64))
                     by (rewrite /U20 upd_ne; [exact HM4s5 | bnz]).
                   assert (HU20s6 : U20 !!! Regidx Rs6 = page_base P4.(ud_root))
                     by (rewrite /U20 upd_ne; [rewrite HM4s6 HP4rt; reflexivity
                                              | bnz]).
                   assert (HU20s9 : U20 !!! Regidx Rs9
                                    = (mword_of_int 4096 : mword 64))
                     by (rewrite /U20 upd_ne; [exact HM4s9 | bnz]).
                   assert (HU20s10 : U20 !!! Regidx Rs10
                                     = (mword_of_int (Z.of_nat i) : mword 64))
                     by (rewrite /U20 upd_ne; [exact HM4s10 | bnz]).
                   assert (HU20s11 : U20 !!! Regidx Rs11
                                     = (mword_of_int 56 : mword 64))
                     by (rewrite /U20 upd_ne; [exact HM4s11 | bnz]).
                   assert (Hpp18c : add_vec_int
                                      (mword_of_int (KXB + 0x188) : mword 64) 4
                                    = mword_of_int (KXB + 0x18c)) by bpcw.
                   iEval (rewrite Hpp18c) in "Hpc".
                   (* ---- the segment's [filesz], as the value the [bgeu]s in
                          the loadseg loop compare ---- *)
                   assert (Hfzr : (0 <= le_at pf 32 4 < 2 ^ 32)%Z).
                   { pose proof (le_at_bound pf 32 4) as Hb.
                     change (2 ^ (8 * Z.of_nat 4))%Z with 4294967296%Z in Hb.
                     change (2 ^ 32)%Z with 4294967296%Z. exact Hb. }
                   assert (HU20s3 : U20 !!! Regidx Rs3
                             = (mword_of_int (w32_uarg (le_at pf 32 4))
                                : mword 64)).
                   { rewrite /U20 upd_eq -kxc_moi32_ztobv.
                     apply w32_arg_moi. exact Hfzr. }
                   assert (Hcmpfz : eq_vec (rget U20 Rs3) (zero_reg : mword 64)
                                    = Z.eqb (w32_uarg (le_at pf 32 4)) 0).
                   { rewrite (rget_ne U20 Rs3 ltac:(bnz)) HU20s3.
                     assert (Hz : (zero_reg : mword 64) = mword_of_int 0)
                       by bpcw.
                     rewrite Hz. apply w32_eq_moi;
                       [ apply w32_uarg_range; exact Hfzr
                       | change (2 ^ 64)%Z with 18446744073709551616%Z; lia ]. }
                   assert (Htgt19c : add_vec
                                       (mword_of_int (KXB + 0x18c) : mword 64)
                                       (sign_extend' 64
                                          (mword_of_int 16 : mword 13))
                                     = mword_of_int (KXB + 0x19c)) by bpcw.
                   destruct (Z.eqb (w32_uarg (le_at pf 32 4)) 0) eqn:Efz.
                   --- (* ---- AN EMPTY SEGMENT: skip loadseg ---- *)
                       iApply (wp_beqz_x0_taken_s_sconf
                                 (mword_of_int (KXB + 0x18c))
                                 (mword_of_int 16 : mword 13) Rs3 U20
                                 (K - 68)%nat eb ltac:(bnz)
                                 ltac:(exact Hcmpfz)
                                 ltac:(rewrite Htgt19c; vm_compute; reflexivity)
                                 with "Hcg Hpc []").
                       { iApply (kxc_18c with "Htext"). }
                       iIntros (CIDv1 Hsv1). iNext. iIntros "Hcg Hpc".
                       iEval (rewrite Htgt19c) in "Hpc".
                       (* the ph buffer goes home: nothing below reads it *)
                       iDestruct (kxc_ph_give sp0 pf Hphal with "Hphb")
                         as "Hph7".
                       iDestruct (kxc_stack8_of_ph sp0 w62 with "Hph7 Hf62")
                         as "Hph8".
                       (* ---- +0x19c: ld s2,-520(s0) -- sz = sz1 ---- *)
                       assert (Hpa65c : add_vec (rget U20 Rs0)
                                          (sign_extend' 64 (mword_of_int 3576
                                                            : mword 12))
                                        = pa_stk sp0 65).
                       { rewrite (rget_ne U20 Rs0 ltac:(bnz)) HU20s0.
                         bs0slot. }
                       iEval (rewrite -Hpa65c) in "Hf65".
                       iApply (wp_ld_s_sconf (mword_of_int (KXB + 0x19c)) Rs2 Rs0
                                 (mword_of_int 3576 : mword 12) U20 (K - 68)%nat
                                 (M4 !!! Regidx Ra0) eb (dqm := DfracOwn 1)
                                 ltac:(bnz) ltac:(rdok)
                                 with "Hcg Hpc [] Hf65").
                       { iApply (kxc_19c with "Htext"). }
                       iIntros (CIDv2 Hsv2) "Hcg Hpc Hf65".
                       iEval (rewrite Hpa65c) in "Hf65".
                       set (U21 := <[Regidx Rs2 := regval_into_reg
                                     (M4 !!! Regidx Ra0)]> U20).
                       assert (HU21s2 : U21 !!! Regidx Rs2 = M4 !!! Regidx Ra0)
                         by (rewrite /U21; apply upd_eq).
                       assert (Hpp1a0 : add_vec_int
                                          (mword_of_int (KXB + 0x19c)
                                           : mword 64) 4
                                        = mword_of_int (KXB + 0x1a0)) by bpcw.
                       iEval (rewrite Hpp1a0) in "Hpc".
                       (* ---- +0x1a0: c.j +0x11a ---- *)
                       assert (Htgt11ab : add_vec
                                 (mword_of_int (KXB + 0x1a0) : mword 64)
                                 (sign_extend' 64 (sign_extend' 21
                                    (concat_vec (mword_of_int 1981 : mword 11)
                                                ('b"0"))))
                               = mword_of_int (KXB + 0x11a)) by bpcw.
                       iApply (wp_cj_s_sconf (mword_of_int (KXB + 0x1a0))
                                 (sign_extend' 21 (concat_vec
                                    (mword_of_int 1981 : mword 11) ('b"0")))
                                 U21 (K - 68)%nat eb
                                 ltac:(rewrite Htgt11ab; vm_compute; reflexivity)
                                 with "Hcg Hpc []").
                       { iApply (kxc_1a0 with "Htext"). }
                       iIntros (CIDv3 Hsv3). iNext. iIntros "Hcg Hpc".
                       iEval (rewrite Htgt11ab) in "Hpc".
                       iDestruct (kxc_pin_intro sp0 ra0 s00 s10 s20 pv av
                                    (m !!! Regidx Rs3) (m !!! Regidx Rs4)
                                    (m !!! Regidx Rs5) (m !!! Regidx Rs6)
                                    (m !!! Regidx Rs7) (m !!! Regidx Rs8)
                                    (m !!! Regidx Rs9) (m !!! Regidx Rs10)
                                    (m !!! Regidx Rs11)
                                    (kxc_off ef i) (M4 !!! Regidx Ra0) w67 w68
                                    with "Hf1 Hf2 Hf3 Hf4 Hf5 Hf6 Hf7 Hf8 Hf9
                                          Hf10 Hf11 Hf12 Hf13 Hust Hph8 Hf63
                                          Hf64 Hf65 Hf66 Hf67 Hf68")
                         as "Hframe".
                       iDestruct (cpu_own_transport CIDz8 CIDv3 0%nat eb
                                    (proc_addr jp) eb ltac:(wp_next_chain)
                                    with "Hcnt") as "Hcnt".
                       iDestruct (trap_csrs_ext_transport CIDrd CIDv3 eb (proc_addr jp)
                                    ltac:(try rewrite Hebb; wp_next_chain) with "Hextc") as "Hextc".
                       iDestruct (cpu_claim_ext_transport CIDrd CIDv3 eb (proc_addr jp)
                                    ltac:(try rewrite Hebb; wp_next_chain) with "Hclmc") as "Hclmc".
                       assert (HU21s0 : U21 !!! Regidx Rs0 = sp0)
                         by (rewrite /U21 upd_ne; [exact HU20s0 | bnz]).
                       assert (HU21sp : U21 !!! Regidx csp_rs1 = pa_stk sp0 68)
                         by (rewrite /U21 upd_ne; [exact HU20sp | bnz]).
                       assert (HU21s4 : U21 !!! Regidx Rs4 = ientry kf)
                         by (rewrite /U21 upd_ne; [exact HU20s4 | bnz]).
                       assert (HU21s5 : U21 !!! Regidx Rs5
                                        = (mword_of_int 4096 : mword 64))
                         by (rewrite /U21 upd_ne; [exact HU20s5 | bnz]).
                       assert (HU21s6 : U21 !!! Regidx Rs6
                                        = page_base P4.(ud_root))
                         by (rewrite /U21 upd_ne; [exact HU20s6 | bnz]).
                       assert (HU21s9 : U21 !!! Regidx Rs9
                                        = (mword_of_int 4096 : mword 64))
                         by (rewrite /U21 upd_ne; [exact HU20s9 | bnz]).
                       assert (HU21s10 : U21 !!! Regidx Rs10
                                 = (mword_of_int (Z.of_nat i) : mword 64))
                         by (rewrite /U21 upd_ne; [exact HU20s10 | bnz]).
                       assert (HU21s11 : U21 !!! Regidx Rs11
                                         = (mword_of_int 56 : mword 64))
                         by (rewrite /U21 upd_ne; [exact HU20s11 | bnz]).
                       iApply (kxc_incr (CID0 := CIDv3) jp bn g gfs gi cn ga gf
                                 cov logstart bmapstart inodestart nib size dev
                                 kf qf sf gyf inumf dnf bmf gilf
                                 gislf n2 plen pfun na avf aslen afun pidv V eb
                                 dqb dqs dqa dqpv dqas m U21 K sp0 ra0 s00 s10 s20 pv av
                                 (m !!! Regidx Rs3) (m !!! Regidx Rs4)
                                 (m !!! Regidx Rs5) (m !!! Regidx Rs6)
                                 (m !!! Regidx Rs7) (m !!! Regidx Rs8)
                                 (m !!! Regidx Rs9) (m !!! Regidx Rs10)
                                 (m !!! Regidx Rs11)
                                 (M4 !!! Regidx Ra0) w67 ef P4 i
                                 (M4 !!! Regidx Ra0)
                                 with "Htext [-Hout Hcont] [Hout Hcont]").
                       { rewrite /kxc_at_11a /kxc_res.
                         iSplitR.
                         { iPureIntro. split_and!;
                             [exact HU21sp | exact HU21s0 | exact HU21s2
                             | exact HU21s4 | exact HU21s5 | exact HU21s6
                             | exact HU21s9 | exact HU21s10 | exact HU21s11]. }
                         iSplitR.
                         { iPureIntro. split_and!;
                             [exact Hk2 | exact Hib | exact Hn2
                             | exact Hal]. }
                         iSplitR.
                         { iPureIntro. split_and!;
                             [exact Hiphn
                             | rewrite HP4tf; exact HPtfp
                             | exact Hbel4n | exact Hcov4n]. }
                         iSplitL "Hpc"; [iExact "Hpc" |].
                         iSplitL "Hcg"; [iExact "Hcg" |].
                         iSplitL "Hcnt"; [iExact "Hcnt" |].
                         iSplitL "Hextc"; [iExact "Hextc" |]. iSplitL "Hclmc"; [iExact "Hclmc" |].
                         iSplitR; [iExact "Hka" |].
                         iSplitL "Hopen"; [iExact "Hopen" |].
                         iSplitL "Hlog"; [iExact "Hlog" |].
                         iSplitL "Hirs"; [iExact "Hirs" |].
                         iSplitL "Hbm"; [iExact "Hbm" |].
                         iSplitL "Hins"; [iExact "Hins" |].
                         iSplitL "Hbits"; [iExact "Hbits" |].
                         iSplitL "Hbs"; [iExact "Hbs" |].
                         iSplitL "Hpt"; [iExact "Hpt" |].
                         iSplitL "Hpriv"; [iExact "Hpriv" |].
                         iSplitL "Hpath"; [iExact "Hpath" |].
                         iSplitL "Hargv"; [iExact "Hargv" |].
                         iSplitL "Hargs"; [iExact "Hargs" |].
                         iSplitL "Helf"; [iExact "Helf" | iExact "Hframe"]. }
                       iIntros (CIDh Hsh M') "Hdisj".
                       assert (Hcrh : true = false \/ proc_addr jp = zero_reg ->
                                 (CIDh : CPU) = (CID0 : CPU)) by wp_next_chain.
                       iDestruct (wp_next_retarget CID0 CIDh true (proc_addr jp)
                                    _ Hcrh with "Hcont") as "Hcont".
                       iSpecialize ("Hout" $! CIDh with "[%]"); [wp_next_chain |].
                       iApply ("Hout" $! M' P4 (M4 !!! Regidx Ra0)
                                 with "Hdisj Hcont").
                   --- (* ---- A NON-EMPTY SEGMENT: run the loadseg loop ---- *)
                       iApply (wp_beqz_x0_fall_s_sconf
                                 (mword_of_int (KXB + 0x18c))
                                 (mword_of_int 16 : mword 13) Rs3 U20
                                 (K - 68)%nat eb ltac:(bnz)
                                 ltac:(exact Hcmpfz)
                                 with "Hcg Hpc []").
                       { iApply (kxc_18c with "Htext"). }
                       iIntros (CIDv1 Hsv1) "Hcg Hpc".
                       assert (Hpp190 : add_vec_int
                                          (mword_of_int (KXB + 0x18c)
                                           : mword 64) 4
                                        = mword_of_int (KXB + 0x190)) by bpcw.
                       iEval (rewrite Hpp190) in "Hpc".
                       (* ---- +0x190: ld s8,-472(s0) -- ph.vaddr ---- *)
                       assert (Hph16b : add_vec (rget U20 Rs0)
                                          (sign_extend' 64 (mword_of_int 3624
                                                            : mword 12))
                                        = pa_add (pa_stk sp0 61) 16).
                       { rewrite (rget_ne U20 Rs0 ltac:(bnz)) HU20s0 kxc_ph_o16.
                         bs0slot. }
                       iDestruct (kxc_win8 (pa_stk sp0 61) pf 16 32 56
                                    ltac:(lia) Hpa16 with "Hphb") as "[Hw Hbk]".
                       iEval (rewrite -Hph16b) in "Hw".
                       iApply (wp_ld_s_sconf (mword_of_int (KXB + 0x190)) Rs8 Rs0
                                 (mword_of_int 3624 : mword 12) U20 (K - 68)%nat
                                 (Z_to_bv 64 (le_at pf 16 8) : mword 64) eb
                                 (dqm := DfracOwn 1) ltac:(bnz) ltac:(rdok)
                                 with "Hcg Hpc [] Hw").
                       { iApply (kxc_190 with "Htext"). }
                       iIntros (CIDv2 Hsv2) "Hcg Hpc Hw".
                       iEval (rewrite Hph16b) in "Hw".
                       iDestruct ("Hbk" with "Hw") as "Hphb".
                       set (U22 := <[Regidx Rs8 := regval_into_reg
                                     (Z_to_bv 64 (le_at pf 16 8)
                                      : mword 64)]> U20).
                       assert (HU22s0 : U22 !!! Regidx Rs0 = sp0)
                         by (rewrite /U22 upd_ne; [exact HU20s0 | bnz]).
                       assert (Hpp194 : add_vec_int
                                          (mword_of_int (KXB + 0x190)
                                           : mword 64) 4
                                        = mword_of_int (KXB + 0x194)) by bpcw.
                       iEval (rewrite Hpp194) in "Hpc".
                       (* ---- +0x194: lw s7,-480(s0) -- ph.off as an int ---- *)
                       assert (Hph8b : add_vec (rget U22 Rs0)
                                         (sign_extend' 64 (mword_of_int 3616
                                                           : mword 12))
                                       = pa_add (pa_stk sp0 61) 8).
                       { rewrite (rget_ne U22 Rs0 ltac:(bnz)) HU22s0 kxc_ph_o8.
                         bs0slot. }
                       iDestruct (kxc_win4 (pa_stk sp0 61) pf 8 44 56 ltac:(lia)
                                    Hpa8 with "Hphb") as "[Hw Hbk]".
                       iEval (rewrite -Hph8b) in "Hw".
                       iApply (wp_lw_s_sconf (mword_of_int (KXB + 0x194)) Rs7 Rs0
                                 (mword_of_int 3616 : mword 12) U22 (K - 68)%nat
                                 (Z_to_bv 32 (le_at pf 8 4) : mword 32) eb
                                 (dqm := DfracOwn 1) ltac:(bnz) ltac:(rdok)
                                 with "Hcg Hpc [] Hw").
                       { iApply (kxc_194 with "Htext"). }
                       iIntros (CIDv3 Hsv3) "Hcg Hpc Hw".
                       iEval (rewrite Hph8b) in "Hw".
                       iDestruct ("Hbk" with "Hw") as "Hphb".
                       set (U23 := <[Regidx Rs7 := regval_into_reg
                                     (sign_extend' 64 (Z_to_bv 32 (le_at pf 8 4)
                                                       : mword 32))]> U22).
                       assert (Hpp198 : add_vec_int
                                          (mword_of_int (KXB + 0x194)
                                           : mword 64) 4
                                        = mword_of_int (KXB + 0x198)) by bpcw.
                       iEval (rewrite Hpp198) in "Hpc".
                       (* ---- +0x198: c.li s1,0 -- the page cursor ---- *)
                       iApply (wp_cli_s_sconf (mword_of_int (KXB + 0x198)) Rs1
                                 (mword_of_int 0 : mword 6)
                                 (mword_of_int 0 : mword 64) U23 (K - 68)%nat
                                 eb ltac:(bnz) ltac:(rdok)
                                 ltac:(apply bv_eq; vm_compute; reflexivity)
                                 with "Hcg Hpc []").
                       { iApply (kxc_198 with "Htext"). }
                       iIntros (CIDv4 Hsv4) "Hcg Hpc".
                       set (U24 := <[Regidx Rs1 := regval_into_reg
                                     (mword_of_int 0 : mword 64)]> U23).
                       assert (Hpp19a : add_vec_int
                                          (mword_of_int (KXB + 0x198)
                                           : mword 64) 2
                                        = mword_of_int (KXB + 0x19a)) by bpcw.
                       iEval (rewrite Hpp19a) in "Hpc".
                       (* ---- +0x19a: c.j +0x0f6 -- into the loadseg loop ---- *)
                       assert (Htgt0f6 : add_vec
                                 (mword_of_int (KXB + 0x19a) : mword 64)
                                 (sign_extend' 64 (sign_extend' 21
                                    (concat_vec (mword_of_int 1966 : mword 11)
                                                ('b"0"))))
                               = mword_of_int (KXB + 0xf6)) by bpcw.
                       iApply (wp_cj_s_sconf (mword_of_int (KXB + 0x19a))
                                 (sign_extend' 21 (concat_vec
                                    (mword_of_int 1966 : mword 11) ('b"0")))
                                 U24 (K - 68)%nat eb
                                 ltac:(rewrite Htgt0f6; vm_compute; reflexivity)
                                 with "Hcg Hpc []").
                       { iApply (kxc_19a with "Htext"). }
                       iIntros (CIDv5 Hsv5). iNext. iIntros "Hcg Hpc".
                       iEval (rewrite Htgt0f6) in "Hpc".
                       (* ---- the ph buffer goes home ---- *)
                       iDestruct (kxc_ph_give sp0 pf Hphal with "Hphb")
                         as "Hph7".
                       iDestruct (kxc_stack8_of_ph sp0 w62 with "Hph7 Hf62")
                         as "Hph8".
                       iDestruct (kxc_pin_intro sp0 ra0 s00 s10 s20 pv av
                                    (m !!! Regidx Rs3) (m !!! Regidx Rs4)
                                    (m !!! Regidx Rs5) (m !!! Regidx Rs6)
                                    (m !!! Regidx Rs7) (m !!! Regidx Rs8)
                                    (m !!! Regidx Rs9) (m !!! Regidx Rs10)
                                    (m !!! Regidx Rs11)
                                    (kxc_off ef i) (M4 !!! Regidx Ra0) w67 w68
                                    with "Hf1 Hf2 Hf3 Hf4 Hf5 Hf6 Hf7 Hf8 Hf9
                                          Hf10 Hf11 Hf12 Hf13 Hust Hph8 Hf63
                                          Hf64 Hf65 Hf66 Hf67 Hf68")
                         as "Hframe".
                       (* ---- the loadseg loop's register premises ---- *)
                       assert (Hpor : (0 <= le_at pf 8 4 < 2 ^ 32)%Z).
                       { pose proof (le_at_bound pf 8 4) as Hb.
                         change (2 ^ (8 * Z.of_nat 4))%Z with 4294967296%Z in Hb.
                         change (2 ^ 32)%Z with 4294967296%Z. exact Hb. }
                       assert (HU24s1 : U24 !!! Regidx Rs1
                                 = sign_extend' 64 (mword_of_int (0%Z)
                                                    : mword 32)).
                       { rewrite /U24 upd_eq. apply w32_moi_arg.
                         change (2 ^ 31)%Z with 2147483648%Z. lia. }
                       assert (HU24s3 : U24 !!! Regidx Rs3
                                 = sign_extend' 64 (mword_of_int (le_at pf 32 4)
                                                    : mword 32)).
                       { rewrite /U24 upd_ne; [| bnz].
                         rewrite /U23 upd_ne; [| bnz].
                         rewrite /U22 upd_ne; [| bnz].
                         rewrite /U20 upd_eq kxc_moi32_ztobv. reflexivity. }
                       assert (HU24s7 : U24 !!! Regidx Rs7
                                 = sign_extend' 64 (mword_of_int (le_at pf 8 4)
                                                    : mword 32)).
                       { rewrite /U24 upd_ne; [| bnz].
                         rewrite /U23 upd_eq kxc_moi32_ztobv. reflexivity. }
                       assert (HU24s8 : U24 !!! Regidx Rs8
                                 = (Z_to_bv 64 (le_at pf 16 8) : mword 64)).
                       { rewrite /U24 upd_ne; [| bnz].
                         rewrite /U23 upd_ne; [| bnz]. rewrite /U22; apply upd_eq. }
                       assert (HU24sp : U24 !!! Regidx csp_rs1 = pa_stk sp0 68).
                       { rewrite /U24 upd_ne; [| bnz].
                         rewrite /U23 upd_ne; [| bnz].
                         rewrite /U22 upd_ne; [exact HU20sp | bnz]. }
                       assert (HU24s0 : U24 !!! Regidx Rs0 = sp0).
                       { rewrite /U24 upd_ne; [| bnz].
                         rewrite /U23 upd_ne; [| bnz].
                         rewrite /U22 upd_ne; [exact HU20s0 | bnz]. }
                       assert (HU24s4 : U24 !!! Regidx Rs4 = ientry kf).
                       { rewrite /U24 upd_ne; [| bnz].
                         rewrite /U23 upd_ne; [| bnz].
                         rewrite /U22 upd_ne; [exact HU20s4 | bnz]. }
                       assert (HU24s5 : U24 !!! Regidx Rs5
                                        = (mword_of_int 4096 : mword 64)).
                       { rewrite /U24 upd_ne; [| bnz].
                         rewrite /U23 upd_ne; [| bnz].
                         rewrite /U22 upd_ne; [exact HU20s5 | bnz]. }
                       assert (HU24s6 : U24 !!! Regidx Rs6
                                        = page_base P4.(ud_root)).
                       { rewrite /U24 upd_ne; [| bnz].
                         rewrite /U23 upd_ne; [| bnz].
                         rewrite /U22 upd_ne; [exact HU20s6 | bnz]. }
                       assert (HU24s9 : U24 !!! Regidx Rs9
                                        = (mword_of_int 4096 : mword 64)).
                       { rewrite /U24 upd_ne; [| bnz].
                         rewrite /U23 upd_ne; [| bnz].
                         rewrite /U22 upd_ne; [exact HU20s9 | bnz]. }
                       assert (HU24s10 : U24 !!! Regidx Rs10
                                 = (mword_of_int (Z.of_nat i) : mword 64)).
                       { rewrite /U24 upd_ne; [| bnz].
                         rewrite /U23 upd_ne; [| bnz].
                         rewrite /U22 upd_ne; [exact HU20s10 | bnz]. }
                       assert (HU24s11 : U24 !!! Regidx Rs11
                                         = (mword_of_int 56 : mword 64)).
                       { rewrite /U24 upd_ne; [| bnz].
                         rewrite /U23 upd_ne; [| bnz].
                         rewrite /U22 upd_ne; [exact HU20s11 | bnz]. }
                       assert (Hguard : (w32_uarg 0 < w32_uarg (le_at pf 32 4))%Z).
                       { rewrite kxc_uarg0.
                         pose proof (w32_uarg_range _ Hfzr) as [Hg0 _].
                         apply Z.eqb_neq in Efz. lia. }
                       iDestruct (cpu_own_transport CIDz8 CIDv5 0%nat eb
                                    (proc_addr jp) eb ltac:(wp_next_chain)
                                    with "Hcnt") as "Hcnt".
                       iDestruct (trap_csrs_ext_transport CIDrd CIDv5 eb (proc_addr jp)
                                    ltac:(try rewrite Hebb; wp_next_chain) with "Hextc") as "Hextc".
                       iDestruct (cpu_claim_ext_transport CIDrd CIDv5 eb (proc_addr jp)
                                    ltac:(try rewrite Hebb; wp_next_chain) with "Hclmc") as "Hclmc".
                       assert (Hcrl : true = false \/ proc_addr jp = zero_reg ->
                                 (CIDv5 : CPU) = (CID0 : CPU)) by wp_next_chain.
                       iDestruct (wp_next_retarget CID0 CIDv5 true (proc_addr jp)
                                    _ Hcrl with "Hcont") as "Hcont".
                       iApply (B2.kxc_ls (CID0 := CIDv5) Q gs jp gl gu gd gk pd pav
                                 pu bn g gfs gi cn gtl gilf gislf ga gf cov
                                 logstart bmapstart inodestart nib size dev
                                 kf qf sf gyf inumf dnf bmf n2 plen pfun na
                                 avf alen aslen afun pidv V dqb dqs dqa dqpv dqas m K
                                 sp0 ra0 s00 s10 s20 pv av (kxc_off ef i)
                                 (M4 !!! Regidx Ra0) w67 ef P4 i
                                 (Z_to_bv 64 (le_at pf 16 8) : mword 64)
                                 (le_at pf 32 4) (le_at pf 8 4) eb ∅
                                 HK Hk Hlg Hsz Hbm0 Hbmc Hbml Hins0 Hcovb Hiregb
                                 Hib Hn2 Hjp Hgs Hdevc Hsp Hra Hs0 Hs1 Hs2
                                 Hal Hbel4n Hcov4n Hfzr Hpor
                                 (Z.to_nat (2 ^ 32)) U24 0%Z
                                 ltac:(change (2 ^ 32)%Z with 4294967296%Z; lia)
                                 ltac:(rewrite Z2Nat.id;
                                       [ pose proof (Z.mod_pos_bound
                                           (le_at pf 8 4 + 0) (2 ^ 32)
                                           ltac:(change (2 ^ 32)%Z
                                                 with 4294967296%Z; lia)); lia
                                       | change (2 ^ 32)%Z with 4294967296%Z;
                                         lia ])
                                 Hguard HU24sp HU24s0 HU24s1 HU24s3 HU24s4
                                 HU24s5 HU24s6 HU24s7 HU24s8 HU24s9 HU24s10
                                 HU24s11
                                 with "Hcg Hcnt Hextc Hclmc Htext Hpc [] Hka
                                       [-Hcont Hout] Hcont [Hout]").
                       { iApply (A.fs_fabric_mk with "Hkd Hpenv Hbio Hlogc Hcrash Hcert
                                                      Hitab Hitinv Hesc Hslks
                                                      Hireg Hropen Hprocs Hdevi Hdgeom
                                                      Hdlock"). }
                       { rewrite /kxc_res.
                         iSplitL "Hopen"; [iExact "Hopen" |].
                         iSplitL "Hlog"; [iExact "Hlog" |].
                         iSplitL "Hirs"; [iExact "Hirs" |].
                         iSplitL "Hbm"; [iExact "Hbm" |].
                         iSplitL "Hins"; [iExact "Hins" |].
                         iSplitL "Hbits"; [iExact "Hbits" |].
                         iSplitL "Hbs"; [iExact "Hbs" |].
                         iSplitL "Hpt"; [iExact "Hpt" |].
                         iSplitL "Hpriv"; [iExact "Hpriv" |].
                         iSplitL "Hpath"; [iExact "Hpath" |].
                         iSplitL "Hargv"; [iExact "Hargv" |].
                         iSplitL "Hargs"; [iExact "Hargs" |].
                         iSplitL "Helf"; [iExact "Helf" | iExact "Hframe"]. }
                       (* ---- +0x116: the segment is in memory ---- *)
                       iIntros (CIDq1 Hsq1 Mx) "%Hmx Hcg Hcnt Hextc Hclmc Hpc Hres Hcont".
                       destruct Hmx as (HMxsp & HMxs0 & HMxs4 & HMxs5 & HMxs6 &
                                        HMxs9 & HMxs10 & HMxs11).
                       rewrite /kxc_res.
                       iDestruct "Hres" as "(Hopen & Hlog & Hirs & Hbm & Hins &
                                             Hbits & Hbs & Hpt & Hpriv & Hpath &
                                             Hargv & Hargs & Helf & Hframe)".
                       rewrite /kxc_frameBpin.
                       iDestruct "Hframe" as "(Hf1 & Hf2 & Hf3 & Hf4 & Hf5 &
                                               Hf6 & Hf7 & Hf8 & Hf9 & Hf10 &
                                               Hf11 & Hf12 & Hf13 & Hust &
                                               Hph8 & Hf63 & Hf64 & Hf65 &
                                               Hf66 & Hf67 & Hf68e)".
                       iDestruct "Hf68e" as (w68b) "Hf68".
                       assert (Hpa65d : add_vec (rget Mx Rs0)
                                          (sign_extend' 64 (mword_of_int 3576
                                                            : mword 12))
                                        = pa_stk sp0 65).
                       { rewrite (rget_ne Mx Rs0 ltac:(bnz)) HMxs0. bs0slot. }
                       iEval (rewrite -Hpa65d) in "Hf65".
                       iApply (wp_ld_s_sconf (mword_of_int (KXB + 0x116)) Rs2 Rs0
                                 (mword_of_int 3576 : mword 12) Mx (K - 68)%nat
                                 (M4 !!! Regidx Ra0) eb (dqm := DfracOwn 1)
                                 ltac:(bnz) ltac:(rdok)
                                 with "Hcg Hpc [] Hf65").
                       { iApply (kxc_116 with "Htext"). }
                       iIntros (CIDq2 Hsq2) "Hcg Hpc Hf65".
                       iEval (rewrite Hpa65d) in "Hf65".
                       set (U25 := <[Regidx Rs2 := regval_into_reg
                                     (M4 !!! Regidx Ra0)]> Mx).
                       assert (HU25s2 : U25 !!! Regidx Rs2 = M4 !!! Regidx Ra0)
                         by (rewrite /U25; apply upd_eq).
                       assert (HU25sp : U25 !!! Regidx csp_rs1 = pa_stk sp0 68)
                         by (rewrite /U25 upd_ne; [exact HMxsp | bnz]).
                       assert (HU25s0 : U25 !!! Regidx Rs0 = sp0)
                         by (rewrite /U25 upd_ne; [exact HMxs0 | bnz]).
                       assert (HU25s4 : U25 !!! Regidx Rs4 = ientry kf)
                         by (rewrite /U25 upd_ne; [exact HMxs4 | bnz]).
                       assert (HU25s5 : U25 !!! Regidx Rs5
                                        = (mword_of_int 4096 : mword 64))
                         by (rewrite /U25 upd_ne; [exact HMxs5 | bnz]).
                       assert (HU25s6 : U25 !!! Regidx Rs6
                                        = page_base P4.(ud_root))
                         by (rewrite /U25 upd_ne; [exact HMxs6 | bnz]).
                       assert (HU25s9 : U25 !!! Regidx Rs9
                                        = (mword_of_int 4096 : mword 64))
                         by (rewrite /U25 upd_ne; [exact HMxs9 | bnz]).
                       assert (HU25s10 : U25 !!! Regidx Rs10
                                 = (mword_of_int (Z.of_nat i) : mword 64))
                         by (rewrite /U25 upd_ne; [exact HMxs10 | bnz]).
                       assert (HU25s11 : U25 !!! Regidx Rs11
                                         = (mword_of_int 56 : mword 64))
                         by (rewrite /U25 upd_ne; [exact HMxs11 | bnz]).
                       assert (Hpp11ab : add_vec_int
                                           (mword_of_int (KXB + 0x116)
                                            : mword 64) 4
                                         = mword_of_int (KXB + 0x11a)) by bpcw.
                       iEval (rewrite Hpp11ab) in "Hpc".
                       iDestruct (kxc_pin_intro sp0 ra0 s00 s10 s20 pv av
                                    (m !!! Regidx Rs3) (m !!! Regidx Rs4)
                                    (m !!! Regidx Rs5) (m !!! Regidx Rs6)
                                    (m !!! Regidx Rs7) (m !!! Regidx Rs8)
                                    (m !!! Regidx Rs9) (m !!! Regidx Rs10)
                                    (m !!! Regidx Rs11)
                                    (kxc_off ef i) (M4 !!! Regidx Ra0) w67 w68b
                                    with "Hf1 Hf2 Hf3 Hf4 Hf5 Hf6 Hf7 Hf8 Hf9
                                          Hf10 Hf11 Hf12 Hf13 Hust Hph8 Hf63
                                          Hf64 Hf65 Hf66 Hf67 Hf68")
                         as "Hframe".
                       iDestruct (cpu_own_transport CIDq1 CIDq2 0%nat eb
                                    (proc_addr jp) eb ltac:(wp_next_chain)
                                    with "Hcnt") as "Hcnt".
                       iDestruct (trap_csrs_ext_transport CIDq1 CIDq2 eb (proc_addr jp)
                                    ltac:(try rewrite Hebb; wp_next_chain) with "Hextc") as "Hextc".
                       iDestruct (cpu_claim_ext_transport CIDq1 CIDq2 eb (proc_addr jp)
                                    ltac:(try rewrite Hebb; wp_next_chain) with "Hclmc") as "Hclmc".
                       iApply (kxc_incr (CID0 := CIDq2) jp bn g gfs gi cn ga gf
                                 cov logstart bmapstart inodestart nib size dev
                                 kf qf sf gyf inumf dnf bmf gilf
                                 gislf n2 plen pfun na avf aslen afun pidv V eb
                                 dqb dqs dqa dqpv dqas m U25 K sp0 ra0 s00 s10 s20 pv av
                                 (m !!! Regidx Rs3) (m !!! Regidx Rs4)
                                 (m !!! Regidx Rs5) (m !!! Regidx Rs6)
                                 (m !!! Regidx Rs7) (m !!! Regidx Rs8)
                                 (m !!! Regidx Rs9) (m !!! Regidx Rs10)
                                 (m !!! Regidx Rs11)
                                 (M4 !!! Regidx Ra0) w67 ef P4 i
                                 (M4 !!! Regidx Ra0)
                                 with "Htext [-Hout Hcont] [Hout Hcont]").
                       { rewrite /kxc_at_11a /kxc_res.
                         iSplitR.
                         { iPureIntro. split_and!;
                             [exact HU25sp | exact HU25s0 | exact HU25s2
                             | exact HU25s4 | exact HU25s5 | exact HU25s6
                             | exact HU25s9 | exact HU25s10 | exact HU25s11]. }
                         iSplitR.
                         { iPureIntro. split_and!;
                             [exact Hk2 | exact Hib | exact Hn2
                             | exact Hal]. }
                         iSplitR.
                         { iPureIntro. split_and!;
                             [exact Hiphn
                             | rewrite HP4tf; exact HPtfp
                             | exact Hbel4n | exact Hcov4n]. }
                         iSplitL "Hpc"; [iExact "Hpc" |].
                         iSplitL "Hcg"; [iExact "Hcg" |].
                         iSplitL "Hcnt"; [iExact "Hcnt" |].
                         iSplitL "Hextc"; [iExact "Hextc" |]. iSplitL "Hclmc"; [iExact "Hclmc" |].
                         iSplitR; [iExact "Hka" |].
                         iSplitL "Hopen"; [iExact "Hopen" |].
                         iSplitL "Hlog"; [iExact "Hlog" |].
                         iSplitL "Hirs"; [iExact "Hirs" |].
                         iSplitL "Hbm"; [iExact "Hbm" |].
                         iSplitL "Hins"; [iExact "Hins" |].
                         iSplitL "Hbits"; [iExact "Hbits" |].
                         iSplitL "Hbs"; [iExact "Hbs" |].
                         iSplitL "Hpt"; [iExact "Hpt" |].
                         iSplitL "Hpriv"; [iExact "Hpriv" |].
                         iSplitL "Hpath"; [iExact "Hpath" |].
                         iSplitL "Hargv"; [iExact "Hargv" |].
                         iSplitL "Hargs"; [iExact "Hargs" |].
                         iSplitL "Helf"; [iExact "Helf" | iExact "Hframe"]. }
                       iIntros (CIDh Hsh M') "Hdisj".
                       (* [Hcont] is the one [kxc_ls] HANDED BACK, so it is
                          anchored at the loop's exit hart, not at [CID0]. *)
                       assert (Hcrh : true = false \/ proc_addr jp = zero_reg ->
                                 (CIDh : CPU) = (CIDq1 : CPU)) by wp_next_chain.
                       iDestruct (wp_next_retarget CIDq1 CIDh true (proc_addr jp)
                                    _ Hcrh with "Hcont") as "Hcont".
                       iSpecialize ("Hout" $! CIDh with "[%]"); [wp_next_chain |].
                       iApply ("Hout" $! M' P4 (M4 !!! Regidx Ra0)
                                 with "Hdisj Hcont").
    - (* ================ A SHORT READ: [bad:] at +0x320 ============ *)
      iApply (wp_bne_taken_s_sconf (mword_of_int (KXB + 0x13e))
                (mword_of_int 482 : mword 13) Rs11 Ra0 M2 (K - 68)%nat eb
                ltac:(bnz) ltac:(bnz)
                ltac:(rewrite Hcmp13e;
                      replace (Z.eqb (Z.of_nat tot) 56) with false;
                      [reflexivity | symmetry; apply Z.eqb_neq; lia])
                ltac:(rewrite Htgt320; vm_compute; reflexivity)
                with "Hcg Hpc []").
      { iApply (kxc_13e with "Htext"). }
      iIntros (CIDb1 Hsb1). iNext. iIntros "Hcg Hpc".
      iEval (rewrite Htgt320) in "Hpc".
      (* ---- +0x320: sd s2,-520(s0) -- the size the tail frees ---- *)
      assert (Hpa65 : add_vec (rget M2 Rs0)
                        (sign_extend' 64 (mword_of_int 3576 : mword 12))
                      = pa_stk sp0 65).
      { rewrite (rget_ne M2 Rs0 ltac:(bnz)) HM2s0. bs0slot. }
      assert (Hsts2 : rget M2 Rs2 = szv)
        by (rewrite (rget_ne M2 Rs2 ltac:(bnz)); exact HM2s2).
      iEval (rewrite -Hpa65) in "Hf65".
      iApply (wp_sd_s_sconf (mword_of_int (KXB + 0x320)) Rs2 Rs0
                (mword_of_int 3576 : mword 12) M2 (K - 68)%nat w65 eb
                with "Hcg Hpc [] Hf65").
      { iApply (kxc_320 with "Htext"). }
      iIntros (CIDb2 Hsb2) "Hcg Hpc Hf65".
      iEval (rewrite Hpa65 Hsts2) in "Hf65".
      assert (Hpp324 : add_vec_int (mword_of_int (KXB + 0x320) : mword 64) 4
                       = mword_of_int (KXB + 0x324)) by bpcw.
      iEval (rewrite Hpp324) in "Hpc".
      iDestruct (kxc_ph_give sp0 pf Hphal with "Hphb") as "Hph7".
      iDestruct (kxc_stack8_of_ph sp0 w62 with "Hph7 Hf62") as "Hph8".
      iDestruct (kxc_pin_intro sp0 ra0 s00 s10 s20 pv av
                   (m !!! Regidx Rs3) (m !!! Regidx Rs4) (m !!! Regidx Rs5)
                   (m !!! Regidx Rs6) (m !!! Regidx Rs7) (m !!! Regidx Rs8)
                   (m !!! Regidx Rs9) (m !!! Regidx Rs10) (m !!! Regidx Rs11)
                   (kxc_off ef i) szv w67 w68
                   with "Hf1 Hf2 Hf3 Hf4 Hf5 Hf6 Hf7 Hf8 Hf9 Hf10 Hf11 Hf12
                         Hf13 Hust Hph8 Hf63 Hf64 Hf65 Hf66 Hf67 Hf68")
        as "Hframe".
      iDestruct (cpu_own_transport CIDrd CIDb2 0%nat eb (proc_addr jp) eb
                   ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
      iDestruct (trap_csrs_ext_transport CIDrd CIDb2 eb (proc_addr jp)
                   ltac:(try rewrite Hebb; wp_next_chain) with "Hextc") as "Hextc".
      iDestruct (cpu_claim_ext_transport CIDrd CIDb2 eb (proc_addr jp)
                   ltac:(try rewrite Hebb; wp_next_chain) with "Hclmc") as "Hclmc".
      assert (Hcrb : true = false \/ proc_addr jp = zero_reg ->
                (CIDb2 : CPU) = (CID0 : CPU)) by wp_next_chain.
      iDestruct (wp_next_retarget CID0 CIDb2 true (proc_addr jp) _ Hcrb
                   with "Hcont") as "Hcont".
      iApply (B2.kxc_bad324 (CID0 := CIDb2) Q gs jp gl gu gd gk pd pav pu bn g
                gfs gi cn gtl gilf gislf ga gf cov logstart bmapstart
                inodestart nib size dev kf qf sf gyf inumf dnf bmf
                n2 plen pfun na avf alen aslen afun pidv V dqb dqs dqa dqpv dqas m M2
                K sp0 ra0 s00 s10 s20 pv av (kxc_off ef i) w67 ef P szv eb ∅
                HK Hk Hlg Hsz Hbm0 Hbmc Hbml Hins0 Hcovb Hiregb Hib Hn2 Hjp
                Hgs Hsp Hra Hs0 Hs1 Hs2 HM2sp HM2s0 HM2s4 HM2s6
                Hal Hbelow Hcov
                with "Hcg Hcnt Hextc Hclmc Htext Hpc [] Hopen Hbm Hins Hbits Hka
                      Hpt Hpriv Hpath Hargv Hargs Helf Hbs Hirs Hlog Hframe
                      Hcont").
      { iApply (A.fs_fabric_mk with "Hkd Hpenv Hbio Hlogc Hcrash Hcert Hitab Hitinv
                                     Hesc Hslks Hireg Hropen Hprocs Hdevi Hdgeom
                                     Hdlock"). }
  Qed.

End KexecB3Body.

(* ===================================================================== *)
(*  THE PHDR LOOP.                                                        *)
(* ===================================================================== *)
(* One [kxc_ph_step] per header, and the measure is [eh_phnum ef - i].  The
   [W = 0] case is not vacuous by arithmetic: the back-edge disjunct carries
   [S i <= eh_phnum ef], which is what contradicts the exhausted fuel. *)
Section KexecB3Loop.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ, !irefslotG Σ, !pavG Σ}.
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
  Notation Rs8 := (mword_of_int 24 : mword 5).
  Notation Rs9 := (mword_of_int 25 : mword 5).
  Notation Rs10 := (mword_of_int 26 : mword 5).
  Notation Rs11 := (mword_of_int 27 : mword 5).
  Notation Ra0 := (mword_of_int 10 : mword 5).

  Lemma kxc_phdr `{CID0 : CpuId}
      (Q : mword 64 -> Prop)
      (gs : list gname) (jp : nat) (gl : gname)
      (gu : uart_names) (gd : disk_names) (gk : gname) (pd pav pu : mword 64)
      (bn : bio_names) (g : log_names) (gfs : fs_names) (gi : gname)
      (cn : ic_names) (gtl : gname) (gilf gislf : gname) (ga gf : gname)
      (cov : gset Z) (logstart bmapstart inodestart : Z) (nib : nat)
      (size : Z) (dev : mword 32)
      (kf : nat) (qf sf : Qp) (gyf : gname) (inumf : mword 32)
      (dnf : dinode) (bmf : blkmap) (n2 : nat)
      (plen : nat) (pfun : nat -> bv 8)
      (na : nat) (avf : nat -> mword 64) (alen aslen : nat -> nat)
      (afun : nat -> nat -> bv 8)
      (pidv : mword 32) (V : pprivate) (eb : bool) (dqb dqs dqa dqpv dqas : dfrac)
      (m : regfile) (K : nat)
      (sp0 ra0 s00 s10 s20 pv av w67 : mword 64)
      (ef : nat -> bv 8) :
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
    (jp < NPROC)%nat ->
    gs !! jp = Some gl ->
    dev = icfg_dev ->
    m !!! Regidx csp_rs1 = sp0 ->
    m !!! Regidx Rra = ra0 ->
    m !!! Regidx Rs0 = s00 ->
    m !!! Regidx Rs1 = s10 ->
    m !!! Regidx Rs2 = s20 ->
    forall (W : nat) (M : regfile) (P : uptd) (i : nat) (szv : mword 64),
    (eh_phnum ef - Z.of_nat i <= Z.of_nat W)%Z ->
    kernel_text -∗
    fs_fabric gs gu gd gk pd pav pu bn g gfs gi cn gtl
              cov logstart inodestart nib dev -∗
    kxc_at_12c jp bn g gfs gi cn ga gf cov logstart bmapstart inodestart nib
               size dev kf qf sf gyf inumf dnf bmf gilf gislf n2
               plen pfun na avf aslen afun pidv V eb dqb dqs dqa dqpv dqas m M K
               sp0 ra0 s00 s10 s20 pv av
               (m !!! Regidx Rs3) (m !!! Regidx Rs4) (m !!! Regidx Rs5)
               (m !!! Regidx Rs6) (m !!! Regidx Rs7) (m !!! Regidx Rs8)
               (m !!! Regidx Rs9) (m !!! Regidx Rs10) (m !!! Regidx Rs11)
               w67 ef P i szv -∗
    wp_next true (proc_addr jp) (fun (CID : CpuId) =>
      ∀ (mf : regfile) (V' : pprivate)
        (entry spv szv' : mword 64),
          ⌜callee_saved m mf⌝ -∗
          ⌜kexec_ok_q Q V V' (mf !!! Regidx Ra0) entry spv szv' na alen⌝ -∗
          sie_cap_gpr KT1 mf K eb (proc_addr jp) -∗
          cpu_own 0 eb (proc_addr jp) eb ∅ -∗
          trap_csrs_ext KT1 eb -∗
          cpu_claim_ext eb (proc_addr jp) -∗
          pc_is (ret_pc ra0) -∗
          sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
          sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
          kalloc_env ga None -∗
          proc_priv gf (proc_addr jp) pidv V' -∗
          ([∗ list] k ∈ seq 0 (S plen), pa_add pv k ↦ₘ[KT1]{dqpv} pfun k) -∗
          ([∗ list] k ∈ seq 0 (S na), pa_add av (8 * k) ↦₈[KT1]{dqa} avf k) -∗
          ([∗ list] k ∈ seq 0 na,
             [∗ list] j ∈ seq 0 (aslen k), pa_add (avf k) j ↦ₘ{dqas} afun k j) -∗
          bslots 3 -∗
          iref_slots 2 -∗
          WP (Loop : expr riscv_lang)) -∗
    wp_next true (proc_addr jp) (fun (CID : CpuId) =>
      ∀ (M' : regfile) (P' : uptd) (szv' : mword 64),
        kxc_at_1a4 jp bn g gfs gi cn ga gf cov logstart bmapstart inodestart
                   nib size dev kf qf sf gyf inumf dnf bmf
                   gilf gislf n2 plen pfun na avf aslen afun pidv V eb
                   dqb dqs dqa dqpv dqas M' K sp0 ra0 s00 s10 s20 pv av
                   (m !!! Regidx Rs3) (m !!! Regidx Rs4) (m !!! Regidx Rs5)
                   (m !!! Regidx Rs6) (m !!! Regidx Rs7) (m !!! Regidx Rs8)
                   (m !!! Regidx Rs9) (m !!! Regidx Rs10) (m !!! Regidx Rs11)
                   w67 ef P' szv' -∗
        wp_next (CID0 := CID) true (proc_addr jp) (fun (CIDy : CpuId) =>
          ∀ (mf : regfile) (V' : pprivate)
            (entry spv szv2 : mword 64),
              ⌜callee_saved m mf⌝ -∗
              ⌜kexec_ok_q Q V V' (mf !!! Regidx Ra0) entry spv szv2 na alen⌝ -∗
              sie_cap_gpr KT1 mf K eb (proc_addr jp) -∗
              cpu_own 0 eb (proc_addr jp) eb ∅ -∗
              trap_csrs_ext KT1 eb -∗
              cpu_claim_ext eb (proc_addr jp) -∗
              pc_is (ret_pc ra0) -∗
              sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
              sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
              kalloc_env ga None -∗
              proc_priv gf (proc_addr jp) pidv V' -∗
              ([∗ list] k ∈ seq 0 (S plen), pa_add pv k ↦ₘ[KT1]{dqpv} pfun k) -∗
              ([∗ list] k ∈ seq 0 (S na), pa_add av (8 * k) ↦₈[KT1]{dqa} avf k) -∗
              ([∗ list] k ∈ seq 0 na,
                 [∗ list] j ∈ seq 0 (aslen k), pa_add (avf k) j ↦ₘ{dqas} afun k j) -∗
              bslots 3 -∗
              iref_slots 2 -∗
              WP (Loop : expr riscv_lang)) -∗
        WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros HK Hk Hlg Hsz Hbm0 Hbmc Hbml Hins0 Hcovb Hiregb Hjp Hgs Hdevc
           Hsp Hra Hs0 Hs1 Hs2.
    intro W. revert CID0.
    induction W as [| W IH]; intros CID0 M P i szv Hfuel;
      iIntros "#Htext #Hfab Hst Hcont Hc1a4";
      iApply (kxc_ph_step (CID0 := CID0) Q gs jp gl gu gd gk pd pav pu bn g gfs
                gi cn gtl gilf gislf ga gf cov logstart bmapstart inodestart
                nib size dev kf qf sf gyf inumf dnf bmf n2 plen
                pfun na avf alen aslen afun pidv V eb dqb dqs dqa dqpv dqas m M K
                sp0 ra0 s00 s10 s20 pv av w67 ef P i szv
                HK Hk Hlg Hsz Hbm0 Hbmc Hbml Hins0 Hcovb Hiregb Hjp Hgs Hdevc
                Hsp Hra Hs0 Hs1 Hs2
                with "Htext Hfab Hst Hcont [Hc1a4]");
      iIntros (CIDn Hsn M' P' szv') "[Hnext | Hexit] Hcont".
    - (* NO FUEL, and the back edge is what refutes it. *)
      iDestruct "Hnext" as "(_ & _ & %Hp3 & _)".
      destruct Hp3 as (HSi & _ & _ & _).
      exfalso. rewrite Nat2Z.inj_succ in HSi.
      change (Z.of_nat 0%nat) with 0%Z in Hfuel. lia.
    - (* NO FUEL: the loop is over anyway. *)
      iSpecialize ("Hc1a4" $! CIDn with "[%]"); [wp_next_chain |].
      iApply ("Hc1a4" $! M' P' szv' with "Hexit Hcont").
    - (* another header *)
      iDestruct "Hnext" as "(%Hp1 & %Hp2 & %Hp3 & Hrest)".
      destruct Hp3 as (HSi & Hp3b & Hp3c & Hp3d).
      assert (Hcr : true = false \/ proc_addr jp = zero_reg ->
                (CIDn : CPU) = (CID0 : CPU)) by wp_next_chain.
      iDestruct (wp_next_retarget CID0 CIDn true (proc_addr jp) _ Hcr
                   with "Hc1a4") as "Hc1a4".
      iApply (IH CIDn M' P' (S i) szv'
                ltac:(rewrite Nat2Z.inj_succ; rewrite Nat2Z.inj_succ in Hfuel;
                      lia)
                with "Htext Hfab [Hrest] Hcont Hc1a4").
      rewrite /kxc_at_12c.
      iSplitR; [iPureIntro; exact Hp1 |].
      iSplitR; [iPureIntro; exact Hp2 |].
      iSplitR; [iPureIntro; split_and!;
                [exact HSi | exact Hp3b | exact Hp3c | exact Hp3d] |].
      iExact "Hrest".
    - (* the loop is over *)
      iSpecialize ("Hc1a4" $! CIDn with "[%]"); [wp_next_chain |].
      iApply ("Hc1a4" $! M' P' szv' with "Hexit Hcont").
  Qed.

End KexecB3Loop.

(* ===================================================================== *)
(*  +0x1a2 .. +0x1ae -- CLOSING THE INODE, AND PHASE B AS ONE LEMMA.      *)
(* ===================================================================== *)
Section KexecB3Close.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ, !irefslotG Σ, !pavG Σ}.
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
  Notation Rs8 := (mword_of_int 24 : mword 5).
  Notation Rs9 := (mword_of_int 25 : mword 5).
  Notation Rs10 := (mword_of_int 26 : mword 5).
  Notation Rs11 := (mword_of_int 27 : mword 5).
  Notation Ra0 := (mword_of_int 10 : mword 5).

  Local Ltac cnz := vm_compute; discriminate.
  Local Ltac cpcw := apply bv_eq; vm_compute; reflexivity.

  (* ---- +0x1a2: c.li s2,0 -- the no-segments path joins at +0x1a4 ---- *)
  Lemma kxc_seam1a2 `{CID0 : CpuId}
      (jp : nat) (bn : bio_names) (g : log_names) (gfs : fs_names) (gi : gname)
      (cn : ic_names) (ga gf : gname)
      (cov : gset Z) (logstart bmapstart inodestart : Z) (nib : nat)
      (size : Z) (dev : mword 32)
      (kf : nat) (qf sf : Qp) (gyf : gname) (inumf : mword 32)
      (dnf : dinode) (bmf : blkmap) (gilf gislf : gname) (n2 : nat)
      (plen : nat) (pfun : nat -> bv 8)
      (na : nat) (avf : nat -> mword 64) (aslen : nat -> nat)
      (afun : nat -> nat -> bv 8)
      (pidv : mword 32) (V : pprivate) (eb : bool) (dqb dqs dqa dqpv dqas : dfrac)
      (m M : regfile) (K : nat)
      (sp0 ra0 s00 s10 s20 pv av : mword 64)
      (w5 w6 w7 w8 w9 w10 w11 w12 w13 w67 : mword 64)
      (ef : nat -> bv 8) (P : uptd) :
    kernel_text -∗
    kxc_at_1a2 jp bn g gfs gi cn ga gf cov logstart bmapstart inodestart nib
               size dev kf qf sf gyf inumf dnf bmf gilf gislf n2
               plen pfun na avf aslen afun pidv V eb dqb dqs dqa dqpv dqas m M K
               sp0 ra0 s00 s10 s20 pv av
               w5 w6 w7 w8 w9 w10 w11 w12 w13 w67 ef P -∗
    wp_next true (proc_addr jp) (fun (CID : CpuId) =>
      ∀ (M' : regfile),
        kxc_at_1a4 jp bn g gfs gi cn ga gf cov logstart bmapstart inodestart
                   nib size dev kf qf sf gyf inumf dnf bmf
                   gilf gislf n2 plen pfun na avf aslen afun pidv V eb
                   dqb dqs dqa dqpv dqas M' K sp0 ra0 s00 s10 s20 pv av
                   w5 w6 w7 w8 w9 w10 w11 w12 w13 w67 ef P
                   (mword_of_int 0 : mword 64) -∗
        WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    iIntros "#Htext Hst Hout".
    rewrite /kxc_at_1a2.
    iDestruct "Hst" as "((%HMsp & %HMs0 & %HMs1 & %HMs2 & %HMs4 & %HMs6 &
                          %HMthr) &
                         (%Hk & %Hib & %Hn2 & %Hal) &
                         (%HPtfp & %Hbelow & %Hcov) &
                         Hpc & Hcg & Hcnt & Hextc & Hclmc & Hopen & Hlog & Hirs & Hbm & Hins &
                         Hbits & Hbs & #Hka & Hpt & Hpriv & Hpath & Hargv &
                         Hargs & Helf & Hframe)".
    iApply (wp_cli_s_sconf (mword_of_int (KXB + 0x1a2)) Rs2
              (mword_of_int 0 : mword 6) (mword_of_int 0 : mword 64)
              M (K - 68)%nat eb ltac:(cnz) ltac:(rdok)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc []").
    { iApply (kxc_1a2 with "Htext"). }
    iIntros (CID1 Hsq1) "Hcg Hpc".
    set (T1 := <[Regidx Rs2 := regval_into_reg
                  (mword_of_int 0 : mword 64)]> M).
    assert (HT1s2 : T1 !!! Regidx Rs2 = (mword_of_int 0 : mword 64))
      by (rewrite /T1; apply upd_eq).
    assert (HT1sp : T1 !!! Regidx csp_rs1 = pa_stk sp0 68)
      by (rewrite /T1 upd_ne; [exact HMsp | cnz]).
    assert (HT1s0 : T1 !!! Regidx Rs0 = sp0)
      by (rewrite /T1 upd_ne; [exact HMs0 | cnz]).
    assert (HT1s4 : T1 !!! Regidx Rs4 = ientry kf)
      by (rewrite /T1 upd_ne; [exact HMs4 | cnz]).
    assert (HT1s6 : T1 !!! Regidx Rs6 = page_base P.(ud_root))
      by (rewrite /T1 upd_ne; [exact HMs6 | cnz]).
    assert (Hpp1a4 : add_vec_int (mword_of_int (KXB + 0x1a2) : mword 64) 2
                     = mword_of_int (KXB + 0x1a4)) by cpcw.
    iEval (rewrite Hpp1a4) in "Hpc".
    iDestruct (cpu_own_transport CID0 CID1 0%nat eb (proc_addr jp) eb
                 ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
    iDestruct (trap_csrs_ext_transport CID0 CID1 eb (proc_addr jp)
                 ltac:(try rewrite Hebb; wp_next_chain) with "Hextc") as "Hextc".
    iDestruct (cpu_claim_ext_transport CID0 CID1 eb (proc_addr jp)
                 ltac:(try rewrite Hebb; wp_next_chain) with "Hclmc") as "Hclmc".
    iSpecialize ("Hout" $! CID1 with "[%]"); [wp_next_chain |].
    iApply ("Hout" $! T1). rewrite /kxc_at_1a4.
    iSplitR.
    { iPureIntro. split_and!;
        [exact HT1sp | exact HT1s0 | exact HT1s2 | exact HT1s4 | exact HT1s6]. }
    iSplitR.
    { iPureIntro. split_and!;
        [exact Hk | exact Hib | exact Hn2 | exact Hal]. }
    iSplitR.
    { iPureIntro. split_and!; [exact HPtfp | exact Hbelow | exact Hcov]. }
    iSplitL "Hpc"; [iExact "Hpc" |]. iSplitL "Hcg"; [iExact "Hcg" |].
    iSplitL "Hcnt"; [iExact "Hcnt" |].
    iSplitL "Hextc"; [iExact "Hextc" |]. iSplitL "Hclmc"; [iExact "Hclmc" |]. iSplitL "Hopen"; [iExact "Hopen" |].
    iSplitL "Hlog"; [iExact "Hlog" |]. iSplitL "Hirs"; [iExact "Hirs" |].
    iSplitL "Hbm"; [iExact "Hbm" |]. iSplitL "Hins"; [iExact "Hins" |].
    iSplitL "Hbits"; [iExact "Hbits" |]. iSplitL "Hbs"; [iExact "Hbs" |].
    iSplitR; [iExact "Hka" |]. iSplitL "Hpt"; [iExact "Hpt" |].
    iSplitL "Hpriv"; [iExact "Hpriv" |]. iSplitL "Hpath"; [iExact "Hpath" |].
    iSplitL "Hargv"; [iExact "Hargv" |]. iSplitL "Hargs"; [iExact "Hargs" |].
    iSplitL "Helf"; [iExact "Helf" | iExact "Hframe"].
  Qed.

  (* ---- +0x1a4 .. +0x1ae: mv a0,s4 ; jal iunlockput ; jal end_op ---- *)
  (*  ProofKexecTail's [kxc_bad64] does the same two calls; what differs   *)
  (*  is only where it goes afterwards.                                    *)
  Lemma kxc_close `{CID0 : CpuId}
      (gs : list gname) (jp : nat) (gl : gname)
      (gu : uart_names) (gd : disk_names) (gk : gname) (pd pav pu : mword 64)
      (bn : bio_names) (g : log_names) (gfs : fs_names) (gi : gname)
      (cn : ic_names) (gtl : gname) (gilf gislf : gname) (ga gf : gname)
      (cov : gset Z) (logstart bmapstart inodestart : Z) (nib : nat)
      (size : Z) (dev : mword 32)
      (kf : nat) (qf sf : Qp) (gyf : gname) (inumf : mword 32)
      (dnf : dinode) (bmf : blkmap) (n2 : nat)
      (plen : nat) (pfun : nat -> bv 8)
      (na : nat) (avf : nat -> mword 64) (aslen : nat -> nat)
      (afun : nat -> nat -> bv 8)
      (pidv : mword 32) (V : pprivate) (eb : bool) (dqb dqs dqa dqpv dqas : dfrac)
      (M : regfile) (K : nat)
      (sp0 ra0 s00 s10 s20 pv av : mword 64)
      (w5 w6 w7 w8 w9 w10 w11 w12 w13 w67 : mword 64)
      (ef : nat -> bv 8) (P : uptd) (szv : mword 64) :
    (K_kexec <= K)%nat ->
    log_geom_ok cov logstart ->
    0 < size <= BPB ->
    0 <= bmapstart ->
    bmapstart ∈ cov ->
    ~ (bmapstart ∈ log_region_set logstart) ->
    0 <= inodestart ->
    cov_below cov size ->
    ireg_blocks_ok inodestart nib cov logstart ->
    (jp < NPROC)%nat ->
    gs !! jp = Some gl ->
    kernel_text -∗
    fs_fabric gs gu gd gk pd pav pu bn g gfs gi cn gtl
              cov logstart inodestart nib dev -∗
    kxc_at_1a4 jp bn g gfs gi cn ga gf cov logstart bmapstart inodestart nib
               size dev kf qf sf gyf inumf dnf bmf gilf gislf n2
               plen pfun na avf aslen afun pidv V eb dqb dqs dqa dqpv dqas M K
               sp0 ra0 s00 s10 s20 pv av
               w5 w6 w7 w8 w9 w10 w11 w12 w13 w67 ef P szv -∗
    wp_next true (proc_addr jp) (fun (CID : CpuId) =>
      ∀ (M' : regfile),
        kxc_at_1ae jp bn gfs ga gf cov logstart bmapstart inodestart size
                   plen pfun na avf aslen afun pidv V eb dqb dqs dqa dqpv dqas
                   M' K sp0 ra0 s00 s10 s20 pv av
                   w5 w6 w7 w8 w9 w10 w11 w12 w13 w67 ef P szv -∗
        WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros HK Hlg Hsz Hbm0 Hbmc Hbml Hins0 Hcovb Hiregb Hjp Hgs.
    pose proof HK as HK'. 
    iIntros "#Htext #Hfab Hst Hout".
    rewrite /kxc_at_1a4.
    iDestruct "Hst" as "((%HMsp & %HMs0 & %HMs2 & %HMs4 & %HMs6) &
                         (%Hk & %Hib & %Hn2 & %Hal) &
                         (%HPtfp & %Hbelow & %Hcov) &
                         Hpc & Hcg & Hcnt & Hextc & Hclmc & Hopen & Hlog & Hirs & Hbm & Hins &
                         #Hbits & Hbs & #Hka & Hpt & Hpriv & Hpath & Hargv &
                         Hargs & Helf & Hframe)".
    destruct (Hiregb inumf Hib) as [Hibc Hibl].
    iDestruct "Hfab" as "(#Hkd & #Hpenv & #Hbio & #Hlogc & #Hcrash & #Hcert & #Hitab & #Hitinv &
                          #Hesc & #Hslks & #Hireg & #Hropen & #Hprocs & #Hdevi & #Hdgeom &
                          #Hdlock)".
    iDestruct "Hopen" as "(#Hslkk & Hslkd & Hdep & Hidev & Hiinum &
                           Hivalid & Hload & #Hity & Hfrz & Hkeep & Hru)".
    iDestruct (proc_priv_bare_acc gf (proc_addr jp) pidv V with "Hpriv")
      as "[Hppid Hpvbk]".
    iDestruct (A.kxa_esc_acc cn gfs gi cov logstart kf Hk with "Hesc")
      as "#Hesck".
    (* ---- +0x1a4: c.mv a0,s4 ---- *)
    iApply (wp_cmv_s_sconf (mword_of_int (KXB + 0x1a4)) Ra0 Rs4
              M (K - 68)%nat eb ltac:(cnz) ltac:(rdok) with "Hcg Hpc []").
    { iApply (kxc_1a4 with "Htext"). }
    iIntros (CIDa Hsa) "Hcg Hpc". iEval (rgne) in "Hcg".
    set (B1 := <[Regidx Ra0 := regval_into_reg
                  (add_vec zero_reg (M !!! Regidx Rs4))]> M).
    assert (HB1a0 : B1 !!! Regidx Ra0 = ientry kf).
    { rewrite /B1 upd_eq HMs4. apply add_vec_zero_l. }
    assert (HB1sp : B1 !!! Regidx csp_rs1 = pa_stk sp0 68)
      by (rewrite /B1 upd_ne; [exact HMsp | cnz]).
    assert (HB1s0 : B1 !!! Regidx Rs0 = sp0)
      by (rewrite /B1 upd_ne; [exact HMs0 | cnz]).
    assert (HB1s2 : B1 !!! Regidx Rs2 = szv)
      by (rewrite /B1 upd_ne; [exact HMs2 | cnz]).
    assert (HB1s6 : B1 !!! Regidx Rs6 = page_base P.(ud_root))
      by (rewrite /B1 upd_ne; [exact HMs6 | cnz]).
    assert (Hpp1a6 : add_vec_int (mword_of_int (KXB + 0x1a4) : mword 64) 2
                     = mword_of_int (KXB + 0x1a6)) by cpcw.
    iEval (rewrite Hpp1a6) in "Hpc".
    (* ---- +0x1a6: jal ra,iunlockput ---- *)
    assert (Htiu : add_vec (mword_of_int (KXB + 0x1a6) : mword 64)
                     (sign_extend' 64 (mword_of_int 2091760 : mword 21))
                   = mword_of_int KernelSyms.iunlockput) by cpcw.
    iApply (wp_jal_s_sconf (mword_of_int (KXB + 0x1a6)) Rra
              (mword_of_int 2091760 : mword 21) B1 (K - 68)%nat eb
              ltac:(cnz) ltac:(rdok)
              ltac:(rewrite Htiu; vm_compute; reflexivity)
              with "Hcg Hpc []").
    { iApply (kxc_1a6 with "Htext"). }
    iIntros (CIDj1 Hsj1) "Hcg Hpc". iEval (rewrite Htiu) in "Hpc".
    set (B2 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (KXB + 0x1a6) : mword 64) 4)]> B1).
    change (<[Regidx Rra := regval_into_reg
              (add_vec_int (mword_of_int (KXB + 0x1a6) : mword 64) 4)]> B1)
      with B2.
    assert (HB2ra : B2 !!! Regidx Rra
                    = add_vec_int (mword_of_int (KXB + 0x1a6) : mword 64) 4)
      by (rewrite /B2; apply upd_eq).
    assert (HB2a0 : B2 !!! Regidx Ra0 = ientry kf)
      by (rewrite /B2 upd_ne; [exact HB1a0 | cnz]).
    assert (HB2sp : B2 !!! Regidx csp_rs1 = pa_stk sp0 68)
      by (rewrite /B2 upd_ne; [exact HB1sp | cnz]).
    assert (HB2s0 : B2 !!! Regidx Rs0 = sp0)
      by (rewrite /B2 upd_ne; [exact HB1s0 | cnz]).
    assert (HB2s2 : B2 !!! Regidx Rs2 = szv)
      by (rewrite /B2 upd_ne; [exact HB1s2 | cnz]).
    assert (HB2s6 : B2 !!! Regidx Rs6 = page_base P.(ud_root))
      by (rewrite /B2 upd_ne; [exact HB1s6 | cnz]).
    iDestruct (cpu_own_transport CID0 CIDj1 0%nat eb (proc_addr jp) eb
                 ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
    iDestruct (trap_csrs_ext_transport CID0 CIDj1 eb (proc_addr jp)
                 ltac:(try rewrite Hebb; wp_next_chain) with "Hextc") as "Hextc".
    iDestruct (cpu_claim_ext_transport CID0 CIDj1 eb (proc_addr jp)
                 ltac:(try rewrite Hebb; wp_next_chain) with "Hclmc") as "Hclmc".
    iApply (Iunlockput.wp_iunlockput_sconf gs jp gl gu gd gk pd pav pu bn g gfs
              gi cn gtl gilf gislf cov logstart bmapstart inodestart nib size
              dev kf qf sf gyf inumf dnf bmf n2 pidv (DfracOwn (1/4))
              dqb dqs B2 (K - 68)%nat eb eb ∅
              V ltac:(lia) Hk Hlg Hsz Hbm0 Hbmc
              Hbml Hins0 Hibc Hibl Hib Hcovb Hn2 Hjp Hgs HB2a0
              with "Hcg Hcnt Hextc Hclmc Htext Hkd Hpc Hpenv Hbio Hlogc Hitab Hitinv Hesck
                    Hireg Hropen Hslkk Hslkd Hdep Hidev Hiinum Hivalid Hload
                    Hity Hfrz [$Hkeep $Hru] Hbm Hins Hbits Hppid Hprocs Hdevi Hdgeom Hdlock
                    Hbs Hlog").
    all: try lkbelow.
    iIntros (CIDu Hsu M1 n3) "%Hcsu Hcg Hcnt Hextc Hclmc Hpc Hppid Hbm Hins
             Hbs %Hn3 Hlog Hirs1".
    assert (Hpc1aa : ret_pc (B2 !!! Regidx Rra) = mword_of_int (KXB + 0x1aa))
      by (rewrite HB2ra; cpcw).
    iEval (rewrite Hpc1aa) in "Hpc".
    assert (HM1sp : M1 !!! Regidx csp_rs1 = pa_stk sp0 68)
      by (rewrite (callee_saved_lookup Hcsu csp_rs1
                     ltac:(vm_compute; reflexivity)); exact HB2sp).
    assert (HM1s0 : M1 !!! Regidx Rs0 = sp0)
      by (rewrite (callee_saved_lookup Hcsu Rs0
                     ltac:(vm_compute; reflexivity)); exact HB2s0).
    assert (HM1s2 : M1 !!! Regidx Rs2 = szv)
      by (rewrite (callee_saved_lookup Hcsu Rs2
                     ltac:(vm_compute; reflexivity)); exact HB2s2).
    assert (HM1s6 : M1 !!! Regidx Rs6 = page_base P.(ud_root))
      by (rewrite (callee_saved_lookup Hcsu Rs6
                     ltac:(vm_compute; reflexivity)); exact HB2s6).
    (* ---- +0x1aa: jal ra,end_op ---- *)
    assert (Hteo : add_vec (mword_of_int (KXB + 0x1aa) : mword 64)
                     (sign_extend' 64 (mword_of_int 2093966 : mword 21))
                   = mword_of_int KernelSyms.end_op) by cpcw.
    iApply (wp_jal_s_sconf (mword_of_int (KXB + 0x1aa)) Rra
              (mword_of_int 2093966 : mword 21) M1 (K - 68)%nat eb
              ltac:(cnz) ltac:(rdok)
              ltac:(rewrite Hteo; vm_compute; reflexivity)
              with "Hcg Hpc []").
    { iApply (kxc_1aa with "Htext"). }
    iIntros (CIDj2 Hsj2) "Hcg Hpc". iEval (rewrite Hteo) in "Hpc".
    set (B3 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (KXB + 0x1aa) : mword 64) 4)]> M1).
    change (<[Regidx Rra := regval_into_reg
              (add_vec_int (mword_of_int (KXB + 0x1aa) : mword 64) 4)]> M1)
      with B3.
    assert (HB3ra : B3 !!! Regidx Rra
                    = add_vec_int (mword_of_int (KXB + 0x1aa) : mword 64) 4)
      by (rewrite /B3; apply upd_eq).
    assert (HB3sp : B3 !!! Regidx csp_rs1 = pa_stk sp0 68)
      by (rewrite /B3 upd_ne; [exact HM1sp | cnz]).
    assert (HB3s0 : B3 !!! Regidx Rs0 = sp0)
      by (rewrite /B3 upd_ne; [exact HM1s0 | cnz]).
    assert (HB3s2 : B3 !!! Regidx Rs2 = szv)
      by (rewrite /B3 upd_ne; [exact HM1s2 | cnz]).
    assert (HB3s6 : B3 !!! Regidx Rs6 = page_base P.(ud_root))
      by (rewrite /B3 upd_ne; [exact HM1s6 | cnz]).
    iDestruct (cpu_own_transport CIDu CIDj2 0%nat eb (proc_addr jp) eb
                 ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
    iDestruct (trap_csrs_ext_transport CIDu CIDj2 eb (proc_addr jp)
                 ltac:(try rewrite Hebb; wp_next_chain) with "Hextc") as "Hextc".
    iDestruct (cpu_claim_ext_transport CIDu CIDj2 eb (proc_addr jp)
                 ltac:(try rewrite Hebb; wp_next_chain) with "Hclmc") as "Hclmc".
    iApply (EndOp.wp_end_op_sconf gs jp gl gu gd gk pd pav pu bn g gfs
              cov logstart dev n3 pidv (DfracOwn (1/4)) B3 (K - 68)%nat
              eb eb ∅ V ltac:(lia) Hlg Hjp Hgs
              with "Hcg Hcnt Hextc Hclmc Htext Hkd Hpc Hpenv Hbio Hlogc Hcrash Hcert
                    Hppid Hprocs Hdevi Hdgeom Hdlock Hlog").
    all: try lkbelow.
    all: try exact (LogInv.end_op_fin_placeholder _ _).
    iIntros (CIDe Hse M2) "%Hcse Hcg Hcnt Hextc Hclmc Hpc Hppid".
    assert (Hpc1ae : ret_pc (B3 !!! Regidx Rra) = mword_of_int (KXB + 0x1ae))
      by (rewrite HB3ra; cpcw).
    iEval (rewrite Hpc1ae) in "Hpc".
    assert (HM2sp : M2 !!! Regidx csp_rs1 = pa_stk sp0 68)
      by (rewrite (callee_saved_lookup Hcse csp_rs1
                     ltac:(vm_compute; reflexivity)); exact HB3sp).
    assert (HM2s0 : M2 !!! Regidx Rs0 = sp0)
      by (rewrite (callee_saved_lookup Hcse Rs0
                     ltac:(vm_compute; reflexivity)); exact HB3s0).
    assert (HM2s2 : M2 !!! Regidx Rs2 = szv)
      by (rewrite (callee_saved_lookup Hcse Rs2
                     ltac:(vm_compute; reflexivity)); exact HB3s2).
    assert (HM2s6 : M2 !!! Regidx Rs6 = page_base P.(ud_root))
      by (rewrite (callee_saved_lookup Hcse Rs6
                     ltac:(vm_compute; reflexivity)); exact HB3s6).
    iDestruct ("Hpvbk" with "Hppid") as "Hpriv".
    iAssert (iref_slots 2) with "[Hirs Hirs1]" as "Hirs2".
    { change 2%nat with (1 + 1)%nat. rewrite iref_slots_op.
      iSplitL "Hirs"; [iExact "Hirs" | iExact "Hirs1"]. }
    iDestruct (cpu_own_transport CIDe CIDe 0%nat eb (proc_addr jp) eb
                 ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
    iDestruct (trap_csrs_ext_transport CIDe CIDe eb (proc_addr jp)
                 ltac:(try rewrite Hebb; wp_next_chain) with "Hextc") as "Hextc".
    iDestruct (cpu_claim_ext_transport CIDe CIDe eb (proc_addr jp)
                 ltac:(try rewrite Hebb; wp_next_chain) with "Hclmc") as "Hclmc".
    iSpecialize ("Hout" $! CIDe with "[%]"); [wp_next_chain |].
    iApply ("Hout" $! M2). rewrite /kxc_at_1ae.
    iSplitR.
    { iPureIntro. split_and!;
        [exact HM2sp | exact HM2s0 | exact HM2s2 | exact HM2s6]. }
    iSplitR.
    { iPureIntro. exact Hal. }
    iSplitR.
    { iPureIntro. split_and!; [exact HPtfp | exact Hbelow | exact Hcov]. }
    iSplitL "Hpc"; [iExact "Hpc" |]. iSplitL "Hcg"; [iExact "Hcg" |].
    iSplitL "Hcnt"; [iExact "Hcnt" |].
    iSplitL "Hextc"; [iExact "Hextc" |]. iSplitL "Hclmc"; [iExact "Hclmc" |]. iSplitL "Hirs2"; [iExact "Hirs2" |].
    iSplitL "Hbm"; [iExact "Hbm" |]. iSplitL "Hins"; [iExact "Hins" |].
    iSplitR; [iExact "Hbits" |]. iSplitL "Hbs"; [iExact "Hbs" |].
    iSplitR; [iExact "Hka" |]. iSplitL "Hpt"; [iExact "Hpt" |].
    iSplitL "Hpriv"; [iExact "Hpriv" |]. iSplitL "Hpath"; [iExact "Hpath" |].
    iSplitL "Hargv"; [iExact "Hargv" |]. iSplitL "Hargs"; [iExact "Hargs" |].
    iSplitL "Helf"; [iExact "Helf" | iExact "Hframe"].
  Qed.

End KexecB3Close.

(* ===================================================================== *)
(*  PHASE B2, WHOLE -- BOTH OF PHASE B1's OUTPUTS.                        *)
(* ===================================================================== *)
(* [kxc_b2] runs the loop; [kxc_b2z] is the [elf.phnum = 0] path, one
   instruction into the same +0x1a4 join.  Both end at +0x1ae, phase C's
   entry, and both hand kexec's exit continuation back untouched -- neither
   the loop nor the inode close owns a [-1] tail that the caller does not
   already know about ([kxc_bad324] closes all five inside the loop). *)
Section KexecB3Main.
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

  Lemma kxc_b2
      (Q : mword 64 -> Prop)
      (gs : list gname) (jp : nat) (gl : gname)
      (gu : uart_names) (gd : disk_names) (gk : gname) (pd pav pu : mword 64)
      (bn : bio_names) (g : log_names) (gfs : fs_names) (gi : gname)
      (cn : ic_names) (gtl : gname) (gilf gislf : gname) (ga gf : gname)
      (cov : gset Z) (logstart bmapstart inodestart : Z) (nib : nat)
      (size : Z) (dev : mword 32)
      (kf : nat) (qf sf : Qp) (gyf : gname) (inumf : mword 32)
      (dnf : dinode) (bmf : blkmap) (n2 : nat)
      (plen : nat) (pfun : nat -> bv 8)
      (na : nat) (avf : nat -> mword 64) (alen aslen : nat -> nat)
      (afun : nat -> nat -> bv 8)
      (pidv : mword 32) (V : pprivate) (eb : bool) (dqb dqs dqa dqpv dqas : dfrac)
      (m M : regfile) (K : nat)
      (sp0 ra0 s00 s10 s20 pv av w67 : mword 64)
      (ef : nat -> bv 8) (P : uptd) (i : nat) (szv : mword 64) :
    kxc_b2_body Q gs jp gl gu gd gk pd pav pu bn g gfs gi cn gtl gilf gislf
      ga gf cov logstart bmapstart inodestart nib size dev
      kf qf sf gyf inumf dnf bmf n2 plen pfun na avf alen aslen afun
      pidv V eb dqb dqs dqa dqpv dqas m M K sp0 ra0 s00 s10 s20 pv av w67
      ef P i szv.
  Proof.
    cbv beta delta [kxc_b2_body].
    intros HK Hk Hlg Hsz Hbm0 Hbmc Hbml Hins0 Hcovb Hiregb Hjp Hgs Hdevc
           Hsp Hra Hs0 Hs1 Hs2.
    iIntros "#Htext #Hfab Hst Hcont Hc1ae".
    iApply (kxc_phdr (CID0 := CID0) Q gs jp gl gu gd gk pd pav pu bn g gfs gi cn
              gtl gilf gislf ga gf cov logstart bmapstart inodestart nib size
              dev kf qf sf gyf inumf dnf bmf n2 plen pfun na avf
              alen aslen afun pidv V eb dqb dqs dqa dqpv dqas m K sp0 ra0 s00 s10 s20
              pv av w67 ef
              HK Hk Hlg Hsz Hbm0 Hbmc Hbml Hins0 Hcovb Hiregb Hjp Hgs Hdevc
              Hsp Hra Hs0 Hs1 Hs2
              (Z.to_nat (eh_phnum ef)) M P i szv
              ltac:(rewrite Z2Nat.id;
                    [ pose proof (Nat2Z.is_nonneg i); lia
                    | pose proof (eh_phnum_bound ef); lia ])
              with "Htext Hfab Hst Hcont [Hc1ae]").
    iIntros (CIDn Hsn M' P' szv') "Hst4 Hcont".
    assert (Hcr : true = false \/ proc_addr jp = zero_reg ->
              (CIDn : CPU) = (CID0 : CPU)) by wp_next_chain.
    iDestruct (wp_next_retarget CID0 CIDn true (proc_addr jp) _ Hcr
                 with "Hc1ae") as "Hc1ae".
    iApply (kxc_close (CID0 := CIDn) gs jp gl gu gd gk pd pav pu bn g gfs gi cn
              gtl gilf gislf ga gf cov logstart bmapstart inodestart nib size
              dev kf qf sf gyf inumf dnf bmf n2 plen pfun na avf
              aslen afun pidv V eb dqb dqs dqa dqpv dqas M' K sp0 ra0 s00 s10 s20 pv av
              (m !!! Regidx Rs3) (m !!! Regidx Rs4) (m !!! Regidx Rs5)
              (m !!! Regidx Rs6) (m !!! Regidx Rs7) (m !!! Regidx Rs8)
              (m !!! Regidx Rs9) (m !!! Regidx Rs10) (m !!! Regidx Rs11)
              w67 ef P' szv'
              HK Hlg Hsz Hbm0 Hbmc Hbml Hins0 Hcovb Hiregb Hjp Hgs
              with "Htext Hfab Hst4 [Hc1ae Hcont]").
    iIntros (CIDm Hsm M'') "Hst1ae".
    assert (Hcr2 : true = false \/ proc_addr jp = zero_reg ->
              (CIDm : CPU) = (CIDn : CPU)) by wp_next_chain.
    iDestruct (wp_next_retarget CIDn CIDm true (proc_addr jp) _ Hcr2
                 with "Hcont") as "Hcont".
    iSpecialize ("Hc1ae" $! CIDm with "[%]"); [wp_next_chain |].
    iApply ("Hc1ae" $! M'' P' szv' with "Hst1ae Hcont").
  Qed.

  Lemma kxc_b2z
      (gs : list gname) (jp : nat) (gl : gname)
      (gu : uart_names) (gd : disk_names) (gk : gname) (pd pav pu : mword 64)
      (bn : bio_names) (g : log_names) (gfs : fs_names) (gi : gname)
      (cn : ic_names) (gtl : gname) (gilf gislf : gname) (ga gf : gname)
      (cov : gset Z) (logstart bmapstart inodestart : Z) (nib : nat)
      (size : Z) (dev : mword 32)
      (kf : nat) (qf sf : Qp) (gyf : gname) (inumf : mword 32)
      (dnf : dinode) (bmf : blkmap) (n2 : nat)
      (plen : nat) (pfun : nat -> bv 8)
      (na : nat) (avf : nat -> mword 64) (alen aslen : nat -> nat)
      (afun : nat -> nat -> bv 8)
      (pidv : mword 32) (V : pprivate) (eb : bool) (dqb dqs dqa dqpv dqas : dfrac)
      (m M : regfile) (K : nat)
      (sp0 ra0 s00 s10 s20 pv av w67 : mword 64)
      (ef : nat -> bv 8) (P : uptd) :
    kxc_b2z_body gs jp gl gu gd gk pd pav pu bn g gfs gi cn gtl gilf gislf
      ga gf cov logstart bmapstart inodestart nib size dev
      kf qf sf gyf inumf dnf bmf n2 plen pfun na avf alen aslen afun
      pidv V eb dqb dqs dqa dqpv dqas m M K sp0 ra0 s00 s10 s20 pv av w67 ef P.
  Proof.
    cbv beta delta [kxc_b2z_body].
    intros HK Hk Hlg Hsz Hbm0 Hbmc Hbml Hins0 Hcovb Hiregb Hjp Hgs.
    iIntros "#Htext #Hfab Hst Hc1ae".
    iApply (kxc_seam1a2 (CID0 := CID0) jp bn g gfs gi cn ga gf cov logstart
              bmapstart inodestart nib size dev kf qf sf gyf inumf
              dnf bmf gilf gislf n2 plen pfun na avf aslen afun pidv V eb
              dqb dqs dqa dqpv dqas m M K sp0 ra0 s00 s10 s20 pv av
              (m !!! Regidx Rs3) (m !!! Regidx Rs4) (m !!! Regidx Rs5)
              (m !!! Regidx Rs6) (m !!! Regidx Rs7) (m !!! Regidx Rs8)
              (m !!! Regidx Rs9) (m !!! Regidx Rs10) (m !!! Regidx Rs11)
              w67 ef P with "Htext Hst [Hc1ae]").
    iIntros (CIDn Hsn M') "Hst4".
    assert (Hcr : true = false \/ proc_addr jp = zero_reg ->
              (CIDn : CPU) = (CID0 : CPU)) by wp_next_chain.
    iDestruct (wp_next_retarget CID0 CIDn true (proc_addr jp) _ Hcr
                 with "Hc1ae") as "Hc1ae".
    iApply (kxc_close (CID0 := CIDn) gs jp gl gu gd gk pd pav pu bn g gfs gi cn
              gtl gilf gislf ga gf cov logstart bmapstart inodestart nib size
              dev kf qf sf gyf inumf dnf bmf n2 plen pfun na avf
              aslen afun pidv V eb dqb dqs dqa dqpv dqas M' K sp0 ra0 s00 s10 s20 pv av
              (m !!! Regidx Rs3) (m !!! Regidx Rs4) (m !!! Regidx Rs5)
              (m !!! Regidx Rs6) (m !!! Regidx Rs7) (m !!! Regidx Rs8)
              (m !!! Regidx Rs9) (m !!! Regidx Rs10) (m !!! Regidx Rs11)
              w67 ef P (mword_of_int 0 : mword 64)
              HK Hlg Hsz Hbm0 Hbmc Hbml Hins0 Hcovb Hiregb Hjp Hgs
              with "Htext Hfab Hst4 [Hc1ae]").
    iIntros (CIDm Hsm M'') "Hst1ae".
    iSpecialize ("Hc1ae" $! CIDm with "[%]"); [wp_next_chain |].
    iApply ("Hc1ae" $! M'' with "Hst1ae").
  Qed.

End KexecB3Main.

End KexecB3Proof.
