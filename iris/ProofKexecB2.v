(* ProofKexecB2.v -- PHASE B of kexec, SECOND CHUNK: the phdr loop, the
   inlined loadseg loop, and the six [bad:] tails they share.

   Its entry seams are ProofKexecSeam.v's [kxc_at_12c] (the phdr loop's BODY,
   which is also its head) and [kxc_at_1a2] (the no-segments path); its exit
   is +0x1ae, phase C's entry.  Nothing here requires ProofKexecB.v -- the
   two chunks meet only through ProofKexecSeam.v, so they compile in
   parallel (ProofKexecTail.v's header has the measurement that made that a
   rule).

   ---- THE FRAME ALGEBRA -------------------------------------------------

   [kxc_frameBpin] is [ProofKexecSeam.kxc_frameB] with slots 63 AND 65
   PINNED, plus
   the three moves between it and its neighbours.  Slot 65 is the C's [sz1],
   and it is existential in [kxc_frameB] for a good reason -- at +0x0cc
   nothing has written it yet -- but from +0x180 on it holds a value the
   [bad:] tail READS, so every state in this file pins it.

   [kxc_frameBpin_to_A6] is the move that tail makes: slots 5 and 7..13 lose
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
Require Import RegFile.
Require Import HartTp.
Require Import WpNext.
Require Import WpMmodeLeafBase.
Require Import RiscvExtras.
Require Import StackOwn.
Require Import CalleeSaved.
Require Import KernelRvcDecode.
Require Import InstrBytes.
Require Import WpSconfAlu WpSconfMem WpSconfCtl WpSconfBtype.
Require Import WpSmodeIntr.
Require Import IntrDefs.
Require Import CpuOwn.
Require Import WpLock.
Require Import FdSlots.
Require Export SwtchCtx.
Require Import WpUart.
Require Import IcacheEscrow.
Require Import W32Arith.
Require Import PageGeom.
Require Import ProcGeom.
Require Import DiskPtsto.
Require Import BioDefs.
(* THE PAYLOAD'S OWN VOCABULARY (durable-disk 2b-inode-3): [top_frag],
   [fs_gamma_L], [era_node] / [inode_rec_local].  IMPORTED BEFORE
   [FsBlocks] on purpose -- the [FsState*] stack exports [fs_view] and
   [byte_range], both of which have live twins below, and the LAST import
   wins (durable-notes, "AND WHERE THAT IMPORT COLLIDES, PUT IT EARLY"). *)
Require Import FsBlocks LogInv.
Require Import BitmapInv.
Require Import InodeInv.
Require Import IrefSlots.
Require Import IcacheRef.
Require Import DinodeEnc.
Require Import ProcInv.
Require Import PtreeType.
Require Import UserPtTree.
Require Import ProcPtOwn.
Require Import UmCovered.
Require Import FileInvDefs.
Require Import SpecKexec.
Require Import SpecMyproc.
Require Import SpecBeginOp.
Require Import SpecEndOp.
Require Import SpecIlock.
Require Import SpecReadi.
Require Import SpecIunlockput.
Require Import SpecNamei.
Require Import SpecProcFreepagetable.
Require Import SpecWalkaddr.
Require Import ProofKexecTail.
Require Import ProofKexecSeam.
Require Import SpecKexecB2.
Require Import CodeKexec.
From Kernel Require KernelSyms.
Require Import ProcAvail.
Local Open Scope Z_scope.

(* A syscall-altitude goal carries [ProcInv.tf_page]'s 4096-conjunct big-op;
   printing one takes tens of minutes, so a one-line mistake reads as a hang.
   durable-notes.md's rule. *)
Set Printing Depth 40.

Require Import KernelDataInv.
Require Import PrintkArgs.
Require Import SpecPanic.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)

Notation KXB := KernelSyms.kexec (only parsing).

(* ===================================================================== *)
(*  THE PANIC MESSAGE.  kexec's one live arm is loadseg's                 *)
(*  [panic("loadseg: address should exist")] at +0xd6 -- walkaddr came    *)
(*  back null for a segment page; the literal sits at 0x800075c0 in       *)
(*  .rodata, twenty-nine characters and a NUL.  NAMED pure lemmas, not    *)
(*  inline [ltac:] -- see optimization.md and the panic recipe.           *)
(* ===================================================================== *)
Definition kxc_msg_a : Z := 0x800075c0.
Definition kxc_msg : string := "loadseg: address should exist".

Lemma kxc_panic_K (K : nat) : (K_kexec <= K)%nat -> (panic_stack <= K - 68)%nat.
Proof. lia. Qed.

Lemma kxc_panic_noff : (Z.of_nat 0 + 2 < 2 ^ 31)%Z.
Proof. lia. Qed.

Lemma kxc_panic_below (lks : gset string) : lks = ∅ -> locks_below lks "pr".
Proof. intros ->. apply locks_below_empty. Qed.

Lemma kxc_msg_nz : eq_vec (mword_of_int kxc_msg_a : mword 64) zero_reg = false.
Proof. vm_compute; reflexivity. Qed.

Lemma kxc_msg_nonul : PrintkFmt.nonul kxc_msg = true.
Proof. vm_compute; reflexivity. Qed.

Lemma kxc_msg_bytes :
  forall j b, cstring_bytes kxc_msg !! j = Some b ->
    KernelData.kernel_data !! (kxc_msg_a + Z.of_nat j)%Z = Some b.
Proof.
  intros j b Hj.
  do 30 (destruct j as [|j]; [ vm_compute in Hj |- *; congruence | ]).
  vm_compute in Hj; discriminate.
Qed.

Section KexecMsg.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId}.

  Lemma kxc_msg_str :
    (kernel_data : iProp Σ) -∗ (mword_of_int kxc_msg_a : mword 64) ↦ₛ□ kxc_msg.
  Proof.
    iIntros "#Hd".
    iApply (kernel_data_string kxc_msg_a kxc_msg _ eq_refl
              ltac:(unfold text_end, kxc_msg_a; lia)
              ltac:(vm_compute; discriminate) kxc_msg_bytes with "Hd").
  Qed.
End KexecMsg.

(* ===================================================================== *)
(*  THE FRAME ALGEBRA AND THE FOURTEEN-RESOURCE BUNDLE now live in          *)
(*  SpecKexecB2.v WHOLESALE -- both [Section KexecB2Frame] and              *)
(*  [Section KexecB2Res], not just their two headline [Definition]s         *)
(*  ([kxc_frameBpin], [kxc_res]).  ProofKexecB3.v turned out to call        *)
(*  several of the small algebra lemmas around them too (unqualified, the   *)
(*  same way it calls [kxc_frameBpin]/[kxc_res] themselves), so moving      *)
(*  only the two [Definition]s left the rest stranded -- see                *)
(*  SpecKexecB2.v's header.  Everything from here through where             *)
(*  [End KexecB2Res.] used to sit is available unqualified below via the    *)
(*  [Require Import SpecKexecB2.] above.                                    *)
(* ===================================================================== *)


(* ===================================================================== *)
(*  THE PROOF.                                                            *)
(* ===================================================================== *)
(* Seven of the eight functor arguments are here only to build [A], the
   KexecTailProof instance that owns [kxc_bad64] -- the +0x064 tail every
   [bad:] entry in this file eventually falls into.  The eighth, [PFP], is
   this chunk's own: the +0x324 tail frees the half-built table. *)
Module KexecB2Proof (Myproc : MYPROC) (BeginOp : BEGIN_OP) (Namei : NAMEI)
                    (Ilock : ILOCK) (Readi : READI) (Iunlockput : IUNLOCKPUT)
                    (EndOp : END_OP) (PFP : PROC_FREEPAGETABLE)
                    (Walkaddr : WALKADDR) (PN : PANIC) : KEXECB2.

Module A := ProofKexecTail.KexecTailProof Myproc BeginOp Namei Ilock Readi
                                          Iunlockput EndOp.

Section KexecB2Body.
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
      (Q : mword 64 -> Prop)
      (gs : list gname) (jp : nat) (gl : gname)
      (gu : uart_names) (gd : disk_names) (gk : gname) (pd pav pu : mword 64)
      (bn : bio_names) (g : log_names) (gi : gname)
      (gtl : gname) (gilf gislf : gname) (ga gf : gname)
      (logstart bmapstart inodestart : Z) (nib : nat)
      (size : Z) (dev : mword 32)
      (kf : nat) (qf sf : Qp) (gyf : gname) (inumf : mword 32)
      (dnf : dinode) (bmf : blkmap) (n2 : nat)
      (plen : nat) (pfun : nat -> bv 8)
      (na : nat) (avf : nat -> mword 64) (alen aslen : nat -> nat)
      (afun : nat -> nat -> bv 8)
      (pidv : mword 32) (V : pprivate) (dqb dqs dqa dqpv dqas : dfrac)
      (m Mt : regfile) (K : nat)
      (sp0 ra0 s00 s10 s20 pv av w63 w67 : mword 64)
      (ef : nat -> bv 8) (P : uptd) (szf : mword 64) (eb : bool) (lks : gset string) :
    kxc_bad324_body Q gs jp gl gu gd gk pd pav pu bn g gi gtl gilf gislf
      ga gf logstart bmapstart inodestart nib size dev
      kf qf sf gyf inumf dnf bmf n2 plen pfun na avf alen aslen afun
      pidv V dqb dqs dqa dqpv dqas m Mt K sp0 ra0 s00 s10 s20 pv av w63 w67
      ef P szf eb lks.
  Proof.
    cbv beta delta [kxc_bad324_body].
    intros HK Hk Hlg Hsz Hbm0 Hbmc Hbml Hins0 Hcovb Hiregb Hib Hn2 Hjp Hgs
           Hsp Hra Hs0 Hs1 Hs2 HMtsp HMts0 HMts4 HMts6 Hal Hbelow Hcov.
    pose proof HK as HK'. 
    destruct (Hiregb inumf Hib) as [Hibc Hibl].
    (* [kalloc_env γa None] is PERSISTENT (KvmSpec.v) and MUST be introduced
       with [#]: proc_freepagetable consumes it and its postcondition does not
       hand it back, while [kxc_bad64] needs it at the exit.  Introduced
       exclusively, the second use fails with [iSpecialize: "Hka" not found]
       -- which names the hypothesis and not the reason. *)
    iIntros "Hcg Hcnt Hextc Hclmc #Htext Hpc #Hfab Hopen Hbm Hins Hbits #Hka Hpt
             Hpriv Hpath Hargv Hargs Helf Hbs Hirs Hlog Hframe Hcont".
    iDestruct (cpu_own_eb_agree with "Hcg Hcnt") as %Hebb.
    (* depth 0 forces the held set empty, so proc_freepagetable's order
       premise needs no hypothesis of this lemma's own. *)
    iDestruct (cpu_own_zero_empty with "Hcnt") as "[%Hlkempty Hcnt]".
    rewrite /kxc_frameBpin.
    iDestruct "Hframe" as "(Hf1 & Hf2 & Hf3 & Hf4 & Hf5 & Hf6 & Hf7 & Hf8 &
                            Hf9 & Hf10 & Hf11 & Hf12 & Hf13 & Hust & Hph &
                            Hf63 & Hf64 & Hf65 & Hf66 & Hf67 & Hf68)".
    (* ---- +0x324: ld a1,-520(s0) -- the size the tail frees ---- *)
    assert (Hpa65 : add_vec (rget Mt Rs0)
                      (sign_extend' 64 (mword_of_int 3576 : mword 12))
                    = pa_stk sp0 65).
    { rewrite (rget_ne Mt Rs0 ltac:(nz)) HMts0. s0slot. }
    iEval (rewrite -Hpa65) in "Hf65".
    iApply (wp_ld_s_sconf (mword_of_int (KXB + 0x31e)) Ra1 Rs0
              (mword_of_int 3576 : mword 12) Mt (K - 68)%nat szf eb
              (dqm := DfracOwn 1) ltac:(nz) ltac:(rdok)
              with "Hcg Hpc [] Hf65").
    { iApply (kxc_31e with "Htext"). }
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
    assert (Hpp322 : add_vec_int (mword_of_int (KXB + 0x31e) : mword 64) 4
                     = mword_of_int (KXB + 0x322)) by pcw.
    iEval (rewrite Hpp322) in "Hpc".
    (* ---- +0x328: c.mv a0,s6 -- the table to destroy ---- *)
    iApply (wp_cmv_s_sconf (mword_of_int (KXB + 0x322)) Ra0 Rs6
              T1 (K - 68)%nat eb ltac:(nz) ltac:(rdok)
              with "Hcg Hpc []").
    { iApply (kxc_322 with "Htext"). }
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
    assert (Hpp324 : add_vec_int (mword_of_int (KXB + 0x322) : mword 64) 2
                     = mword_of_int (KXB + 0x324)) by pcw.
    iEval (rewrite Hpp324) in "Hpc".
    (* ---- +0x32a: jal ra,proc_freepagetable ---- *)
    assert (Htpf : add_vec (mword_of_int (KXB + 0x324) : mword 64)
                     (sign_extend' 64 (mword_of_int 2084748 : mword 21))
                   = mword_of_int KernelSyms.proc_freepagetable) by pcw.
    iApply (wp_jal_s_sconf (mword_of_int (KXB + 0x324)) Rra
              (mword_of_int 2084748 : mword 21) T2 (K - 68)%nat eb
              ltac:(nz) ltac:(rdok)
              ltac:(rewrite Htpf; vm_compute; reflexivity)
              with "Hcg Hpc []").
    { iApply (kxc_324 with "Htext"). }
    iIntros (CID3 Hsq3) "Hcg Hpc". iEval (rewrite Htpf) in "Hpc".
    set (T3 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (KXB + 0x324) : mword 64) 4)]> T2).
    change (<[Regidx Rra := regval_into_reg
              (add_vec_int (mword_of_int (KXB + 0x324) : mword 64) 4)]> T2)
      with T3.
    assert (HT3ra : T3 !!! Regidx Rra
                    = add_vec_int (mword_of_int (KXB + 0x324) : mword 64) 4)
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
    iDestruct (cpu_own_transport CID0 CID3 0%nat eb (proc_addr jp) eb
                 ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
    iDestruct (trap_csrs_ext_transport CID0 CID3 eb (proc_addr jp)
                 ltac:(try rewrite Hebb; wp_next_chain) with "Hextc") as "Hextc".
    iDestruct (cpu_claim_ext_transport CID0 CID3 eb (proc_addr jp)
                 ltac:(try rewrite Hebb; wp_next_chain) with "Hclmc") as "Hclmc".
    iApply (PFP.wp_proc_freepagetable_sconf ga T3 P (K - 68)%nat eb
              (proc_addr jp) 0%nat eb lks
              ltac:(lia) kxc_lvl0 HT3a0
              ltac:(rewrite HT3a1 uint_unsigned;
                    exact (proc_pt_covered_maxsz P szf Hwf Hcov))
              ltac:(rewrite HT3a1; exact Hbelow)
              with "Hcg Hcnt Htext Hpc Hpt Hka").
    all: try lkbelow.
    iIntros (CID4 Hsq4 mr) "Hcg Hcnt Hpc %Hcspf".
    assert (Hpc328 : ret_pc (T3 !!! Regidx Rra) = mword_of_int (KXB + 0x328))
      by (rewrite HT3ra; pcw).
    iEval (rewrite Hpc328) in "Hpc".
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
    iApply (wp_cldsp_s_sconf (mword_of_int (KXB + 0x328))
              (mword_of_int 63 : mword 6) Rs3 mr (K - 68)%nat
              (m !!! Regidx Rs3) eb (dqm := DfracOwn 1)
              ltac:(nz) ltac:(rdok) with "Hcg Hpc [] Hf5").
    { iApply (kxc_328 with "Htext"). }
    iIntros (CID5 Hsq5) "Hcg Hpc Hf5". iEval (rewrite Hpa5) in "Hf5".
    set (U1 := <[Regidx Rs3 := regval_into_reg (m !!! Regidx Rs3)]> mr).
    assert (HU1sp : U1 !!! Regidx csp_rs1 = pa_stk sp0 68)
      by (rewrite /U1 upd_ne; [exact Hmrsp | nz]).
    assert (Hpp32a : add_vec_int (mword_of_int (KXB + 0x328) : mword 64) 2
                     = mword_of_int (KXB + 0x32a)) by pcw.
    iEval (rewrite Hpp32a) in "Hpc".
    (* +0x330: c.ldsp s5,488(sp) *)
    assert (Hpa7 : add_vec (U1 !!! Regidx csp_rs1)
              (zero_extend' 64 (concat_vec (mword_of_int 61 : mword 6) ('b"000")))
                   = pa_stk sp0 7).
    { rewrite HU1sp. apply (kxc_sp_slot sp0 7 61 _ ltac:(lia)). pcw. }
    iEval (rewrite -Hpa7) in "Hf7".
    iApply (wp_cldsp_s_sconf (mword_of_int (KXB + 0x32a))
              (mword_of_int 61 : mword 6) Rs5 U1 (K - 68)%nat
              (m !!! Regidx Rs5) eb (dqm := DfracOwn 1)
              ltac:(nz) ltac:(rdok) with "Hcg Hpc [] Hf7").
    { iApply (kxc_32a with "Htext"). }
    iIntros (CID6 Hsq6) "Hcg Hpc Hf7". iEval (rewrite Hpa7) in "Hf7".
    set (U2 := <[Regidx Rs5 := regval_into_reg (m !!! Regidx Rs5)]> U1).
    assert (HU2sp : U2 !!! Regidx csp_rs1 = pa_stk sp0 68)
      by (rewrite /U2 upd_ne; [exact HU1sp | nz]).
    assert (Hpp32c : add_vec_int (mword_of_int (KXB + 0x32a) : mword 64) 2
                     = mword_of_int (KXB + 0x32c)) by pcw.
    iEval (rewrite Hpp32c) in "Hpc".
    (* +0x332: c.ldsp s6,480(sp) *)
    assert (Hpa8 : add_vec (U2 !!! Regidx csp_rs1)
              (zero_extend' 64 (concat_vec (mword_of_int 60 : mword 6) ('b"000")))
                   = pa_stk sp0 8).
    { rewrite HU2sp. apply (kxc_sp_slot sp0 8 60 _ ltac:(lia)). pcw. }
    iEval (rewrite -Hpa8) in "Hf8".
    iApply (wp_cldsp_s_sconf (mword_of_int (KXB + 0x32c))
              (mword_of_int 60 : mword 6) Rs6 U2 (K - 68)%nat
              (m !!! Regidx Rs6) eb (dqm := DfracOwn 1)
              ltac:(nz) ltac:(rdok) with "Hcg Hpc [] Hf8").
    { iApply (kxc_32c with "Htext"). }
    iIntros (CID7 Hsq7) "Hcg Hpc Hf8". iEval (rewrite Hpa8) in "Hf8".
    set (U3 := <[Regidx Rs6 := regval_into_reg (m !!! Regidx Rs6)]> U2).
    assert (HU3sp : U3 !!! Regidx csp_rs1 = pa_stk sp0 68)
      by (rewrite /U3 upd_ne; [exact HU2sp | nz]).
    assert (Hpp32e : add_vec_int (mword_of_int (KXB + 0x32c) : mword 64) 2
                     = mword_of_int (KXB + 0x32e)) by pcw.
    iEval (rewrite Hpp32e) in "Hpc".
    (* +0x334: c.ldsp s7,472(sp) *)
    assert (Hpa9 : add_vec (U3 !!! Regidx csp_rs1)
              (zero_extend' 64 (concat_vec (mword_of_int 59 : mword 6) ('b"000")))
                   = pa_stk sp0 9).
    { rewrite HU3sp. apply (kxc_sp_slot sp0 9 59 _ ltac:(lia)). pcw. }
    iEval (rewrite -Hpa9) in "Hf9".
    iApply (wp_cldsp_s_sconf (mword_of_int (KXB + 0x32e))
              (mword_of_int 59 : mword 6) Rs7 U3 (K - 68)%nat
              (m !!! Regidx Rs7) eb (dqm := DfracOwn 1)
              ltac:(nz) ltac:(rdok) with "Hcg Hpc [] Hf9").
    { iApply (kxc_32e with "Htext"). }
    iIntros (CID8 Hsq8) "Hcg Hpc Hf9". iEval (rewrite Hpa9) in "Hf9".
    set (U4 := <[Regidx Rs7 := regval_into_reg (m !!! Regidx Rs7)]> U3).
    assert (HU4sp : U4 !!! Regidx csp_rs1 = pa_stk sp0 68)
      by (rewrite /U4 upd_ne; [exact HU3sp | nz]).
    assert (Hpp330 : add_vec_int (mword_of_int (KXB + 0x32e) : mword 64) 2
                     = mword_of_int (KXB + 0x330)) by pcw.
    iEval (rewrite Hpp330) in "Hpc".
    (* +0x336: c.ldsp s8,464(sp) *)
    assert (Hpa10 : add_vec (U4 !!! Regidx csp_rs1)
              (zero_extend' 64 (concat_vec (mword_of_int 58 : mword 6) ('b"000")))
                    = pa_stk sp0 10).
    { rewrite HU4sp. apply (kxc_sp_slot sp0 10 58 _ ltac:(lia)). pcw. }
    iEval (rewrite -Hpa10) in "Hf10".
    iApply (wp_cldsp_s_sconf (mword_of_int (KXB + 0x330))
              (mword_of_int 58 : mword 6) Rs8 U4 (K - 68)%nat
              (m !!! Regidx Rs8) eb (dqm := DfracOwn 1)
              ltac:(nz) ltac:(rdok) with "Hcg Hpc [] Hf10").
    { iApply (kxc_330 with "Htext"). }
    iIntros (CID9 Hsq9) "Hcg Hpc Hf10". iEval (rewrite Hpa10) in "Hf10".
    set (U5 := <[Regidx Rs8 := regval_into_reg (m !!! Regidx Rs8)]> U4).
    assert (HU5sp : U5 !!! Regidx csp_rs1 = pa_stk sp0 68)
      by (rewrite /U5 upd_ne; [exact HU4sp | nz]).
    assert (Hpp332 : add_vec_int (mword_of_int (KXB + 0x330) : mword 64) 2
                     = mword_of_int (KXB + 0x332)) by pcw.
    iEval (rewrite Hpp332) in "Hpc".
    (* +0x338: c.ldsp s9,456(sp) *)
    assert (Hpa11 : add_vec (U5 !!! Regidx csp_rs1)
              (zero_extend' 64 (concat_vec (mword_of_int 57 : mword 6) ('b"000")))
                    = pa_stk sp0 11).
    { rewrite HU5sp. apply (kxc_sp_slot sp0 11 57 _ ltac:(lia)). pcw. }
    iEval (rewrite -Hpa11) in "Hf11".
    iApply (wp_cldsp_s_sconf (mword_of_int (KXB + 0x332))
              (mword_of_int 57 : mword 6) Rs9 U5 (K - 68)%nat
              (m !!! Regidx Rs9) eb (dqm := DfracOwn 1)
              ltac:(nz) ltac:(rdok) with "Hcg Hpc [] Hf11").
    { iApply (kxc_332 with "Htext"). }
    iIntros (CID10 Hsq10) "Hcg Hpc Hf11". iEval (rewrite Hpa11) in "Hf11".
    set (U6 := <[Regidx Rs9 := regval_into_reg (m !!! Regidx Rs9)]> U5).
    assert (HU6sp : U6 !!! Regidx csp_rs1 = pa_stk sp0 68)
      by (rewrite /U6 upd_ne; [exact HU5sp | nz]).
    assert (Hpp334 : add_vec_int (mword_of_int (KXB + 0x332) : mword 64) 2
                     = mword_of_int (KXB + 0x334)) by pcw.
    iEval (rewrite Hpp334) in "Hpc".
    (* +0x33a: c.ldsp s10,448(sp) *)
    assert (Hpa12 : add_vec (U6 !!! Regidx csp_rs1)
              (zero_extend' 64 (concat_vec (mword_of_int 56 : mword 6) ('b"000")))
                    = pa_stk sp0 12).
    { rewrite HU6sp. apply (kxc_sp_slot sp0 12 56 _ ltac:(lia)). pcw. }
    iEval (rewrite -Hpa12) in "Hf12".
    iApply (wp_cldsp_s_sconf (mword_of_int (KXB + 0x334))
              (mword_of_int 56 : mword 6) Rs10 U6 (K - 68)%nat
              (m !!! Regidx Rs10) eb (dqm := DfracOwn 1)
              ltac:(nz) ltac:(rdok) with "Hcg Hpc [] Hf12").
    { iApply (kxc_334 with "Htext"). }
    iIntros (CID11 Hsq11) "Hcg Hpc Hf12". iEval (rewrite Hpa12) in "Hf12".
    set (U7 := <[Regidx Rs10 := regval_into_reg (m !!! Regidx Rs10)]> U6).
    assert (HU7sp : U7 !!! Regidx csp_rs1 = pa_stk sp0 68)
      by (rewrite /U7 upd_ne; [exact HU6sp | nz]).
    assert (Hpp336 : add_vec_int (mword_of_int (KXB + 0x334) : mword 64) 2
                     = mword_of_int (KXB + 0x336)) by pcw.
    iEval (rewrite Hpp336) in "Hpc".
    (* +0x33c: c.ldsp s11,440(sp) *)
    assert (Hpa13 : add_vec (U7 !!! Regidx csp_rs1)
              (zero_extend' 64 (concat_vec (mword_of_int 55 : mword 6) ('b"000")))
                    = pa_stk sp0 13).
    { rewrite HU7sp. apply (kxc_sp_slot sp0 13 55 _ ltac:(lia)). pcw. }
    iEval (rewrite -Hpa13) in "Hf13".
    iApply (wp_cldsp_s_sconf (mword_of_int (KXB + 0x336))
              (mword_of_int 55 : mword 6) Rs11 U7 (K - 68)%nat
              (m !!! Regidx Rs11) eb (dqm := DfracOwn 1)
              ltac:(nz) ltac:(rdok) with "Hcg Hpc [] Hf13").
    { iApply (kxc_336 with "Htext"). }
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
    assert (Hpp338 : add_vec_int (mword_of_int (KXB + 0x336) : mword 64) 2
                     = mword_of_int (KXB + 0x338)) by pcw.
    iEval (rewrite Hpp338) in "Hpc".
    (* ---- +0x33e: c.j +0x64 -- into the shared [bad:] tail ---- *)
    assert (Htgt64 : add_vec (mword_of_int (KXB + 0x338) : mword 64)
              (sign_extend' 64
                 (sign_extend' 21 (concat_vec (mword_of_int 1686 : mword 11)
                                              ('b"0"))))
            = mword_of_int (KXB + 0x064)) by pcw.
    iApply (wp_cj_s_sconf (mword_of_int (KXB + 0x338))
              (sign_extend' 21 (concat_vec (mword_of_int 1686 : mword 11)
                                           ('b"0")))
              U8 (K - 68)%nat eb
              ltac:(rewrite Htgt64; vm_compute; reflexivity)
              with "Hcg Hpc []").
    { iApply (kxc_338 with "Htext"). }
    iIntros (CID13 Hsq13). iNext. iIntros "Hcg Hpc".
    iEval (rewrite Htgt64) in "Hpc".
    iDestruct (cpu_own_transport CID4 CID13 0%nat eb (proc_addr jp) eb
                 ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
    iDestruct (trap_csrs_ext_transport CID3 CID13 eb (proc_addr jp)
                 ltac:(try rewrite Hebb; wp_next_chain) with "Hextc") as "Hextc".
    iDestruct (cpu_claim_ext_transport CID3 CID13 eb (proc_addr jp)
                 ltac:(try rewrite Hebb; wp_next_chain) with "Hclmc") as "Hclmc".
    iDestruct "Hopen" as "(#Hslkk & Hslkd & Hdep & Hidev & Hiinum &
                           Hivalid & Hload & #Hity & Hfrz & Hkeep & Hru)".
    (* [kxc_bad64] pins its own [CID0] from "Hcg", so kexec's exit -- still
       anchored at the section's [CID0] -- is re-anchored there, and the
       crossing fact goes by NAME (durable-notes.md). *)
    assert (Hcr : true = false \/ proc_addr jp = zero_reg ->
                  (CID13 : CPU) = (CID0 : CPU)) by wp_next_chain.
    iDestruct (wp_next_retarget CID0 CID13 true (proc_addr jp) _ Hcr
                 with "Hcont") as "Hcont".
    iApply (A.kxc_bad64 Q gs jp gl gu gd gk pd pav pu bn g gi gtl
              gilf gislf ga gf logstart bmapstart inodestart nib size
              dev kf qf sf gyf inumf dnf bmf n2
              plen pfun na avf alen aslen afun pidv V dqb dqs dqa dqpv dqas
              m U8 K eb lks sp0 ra0 s00 s10 s20 pv av
              HK Hk Hlg Hsz Hbm0 Hbmc Hbml Hins0 Hibc Hibl Hib Hcovb Hn2
              Hjp Hgs Hsp Hra Hs0 Hs1 Hs2 HU8sp HU8s4 HU8thr
              with "Hcg Hcnt Hextc Hclmc Htext Hpc Hfab Hslkk Hslkd Hdep
                    Hidev Hiinum Hivalid Hload Hity Hfrz Hkeep Hru Hbm Hins Hbits
                    Hka Hpriv Hpath Hargv Hargs Hbs Hirs Hlog [-Hcont]
                    Hcont").
    iApply (kxc_frameBpin_to_A6 sp0 ra0 s00 s10 s20 pv av
              _ _ _ _ _ _ _ _ _ _ _ _ ef Hal with "[-Helf] Helf").
    rewrite /kxc_frameBpin.
    iSplitL "Hf1"; [iExact "Hf1" |]. iSplitL "Hf2"; [iExact "Hf2" |].
    iSplitL "Hf3"; [iExact "Hf3" |]. iSplitL "Hf4"; [iExact "Hf4" |].
    iSplitL "Hf5"; [iExact "Hf5" |]. iSplitL "Hf6"; [iExact "Hf6" |].
    iSplitL "Hf7"; [iExact "Hf7" |]. iSplitL "Hf8"; [iExact "Hf8" |].
    iSplitL "Hf9"; [iExact "Hf9" |]. iSplitL "Hf10"; [iExact "Hf10" |].
    iSplitL "Hf11"; [iExact "Hf11" |]. iSplitL "Hf12"; [iExact "Hf12" |].
    iSplitL "Hf13"; [iExact "Hf13" |]. iSplitL "Hust"; [iExact "Hust" |].
    iSplitL "Hph"; [iExact "Hph" |]. iSplitL "Hf63"; [iExact "Hf63" |].
    iSplitL "Hf64"; [iExact "Hf64" |].
    iSplitL "Hf65"; [iExact "Hf65" |]. iSplitL "Hf66"; [iExact "Hf66" |].
    iSplitL "Hf67"; [iExact "Hf67" | iExact "Hf68"].
  Qed.

End KexecB2Body.

(* ===================================================================== *)
(*  THE TWO LOOPS.                                                        *)
(* ===================================================================== *)
(* THEIR OWN SECTION, and that is forced.  A loop lemma is APPLIED at the
   hart the iteration was re-entered on, which needs a [(CID0 := ...)]
   annotation -- and a still-open section rejects one for its own [Context]
   variable ("Wrong argument name CID0", durable-notes.md).  [kxc_bad324]
   above sits in the section just closed, so it can be aimed; the loops here
   bind their own hart and are aimed by their callers in turn. *)
Section KexecB2Loops.
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

  Local Ltac lregne := reg_ne_side.
  Local Ltac lpcw := apply bv_eq; vm_compute; reflexivity.
  Local Ltac lnz := vm_compute; discriminate.

  (* =================================================================== *)
  (*  +0x0f6 .. +0x114 and +0x0da .. +0x0f2 -- THE INLINED loadseg PAGE   *)
  (*  LOOP, plus the +0x0ce panic arm.                                    *)
  (*                                                                      *)
  (*    +0x0f6  slli a1,s1,0x20  } (uint64) i, zero-extended -- the C's    *)
  (*    +0x0fa  srli a1,a1,0x20  }   [va + i] at [int] width               *)
  (*    +0x0fc  add  a1,a1,s8        a1 = va + i                           *)
  (*    +0x0fe  mv   a0,s6                                                 *)
  (*    +0x100  jal  walkaddr                                              *)
  (*    +0x104  mv   a2,a0                                                 *)
  (*    +0x106  beqz a0,+0x0ce       panic("loadseg: address should exist") *)
  (*    +0x108  subw a5,s3,s1        filesz - i, in 32 bits                *)
  (*    +0x10c  mv   s2,a5                                                 *)
  (*    +0x10e  bgeu s9,a5,+0x0da    n = min(filesz - i, PGSIZE)           *)
  (*    +0x112  mv   s2,s5                                                 *)
  (*    +0x114  j    +0x0da                                                *)
  (*    +0x0da  sext.w s2,s2                                               *)
  (*    +0x0dc  mv   a4,s2                                                 *)
  (*    +0x0de  addw a3,s7,s1        off = ph.off + i, in 32 bits          *)
  (*    +0x0e2  li   a1,0            THE KERNEL ARM                        *)
  (*    +0x0e4  mv   a0,s4                                                 *)
  (*    +0x0e6  jal  readi                                                 *)
  (*    +0x0ea  bne  s2,a0,+0x324    short read -> [bad:]                  *)
  (*    +0x0ee  addw s1,s5,s1        i += PGSIZE                           *)
  (*    +0x0f2  bgeu s1,s3,+0x116    done                                  *)
  (*                                                                      *)
  (*  WHAT THE INVARIANT IS, AND WHAT IT IS NOT.                          *)
  (*                                                                      *)
  (*  It carries NOTHING about the page table.  walkaddr's failure arm     *)
  (*  reaches [panic("loadseg: address should exist")], which is           *)
  (*  discharged against [SpecPanic], so the loop never has to             *)
  (*  show its destination is mapped -- and it does not have to show the   *)
  (*  destination is page-ALIGNED either, because readi is handed the      *)
  (*  whole 4096-byte page walkaddr returned and [n <= PGSIZE].  That is   *)
  (*  the entire reason this loop is short.                                *)
  (*                                                                      *)
  (*  What it does carry is three ABI uints -- the cursor [ii], the        *)
  (*  segment's [fz = ph.filesz] and its [po = ph.off], each at the FULL   *)
  (*  32-bit range, because all three come out of an untrusted ELF and     *)
  (*  [exec] checks none of them.  [W32Arith.w32_uarg] is what such a      *)
  (*  register is worth to the [bgeu]s that decide the loop.               *)
  (*                                                                      *)
  (*  THE FUEL IS [2^32 - off], AND THE BASE CASE IS VACUOUS BECAUSE OF    *)
  (*  IT.  The obvious measure -- the file's size minus the offset -- is   *)
  (*  not available at the head: [ph.off] is untrusted, so the FIRST       *)
  (*  iteration may already be past the end of the file (that is the       *)
  (*  +0x0ea exit).  What IS available is that a continuing iteration has  *)
  (*  had readi return the full count, hence [off + n <= size <=           *)
  (*  MAXFILE*BSIZE], hence [off + PGSIZE] does not wrap -- so [off]       *)
  (*  strictly increases by PGSIZE and [2^32 - off] strictly decreases,    *)
  (*  while [0 <= off < 2^32] makes [2^32 - off <= 0] absurd.  The fuel is *)
  (*  enormous and never computed; what matters is that it is a [nat] the  *)
  (*  head can always supply.                                              *)
  (* =================================================================== *)
  Lemma kxc_ls `{CID0 : CpuId}
      (Q : mword 64 -> Prop)
      (gs : list gname) (jp : nat) (gl : gname)
      (gu : uart_names) (gd : disk_names) (gk : gname) (pd pav pu : mword 64)
      (bn : bio_names) (g : log_names) (gi : gname)
      (gtl : gname) (gilf gislf : gname) (ga gf : gname)
      (logstart bmapstart inodestart : Z) (nib : nat)
      (size : Z) (dev : mword 32)
      (kf : nat) (qf sf : Qp) (gyf : gname) (inumf : mword 32)
      (dnf : dinode) (bmf : blkmap) (n2 : nat)
      (plen : nat) (pfun : nat -> bv 8)
      (na : nat) (avf : nat -> mword 64) (alen aslen : nat -> nat)
      (afun : nat -> nat -> bv 8)
      (pidv : mword 32) (V : pprivate) (dqb dqs dqa dqpv dqas : dfrac)
      (m : regfile) (K : nat)
      (sp0 ra0 s00 s10 s20 pv av w63 w65 w67 : mword 64)
      (ef : nat -> bv 8) (P : uptd)
      (ip : nat) (va : mword 64) (fz po : Z) (eb : bool) (lks : gset string) :
    kxc_ls_body Q gs jp gl gu gd gk pd pav pu bn g gi gtl gilf gislf
      ga gf logstart bmapstart inodestart nib size dev
      kf qf sf gyf inumf dnf bmf n2 plen pfun na avf alen aslen afun
      pidv V dqb dqs dqa dqpv dqas m K sp0 ra0 s00 s10 s20 pv av w63 w65 w67
      ef P ip va fz po eb lks.
  Proof.
    cbv beta delta [kxc_ls_body].
    intros HK Hk Hlg Hsz Hbm0 Hbmc Hbml Hins0 Hcovb Hiregb Hib Hn2 Hjp Hgs
           Hdevc Hsp Hra Hs0 Hs1 Hs2 Hal Hbelow Hcovp Hfzr Hpor.
    pose proof HK as HK'. 
    assert (Hmb : (Z.of_nat MAXFILE * Z.of_nat BSIZE = 274432)%Z)
      by (vm_compute; reflexivity).
    intro W. revert CID0.
    induction W as [| W IH];
      intros CID0 Ml ii Hiir Hfuel Hguard
             HMsp HMs0 HMs1 HMs3 HMs4 HMs5 HMs6 HMs7 HMs8 HMs9 HMs10 HMs11.
    { (* NO FUEL.  [off] is an unsigned 32-bit reading, so [2^32 - off] is at
         least one and the zero case cannot arise. *)
      exfalso.
      assert (Hlt : ((po + ii) `mod` 2 ^ 32 < 2 ^ 32)%Z)
        by (apply Z.mod_pos_bound; lia).
      cbn in Hfuel. lia. }
    iIntros "Hcg Hcnt Hextc Hclmc #Htext Hpc #Hfab #Hka Hres Hcont Hc116".
    iDestruct (cpu_own_eb_agree with "Hcg Hcnt") as %Hebb.
    (* depth 0 forces the held set empty, so readi's order premise needs no
       hypothesis of this lemma's own. *)
    iDestruct (cpu_own_zero_empty with "Hcnt") as "[%Hlkempty Hcnt]".
    iDestruct "Hfab" as "(#Hkd & #Hpenv & #Hbio & #Hlogc & #Hcrash & #Hcert & #Hitab & #Hitinv &
                          #Hesc & #Hslks & #Hireg & #Hropen & #Hprocs & #Hdevi & #Hdgeom &
                          #Hdlock & %Hclogf)".
    rewrite /kxc_res.
    iDestruct "Hres" as "(Hopen & Hlog & Hirs & Hbm & Hins & Hbits & Hbs & Hpt &
                          Hpriv & Hpath & Hargv & Hargs & Helf & Hframe)".
    (* ---- +0x0f6: slli a1,s1,0x20 ---- *)
    iApply (wp_slli_s_sconf (mword_of_int (KXB + 0x0f6)) Ra1 Rs1
              (mword_of_int 32 : mword 6)
              (shift_bits_left (sign_extend' 64 (mword_of_int ii : mword 32))
                 (subrange_vec_dec (mword_of_int 32 : mword 6)
                    (Z.sub log2_xlen 1) 0))
              Ml (K - 68)%nat eb ltac:(lnz) ltac:(rdok)
              ltac:(rewrite (rget_ne Ml Rs1 ltac:(lnz)) HMs1; reflexivity)
              with "Hcg Hpc []").
    { iApply (kxc_0f6 with "Htext"). }
    iIntros (CID1 Hsq1) "Hcg Hpc".
    set (N1 := <[Regidx Ra1 := regval_into_reg
                  (shift_bits_left (sign_extend' 64 (mword_of_int ii : mword 32))
                     (subrange_vec_dec (mword_of_int 32 : mword 6)
                        (Z.sub log2_xlen 1) 0))]> Ml).
    assert (HN1a1 : N1 !!! Regidx Ra1
              = shift_bits_left (sign_extend' 64 (mword_of_int ii : mword 32))
                  (subrange_vec_dec (mword_of_int 32 : mword 6)
                     (Z.sub log2_xlen 1) 0))
      by (rewrite /N1; apply upd_eq).
    assert (Hpp0fa : add_vec_int (mword_of_int (KXB + 0x0f6) : mword 64) 4
                     = mword_of_int (KXB + 0x0fa)) by lpcw.
    iEval (rewrite Hpp0fa) in "Hpc".
    (* ---- +0x0fa: c.srli a1,a1,0x20 -- a1 = (uint64) i ---- *)
    iApply (wp_csrli_s_sconf (mword_of_int (KXB + 0x0fa))
              (Cregidx (mword_of_int 3)) Ra1 (mword_of_int 32 : mword 6)
              N1 (K - 68)%nat eb ltac:(vm_compute; reflexivity)
              ltac:(lnz) ltac:(rdok) with "Hcg Hpc []").
    { iApply (kxc_0fa with "Htext"). }
    iIntros (CID2 Hsq2) "Hcg Hpc". iEval (rgne) in "Hcg".
    set (N2 := <[Regidx Ra1 := regval_into_reg
                  (shift_bits_right (N1 !!! Regidx Ra1)
                     (subrange_vec_dec (mword_of_int 32 : mword 6)
                        (Z.sub log2_xlen 1) 0))]> N1).
    assert (HN2a1 : N2 !!! Regidx Ra1 = (mword_of_int ii : mword 64)).
    { rewrite /N2 upd_eq HN1a1. exact (w32_zext_arg ii Hiir). }
    assert (Hpp0fc : add_vec_int (mword_of_int (KXB + 0x0fa) : mword 64) 2
                     = mword_of_int (KXB + 0x0fc)) by lpcw.
    iEval (rewrite Hpp0fc) in "Hpc".
    (* ---- +0x0fc: c.add a1,a1,s8 -- a1 = va + i ---- *)
    iApply (wp_cadd_s_sconf (mword_of_int (KXB + 0x0fc)) Ra1 Rs8
              N2 (K - 68)%nat eb ltac:(lnz) ltac:(rdok)
              with "Hcg Hpc []").
    { iApply (kxc_0fc with "Htext"). }
    iIntros (CID3 Hsq3) "Hcg Hpc". iEval (rgne) in "Hcg". iEval (rgne) in "Hcg".
    set (vai := add_vec (mword_of_int ii : mword 64) va).
    assert (HN2s8 : N2 !!! Regidx Rs8 = va).
    { rewrite /N2 upd_ne; [| lnz]. rewrite /N1 upd_ne; [exact HMs8 | lnz]. }
    set (N3 := <[Regidx Ra1 := regval_into_reg
                  (add_vec (N2 !!! Regidx Ra1) (N2 !!! Regidx Rs8))]> N2).
    assert (HN3a1 : N3 !!! Regidx Ra1 = vai).
    { rewrite /N3 upd_eq HN2a1 HN2s8. reflexivity. }
    assert (Hpp0fe : add_vec_int (mword_of_int (KXB + 0x0fc) : mword 64) 2
                     = mword_of_int (KXB + 0x0fe)) by lpcw.
    iEval (rewrite Hpp0fe) in "Hpc".
    (* ---- +0x0fe: c.mv a0,s6 -- the NEW table's root ---- *)
    iApply (wp_cmv_s_sconf (mword_of_int (KXB + 0x0fe)) Ra0 Rs6
              N3 (K - 68)%nat eb ltac:(lnz) ltac:(rdok)
              with "Hcg Hpc []").
    { iApply (kxc_0fe with "Htext"). }
    iIntros (CID4 Hsq4) "Hcg Hpc". iEval (rgne) in "Hcg".
    set (N4 := <[Regidx Ra0 := regval_into_reg
                  (add_vec zero_reg (N3 !!! Regidx Rs6))]> N3).
    assert (HN3s6 : N3 !!! Regidx Rs6 = page_base P.(ud_root)).
    { rewrite /N3 upd_ne; [| lnz]. rewrite /N2 upd_ne; [| lnz].
      rewrite /N1 upd_ne; [exact HMs6 | lnz]. }
    assert (HN4a0 : N4 !!! Regidx Ra0 = page_base P.(ud_root))
      by (rewrite /N4 upd_eq HN3s6 w32_zero_add; reflexivity).
    assert (HN4a1 : N4 !!! Regidx Ra1 = vai)
      by (rewrite /N4 upd_ne; [exact HN3a1 | lnz]).
    assert (Hpp100 : add_vec_int (mword_of_int (KXB + 0x0fe) : mword 64) 2
                     = mword_of_int (KXB + 0x100)) by lpcw.
    iEval (rewrite Hpp100) in "Hpc".
    (* the register facts that survive to the far side of walkaddr *)
    assert (HN4get : forall r : mword 5, is_cs_idx r = true ->
              N4 !!! Regidx r = Ml !!! Regidx r).
    { intros r Hr. rewrite /N4 upd_ne; [| lregne]. rewrite /N3 upd_ne; [| lregne].
      rewrite /N2 upd_ne; [| lregne]. rewrite /N1 upd_ne; [| lregne].
      reflexivity. }
    (* ---- +0x100: jal ra,walkaddr ---- *)
    iDestruct (proc_pt_acc_rep0 P with "Hpt") as
      (t m_ad) "(%Hrep & %Hview & %Hbase & %Hwf & Hptree & Hown)".
    assert (HN4root : N4 !!! Regidx Ra0
                      = zero_extend' 64 (concat_vec (pt_base t)
                                           (zeros' 12 : mword 12))).
    { rewrite HN4a0 Hbase. reflexivity. }
    assert (Htwa : add_vec (mword_of_int (KXB + 0x100) : mword 64)
                     (sign_extend' 64 (mword_of_int 2082534 : mword 21))
                   = mword_of_int KernelSyms.walkaddr) by lpcw.
    iApply (wp_jal_s_sconf (mword_of_int (KXB + 0x100)) Rra
              (mword_of_int 2082534 : mword 21) N4 (K - 68)%nat eb
              ltac:(lnz) ltac:(rdok)
              ltac:(rewrite Htwa; vm_compute; reflexivity)
              with "Hcg Hpc []").
    { iApply (kxc_100 with "Htext"). }
    iIntros (CID5 Hsq5) "Hcg Hpc". iEval (rewrite Htwa) in "Hpc".
    set (N5 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (KXB + 0x100) : mword 64) 4)]> N4).
    change (<[Regidx Rra := regval_into_reg
              (add_vec_int (mword_of_int (KXB + 0x100) : mword 64) 4)]> N4)
      with N5.
    assert (HN5ra : N5 !!! Regidx Rra
                    = add_vec_int (mword_of_int (KXB + 0x100) : mword 64) 4)
      by (rewrite /N5; apply upd_eq).
    assert (HN5a0 : N5 !!! Regidx Ra0
                    = zero_extend' 64 (concat_vec (pt_base t)
                                         (zeros' 12 : mword 12)))
      by (rewrite /N5 upd_ne; [exact HN4root | lnz]).
    assert (HN5a1 : N5 !!! Regidx Ra1 = vai)
      by (rewrite /N5 upd_ne; [exact HN4a1 | lnz]).
    assert (HN5get : forall r : mword 5, is_cs_idx r = true ->
              N5 !!! Regidx r = Ml !!! Regidx r).
    { intros r Hr. rewrite /N5 upd_ne; [| lregne]. exact (HN4get r Hr). }
    iApply (Walkaddr.wp_walkaddr_sconf N5 t m_ad (K - 68)%nat (DfracOwn 1)
              eb (proc_addr jp) ltac:(lia) HN5a0 Hrep
              with "Hcg Htext Hpc Hptree").
    iIntros (CIDw Hsw mr) "Hcg Hpc Hptree %Hwacs %Hwapay".
    rewrite HN5a1 in Hwapay.
    assert (Hpc104 : ret_pc (N5 !!! Regidx Rra) = mword_of_int (KXB + 0x104))
      by (rewrite HN5ra; lpcw).
    iEval (rewrite Hpc104) in "Hpc".
    assert (Hmrget : forall r : mword 5, is_cs_idx r = true ->
              mr !!! Regidx r = Ml !!! Regidx r).
    { intros r Hr. rewrite (callee_saved_lookup Hwacs r Hr). exact (HN5get r Hr). }
    (* ---- +0x104: c.mv a2,a0 ---- *)
    iApply (wp_cmv_s_sconf (mword_of_int (KXB + 0x104)) Ra2 Ra0
              mr (K - 68)%nat eb ltac:(lnz) ltac:(rdok)
              with "Hcg Hpc []").
    { iApply (kxc_104 with "Htext"). }
    iIntros (CID6 Hsq6) "Hcg Hpc". iEval (rgne) in "Hcg".
    set (N6 := <[Regidx Ra2 := regval_into_reg
                  (add_vec zero_reg (mr !!! Regidx Ra0))]> mr).
    assert (HN6a2 : N6 !!! Regidx Ra2 = mr !!! Regidx Ra0)
      by (rewrite /N6 upd_eq w32_zero_add; reflexivity).
    assert (HN6a0 : N6 !!! Regidx Ra0 = mr !!! Regidx Ra0)
      by (rewrite /N6 upd_ne; [reflexivity | lnz]).
    assert (HN6get : forall r : mword 5, is_cs_idx r = true ->
              N6 !!! Regidx r = Ml !!! Regidx r).
    { intros r Hr. rewrite /N6 upd_ne; [| lregne]. exact (Hmrget r Hr). }
    assert (Hpp106 : add_vec_int (mword_of_int (KXB + 0x104) : mword 64) 2
                     = mword_of_int (KXB + 0x106)) by lpcw.
    iEval (rewrite Hpp106) in "Hpc".
    (* ---- +0x106: c.beqz a0,+0x0ce -- the panic arm ---- *)
    destruct Hwapay as [(Ha0z & _) | (wpte & Hsome & Hvu & _ & Ha0v)].
    { (* walkaddr missed: panic("loadseg: address should exist"), which the
         arm is discharged against [SpecPanic] -- so it needs nothing back. *)
      assert (Htgt0ce : add_vec (mword_of_int (KXB + 0x106) : mword 64)
                (sign_extend' 64
                   (sign_extend' 13 (concat_vec (mword_of_int 228 : mword 8)
                                                ('b"0"))))
              = mword_of_int (KXB + 0x0ce)) by lpcw.
      iApply (wp_cbeqz_taken_s_sconf (mword_of_int (KXB + 0x106))
                (mword_of_int 228 : mword 8) (Cregidx (mword_of_int 2)) Ra0
                N6 (K - 68)%nat eb ltac:(vm_compute; reflexivity) ltac:(lnz)
                ltac:(rgne; rewrite HN6a0 Ha0z; apply eq_vec_true_iff;
                      apply bv_eq; vm_compute; reflexivity)
                ltac:(rewrite Htgt0ce; vm_compute; reflexivity)
                with "Hcg Hpc []").
      { iApply (kxc_106 with "Htext"). }
      iIntros (CIDp0 Hsp0). iNext. iIntros "Hcg Hpc".
      iEval (rewrite Htgt0ce) in "Hpc".
      (* +0x0ce auipc a0,0x3 *)
      iApply (wp_auipc_s_sconf (mword_of_int (KXB + 0x0ce)) Ra0
                (mword_of_int 3 : mword 20) N6 (K - 68)%nat eb
                ltac:(lnz) ltac:(rdok) with "Hcg Hpc []").
      { iApply (kxc_0ce with "Htext"). }
      iIntros (CIDp1 Hsp1) "Hcg Hpc".
      set (Np1 := <[Regidx Ra0 := regval_into_reg
                     (add_vec (mword_of_int (KXB + 0x0ce) : mword 64)
                        (auipc_off (mword_of_int 3 : mword 20)))]> N6).
      assert (Hpp0d2 : add_vec_int (mword_of_int (KXB + 0x0ce) : mword 64) 4
                       = mword_of_int (KXB + 0x0d2)) by lpcw.
      iEval (rewrite Hpp0d2) in "Hpc".
      (* +0x0d2 addi a0,a0,3482 *)
      iApply (wp_addi4_s_sconf (mword_of_int (KXB + 0x0d2)) Ra0 Ra0
                (mword_of_int 3374 : mword 12) Np1 (K - 68)%nat eb
                ltac:(lnz) ltac:(rdok) with "Hcg Hpc []").
      { iApply (kxc_0d2 with "Htext"). }
      iIntros (CIDp2 Hsp2) "Hcg Hpc".
      set (Np2 := <[Regidx Ra0 := regval_into_reg
                     (add_vec (rget Np1 Ra0)
                        (sign_extend' 64 (mword_of_int 3374 : mword 12)))]> Np1).
      assert (Hpp0d6 : add_vec_int (mword_of_int (KXB + 0x0d2) : mword 64) 4
                       = mword_of_int (KXB + 0x0d6)) by lpcw.
      iEval (rewrite Hpp0d6) in "Hpc".
      (* +0x0d6 jal ra,panic -- and panic() never returns *)
      assert (Htpn : add_vec (mword_of_int (KXB + 0x0d6) : mword 64)
                       (sign_extend' 64 (mword_of_int 2080634 : mword 21))
                     = mword_of_int KernelSyms.panic) by lpcw.
      iApply (wp_jal_s_sconf (mword_of_int (KXB + 0x0d6)) Rra
                (mword_of_int 2080634 : mword 21) Np2 (K - 68)%nat eb
                ltac:(lnz) ltac:(rdok)
                ltac:(rewrite Htpn; vm_compute; reflexivity)
                with "Hcg Hpc []").
      { iApply (kxc_0d6 with "Htext"). }
      iIntros (CIDp3 Hsp3) "Hcg Hpc". iEval (rewrite Htpn) in "Hpc".
      (* ---- panic() AS AN ORDINARY CALL, against SpecPanic ----
         a0 holds &"loadseg: address should exist"; [kernel_data] and
         [panic_env] both come out of [fs_fabric], and [cpu_own] has to
         arrive AT THE PANIC HART (CIDp3). *)
      iPoseProof (kxc_msg_str with "Hkd") as "#Hstr".
      iDestruct (cpu_own_transport CID0 CIDp3 0%nat eb (proc_addr jp) eb
                   ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
      iDestruct (trap_csrs_ext_transport CID0 CIDp3 eb (proc_addr jp)
                   ltac:(try rewrite Hebb; wp_next_chain) with "Hextc") as "Hextc".
      iDestruct (cpu_claim_ext_transport CID0 CIDp3 eb (proc_addr jp)
                   ltac:(try rewrite Hebb; wp_next_chain) with "Hclmc") as "Hclmc".
      (* THE REGFILE THE SPEC WANTS IS THE POST-JAL ONE. *)
      pose (Np3 := <[Regidx Rra := regval_into_reg
                       (add_vec_int (mword_of_int (KXB + 0x0d6) : mword 64) 4)]> Np2).
      assert (Ha0msg : Np3 !!! Regidx Ra0 = (mword_of_int kxc_msg_a : mword 64))
        by lpcw.
      iApply (PN.wp_panic_sconf KT1 (CID := CIDp3) Np3 (K - 68)%nat
                0%nat eb eb (proc_addr jp) (PkAStr DfracDiscarded kxc_msg) lks
                (kxc_panic_K K HK) eq_refl kxc_panic_noff
                (kxc_panic_below lks Hlkempty)
                with "Hcg Hcnt Htext Hkd Hpc Hpenv [Hstr]").
      { rewrite /pk_desc_res Ha0msg.
        iSplit; [iPureIntro; exact kxc_msg_nonul|].
        iSplit; [iPureIntro; exact kxc_msg_nz|]. iExact "Hstr". } }
    (* ===== walkaddr hit: the page is there ===== *)
    destruct (upt_ad_view_vu P.(ud_tfp) P.(ud_um) m_ad (svpn_of vai) wpte
                Hview Hsome Hvu) as (w0 & Hum0 & Hppn0).
    assert (Hpv0 : page_valid (page_base (pte_ppn w0)))
      by exact (um_page_valid P (svpn_of vai) w0 Hwf Hum0).
    assert (Hpa0v : mr !!! Regidx Ra0 = page_base (pte_ppn w0))
      by (rewrite Ha0v Hppn0; reflexivity).
    iDestruct (proc_pt_rebuild P t m_ad Hwf Hview Hrep Hbase
                 with "Hptree Hown") as "Hpt".
    assert (Ha0nz : eq_vec (rget N6 Ra0) zero_reg = false).
    { rewrite (rget_ne N6 Ra0 ltac:(lnz)) HN6a0 Hpa0v.
      apply eq_vec_false_iff. intro Hc.
      apply (page_valid_ne_null _ Hpv0). rewrite Hc.
      apply bv_eq; vm_compute; reflexivity. }
    iApply (wp_cbeqz_fall_s_sconf (mword_of_int (KXB + 0x106))
              (mword_of_int 228 : mword 8) (Cregidx (mword_of_int 2)) Ra0
              N6 (K - 68)%nat eb ltac:(vm_compute; reflexivity) ltac:(lnz)
              Ha0nz with "Hcg Hpc []").
    { iApply (kxc_106 with "Htext"). }
    iIntros (CID7 Hsq7) "Hcg Hpc".
    assert (Hpp108 : add_vec_int (mword_of_int (KXB + 0x106) : mword 64) 2
                     = mword_of_int (KXB + 0x108)) by lpcw.
    iEval (rewrite Hpp108) in "Hpc".
    (* ---- +0x108: subw a5,s3,s1 -- (uint)(filesz - i) ---- *)
    assert (HN6s3 : N6 !!! Regidx Rs3
                    = sign_extend' 64 (mword_of_int fz : mword 32))
      by (rewrite (HN6get Rs3 ltac:(vm_compute; reflexivity)); exact HMs3).
    assert (HN6s1 : N6 !!! Regidx Rs1
                    = sign_extend' 64 (mword_of_int ii : mword 32))
      by (rewrite (HN6get Rs1 ltac:(vm_compute; reflexivity)); exact HMs1).
    iApply (wp_subw_s_sconf (mword_of_int (KXB + 0x108)) Ra5 Rs3 Rs1
              N6 (K - 68)%nat eb ltac:(lnz) ltac:(rdok)
              with "Hcg Hpc []").
    { iApply (kxc_108 with "Htext"). }
    iIntros (CID8 Hsq8) "Hcg Hpc". iEval (rgne) in "Hcg". iEval (rgne) in "Hcg".
    set (dz := ((fz - ii) `mod` 2 ^ 32)%Z).
    set (N8 := <[Regidx Ra5 := regval_into_reg
                  (sign_extend' 64 (sub_vec
                     (subrange_vec_dec (N6 !!! Regidx Rs3) 31 0 : mword 32)
                     (subrange_vec_dec (N6 !!! Regidx Rs1) 31 0
                      : mword 32)))]> N6).
    assert (Hdzr : (0 <= dz < 2 ^ 32)%Z)
      by (rewrite /dz; apply Z.mod_pos_bound; lia).
    (* the guard says the cursor has not reached the size, so the difference
       is nonzero -- which is what makes [n] at least one, and hence what
       makes a successful readi bound [off] by the file's size *)
    assert (Hdznz : dz <> 0%Z).
    { rewrite /dz. intro Hc.
      assert (Hfi : fz = ii).
      { assert (Hmm : ((fz - ii) `mod` 2 ^ 32 = 0)%Z) by exact Hc.
        apply Z.mod_divide in Hmm; [| lia]. destruct Hmm as [kq Hkq]. lia. }
      rewrite Hfi in Hguard. lia. }
    assert (HN8a5 : N8 !!! Regidx Ra5
                    = sign_extend' 64 (mword_of_int dz : mword 32)).
    { rewrite /N8 upd_eq HN6s3 HN6s1 w32_subw_arg2 /dz.
      symmetry. apply w32_arg_mod. }
    assert (HN8get : forall r : mword 5, is_cs_idx r = true ->
              N8 !!! Regidx r = Ml !!! Regidx r).
    { intros r Hr. rewrite /N8 upd_ne; [| lregne]. exact (HN6get r Hr). }
    assert (HN8a2 : N8 !!! Regidx Ra2 = page_base (pte_ppn w0))
      by (rewrite /N8 upd_ne; [rewrite HN6a2 Hpa0v; reflexivity | lnz]).
    assert (Hpp10c : add_vec_int (mword_of_int (KXB + 0x108) : mword 64) 4
                     = mword_of_int (KXB + 0x10c)) by lpcw.
    iEval (rewrite Hpp10c) in "Hpc".
    (* ---- +0x10c: c.mv s2,a5 ---- *)
    iApply (wp_cmv_s_sconf (mword_of_int (KXB + 0x10c)) Rs2 Ra5
              N8 (K - 68)%nat eb ltac:(lnz) ltac:(rdok)
              with "Hcg Hpc []").
    { iApply (kxc_10c with "Htext"). }
    iIntros (CID9 Hsq9) "Hcg Hpc". iEval (rgne) in "Hcg".
    set (N9 := <[Regidx Rs2 := regval_into_reg
                  (add_vec zero_reg (N8 !!! Regidx Ra5))]> N8).
    assert (HN9a5 : N9 !!! Regidx Ra5
                    = sign_extend' 64 (mword_of_int dz : mword 32))
      by (rewrite /N9 upd_ne; [exact HN8a5 | lnz]).
    assert (HN9s2 : N9 !!! Regidx Rs2
                    = sign_extend' 64 (mword_of_int dz : mword 32)).
    { rewrite /N9 upd_eq HN8a5 w32_zero_add. reflexivity. }
    assert (HN9s9 : N9 !!! Regidx Rs9 = (mword_of_int 4096 : mword 64)).
    { rewrite /N9 upd_ne; [| lnz].
      rewrite (HN8get Rs9 ltac:(vm_compute; reflexivity)). exact HMs9. }
    assert (HN9s5 : N9 !!! Regidx Rs5 = (mword_of_int 4096 : mword 64)).
    { rewrite /N9 upd_ne; [| lnz].
      rewrite (HN8get Rs5 ltac:(vm_compute; reflexivity)). exact HMs5. }
    assert (HN9a2 : N9 !!! Regidx Ra2 = page_base (pte_ppn w0))
      by (rewrite /N9 upd_ne; [exact HN8a2 | lnz]).
    assert (HN9get : forall r : mword 5, is_cs_idx r = true -> r <> Rs2 ->
              N9 !!! Regidx r = Ml !!! Regidx r).
    { intros r Hr Hne. rewrite /N9 upd_ne; [| lregne]. exact (HN8get r Hr). }
    assert (Hpp10e : add_vec_int (mword_of_int (KXB + 0x10c) : mword 64) 2
                     = mword_of_int (KXB + 0x10e)) by lpcw.
    iEval (rewrite Hpp10e) in "Hpc".
    (* =================================================================
       +0x0da .. +0x0f2, AS ONE CONTINUATION.  Both arms of the [bgeu] at
       +0x10e reach it, with the SAME state but a different [n], so it is
       asserted once here and applied twice below rather than written out
       on each arm.  [nn] is the count readi is asked for; [1 <= nn <= 4096]
       is everything the block needs of it.
       ================================================================= *)
    iAssert (∀ (CIDd : CpuId) (Md : regfile) (nn : nat),
               ⌜true = false \/ proc_addr jp = zero_reg ->
                 (CIDd : CPU) = (CID0 : CPU)⌝ -∗
               ⌜(1 <= nn)%nat /\ (nn <= 4096)%nat /\
                 Md !!! Regidx Rs2 = (mword_of_int (Z.of_nat nn) : mword 64) /\
                 Md !!! Regidx Ra2 = page_base (pte_ppn w0) /\
                 (forall r : mword 5, is_cs_idx r = true -> r <> Rs2 ->
                    Md !!! Regidx r = Ml !!! Regidx r)⌝ -∗
               sie_cap_gpr KT1 Md (K - 68)%nat eb (proc_addr jp) -∗
               cpu_own (CID := CIDd) 0 eb (proc_addr jp) eb lks -∗
               trap_csrs_ext KT1 eb -∗
               cpu_claim_ext eb (proc_addr jp) -∗
               pc_is (mword_of_int (KXB + 0x0da) : mword 64) -∗
               WP (Loop : expr riscv_lang))%I
      with "[Hopen Hlog Hirs Hbm Hins Hbits Hbs Hpt Hpriv
             Hpath Hargv Hargs Helf Hframe Hcont Hc116]" as "AT0DA".
    {
      (* =============================================================
         +0x0da .. +0x0f2 -- the readi, the short-read exit and the
         back edge.
         ============================================================= *)
      iIntros (CIDd Md nn) "%Hcrd %Hdf Hcg Hcnt Hextc Hclmc Hpc".
      destruct Hdf as (Hnn1 & Hnn2 & HMds2 & HMda2 & HMdget).
      set (offz := ((po + ii) `mod` 2 ^ 32)%Z).
      assert (Hoffr : (0 <= offz < 2 ^ 32)%Z)
        by (rewrite /offz; apply Z.mod_pos_bound; lia).
      set (offn := Z.to_nat offz).
      assert (HoffnZ : Z.of_nat offn = offz) by (rewrite /offn Z2Nat.id; lia).
      (* ---- +0x0da: c.addiw s2,s2,0 -- the C's [n] is a [uint] ---- *)
      iApply (wp_caddiw_s_sconf (mword_of_int (KXB + 0x0da)) Rs2
                (mword_of_int 0 : mword 6) Md (K - 68)%nat eb
                ltac:(lnz) ltac:(rdok) with "Hcg Hpc []").
      { iApply (kxc_0da with "Htext"). }
      iIntros (CIDd1 Hsd1) "Hcg Hpc". iEval (rgne) in "Hcg".
      set (D1 := <[Regidx Rs2 := regval_into_reg
                    (sign_extend' 64 (subrange_vec_dec
                       (add_vec (Md !!! Regidx Rs2)
                          (sign_extend' 64 (sign_extend' 12
                             (mword_of_int 0 : mword 6)))) 31 0))]> Md).
      assert (HD1s2 : D1 !!! Regidx Rs2
                      = (mword_of_int (Z.of_nat nn) : mword 64)).
      { rewrite /D1 upd_eq HMds2. apply w32_sextw6_moi.
        change (2 ^ 31)%Z with 2147483648%Z. lia. }
      assert (HD1a2 : D1 !!! Regidx Ra2 = page_base (pte_ppn w0))
        by (rewrite /D1 upd_ne; [exact HMda2 | lnz]).
      assert (HD1get : forall r : mword 5, is_cs_idx r = true -> r <> Rs2 ->
                D1 !!! Regidx r = Ml !!! Regidx r).
      { intros r Hr Hne. rewrite /D1 upd_ne; [| lregne].
        exact (HMdget r Hr Hne). }
      assert (Hppdc : add_vec_int (mword_of_int (KXB + 0x0da) : mword 64) 2
                      = mword_of_int (KXB + 0x0dc)) by lpcw.
      iEval (rewrite Hppdc) in "Hpc".
      (* ---- +0x0dc: c.mv a4,s2 ---- *)
      iApply (wp_cmv_s_sconf (mword_of_int (KXB + 0x0dc)) Ra4 Rs2
                D1 (K - 68)%nat eb ltac:(lnz) ltac:(rdok)
                with "Hcg Hpc []").
      { iApply (kxc_0dc with "Htext"). }
      iIntros (CIDd2 Hsd2) "Hcg Hpc". iEval (rgne) in "Hcg".
      set (D2 := <[Regidx Ra4 := regval_into_reg
                    (add_vec zero_reg (D1 !!! Regidx Rs2))]> D1).
      assert (HD2a4 : D2 !!! Regidx Ra4
                = sign_extend' 64 (mword_of_int (Z.of_nat nn) : mword 32)).
      { rewrite /D2 upd_eq HD1s2 w32_zero_add. apply rd_arg32_small.
        change (2 ^ 31)%Z with 2147483648%Z. lia. }
      assert (HD2s2 : D2 !!! Regidx Rs2
                      = (mword_of_int (Z.of_nat nn) : mword 64))
        by (rewrite /D2 upd_ne; [exact HD1s2 | lnz]).
      assert (HD2a2 : D2 !!! Regidx Ra2 = page_base (pte_ppn w0))
        by (rewrite /D2 upd_ne; [exact HD1a2 | lnz]).
      assert (HD2get : forall r : mword 5, is_cs_idx r = true -> r <> Rs2 ->
                D2 !!! Regidx r = Ml !!! Regidx r).
      { intros r Hr Hne. rewrite /D2 upd_ne; [| lregne].
        exact (HD1get r Hr Hne). }
      assert (Hppde : add_vec_int (mword_of_int (KXB + 0x0dc) : mword 64) 2
                      = mword_of_int (KXB + 0x0de)) by lpcw.
      iEval (rewrite Hppde) in "Hpc".
      (* ---- +0x0de: addw a3,s7,s1 -- off = ph.off + i, in 32 bits ---- *)
      assert (HD2s7 : D2 !!! Regidx Rs7
                      = sign_extend' 64 (mword_of_int po : mword 32))
        by (rewrite (HD2get Rs7 ltac:(vm_compute; reflexivity) ltac:(lnz));
            exact HMs7).
      assert (HD2s1 : D2 !!! Regidx Rs1
                      = sign_extend' 64 (mword_of_int ii : mword 32))
        by (rewrite (HD2get Rs1 ltac:(vm_compute; reflexivity) ltac:(lnz));
            exact HMs1).
      iApply (wp_addw4_s_sconf (mword_of_int (KXB + 0x0de)) Ra3 Rs7 Rs1
                D2 (K - 68)%nat eb ltac:(lnz) ltac:(rdok)
                with "Hcg Hpc []").
      { iApply (kxc_0de with "Htext"). }
      iIntros (CIDd3 Hsd3) "Hcg Hpc". iEval (rgne) in "Hcg".
      iEval (rgne) in "Hcg".
      set (D3 := <[Regidx Ra3 := regval_into_reg
                    (sign_extend' 64 (add_vec
                       (subrange_vec_dec (D2 !!! Regidx Rs7) 31 0 : mword 32)
                       (subrange_vec_dec (D2 !!! Regidx Rs1) 31 0
                        : mword 32)))]> D2).
      assert (HD3a3 : D3 !!! Regidx Ra3
                = sign_extend' 64 (mword_of_int (Z.of_nat offn) : mword 32)).
      { rewrite /D3 upd_eq HD2s7 HD2s1 w32_addw_arg2 HoffnZ /offz.
        symmetry. apply w32_arg_mod. }
      assert (HD3a4 : D3 !!! Regidx Ra4
                = sign_extend' 64 (mword_of_int (Z.of_nat nn) : mword 32))
        by (rewrite /D3 upd_ne; [exact HD2a4 | lnz]).
      assert (HD3s2 : D3 !!! Regidx Rs2
                      = (mword_of_int (Z.of_nat nn) : mword 64))
        by (rewrite /D3 upd_ne; [exact HD2s2 | lnz]).
      assert (HD3a2 : D3 !!! Regidx Ra2 = page_base (pte_ppn w0))
        by (rewrite /D3 upd_ne; [exact HD2a2 | lnz]).
      assert (HD3get : forall r : mword 5, is_cs_idx r = true -> r <> Rs2 ->
                D3 !!! Regidx r = Ml !!! Regidx r).
      { intros r Hr Hne. rewrite /D3 upd_ne; [| lregne].
        exact (HD2get r Hr Hne). }
      assert (Hppe2 : add_vec_int (mword_of_int (KXB + 0x0de) : mword 64) 4
                      = mword_of_int (KXB + 0x0e2)) by lpcw.
      iEval (rewrite Hppe2) in "Hpc".
      (* ---- +0x0e2: c.li a1,0 -- THE KERNEL ARM of readi ---- *)
      iApply (wp_cli_s_sconf (mword_of_int (KXB + 0x0e2)) Ra1
                (mword_of_int 0 : mword 6) (mword_of_int 0 : mword 64)
                D3 (K - 68)%nat eb ltac:(lnz) ltac:(rdok)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                with "Hcg Hpc []").
      { iApply (kxc_0e2 with "Htext"). }
      iIntros (CIDd4 Hsd4) "Hcg Hpc".
      set (D4 := <[Regidx Ra1 := regval_into_reg
                    (mword_of_int 0 : mword 64)]> D3).
      assert (Hppe4 : add_vec_int (mword_of_int (KXB + 0x0e2) : mword 64) 2
                      = mword_of_int (KXB + 0x0e4)) by lpcw.
      iEval (rewrite Hppe4) in "Hpc".
      (* ---- +0x0e4: c.mv a0,s4 ---- *)
      iApply (wp_cmv_s_sconf (mword_of_int (KXB + 0x0e4)) Ra0 Rs4
                D4 (K - 68)%nat eb ltac:(lnz) ltac:(rdok)
                with "Hcg Hpc []").
      { iApply (kxc_0e4 with "Htext"). }
      iIntros (CIDd5 Hsd5) "Hcg Hpc". iEval (rgne) in "Hcg".
      set (D5 := <[Regidx Ra0 := regval_into_reg
                    (add_vec zero_reg (D4 !!! Regidx Rs4))]> D4).
      assert (HD4s4 : D4 !!! Regidx Rs4 = ientry kf).
      { rewrite /D4 upd_ne; [| lnz].
        rewrite (HD3get Rs4 ltac:(vm_compute; reflexivity) ltac:(lnz)).
        exact HMs4. }
      assert (Hppe6 : add_vec_int (mword_of_int (KXB + 0x0e4) : mword 64) 2
                      = mword_of_int (KXB + 0x0e6)) by lpcw.
      iEval (rewrite Hppe6) in "Hpc".
      (* ---- +0x0e6: jal ra,readi ---- *)
      assert (Htrd : add_vec (mword_of_int (KXB + 0x0e6) : mword 64)
                       (sign_extend' 64 (mword_of_int 2092342 : mword 21))
                     = mword_of_int KernelSyms.readi) by lpcw.
      iApply (wp_jal_s_sconf (mword_of_int (KXB + 0x0e6)) Rra
                (mword_of_int 2092342 : mword 21) D5 (K - 68)%nat eb
                ltac:(lnz) ltac:(rdok)
                ltac:(rewrite Htrd; vm_compute; reflexivity)
                with "Hcg Hpc []").
      { iApply (kxc_0e6 with "Htext"). }
      iIntros (CIDd6 Hsd6) "Hcg Hpc". iEval (rewrite Htrd) in "Hpc".
      set (D6 := <[Regidx Rra := regval_into_reg
                    (add_vec_int (mword_of_int (KXB + 0x0e6) : mword 64) 4)]> D5).
      change (<[Regidx Rra := regval_into_reg
                (add_vec_int (mword_of_int (KXB + 0x0e6) : mword 64) 4)]> D5)
        with D6.
      assert (HD6ra : D6 !!! Regidx Rra
                = add_vec_int (mword_of_int (KXB + 0x0e6) : mword 64) 4)
        by (rewrite /D6; apply upd_eq).
      assert (HD6a0 : D6 !!! Regidx Ra0 = ientry kf).
      { rewrite /D6 upd_ne; [| lnz]. rewrite /D5 upd_eq HD4s4.
        apply w32_zero_add. }
      assert (HD6a1 : D6 !!! Regidx Ra1 = (mword_of_int 0 : mword 64)).
      { rewrite /D6 upd_ne; [| lnz]. rewrite /D5 upd_ne; [| lnz].
        rewrite /D4; apply upd_eq. }
      assert (HD6a2 : D6 !!! Regidx Ra2 = page_base (pte_ppn w0)).
      { rewrite /D6 upd_ne; [| lnz]. rewrite /D5 upd_ne; [| lnz].
        rewrite /D4 upd_ne; [exact HD3a2 | lnz]. }
      assert (HD6a3 : D6 !!! Regidx Ra3
                = sign_extend' 64 (mword_of_int (Z.of_nat offn) : mword 32)).
      { rewrite /D6 upd_ne; [| lnz]. rewrite /D5 upd_ne; [| lnz].
        rewrite /D4 upd_ne; [exact HD3a3 | lnz]. }
      assert (HD6a4 : D6 !!! Regidx Ra4
                = sign_extend' 64 (mword_of_int (Z.of_nat nn) : mword 32)).
      { rewrite /D6 upd_ne; [| lnz]. rewrite /D5 upd_ne; [| lnz].
        rewrite /D4 upd_ne; [exact HD3a4 | lnz]. }
      assert (HD6s2 : D6 !!! Regidx Rs2
                      = (mword_of_int (Z.of_nat nn) : mword 64)).
      { rewrite /D6 upd_ne; [| lnz]. rewrite /D5 upd_ne; [| lnz].
        rewrite /D4 upd_ne; [exact HD3s2 | lnz]. }
      assert (HD6get : forall r : mword 5, is_cs_idx r = true -> r <> Rs2 ->
                D6 !!! Regidx r = Ml !!! Regidx r).
      { intros r Hr Hne. rewrite /D6 upd_ne; [| lregne].
        rewrite /D5 upd_ne; [| lregne]. rewrite /D4 upd_ne; [| lregne].
        exact (HD3get r Hr Hne). }
      (* ---- the resources readi asks for ---- *)
      iDestruct "Hopen" as "(#Hslkk & Hslkd & Hdep & Hidev & Hiinum &
                             Hivalid & Hload & #Hity & Hfrz & Hkeep & Hru)".
      iDestruct (kxc_load_peel with "Hload") as
        (datl) "(%Hiok & %Hrl & %Hdok & %Hddix & %Hdoc & %Hduq & Hdlk & Hdiat & Hmeta
               & Hmap & Hblocks & Hdview & Hfview & Htop)".
      pose proof Hiok as Hiok'.
      destruct Hiok' as (Hbmwf & Hbmcov & Hdaddr & Hdty & Hszb & Hholes & Hsized).
      iDestruct (proc_priv_bare_acc gf (proc_addr jp) pidv V with "Hpriv")
        as "[Hppid Hpvbk]".
      iDestruct (A.kxa_bs3_split with "Hbs") as "[Hbs1 Hbs2]".
      iDestruct (sie_cap_gpr_dup_hw_config with "Hcg") as "[Hhwc Hcg]".
      iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
        "(_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
          #Hkmapb & _)".
      iDestruct (proc_pt_page_acc P (svpn_of vai) w0 Hum0 with "Hkmapb Hpt")
        as "[Hpage Hgive]".
      iDestruct (kxc_page_take (page_base (pte_ppn w0)) nn ltac:(lia)
                   with "Hpage") as (fpg) "[Hdst Hrest]".
      iEval (rewrite -HD6a2) in "Hdst".
      iDestruct (cpu_own_transport CIDd CIDd6 0%nat eb (proc_addr jp) eb
                   ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
      iDestruct (trap_csrs_ext_transport CIDd CIDd6 eb (proc_addr jp)
                   ltac:(try rewrite Hebb; wp_next_chain) with "Hextc") as "Hextc".
      iDestruct (cpu_claim_ext_transport CIDd CIDd6 eb (proc_addr jp)
                   ltac:(try rewrite Hebb; wp_next_chain) with "Hclmc") as "Hclmc".
      (* the byte view's row (durable-disk 1c-flip step 3) *)
      iPoseProof (log_ctx_bytes_any with "Hlogc") as "#Hrow".
      iDestruct (inode_map_q_1_to _ _ _ _ eq_refl with "Hmap") as "Hmap".
      iDestruct (inode_blocks_q_1_to _ _ _ _ eq_refl with "Hblocks") as "Hblocks".
      iApply (Readi.wp_readi_sconf KT0 gs jp gl gu gd gk pd pav pu bn ga gf
                logstart dev (ientry kf) bmf datl dnf false offn nn fpg V
                pidv (DfracOwn 1) (DfracOwn (1/2)) D6 (K - 68)%nat eb
                eb lks ltac:(lia) Hlg Hbmwf Hbmcov Hszb
                ltac:(rewrite HoffnZ; lia)
                ltac:(intros Hg; rewrite HoffnZ in Hg |- *;
                      pose proof Hszb as Hs; rewrite Hmb in Hs; lia)
                Hjp Hgs HD6a0
                ltac:(rewrite HD6a1; vm_compute; reflexivity) HD6a3 HD6a4
                with "Hcg Hcnt Hextc Hclmc Htext Hkd Hpc Hpenv Hbio Hrow Hka Hidev Hmeta Hmap
                      Hblocks [Hdst Hppid] Hprocs Hdevi Hdgeom Hdlock Hbs1").
      all: try lkbelow.
      { iSplitL "Hdst"; [iExact "Hdst" | iExact "Hppid"]. }
      iIntros (CIDrd Hsrd M2 tot P') "%Hcsrd %Hupt %Htotb %Hret Hcg Hcnt Hextc Hclmc Hpc
               Hidev Hmeta Hmap Hblocks [Hdst Hppid] Hbs1".
      iDestruct (inode_map_q_1_of _ _ _ _ eq_refl with "Hmap") as "Hmap".
      iDestruct (inode_blocks_q_1_of _ _ _ _ eq_refl with "Hblocks") as "Hblocks".
      assert (Hpcea : ret_pc (D6 !!! Regidx Rra) = mword_of_int (KXB + 0x0ea))
        by (rewrite HD6ra; lpcw).
      iEval (rewrite Hpcea) in "Hpc".
      iEval (rewrite HD6a2) in "Hdst".
      (* ---- put back everything readi borrowed ---- *)
      iDestruct ("Hpvbk" with "Hppid") as "Hpriv".
      iDestruct (kxc_page_give (page_base (pte_ppn w0)) nn fpg
                   (rd_delivered datl fpg offn tot) ltac:(lia)
                   with "Hdst Hrest") as "Hpage".
      iDestruct ("Hgive" with "Hpage") as "Hpt".
      iDestruct (kxc_load_seal gi logstart kf inumf dnf bmf datl
                   Hiok Hrl Hdok Hddix Hdoc Hduq
                   with "Hdlk Hdiat Hmeta Hmap Hblocks Hdview Hfview Htop") as "Hload".
      iDestruct (A.kxa_bs3_join with "Hbs1 Hbs2") as "Hbs".
      iDestruct (kxc_open_intro gi logstart dev pidv kf qf sf gyf
                   inumf dnf bmf gilf gislf
                   with "Hslkk Hslkd Hdep Hidev Hiinum Hivalid Hload
                         Hity Hfrz Hkeep Hru") as "Hopen".
      (* ---- the register facts on the far side of readi ---- *)
      assert (HM2s2 : M2 !!! Regidx Rs2
                      = (mword_of_int (Z.of_nat nn) : mword 64)).
      { rewrite (callee_saved_lookup Hcsrd Rs2 ltac:(vm_compute; reflexivity)).
        exact HD6s2. }
      assert (HM2get : forall r : mword 5, is_cs_idx r = true -> r <> Rs2 ->
                M2 !!! Regidx r = Ml !!! Regidx r).
      { intros r Hr Hne. rewrite (callee_saved_lookup Hcsrd r Hr).
        exact (HD6get r Hr Hne). }
      assert (HM2a0 : M2 !!! Regidx Ra0
                      = (mword_of_int (Z.of_nat tot) : mword 64)).
      { destruct Hret as [(_ & Hbad) | (Hv & _)]; [discriminate Hbad | exact Hv]. }
      assert (Htoteq : tot = rd_clamp (di_size dnf) offn nn).
      { destruct Hret as [(_ & Hbad) | (_ & Hv)]; [discriminate Hbad | exact Hv]. }
      (* ---- +0x0ea: bne s2,a0,+0x324 -- the short read goes to [bad:] ---- *)
      assert (Hszn : (Z.of_nat (Z.to_nat (bv_unsigned (di_size dnf)))
                      <= 274432)%Z).
      { pose proof (bv_unsigned_in_range 32 (di_size dnf)) as [Hsz0 _].
        rewrite Z2Nat.id; [| exact Hsz0]. rewrite -Hmb. exact Hszb. }
      assert (Htotle : (Z.of_nat tot <= 274432)%Z).
      { rewrite /rd_clamp in Htotb.
        destruct (decide (Z.to_nat (bv_unsigned (di_size dnf))
                          < offn + nn)%nat); lia. }
      assert (Hcmpe : neq_vec (rget M2 Rs2) (rget M2 Ra0)
                      = negb (Z.eqb (Z.of_nat nn) (Z.of_nat tot))).
      { rewrite (rget_ne M2 Rs2 ltac:(lnz)) (rget_ne M2 Ra0 ltac:(lnz))
                HM2s2 HM2a0.
        apply w32_neq_moi; change (2 ^ 64)%Z with 18446744073709551616%Z; lia. }
      assert (Htgt31e : add_vec (mword_of_int (KXB + 0x0ea) : mword 64)
                          (sign_extend' 64 (mword_of_int 564 : mword 13))
                        = mword_of_int (KXB + 0x31e)) by lpcw.
      destruct (decide (nn = tot)) as [Hntot | Hntot].
      + (* the full count arrived: the segment page is loaded *)
        iApply (wp_bne_fall_s_sconf (mword_of_int (KXB + 0x0ea))
                  (mword_of_int 564 : mword 13) Ra0 Rs2 M2 (K - 68)%nat eb
                  ltac:(lnz) ltac:(lnz)
                  ltac:(rewrite Hcmpe Hntot Z.eqb_refl; reflexivity)
                  with "Hcg Hpc []").
        { iApply (kxc_0ea with "Htext"). }
        iIntros (CIDe1 Hse1) "Hcg Hpc".
        assert (Hppee : add_vec_int (mword_of_int (KXB + 0x0ea) : mword 64) 4
                        = mword_of_int (KXB + 0x0ee)) by lpcw.
        iEval (rewrite Hppee) in "Hpc".
        (* THE OFFSET IS INSIDE THE FILE, and that is where the fuel comes
           from: [rd_clamp] hands back the full [nn >= 1] only when
           [off + nn <= size], and [size <= MAXFILE*BSIZE]. *)
        assert (Hoffsz : (Z.of_nat offn + Z.of_nat nn
                  <= Z.of_nat (Z.to_nat (bv_unsigned (di_size dnf))))%Z).
        { rewrite /rd_clamp in Htoteq.
          destruct (decide (Z.to_nat (bv_unsigned (di_size dnf))
                            < offn + nn)%nat) as [Hlt | Hge]; lia. }
        assert (Hoffb : (offz + 4096 < 2 ^ 32)%Z).
        { rewrite -HoffnZ. change (2 ^ 32)%Z with 4294967296%Z. lia. }
        (* ---- +0x0ee: addw s1,s5,s1 -- i += PGSIZE ---- *)
        assert (HM2s5 : M2 !!! Regidx Rs5 = (mword_of_int 4096 : mword 64))
          by (rewrite (HM2get Rs5 ltac:(vm_compute; reflexivity) ltac:(lnz));
              exact HMs5).
        assert (HM2s1 : M2 !!! Regidx Rs1
                        = sign_extend' 64 (mword_of_int ii : mword 32))
          by (rewrite (HM2get Rs1 ltac:(vm_compute; reflexivity) ltac:(lnz));
              exact HMs1).
        iApply (wp_addw4_s_sconf (mword_of_int (KXB + 0x0ee)) Rs1 Rs5 Rs1
                  M2 (K - 68)%nat eb ltac:(lnz) ltac:(rdok)
                  with "Hcg Hpc []").
        { iApply (kxc_0ee with "Htext"). }
        iIntros (CIDe2 Hse2) "Hcg Hpc". iEval (rgne) in "Hcg".
        iEval (rgne) in "Hcg".
        set (ii' := ((ii + 4096) `mod` 2 ^ 32)%Z).
        assert (Hii'r : (0 <= ii' < 2 ^ 32)%Z)
          by (rewrite /ii'; apply Z.mod_pos_bound; lia).
        set (E1 := <[Regidx Rs1 := regval_into_reg
                      (sign_extend' 64 (add_vec
                         (subrange_vec_dec (M2 !!! Regidx Rs5) 31 0 : mword 32)
                         (subrange_vec_dec (M2 !!! Regidx Rs1) 31 0
                          : mword 32)))]> M2).
        assert (HE1s1 : E1 !!! Regidx Rs1
                        = sign_extend' 64 (mword_of_int ii' : mword 32)).
        { rewrite /E1 upd_eq HM2s5 HM2s1
                  (w32_moi_arg 4096 ltac:(change (2 ^ 31)%Z with 2147483648%Z;
                                          lia))
                  w32_addw_arg2 /ii' (Z.add_comm ii 4096)
                  (w32_arg_mod (4096 + ii)). reflexivity. }
        assert (HE1s3 : E1 !!! Regidx Rs3
                        = sign_extend' 64 (mword_of_int fz : mword 32)).
        { rewrite /E1 upd_ne; [| lnz].
          rewrite (HM2get Rs3 ltac:(vm_compute; reflexivity) ltac:(lnz)).
          exact HMs3. }
        assert (HE1get : forall r : mword 5, is_cs_idx r = true ->
                  r <> Rs2 -> r <> Rs1 ->
                  E1 !!! Regidx r = Ml !!! Regidx r).
        { intros r Hr H2 H1. rewrite /E1 upd_ne; [| lregne].
          exact (HM2get r Hr H2). }
        assert (Hppf2 : add_vec_int (mword_of_int (KXB + 0x0ee) : mword 64) 4
                        = mword_of_int (KXB + 0x0f2)) by lpcw.
        iEval (rewrite Hppf2) in "Hpc".
        (* ---- +0x0f2: bgeu s1,s3,+0x116 ---- *)
        assert (Hcmpf : zopz0zKzJ_u (rget E1 Rs1) (rget E1 Rs3)
                        = Z.geb (w32_uarg ii') (w32_uarg fz)).
        { rewrite (rget_ne E1 Rs1 ltac:(lnz)) (rget_ne E1 Rs3 ltac:(lnz))
                  HE1s1 HE1s3.
          apply w32_bgeu_arg; [exact Hii'r | exact Hfzr]. }
        assert (Htgt116 : add_vec (mword_of_int (KXB + 0x0f2) : mword 64)
                            (sign_extend' 64 (mword_of_int 36 : mword 13))
                          = mword_of_int (KXB + 0x116)) by lpcw.
        destruct (Z.geb (w32_uarg ii') (w32_uarg fz)) eqn:Egf.
        * (* the whole segment is in: leave for +0x116 *)
          iApply (wp_bgeu_taken_s_sconf (mword_of_int (KXB + 0x0f2))
                    (mword_of_int 36 : mword 13) Rs3 Rs1 E1 (K - 68)%nat eb
                    ltac:(lnz) ltac:(lnz) ltac:(exact Hcmpf)
                    ltac:(rewrite Htgt116; vm_compute; reflexivity)
                    with "Hcg Hpc []").
          { iApply (kxc_0f2 with "Htext"). }
          iIntros (CIDx1 Hsx1). iNext. iIntros "Hcg Hpc".
          iEval (rewrite Htgt116) in "Hpc".
          iDestruct (cpu_own_transport CIDrd CIDx1 0%nat eb (proc_addr jp)
                       eb ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
          iDestruct (trap_csrs_ext_transport CIDrd CIDx1 eb (proc_addr jp)
                       ltac:(try rewrite Hebb; wp_next_chain) with "Hextc") as "Hextc".
          iDestruct (cpu_claim_ext_transport CIDrd CIDx1 eb (proc_addr jp)
                       ltac:(try rewrite Hebb; wp_next_chain) with "Hclmc") as "Hclmc".
          iSpecialize ("Hc116" $! CIDx1 with "[%]"); [wp_next_chain |].
          iApply ("Hc116" $! E1 with "[%] Hcg Hcnt Hextc Hclmc Hpc [Hopen Hlog Hirs Hbm Hins
                    Hbits Hbs Hpt Hpriv Hpath Hargv Hargs Helf Hframe] [Hcont]").
          { split_and!.
            - rewrite (HE1get csp_rs1 ltac:(vm_compute; reflexivity)
                         ltac:(lnz) ltac:(lnz)). exact HMsp.
            - rewrite (HE1get Rs0 ltac:(vm_compute; reflexivity)
                         ltac:(lnz) ltac:(lnz)). exact HMs0.
            - rewrite (HE1get Rs4 ltac:(vm_compute; reflexivity)
                         ltac:(lnz) ltac:(lnz)). exact HMs4.
            - rewrite (HE1get Rs5 ltac:(vm_compute; reflexivity)
                         ltac:(lnz) ltac:(lnz)). exact HMs5.
            - rewrite (HE1get Rs6 ltac:(vm_compute; reflexivity)
                         ltac:(lnz) ltac:(lnz)). exact HMs6.
            - rewrite (HE1get Rs9 ltac:(vm_compute; reflexivity)
                         ltac:(lnz) ltac:(lnz)). exact HMs9.
            - rewrite (HE1get Rs10 ltac:(vm_compute; reflexivity)
                         ltac:(lnz) ltac:(lnz)). exact HMs10.
            - rewrite (HE1get Rs11 ltac:(vm_compute; reflexivity)
                         ltac:(lnz) ltac:(lnz)). exact HMs11. }
          { rewrite /kxc_res.
            iSplitL "Hopen"; [iExact "Hopen" |].
            iSplitL "Hlog"; [iExact "Hlog" |]. iSplitL "Hirs"; [iExact "Hirs" |].
            iSplitL "Hbm"; [iExact "Hbm" |]. iSplitL "Hins"; [iExact "Hins" |].
            iSplitL "Hbits"; [iExact "Hbits" |].
            iSplitL "Hbs"; [iExact "Hbs" |]. iSplitL "Hpt"; [iExact "Hpt" |].
            iSplitL "Hpriv"; [iExact "Hpriv" |].
            iSplitL "Hpath"; [iExact "Hpath" |].
            iSplitL "Hargv"; [iExact "Hargv" |].
            iSplitL "Hargs"; [iExact "Hargs" |].
            iSplitL "Helf"; [iExact "Helf" | iExact "Hframe"]. }
          { assert (Hcr2 : true = false \/ proc_addr jp = zero_reg ->
                      (CIDx1 : CPU) = (CID0 : CPU)) by wp_next_chain.
            iApply (wp_next_retarget CID0 CIDx1 true (proc_addr jp) _ Hcr2
                      with "Hcont"). }
        * (* another page: the back edge to +0x0f6 *)
          iApply (wp_bgeu_fall_s_sconf (mword_of_int (KXB + 0x0f2))
                    (mword_of_int 36 : mword 13) Rs3 Rs1 E1 (K - 68)%nat eb
                    ltac:(lnz) ltac:(lnz) ltac:(exact Hcmpf)
                    with "Hcg Hpc []").
          { iApply (kxc_0f2 with "Htext"). }
          iIntros (CIDx2 Hsx2) "Hcg Hpc".
          assert (Hppf6 : add_vec_int (mword_of_int (KXB + 0x0f2) : mword 64) 4
                          = mword_of_int (KXB + 0x0f6)) by lpcw.
          iEval (rewrite Hppf6) in "Hpc".
          iDestruct (cpu_own_transport CIDrd CIDx2 0%nat eb (proc_addr jp)
                       eb ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
          iDestruct (trap_csrs_ext_transport CIDrd CIDx2 eb (proc_addr jp)
                       ltac:(try rewrite Hebb; wp_next_chain) with "Hextc") as "Hextc".
          iDestruct (cpu_claim_ext_transport CIDrd CIDx2 eb (proc_addr jp)
                       ltac:(try rewrite Hebb; wp_next_chain) with "Hclmc") as "Hclmc".
          assert (Hcr2 : true = false \/ proc_addr jp = zero_reg ->
                    (CIDx2 : CPU) = (CID0 : CPU)) by wp_next_chain.
          iDestruct (wp_next_retarget CID0 CIDx2 true (proc_addr jp) _ Hcr2
                       with "Hcont") as "Hcont".
          iDestruct (wp_next_retarget CID0 CIDx2 true (proc_addr jp) _ Hcr2
                       with "Hc116") as "Hc116".
          (* THE FUEL DECREASES: the offset advanced by a whole page and,
             because readi delivered the full count, it had not passed the
             end of the file, so nothing wrapped. *)
          assert (Hoff' : ((po + ii') `mod` 2 ^ 32 = offz + 4096)%Z).
          { rewrite /ii' /offz.
            rewrite Zplus_mod_idemp_r.
            replace (po + (ii + 4096))%Z with ((po + ii) + 4096)%Z by lia.
            rewrite <- Zplus_mod_idemp_l.
            apply Z.mod_small. lia. }
          assert (Hguard' : (w32_uarg ii' < w32_uarg fz)%Z).
          { rewrite Z.geb_leb in Egf. apply Z.leb_gt in Egf. lia. }
          iApply (IH CIDx2 E1 ii' Hii'r ltac:(rewrite Hoff'; lia) Hguard'
                    ltac:(rewrite (HE1get csp_rs1 ltac:(vm_compute; reflexivity)
                                    ltac:(lnz) ltac:(lnz)); exact HMsp)
                    ltac:(rewrite (HE1get Rs0 ltac:(vm_compute; reflexivity)
                                    ltac:(lnz) ltac:(lnz)); exact HMs0)
                    HE1s1 HE1s3
                    ltac:(rewrite (HE1get Rs4 ltac:(vm_compute; reflexivity)
                                    ltac:(lnz) ltac:(lnz)); exact HMs4)
                    ltac:(rewrite (HE1get Rs5 ltac:(vm_compute; reflexivity)
                                    ltac:(lnz) ltac:(lnz)); exact HMs5)
                    ltac:(rewrite (HE1get Rs6 ltac:(vm_compute; reflexivity)
                                    ltac:(lnz) ltac:(lnz)); exact HMs6)
                    ltac:(rewrite (HE1get Rs7 ltac:(vm_compute; reflexivity)
                                    ltac:(lnz) ltac:(lnz)); exact HMs7)
                    ltac:(rewrite (HE1get Rs8 ltac:(vm_compute; reflexivity)
                                    ltac:(lnz) ltac:(lnz)); exact HMs8)
                    ltac:(rewrite (HE1get Rs9 ltac:(vm_compute; reflexivity)
                                    ltac:(lnz) ltac:(lnz)); exact HMs9)
                    ltac:(rewrite (HE1get Rs10 ltac:(vm_compute; reflexivity)
                                    ltac:(lnz) ltac:(lnz)); exact HMs10)
                    ltac:(rewrite (HE1get Rs11 ltac:(vm_compute; reflexivity)
                                    ltac:(lnz) ltac:(lnz)); exact HMs11)
                    with "Hcg Hcnt Hextc Hclmc Htext Hpc [] Hka
                          [Hopen Hlog Hirs Hbm Hins Hbits Hbs Hpt Hpriv Hpath
                           Hargv Hargs Helf Hframe] Hcont Hc116").
          { iApply (A.fs_fabric_mk with "[%] Hkd Hpenv Hbio Hlogc Hcrash Hcert Hitab Hitinv
                                         Hesc Hslks Hireg Hropen Hprocs Hdevi Hdgeom
                                         Hdlock"). exact Hclogf. }
          { rewrite /kxc_res.
            iSplitL "Hopen"; [iExact "Hopen" |].
            iSplitL "Hlog"; [iExact "Hlog" |]. iSplitL "Hirs"; [iExact "Hirs" |].
            iSplitL "Hbm"; [iExact "Hbm" |]. iSplitL "Hins"; [iExact "Hins" |].
            iSplitL "Hbits"; [iExact "Hbits" |].
            iSplitL "Hbs"; [iExact "Hbs" |]. iSplitL "Hpt"; [iExact "Hpt" |].
            iSplitL "Hpriv"; [iExact "Hpriv" |].
            iSplitL "Hpath"; [iExact "Hpath" |].
            iSplitL "Hargv"; [iExact "Hargv" |].
            iSplitL "Hargs"; [iExact "Hargs" |].
            iSplitL "Helf"; [iExact "Helf" | iExact "Hframe"]. }
      + (* SHORT READ -- the malformed executable's [bad:] exit at +0x324 *)
        iApply (wp_bne_taken_s_sconf (mword_of_int (KXB + 0x0ea))
                  (mword_of_int 564 : mword 13) Ra0 Rs2 M2 (K - 68)%nat eb
                  ltac:(lnz) ltac:(lnz)
                  ltac:(rewrite Hcmpe;
                        replace (Z.eqb (Z.of_nat nn) (Z.of_nat tot)) with false;
                        [reflexivity | symmetry; apply Z.eqb_neq; lia])
                  ltac:(rewrite Htgt31e; vm_compute; reflexivity)
                  with "Hcg Hpc []").
        { iApply (kxc_0ea with "Htext"). }
        iIntros (CIDb1 Hsb1). iNext. iIntros "Hcg Hpc".
        iEval (rewrite Htgt31e) in "Hpc".
        iDestruct (cpu_own_transport CIDrd CIDb1 0%nat eb (proc_addr jp)
                     eb ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
        iDestruct (trap_csrs_ext_transport CIDrd CIDb1 eb (proc_addr jp)
                     ltac:(try rewrite Hebb; wp_next_chain) with "Hextc") as "Hextc".
        iDestruct (cpu_claim_ext_transport CIDrd CIDb1 eb (proc_addr jp)
                     ltac:(try rewrite Hebb; wp_next_chain) with "Hclmc") as "Hclmc".
        assert (Hcr3 : true = false \/ proc_addr jp = zero_reg ->
                  (CIDb1 : CPU) = (CID0 : CPU)) by wp_next_chain.
        iDestruct (wp_next_retarget CID0 CIDb1 true (proc_addr jp) _ Hcr3
                     with "Hcont") as "Hcont".
        iApply (kxc_bad324 (CID0 := CIDb1) Q gs jp gl gu gd gk pd pav pu bn g
                  gi gtl gilf gislf ga gf logstart bmapstart inodestart
                  nib size dev kf qf sf gyf inumf dnf bmf n2 plen
                  pfun na avf alen aslen afun pidv V dqb dqs dqa dqpv dqas m M2 K
                  sp0 ra0 s00 s10 s20 pv av w63 w67 ef P w65 eb lks
                  HK Hk Hlg Hsz Hbm0 Hbmc Hbml Hins0 Hcovb Hiregb Hib Hn2 Hjp
                  Hgs Hsp Hra Hs0 Hs1 Hs2
                  ltac:(rewrite (HM2get csp_rs1 ltac:(vm_compute; reflexivity)
                                  ltac:(lnz)); exact HMsp)
                  ltac:(rewrite (HM2get Rs0 ltac:(vm_compute; reflexivity)
                                  ltac:(lnz)); exact HMs0)
                  ltac:(rewrite (HM2get Rs4 ltac:(vm_compute; reflexivity)
                                  ltac:(lnz)); exact HMs4)
                  ltac:(rewrite (HM2get Rs6 ltac:(vm_compute; reflexivity)
                                  ltac:(lnz)); exact HMs6)
                  Hal Hbelow Hcovp
                  with "Hcg Hcnt Hextc Hclmc Htext Hpc [] Hopen Hbm Hins Hbits Hka
                        Hpt Hpriv Hpath Hargv Hargs Helf Hbs Hirs Hlog Hframe
                        Hcont").
        { iApply (A.fs_fabric_mk with "[%] Hkd Hpenv Hbio Hlogc Hcrash Hcert Hitab Hitinv
                                       Hesc Hslks Hireg Hropen Hprocs Hdevi Hdgeom
                                       Hdlock"). exact Hclogf. } }

    (* ---- +0x10e: bgeu s9,a5,+0x0da ---- *)
    assert (Hcmp : zopz0zKzJ_u (rget N9 Rs9) (rget N9 Ra5)
                   = Z.geb 4096 (w32_uarg dz)).
    { rewrite (rget_ne N9 Rs9 ltac:(lnz)) (rget_ne N9 Ra5 ltac:(lnz))
              HN9s9 HN9a5.
      apply w32_bgeu_lit_arg; [ change (2 ^ 31)%Z with 2147483648%Z; lia
                              | exact Hdzr ]. }
    assert (Htgt0da : add_vec (mword_of_int (KXB + 0x10e) : mword 64)
                        (sign_extend' 64 (mword_of_int 8140 : mword 13))
                      = mword_of_int (KXB + 0x0da)) by lpcw.
    destruct (Z.geb 4096 (w32_uarg dz)) eqn:Egeu.
    - (* n = filesz - i, and the difference is small *)
      assert (Hdzle : (dz <= 4096)%Z).
      { apply Z.geb_le in Egeu. pose proof (w32_uarg_lb dz). lia. }
      iApply (wp_bgeu_taken_s_sconf (mword_of_int (KXB + 0x10e))
                (mword_of_int 8140 : mword 13) Ra5 Rs9 N9 (K - 68)%nat eb
                ltac:(lnz) ltac:(lnz) ltac:(exact Hcmp)
                ltac:(rewrite Htgt0da; vm_compute; reflexivity)
                with "Hcg Hpc []").
      { iApply (kxc_10e with "Htext"). }
      iIntros (CIDt1 Hst1). iNext. iIntros "Hcg Hpc".
      iEval (rewrite Htgt0da) in "Hpc".
      iDestruct (cpu_own_transport CID0 CIDt1 0%nat eb (proc_addr jp) eb
                   ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
      iDestruct (trap_csrs_ext_transport CID0 CIDt1 eb (proc_addr jp)
                   ltac:(try rewrite Hebb; wp_next_chain) with "Hextc") as "Hextc".
      iDestruct (cpu_claim_ext_transport CID0 CIDt1 eb (proc_addr jp)
                   ltac:(try rewrite Hebb; wp_next_chain) with "Hclmc") as "Hclmc".
      iApply ("AT0DA" $! CIDt1 N9 (Z.to_nat dz) with "[%] [%] Hcg Hcnt Hextc Hclmc Hpc").
      + wp_next_chain.
      + split_and!.
        * lia.
        * lia.
        * rewrite HN9s2 Z2Nat.id; [| lia].
          apply w32_sext_moi. change (2 ^ 31)%Z with 2147483648%Z. lia.
        * exact HN9a2.
        * exact HN9get.
    - (* n = PGSIZE *)
      assert (Hdzgt : (4096 < dz)%Z).
      { assert (Hgu : (4096 < w32_uarg dz)%Z).
        { rewrite Z.geb_leb in Egeu. apply Z.leb_gt in Egeu. exact Egeu. }
        destruct (Z_le_gt_dec dz 4096) as [Hle | Hgt]; [| lia].
        exfalso. pose proof (w32_uarg_le dz 4096
                               ltac:(change (2 ^ 31)%Z with 2147483648%Z; lia)
                               Hle). lia. }
      iApply (wp_bgeu_fall_s_sconf (mword_of_int (KXB + 0x10e))
                (mword_of_int 8140 : mword 13) Ra5 Rs9 N9 (K - 68)%nat eb
                ltac:(lnz) ltac:(lnz) ltac:(exact Hcmp)
                with "Hcg Hpc []").
      { iApply (kxc_10e with "Htext"). }
      iIntros (CIDf1 Hsf1) "Hcg Hpc".
      assert (Hpp112 : add_vec_int (mword_of_int (KXB + 0x10e) : mword 64) 4
                       = mword_of_int (KXB + 0x112)) by lpcw.
      iEval (rewrite Hpp112) in "Hpc".
      (* +0x112: c.mv s2,s5 *)
      iApply (wp_cmv_s_sconf (mword_of_int (KXB + 0x112)) Rs2 Rs5
                N9 (K - 68)%nat eb ltac:(lnz) ltac:(rdok)
                with "Hcg Hpc []").
      { iApply (kxc_112 with "Htext"). }
      iIntros (CIDf2 Hsf2) "Hcg Hpc". iEval (rgne) in "Hcg".
      set (Nf := <[Regidx Rs2 := regval_into_reg
                    (add_vec zero_reg (N9 !!! Regidx Rs5))]> N9).
      assert (HNfs2 : Nf !!! Regidx Rs2 = (mword_of_int 4096 : mword 64)).
      { rewrite /Nf upd_eq HN9s5 w32_zero_add. reflexivity. }
      assert (HNfa2 : Nf !!! Regidx Ra2 = page_base (pte_ppn w0))
        by (rewrite /Nf upd_ne; [exact HN9a2 | lnz]).
      assert (HNfget : forall r : mword 5, is_cs_idx r = true -> r <> Rs2 ->
                Nf !!! Regidx r = Ml !!! Regidx r).
      { intros r Hr Hne. rewrite /Nf upd_ne; [| lregne].
        exact (HN9get r Hr Hne). }
      assert (Hpp114 : add_vec_int (mword_of_int (KXB + 0x112) : mword 64) 2
                       = mword_of_int (KXB + 0x114)) by lpcw.
      iEval (rewrite Hpp114) in "Hpc".
      (* +0x114: c.j +0x0da *)
      assert (Htgtj : add_vec (mword_of_int (KXB + 0x114) : mword 64)
                (sign_extend' 64
                   (sign_extend' 21 (concat_vec (mword_of_int 2019 : mword 11)
                                                ('b"0"))))
              = mword_of_int (KXB + 0x0da)) by lpcw.
      iApply (wp_cj_s_sconf (mword_of_int (KXB + 0x114))
                (sign_extend' 21 (concat_vec (mword_of_int 2019 : mword 11)
                                             ('b"0")))
                Nf (K - 68)%nat eb
                ltac:(rewrite Htgtj; vm_compute; reflexivity)
                with "Hcg Hpc []").
      { iApply (kxc_114 with "Htext"). }
      iIntros (CIDf3 Hsf3). iNext. iIntros "Hcg Hpc".
      iEval (rewrite Htgtj) in "Hpc".
      iDestruct (cpu_own_transport CID0 CIDf3 0%nat eb (proc_addr jp) eb
                   ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
      iDestruct (trap_csrs_ext_transport CID0 CIDf3 eb (proc_addr jp)
                   ltac:(try rewrite Hebb; wp_next_chain) with "Hextc") as "Hextc".
      iDestruct (cpu_claim_ext_transport CID0 CIDf3 eb (proc_addr jp)
                   ltac:(try rewrite Hebb; wp_next_chain) with "Hclmc") as "Hclmc".
      iApply ("AT0DA" $! CIDf3 Nf 4096%nat with "[%] [%] Hcg Hcnt Hextc Hclmc Hpc").
      + wp_next_chain.
      + split_and!.
        * lia.
        * lia.
        * rewrite HNfs2; f_equal; vm_compute; reflexivity.
        * exact HNfa2.
        * exact HNfget.
  Qed.

End KexecB2Loops.

End KexecB2Proof.
