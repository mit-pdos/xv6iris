(* ProofKexecB.v -- PHASE B of kexec, FIRST CHUNK: [kexec+0x090] ..
   [kexec+0x0cc] -- proc_pagetable, the seven remaining lazy register spills,
   the [elf.phnum] test and the phdr loop's SETUP -- plus the one [bad:] tail
   that stretch owns, at +0x31c.

     +0x090  sd   s6,480(sp)         the LAZY spill of s6 -> slot 8
     +0x092  mv   a0,s1              a0 = p
     +0x094  jal  proc_pagetable     -> a0 = the NEW table root, or 0
     +0x098  mv   s6,a0
     +0x09a  beqz a0, +0x31c         failed -> the tail below
     +0x09e  sd   s3,504(sp)   } the seven remaining LAZY spills:
     +0x0a0  sd   s5,488(sp)   }   slots 5,7,9,10,11,12,13
     +0x0a2  sd   s7,472(sp)   }   = s3,s5,s7,s8,s9,s10,s11
     +0x0a4  sd   s8,464(sp)   }
     +0x0a6  sd   s9,456(sp)   }
     +0x0a8  sd   s10,448(sp)  }
     +0x0aa  sd   s11,440(sp)  }
     +0x0ac  lhu  a5,-376(s0)        elf.phnum   (slot 47, in the elf carve)
     +0x0b0  beqz a5, +0x1a2         no program headers at all
     +0x0b4  lw   a3,-400(s0)        elf.phoff (slot 50, LOW SIGNED WORD)
     +0x0b8  li   s2,0               sz  = 0
     +0x0ba  li   s10,0              i   = 0
     +0x0bc  li   s11,56             sizeof(struct proghdr)
     +0x0c0  lui  s9,0x1             s9  = 4096
     +0x0c2  addi a5,s9,-1           a5  = 0xfff
     +0x0c6  sd   a5,-536(s0)        the PGSIZE-1 mask -> slot 67
     +0x0ca  lui  s5,0x1             s5  = 4096
     +0x0cc  j    +0x12c             into the phdr loop BODY

     [+0x31c tail:]  ld s6,480(sp) ; j +0x64   -- and +0x064 is phase A's
     already-proven [ProofKexecA.KexecAProof.kxc_bad64].  It restores ONLY
     s6 because at that point s6 is the only one of s3..s11 this stretch has
     spilled: the [beqz] at +0x9a is BEFORE the other seven spills.  That is
     the lazy-spill hazard of claude-notes/projects/kexec.md, and it is why
     [kxc_frameA6] takes slots 5,7..13 existentially -- the tail hands the
     frame back in exactly the shape it received it.

   ---- WHAT IS PROVEN HERE ----------------------------------------------

   [kxc_b1]: the stretch above, with THREE continuation premises --
   kexec's own [-1] exit (which the +0x31c tail discharges), the [+0x1a2]
   fall-out (phnum = 0, skip the loop) and the [+0x12c] fall-through (the
   phdr loop's body entry).  Convention 3 of projects/kexec.md: a block owns
   every exit that reaches the epilogue and its only OUTPUTS are its
   fall-throughs.  No [admit] / [Admitted] / [Axiom].

   NOT here: the phdr loop and the inlined loadseg (the next chunk), which
   consume [kxc_at_12c] below.

   ---- proc_pagetable IS CALLED AT THE UNCOUNTED CONTRACT ----------------

   kexec runs at [kalloc_env ga None] (uvmalloc and proc_freepagetable both
   require it), so [SpecProcPagetable.PROC_PAGETABLE]'s counted premise
   ([on = Some nb] with [K_proc_pagetable < nb]) is unpayable.  The general
   [PROC_PAGETABLE_GEN] / [wp_proc_pagetable_core] is what applies: its post
   is the [ppt_post] DISJUNCTION at an ARBITRARY [on], including [None].
   kexec is precisely the caller that can use it, because it TESTS the result
   against 0 ([beqz a0] at +0x9a) and has a live [bad:] arm for the failure
   -- [ppt_post]'s failure arm hands back [rv = 0] and [kalloc_env ga None],
   which is the +0x31c tail.  Its success arm joins the [proc_pt] tier with
   [ProcPtOwn.proc_pt_intro_ppt]; the [page_valid (page_base tfp)] that lemma
   asks for is a PROJECTION of the process's own block
   ([ProofKforkParts.proc_priv_tfp_valid]), not a premise on the caller.

   proc_pagetable's only precondition on the process is the [p_trapframe]
   cell at any fraction, which [ProcInv.proc_priv_trapframe] lends at 1/4 and
   takes back -- so [proc_priv] travels WHOLE across this block (convention 2).

   ---- THE TWO OUTPUT STATES ---------------------------------------------

   [kxc_at_1a2] and [kxc_at_12c] are named [iProp]s in ProofKexecSeam.v, and
   that is where their shape is documented -- the elf buffer travelling
   NAMED rather than as existential [stack_own], [kxc_off]'s [int]
   truncation, and the coverage half of the loop invariant.  They live in
   their own file so that phase B2, which consumes them, does not have to
   wait for this one to compile; the same reason ProofKexecTail.v exists.

   ---- CONVENTIONS FOLLOWED (projects/kexec.md) --------------------------

   1. Every statement is relative to its OWN entry map, never to kexec's [m];
      what relates them is the threading conjunct over the callee-saved
      registers this stretch has not written.
   2. [proc_priv] travels whole.
   4. [b = eb = true] is pinned FIRST, with [ProofKexecA.kxc_sie_b_agree].
   5. [stack_own] is the seam currency; the elf buffer is carved at the one
      place it is read and (here) kept named because the loop needs it. *)
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
Require Import CalleeSaved.
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
Require Import FsCrash.
Require Import InodeRegion.
Require Import IcacheEscrow.
Require Import ElfEnc.
Require Import PageGeom.
Require Import ProcGeom.
Require Import ProcInv.
Require Import DiskPtsto.
Require Import BioDefs.
Require Import FsBlocks LogInv.
Require Import BitmapInv.
Require Import InodeInv.
Require Import IrefSlots.
Require Import IcacheRef.
Require Import IcacheInv.
Require Import KallocInv.
Require Import KvmSpec.
Require Import FileInvDefs.
Require Import DinodeEnc.
Require Import ProcInv.
Require Import PtreeType.
Require Import UserPtTree.
Require Import ProcPtOwn.
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
Require Import SpecProcPagetable.
Require Import ProofKexecTail.
Require Import ProofKexecSeam.
Require Import ProofKforkParts.
Require Import CodeKexec.
From Kernel Require KernelSyms.
Require Import ProcAvail.
Local Open Scope Z_scope.

(* A syscall-altitude goal carries [ProcInv.tf_page]'s 4096-conjunct big-op;
   printing one takes tens of minutes, so a one-line mistake reads as a hang.
   durable-notes.md's rule. *)
Set Printing Depth 40.

Notation KXB := KernelSyms.kexec (only parsing).


(* ===================================================================== *)
(*  THE PROOF.                                                            *)
(* ===================================================================== *)
(* [Iunlockput] and [EndOp] are used only through the +0x064 tail
   [kxc_bad64], so all seven of that functor's arguments have to be supplied
   here.  The tail lives in ProofKexecTail.v rather than in ProofKexecA.v so
   that phase B does not have to wait for phase A to compile; see that file's
   header. *)
Module KexecBProof (Myproc : MYPROC) (BeginOp : BEGIN_OP) (Namei : NAMEI)
                   (Ilock : ILOCK) (Readi : READI) (Iunlockput : IUNLOCKPUT)
                   (EndOp : END_OP) (PPT : PROC_PAGETABLE_GEN).

Module A := ProofKexecTail.KexecTailProof Myproc BeginOp Namei Ilock Readi
                                          Iunlockput EndOp.

Section KexecBBody.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !fileG Σ, !kallocG Σ,
            !bioG Σ, !diskGhostG Σ, !uartGhostG Σ, !fsLogG Σ, !logG Σ,
            !fsCrashG Σ, !irefslotG Σ, !pavG Σ, !iregG Σ}.
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

  Local Ltac regne := reg_ne_side.
  Local Ltac pcw := apply bv_eq; vm_compute; reflexivity.
  Local Ltac nz := vm_compute; discriminate.

  (* =================================================================== *)
  (*  +0x090 .. +0x0cc, PLUS the [bad:] tail at +0x31c.                   *)
  (* =================================================================== *)
  Lemma kxc_b1
      (gs : list gname) (jp : nat) (gl : gname)
      (gu : uart_names) (gd : disk_names) (gk : gname)
      (pd pav pu : mword 64)
      (bn : bio_names)
      (g : log_names) (gfs : fs_names) (gi : gname)
      (cn : ic_names) (gtl : gname)
      (ga : gname) (gf : gname)
      (cov : gset Z) (logstart bmapstart inodestart : Z) (nib : nat)
      (size : Z) (dev : mword 32)
      (used used2 : gset Z)
      (kf : nat) (qf sf : Qp) (gyf : gname) (inumf : mword 32)
      (dnf : dinode) (bmf : blkmap)
      (gilf gislf : gname) (n2 : nat)
      (plen : nat) (pfun : nat -> bv 8)
      (na : nat) (avf : nat -> mword 64)
      (alen : nat -> nat) (aslen : nat -> nat)
      (afun : nat -> nat -> bv 8)
      (pidv : mword 32) (V : pprivate)
      (dqb dqs dqa : dfrac)
      (m M90 : regfile) (K : nat) (eb : bool) (b : bool)
      (lks : gset string)
      (sp0 ra0 s00 s10 s20 pv av : mword 64) :
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
    eb = true ->
    used2 ⊆ used ->
    (kf < NINODE)%nat ->
    bv_unsigned inumf < 16 * Z.of_nat nib ->
    (iput_units <= n2)%nat ->
    m !!! Regidx csp_rs1 = sp0 ->
    m !!! Regidx Rra = ra0 ->
    m !!! Regidx Rs0 = s00 ->
    m !!! Regidx Rs1 = s10 ->
    m !!! Regidx Rs2 = s20 ->
    (* ---- the register state at [pc_is (kexec + 0x90)], phase A's output ---- *)
    M90 !!! Regidx csp_rs1 = pa_stk sp0 68 ->
    M90 !!! Regidx Rs0 = sp0 ->
    M90 !!! Regidx Rs1 = proc_addr jp ->
    M90 !!! Regidx Rs2 = pv ->
    M90 !!! Regidx Rs4 = ientry kf ->
    (forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 ->
        r <> Rs0 -> r <> Rs1 -> r <> Rs2 -> r <> Rs4 ->
        M90 !!! Regidx r = m !!! Regidx r) ->
    kernel_text -∗
    fs_fabric gs gu gd gk pd pav pu bn g gfs gi cn gtl
              cov logstart inodestart nib dev -∗
    pc_is (mword_of_int (KXB + 0x90) : mword 64) -∗
    sie_cap_gpr KT1 M90 (K - 68)%nat b (proc_addr jp) -∗
    cpu_own 0 eb (proc_addr jp) b lks -∗
    kxc_open gfs gi cn cov logstart dev pidv kf qf sf gyf inumf dnf bmf
              gilf gislf -∗
    log_op g n2 -∗
    iref_slots 1 -∗
    sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
    sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
    bitmap_res gfs bmapstart cov logstart size used2 -∗
    bslots bn 3 -∗
    kalloc_env ga None -∗
    proc_priv gf (proc_addr jp) pidv V -∗
    ([∗ list] i ∈ seq 0 (S plen), pa_add pv i ↦ₘ[KT1] pfun i) -∗
    ([∗ list] i ∈ seq 0 (S na), pa_add av (8 * i) ↦₈{dqa} avf i) -∗
    ([∗ list] i ∈ seq 0 na,
       [∗ list] j ∈ seq 0 (aslen i), pa_add (avf i) j ↦ₘ afun i j) -∗
    kxc_frameA6 sp0 ra0 s00 s10 s20 pv av (m !!! Regidx Rs4) -∗
    (* ---- kexec's OWN continuation: the +0x31c tail closes the -1 arm ---- *)
    wp_next b (proc_addr jp) (fun (CID : CpuId) =>
      ∀ (mf : regfile) (used' : gset Z) (V' : pprivate)
        (entry spv szv' : mword 64),
          ⌜callee_saved m mf⌝ -∗
          ⌜kexec_ok V V' (mf !!! Regidx Ra0) entry spv szv' na alen⌝ -∗
          sie_cap_gpr KT1 mf K b (proc_addr jp) -∗
          cpu_own 0 eb (proc_addr jp) b lks -∗
          pc_is (ret_pc ra0) -∗
          sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
          sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
          ⌜used' ⊆ used⌝ -∗
          bitmap_res gfs bmapstart cov logstart size used' -∗
          kalloc_env ga None -∗
          proc_priv gf (proc_addr jp) pidv V' -∗
          ([∗ list] i ∈ seq 0 (S plen), pa_add pv i ↦ₘ[KT1] pfun i) -∗
          ([∗ list] i ∈ seq 0 (S na), pa_add av (8 * i) ↦₈{dqa} avf i) -∗
          ([∗ list] i ∈ seq 0 na,
             [∗ list] j ∈ seq 0 (aslen i), pa_add (avf i) j ↦ₘ afun i j) -∗
          bslots bn 3 -∗
          iref_slots 2 -∗
          WP (Loop : expr riscv_lang)) -∗
    (* ---- OUTPUT 1: [elf.phnum = 0], the loop is skipped ---- *)
    wp_next b (proc_addr jp) (fun (CID : CpuId) =>
      ∀ (M : regfile) (ef : nat -> bv 8) (P : uptd) (w67 : mword 64),
        kxc_at_1a2 jp bn g gfs gi cn ga gf cov logstart bmapstart inodestart
                   nib size dev used used2 kf qf sf gyf inumf dnf bmf
                   gilf gislf n2
                   plen pfun na avf aslen afun pidv V dqb dqs dqa
                   m M K sp0 ra0 s00 s10 s20 pv av
                   (m !!! Regidx Rs3) (m !!! Regidx Rs4) (m !!! Regidx Rs5)
                   (m !!! Regidx Rs6) (m !!! Regidx Rs7) (m !!! Regidx Rs8)
                   (m !!! Regidx Rs9) (m !!! Regidx Rs10) (m !!! Regidx Rs11)
                   w67 ef P -∗
        (* THE EXIT, HANDED BACK: a [wp_next] continuation is LINEAR, and the
           +0x31c tail above already owns one copy, so the successor cannot
           be left without one.  durable-notes' "CHAINING TWO HALVES". *)
        wp_next (CID0 := CID) b (proc_addr jp) (fun (CIDy : CpuId) =>
          ∀ (mf : regfile) (used' : gset Z) (V' : pprivate)
            (entry spv szv' : mword 64),
              ⌜callee_saved m mf⌝ -∗
              ⌜kexec_ok V V' (mf !!! Regidx Ra0) entry spv szv' na alen⌝ -∗
              sie_cap_gpr KT1 mf K b (proc_addr jp) -∗
              cpu_own 0 eb (proc_addr jp) b lks -∗
              pc_is (ret_pc ra0) -∗
              sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
              sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
              ⌜used' ⊆ used⌝ -∗
              bitmap_res gfs bmapstart cov logstart size used' -∗
              kalloc_env ga None -∗
              proc_priv gf (proc_addr jp) pidv V' -∗
              ([∗ list] i ∈ seq 0 (S plen), pa_add pv i ↦ₘ[KT1] pfun i) -∗
              ([∗ list] i ∈ seq 0 (S na), pa_add av (8 * i) ↦₈{dqa} avf i) -∗
              ([∗ list] i ∈ seq 0 na,
                 [∗ list] j ∈ seq 0 (aslen i), pa_add (avf i) j ↦ₘ afun i j) -∗
              bslots bn 3 -∗
              iref_slots 2 -∗
              WP (Loop : expr riscv_lang)) -∗
        WP (Loop : expr riscv_lang)) -∗
    (* ---- OUTPUT 2: the phdr loop's body entry, at [i = 0], [sz = 0] ---- *)
    wp_next b (proc_addr jp) (fun (CID : CpuId) =>
      ∀ (M : regfile) (ef : nat -> bv 8) (P : uptd),
        kxc_at_12c jp bn g gfs gi cn ga gf cov logstart bmapstart inodestart
                   nib size dev used used2 kf qf sf gyf inumf dnf bmf
                   gilf gislf n2
                   plen pfun na avf aslen afun pidv V dqb dqs dqa
                   m M K sp0 ra0 s00 s10 s20 pv av
                   (m !!! Regidx Rs3) (m !!! Regidx Rs4) (m !!! Regidx Rs5)
                   (m !!! Regidx Rs6) (m !!! Regidx Rs7) (m !!! Regidx Rs8)
                   (m !!! Regidx Rs9) (m !!! Regidx Rs10) (m !!! Regidx Rs11)
                   (mword_of_int 4095 : mword 64)
                   ef P 0%nat (mword_of_int 0 : mword 64) -∗
        (* THE EXIT, HANDED BACK: a [wp_next] continuation is LINEAR, and the
           +0x31c tail above already owns one copy, so the successor cannot
           be left without one.  durable-notes' "CHAINING TWO HALVES". *)
        wp_next (CID0 := CID) b (proc_addr jp) (fun (CIDy : CpuId) =>
          ∀ (mf : regfile) (used' : gset Z) (V' : pprivate)
            (entry spv szv' : mword 64),
              ⌜callee_saved m mf⌝ -∗
              ⌜kexec_ok V V' (mf !!! Regidx Ra0) entry spv szv' na alen⌝ -∗
              sie_cap_gpr KT1 mf K b (proc_addr jp) -∗
              cpu_own 0 eb (proc_addr jp) b lks -∗
              pc_is (ret_pc ra0) -∗
              sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
              sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
              ⌜used' ⊆ used⌝ -∗
              bitmap_res gfs bmapstart cov logstart size used' -∗
              kalloc_env ga None -∗
              proc_priv gf (proc_addr jp) pidv V' -∗
              ([∗ list] i ∈ seq 0 (S plen), pa_add pv i ↦ₘ[KT1] pfun i) -∗
              ([∗ list] i ∈ seq 0 (S na), pa_add av (8 * i) ↦₈{dqa} avf i) -∗
              ([∗ list] i ∈ seq 0 na,
                 [∗ list] j ∈ seq 0 (aslen i), pa_add (avf i) j ↦ₘ afun i j) -∗
              bslots bn 3 -∗
              iref_slots 2 -∗
              WP (Loop : expr riscv_lang)) -∗
        WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros HK Hlg Hsz Hbm0 Hbmc Hbml Hins0 Hcovb Hiregb Hjp Hgs Heb Hu2
           Hk Hib Hn2 Hsp Hra Hs0 Hs1 Hs2
           HM90sp HM90s0 HM90s1 HM90s2 HM90s4 HM90thr.
    pose proof HK as HK'. 
    destruct (Hiregb inumf Hib) as [Hibc Hibl].
    iIntros "#Htext #Hfab Hpc Hcg Hcnt Hopen Hlog Hirs Hbm Hins Hbits
             Hbs #Hka Hpriv Hpath Hargv Hargs Hframe Hcont Hcont1a2 Hcont12c".
    (* ---- convention 4: pin [b = eb = true] FIRST ---- *)
    iDestruct (kxc_sie_b_agree M90 0%nat (K - 68)%nat eb b (proc_addr jp)
                 with "Hcg Hcnt") as %Houtb.
    subst eb. cbn in Houtb. subst b.
    (* depth 0 forces the held set empty, so proc_pagetable's order premise
       needs no hypothesis of this lemma's own. *)
    iDestruct (cpu_own_zero_empty with "Hcnt") as "[%Hlkempty Hcnt]".
    (* ---- the frame, opened ---- *)
    rewrite /kxc_frameA6.
    iDestruct "Hframe" as "(Hf1 & Hf2 & Hf3 & Hf4 & (%v5 & Hf5) & Hf6 &
                            (%v7 & Hf7) & (%v8 & Hf8) & (%v9 & Hf9) &
                            (%v10 & Hf10) & (%v11 & Hf11) & (%v12 & Hf12) &
                            (%v13 & Hf13) & Hmid & Hf64 & Hf65 & Hf66 &
                            (%v67 & Hf67) & Hf68)".
    iDestruct (kxc_mid_split sp0 with "Hmid") as "(Hust & Helf & Hph)".
    iPoseProof (kxc_090 with "Htext") as "Hi090".
    iPoseProof (kxc_092 with "Htext") as "Hi092".
    iPoseProof (kxc_094 with "Htext") as "Hi094".
    iPoseProof (kxc_098 with "Htext") as "Hi098".
    iPoseProof (kxc_09a with "Htext") as "Hi09a".
    iPoseProof (kxc_09e with "Htext") as "Hi09e".
    iPoseProof (kxc_0a0 with "Htext") as "Hi0a0".
    iPoseProof (kxc_0a2 with "Htext") as "Hi0a2".
    iPoseProof (kxc_0a4 with "Htext") as "Hi0a4".
    iPoseProof (kxc_0a6 with "Htext") as "Hi0a6".
    iPoseProof (kxc_0a8 with "Htext") as "Hi0a8".
    iPoseProof (kxc_0aa with "Htext") as "Hi0aa".
    iPoseProof (kxc_0ac with "Htext") as "Hi0ac".
    iPoseProof (kxc_0b0 with "Htext") as "Hi0b0".
    iPoseProof (kxc_0b4 with "Htext") as "Hi0b4".
    iPoseProof (kxc_0b8 with "Htext") as "Hi0b8".
    iPoseProof (kxc_0ba with "Htext") as "Hi0ba".
    iPoseProof (kxc_0bc with "Htext") as "Hi0bc".
    iPoseProof (kxc_0c0 with "Htext") as "Hi0c0".
    iPoseProof (kxc_0c2 with "Htext") as "Hi0c2".
    iPoseProof (kxc_0c6 with "Htext") as "Hi0c6".
    iPoseProof (kxc_0ca with "Htext") as "Hi0ca".
    iPoseProof (kxc_0cc with "Htext") as "Hi0cc".
    iPoseProof (kxc_31c with "Htext") as "Hi31c".
    iPoseProof (kxc_31e with "Htext") as "Hi31e".
    (* the entry values of the eight callee-saved registers this stretch
       spills, all of them still kexec's own ([HM90thr]) *)
    assert (HM90s3 : M90 !!! Regidx Rs3 = m !!! Regidx Rs3)
      by exact (HM90thr Rs3 ltac:(vm_compute; reflexivity) ltac:(nz) ltac:(nz)
                        ltac:(nz) ltac:(nz) ltac:(nz)).
    assert (HM90s5 : M90 !!! Regidx Rs5 = m !!! Regidx Rs5)
      by exact (HM90thr Rs5 ltac:(vm_compute; reflexivity) ltac:(nz) ltac:(nz)
                        ltac:(nz) ltac:(nz) ltac:(nz)).
    assert (HM90s6 : M90 !!! Regidx Rs6 = m !!! Regidx Rs6)
      by exact (HM90thr Rs6 ltac:(vm_compute; reflexivity) ltac:(nz) ltac:(nz)
                        ltac:(nz) ltac:(nz) ltac:(nz)).
    assert (HM90s7 : M90 !!! Regidx Rs7 = m !!! Regidx Rs7)
      by exact (HM90thr Rs7 ltac:(vm_compute; reflexivity) ltac:(nz) ltac:(nz)
                        ltac:(nz) ltac:(nz) ltac:(nz)).
    assert (HM90s8 : M90 !!! Regidx Rs8 = m !!! Regidx Rs8)
      by exact (HM90thr Rs8 ltac:(vm_compute; reflexivity) ltac:(nz) ltac:(nz)
                        ltac:(nz) ltac:(nz) ltac:(nz)).
    assert (HM90s9 : M90 !!! Regidx Rs9 = m !!! Regidx Rs9)
      by exact (HM90thr Rs9 ltac:(vm_compute; reflexivity) ltac:(nz) ltac:(nz)
                        ltac:(nz) ltac:(nz) ltac:(nz)).
    assert (HM90s10 : M90 !!! Regidx Rs10 = m !!! Regidx Rs10)
      by exact (HM90thr Rs10 ltac:(vm_compute; reflexivity) ltac:(nz) ltac:(nz)
                        ltac:(nz) ltac:(nz) ltac:(nz)).
    assert (HM90s11 : M90 !!! Regidx Rs11 = m !!! Regidx Rs11)
      by exact (HM90thr Rs11 ltac:(vm_compute; reflexivity) ltac:(nz) ltac:(nz)
                        ltac:(nz) ltac:(nz) ltac:(nz)).
    (* ---- +0x090: c.sdsp s6,480(sp) -- the LAZY spill of s6, slot 8 ---- *)
    assert (Hpa8 : add_vec (M90 !!! Regidx csp_rs1)
                     (zero_extend' 64 (concat_vec (mword_of_int 60 : mword 6)
                                                  ('b"000")))
                   = pa_stk sp0 8).
    { rewrite HM90sp.
      apply (kxc_sp_slot sp0 8 60 _ ltac:(lia)). apply bv_eq; vm_compute; reflexivity. }
    assert (Hrs6 : rget M90 Rs6 = M90 !!! Regidx Rs6) by (apply rget_ne; nz).
    iEval (rewrite -Hpa8) in "Hf8".
    iApply (wp_csdsp_s_sconf (mword_of_int (KXB + 0x90))
              (mword_of_int 60 : mword 6) Rs6 M90 (K - 68)%nat v8 true
              with "Hcg Hpc Hi090 Hf8").
    iIntros (CID1 Hsq1) "Hcg Hpc Hf8".
    iEval (rewrite Hpa8 Hrs6 HM90s6) in "Hf8".
    assert (Hpp092 : add_vec_int (mword_of_int (KXB + 0x90) : mword 64) 2
                     = mword_of_int (KXB + 0x92)) by pcw.
    iEval (rewrite Hpp092) in "Hpc".
    (* ---- +0x092: c.mv a0,s1 -- a0 := p ---- *)
    iApply (wp_cmv_s_sconf (mword_of_int (KXB + 0x92)) Ra0 Rs1
              M90 (K - 68)%nat true ltac:(nz) ltac:(rdok)
              with "Hcg Hpc Hi092").
    iIntros (CID2 Hsq2) "Hcg Hpc". iEval (rgne) in "Hcg".
    set (G1 := <[Regidx Ra0 := regval_into_reg
                  (add_vec zero_reg (M90 !!! Regidx Rs1))]> M90).
    assert (HG1a0 : G1 !!! Regidx Ra0 = proc_addr jp).
    { rewrite /G1 upd_eq HM90s1. apply add_vec_zero_l. }
    assert (HG1sp : G1 !!! Regidx csp_rs1 = pa_stk sp0 68)
      by (rewrite /G1 upd_ne; [exact HM90sp | nz]).
    assert (HG1s0 : G1 !!! Regidx Rs0 = sp0)
      by (rewrite /G1 upd_ne; [exact HM90s0 | nz]).
    assert (HG1s1 : G1 !!! Regidx Rs1 = proc_addr jp)
      by (rewrite /G1 upd_ne; [exact HM90s1 | nz]).
    assert (HG1s2 : G1 !!! Regidx Rs2 = pv)
      by (rewrite /G1 upd_ne; [exact HM90s2 | nz]).
    assert (HG1s4 : G1 !!! Regidx Rs4 = ientry kf)
      by (rewrite /G1 upd_ne; [exact HM90s4 | nz]).
    assert (HG1thr : forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 ->
              r <> Rs0 -> r <> Rs1 -> r <> Rs2 -> r <> Rs4 ->
              G1 !!! Regidx r = m !!! Regidx r).
    { intros r Hr Nsp Ns0 Ns1 Ns2 Ns4.
      rewrite /G1 upd_ne; [| regne]. exact (HM90thr r Hr Nsp Ns0 Ns1 Ns2 Ns4). }
    assert (Hpp094 : add_vec_int (mword_of_int (KXB + 0x92) : mword 64) 2
                     = mword_of_int (KXB + 0x94)) by pcw.
    iEval (rewrite Hpp094) in "Hpc".
    (* ---- +0x094: jal ra,proc_pagetable ---- *)
    assert (Htpp : add_vec (mword_of_int (KXB + 0x94) : mword 64)
                     (sign_extend' 64 (mword_of_int 2085380 : mword 21))
                   = mword_of_int KernelSyms.proc_pagetable) by pcw.
    iApply (wp_jal_s_sconf (mword_of_int (KXB + 0x94)) Rra
              (mword_of_int 2085380 : mword 21) G1 (K - 68)%nat true
              ltac:(nz) ltac:(rdok)
              ltac:(rewrite Htpp; vm_compute; reflexivity)
              with "Hcg Hpc Hi094").
    iIntros (CID3 Hsq3) "Hcg Hpc". iEval (rewrite Htpp) in "Hpc".
    set (G2 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (KXB + 0x94) : mword 64) 4)]> G1).
    change (<[Regidx Rra := regval_into_reg
              (add_vec_int (mword_of_int (KXB + 0x94) : mword 64) 4)]> G1) with G2.
    assert (HG2ra : G2 !!! Regidx Rra
                    = add_vec_int (mword_of_int (KXB + 0x94) : mword 64) 4)
      by (rewrite /G2; apply upd_eq).
    assert (HG2a0 : G2 !!! Regidx Ra0 = proc_addr jp)
      by (rewrite /G2 upd_ne; [exact HG1a0 | nz]).
    assert (HG2sp : G2 !!! Regidx csp_rs1 = pa_stk sp0 68)
      by (rewrite /G2 upd_ne; [exact HG1sp | nz]).
    assert (HG2s0 : G2 !!! Regidx Rs0 = sp0)
      by (rewrite /G2 upd_ne; [exact HG1s0 | nz]).
    assert (HG2s1 : G2 !!! Regidx Rs1 = proc_addr jp)
      by (rewrite /G2 upd_ne; [exact HG1s1 | nz]).
    assert (HG2s2 : G2 !!! Regidx Rs2 = pv)
      by (rewrite /G2 upd_ne; [exact HG1s2 | nz]).
    assert (HG2s4 : G2 !!! Regidx Rs4 = ientry kf)
      by (rewrite /G2 upd_ne; [exact HG1s4 | nz]).
    assert (HG2thr : forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 ->
              r <> Rs0 -> r <> Rs1 -> r <> Rs2 -> r <> Rs4 ->
              G2 !!! Regidx r = m !!! Regidx r).
    { intros r Hr Nsp Ns0 Ns1 Ns2 Ns4.
      rewrite /G2 upd_ne; [| regne]. exact (HG1thr r Hr Nsp Ns0 Ns1 Ns2 Ns4). }
    (* ---- the trapframe cell, lent out of the process's block ---- *)
    iDestruct (proc_priv_tfp_valid gf (proc_addr jp) pidv V with "Hpriv")
      as %Hpvtf.
    iDestruct (proc_priv_trapframe gf (proc_addr jp) pidv V with "Hpriv")
      as "(Htfc & Hpvbk)".
    set (tfr := page_base (ud_tfp (pv_upt V))).
    set (tfp := (autocast (T := mword) (subrange_vec_dec tfr 55 12) : mword 44)).
    assert (Hbasetf : page_base tfp = tfr)
      by (rewrite /tfp /tfr; apply page_base_of_valid; exact Hpvtf).
    assert (Htfpeq : tfp = ud_tfp (pv_upt V)).
    { apply kxc_page_base_inj. rewrite Hbasetf. reflexivity. }
    iDestruct (cpu_own_transport CID0 CID3 0%nat true (proc_addr jp) true
                 ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
    iApply (PPT.wp_proc_pagetable_core ga G2 tfr (DfracOwn (1/4)) 0%nat
              (K - 68)%nat true (proc_addr jp) None true lks
              kxc_lvl0 ltac:(lia)
              (kxc_tf_align tfr Hpvtf) (kxc_tf_bound tfr Hpvtf)
              with "Hcg Hcnt Htext Hpc [Htfc] Hka").
    all: try lkbelow.
    { iEval (rewrite HG2a0). iExact "Htfc". }
    iIntros (CID4 Hsq4 mr) "Hcg Hcnt Hpc Htfc Hppt %Hcspt".
    iEval (rewrite HG2a0) in "Htfc".
    assert (Hpc98 : ret_pc (G2 !!! Regidx Rra) = mword_of_int (KXB + 0x98))
      by (rewrite HG2ra; pcw).
    iEval (rewrite Hpc98) in "Hpc".
    assert (Hmrsp : mr !!! Regidx csp_rs1 = pa_stk sp0 68).
    { rewrite (callee_saved_lookup Hcspt csp_rs1 ltac:(vm_compute; reflexivity)).
      exact HG2sp. }
    assert (Hmrs0 : mr !!! Regidx Rs0 = sp0).
    { rewrite (callee_saved_lookup Hcspt Rs0 ltac:(vm_compute; reflexivity)).
      exact HG2s0. }
    assert (Hmrs1 : mr !!! Regidx Rs1 = proc_addr jp).
    { rewrite (callee_saved_lookup Hcspt Rs1 ltac:(vm_compute; reflexivity)).
      exact HG2s1. }
    assert (Hmrs2 : mr !!! Regidx Rs2 = pv).
    { rewrite (callee_saved_lookup Hcspt Rs2 ltac:(vm_compute; reflexivity)).
      exact HG2s2. }
    assert (Hmrs4 : mr !!! Regidx Rs4 = ientry kf).
    { rewrite (callee_saved_lookup Hcspt Rs4 ltac:(vm_compute; reflexivity)).
      exact HG2s4. }
    assert (Hmrthr : forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 ->
              r <> Rs0 -> r <> Rs1 -> r <> Rs2 -> r <> Rs4 ->
              mr !!! Regidx r = m !!! Regidx r).
    { intros r Hr Nsp Ns0 Ns1 Ns2 Ns4.
      rewrite (callee_saved_lookup Hcspt r Hr).
      exact (HG2thr r Hr Nsp Ns0 Ns1 Ns2 Ns4). }
    (* ---- +0x098: c.mv s6,a0 ---- *)
    iApply (wp_cmv_s_sconf (mword_of_int (KXB + 0x98)) Rs6 Ra0
              mr (K - 68)%nat true ltac:(nz) ltac:(rdok)
              with "Hcg Hpc Hi098").
    iIntros (CID5 Hsq5) "Hcg Hpc". iEval (rgne) in "Hcg".
    set (G3 := <[Regidx Rs6 := regval_into_reg
                  (add_vec zero_reg (mr !!! Regidx Ra0))]> mr).
    assert (HG3a0 : G3 !!! Regidx Ra0 = mr !!! Regidx Ra0)
      by (rewrite /G3 upd_ne; [reflexivity | nz]).
    assert (HG3sp : G3 !!! Regidx csp_rs1 = pa_stk sp0 68)
      by (rewrite /G3 upd_ne; [exact Hmrsp | nz]).
    assert (HG3s0 : G3 !!! Regidx Rs0 = sp0)
      by (rewrite /G3 upd_ne; [exact Hmrs0 | nz]).
    assert (HG3s1 : G3 !!! Regidx Rs1 = proc_addr jp)
      by (rewrite /G3 upd_ne; [exact Hmrs1 | nz]).
    assert (HG3s2 : G3 !!! Regidx Rs2 = pv)
      by (rewrite /G3 upd_ne; [exact Hmrs2 | nz]).
    assert (HG3s4 : G3 !!! Regidx Rs4 = ientry kf)
      by (rewrite /G3 upd_ne; [exact Hmrs4 | nz]).
    assert (HG3s6 : G3 !!! Regidx Rs6 = add_vec zero_reg (mr !!! Regidx Ra0))
      by (rewrite /G3; apply upd_eq).
    assert (HG3thr : forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 ->
              r <> Rs0 -> r <> Rs1 -> r <> Rs2 -> r <> Rs4 -> r <> Rs6 ->
              G3 !!! Regidx r = m !!! Regidx r).
    { intros r Hr Nsp Ns0 Ns1 Ns2 Ns4 Ns6.
      rewrite /G3 upd_ne; [| congruence]. exact (Hmrthr r Hr Nsp Ns0 Ns1 Ns2 Ns4). }
    assert (Hpp09a : add_vec_int (mword_of_int (KXB + 0x98) : mword 64) 2
                     = mword_of_int (KXB + 0x9a)) by pcw.
    iEval (rewrite Hpp09a) in "Hpc".
    assert (Hrga0 : rget G3 Ra0 = G3 !!! Regidx Ra0) by (apply rget_ne; nz).
    (* ---- +0x09a: beqz a0 -- proc_pagetable's verdict ---- *)
    iDestruct "Hppt" as "[(%t & %Hroot & Htree & %Hrep & %Hnodes & Henv)
                        | (%Hptz & %Hdry & Henv)]".
    - (* ============ SUCCESS: a new table, on to the phdr setup ============
         [kalloc_env ga None] is PERSISTENT (KvmSpec.kalloc_env_None_persistent),
         so the copy proc_pagetable hands back is redundant: "Hka" is still
         there, at [None] rather than at [avail_sub None (pt_nodes t)]. ------ *)
      (* the join with the [proc_pt] tier *)
      iDestruct (proc_pt_intro_ppt t tfp Hrep
                   ltac:(rewrite Hbasetf; exact Hpvtf) with "Htree") as "Hpt".
      set (P := upt_desc (pt_base t) tfp).
      iDestruct (proc_pt_root_valid P with "Hpt") as %Hrootv.
      assert (HProot : ud_root P = pt_base t) by reflexivity.
      assert (HPtfp : ud_tfp P = ud_tfp (pv_upt V)) by exact Htfpeq.
      assert (HPum : ud_um P = ∅) by reflexivity.
      assert (Ha0v : mr !!! Regidx Ra0 = page_base (ud_root P))
        by (rewrite Hroot HProot; reflexivity).
      assert (Hnzero : eq_vec (rget G3 Ra0) (zero_reg : mword 64) = false).
      { rewrite Hrga0 HG3a0 Ha0v.
        pose proof (page_valid_neq_zero (page_base (ud_root P)) Hrootv) as Hne.
        unfold neq_vec in Hne. destruct (eq_vec (page_base (ud_root P))
          (zero_reg : mword 64)); [discriminate | reflexivity]. }
      iApply (wp_beqz_x0_fall_s_sconf (mword_of_int (KXB + 0x9a))
                (mword_of_int 642 : mword 13) Ra0 G3 (K - 68)%nat true
                ltac:(nz) Hnzero with "Hcg Hpc Hi09a").
      iIntros (CID6 Hsq6) "Hcg Hpc".
      assert (Hpp09e : add_vec_int (mword_of_int (KXB + 0x9a) : mword 64) 4
                       = mword_of_int (KXB + 0x9e)) by pcw.
      iEval (rewrite Hpp09e) in "Hpc".
      assert (HG3s6v : G3 !!! Regidx Rs6 = page_base (ud_root P)).
      { rewrite HG3s6 Ha0v. apply add_vec_zero_l. }
      (* ---- +0x09e .. +0x0aa: the seven remaining LAZY spills ---- *)
      assert (Hpa5 : add_vec (G3 !!! Regidx csp_rs1)
                       (zero_extend' 64 (concat_vec (mword_of_int 63 : mword 6)
                                                    ('b"000")))
                     = pa_stk sp0 5).
      { rewrite HG3sp. apply (kxc_sp_slot sp0 5 63 _ ltac:(lia)).
        apply bv_eq; vm_compute; reflexivity. }
      assert (Hrs3 : rget G3 Rs3 = G3 !!! Regidx Rs3) by (apply rget_ne; nz).
      assert (HG3s3 : G3 !!! Regidx Rs3 = m !!! Regidx Rs3)
        by exact (HG3thr Rs3 ltac:(vm_compute; reflexivity) ltac:(nz) ltac:(nz)
                         ltac:(nz) ltac:(nz) ltac:(nz) ltac:(nz)).
      iEval (rewrite -Hpa5) in "Hf5".
      iApply (wp_csdsp_s_sconf (mword_of_int (KXB + 0x9e))
                (mword_of_int 63 : mword 6) Rs3 G3 (K - 68)%nat v5 true
                with "Hcg Hpc Hi09e Hf5").
      iIntros (CID7 Hsq7) "Hcg Hpc Hf5".
      iEval (rewrite Hpa5 Hrs3 HG3s3) in "Hf5".
      assert (Hpp0a0 : add_vec_int (mword_of_int (KXB + 0x9e) : mword 64) 2
                       = mword_of_int (KXB + 0xa0)) by pcw.
      iEval (rewrite Hpp0a0) in "Hpc".
      assert (Hpa7 : add_vec (G3 !!! Regidx csp_rs1)
                       (zero_extend' 64 (concat_vec (mword_of_int 61 : mword 6)
                                                    ('b"000")))
                     = pa_stk sp0 7).
      { rewrite HG3sp. apply (kxc_sp_slot sp0 7 61 _ ltac:(lia)).
        apply bv_eq; vm_compute; reflexivity. }
      assert (Hrs5 : rget G3 Rs5 = G3 !!! Regidx Rs5) by (apply rget_ne; nz).
      assert (HG3s5 : G3 !!! Regidx Rs5 = m !!! Regidx Rs5)
        by exact (HG3thr Rs5 ltac:(vm_compute; reflexivity) ltac:(nz) ltac:(nz)
                         ltac:(nz) ltac:(nz) ltac:(nz) ltac:(nz)).
      iEval (rewrite -Hpa7) in "Hf7".
      iApply (wp_csdsp_s_sconf (mword_of_int (KXB + 0xa0))
                (mword_of_int 61 : mword 6) Rs5 G3 (K - 68)%nat v7 true
                with "Hcg Hpc Hi0a0 Hf7").
      iIntros (CID8 Hsq8) "Hcg Hpc Hf7".
      iEval (rewrite Hpa7 Hrs5 HG3s5) in "Hf7".
      assert (Hpp0a2 : add_vec_int (mword_of_int (KXB + 0xa0) : mword 64) 2
                       = mword_of_int (KXB + 0xa2)) by pcw.
      iEval (rewrite Hpp0a2) in "Hpc".
      assert (Hpa9 : add_vec (G3 !!! Regidx csp_rs1)
                       (zero_extend' 64 (concat_vec (mword_of_int 59 : mword 6)
                                                    ('b"000")))
                     = pa_stk sp0 9).
      { rewrite HG3sp. apply (kxc_sp_slot sp0 9 59 _ ltac:(lia)).
        apply bv_eq; vm_compute; reflexivity. }
      assert (Hrs7 : rget G3 Rs7 = G3 !!! Regidx Rs7) by (apply rget_ne; nz).
      assert (HG3s7 : G3 !!! Regidx Rs7 = m !!! Regidx Rs7)
        by exact (HG3thr Rs7 ltac:(vm_compute; reflexivity) ltac:(nz) ltac:(nz)
                         ltac:(nz) ltac:(nz) ltac:(nz) ltac:(nz)).
      iEval (rewrite -Hpa9) in "Hf9".
      iApply (wp_csdsp_s_sconf (mword_of_int (KXB + 0xa2))
                (mword_of_int 59 : mword 6) Rs7 G3 (K - 68)%nat v9 true
                with "Hcg Hpc Hi0a2 Hf9").
      iIntros (CID9 Hsq9) "Hcg Hpc Hf9".
      iEval (rewrite Hpa9 Hrs7 HG3s7) in "Hf9".
      assert (Hpp0a4 : add_vec_int (mword_of_int (KXB + 0xa2) : mword 64) 2
                       = mword_of_int (KXB + 0xa4)) by pcw.
      iEval (rewrite Hpp0a4) in "Hpc".
      assert (Hpa10 : add_vec (G3 !!! Regidx csp_rs1)
                        (zero_extend' 64 (concat_vec (mword_of_int 58 : mword 6)
                                                     ('b"000")))
                      = pa_stk sp0 10).
      { rewrite HG3sp. apply (kxc_sp_slot sp0 10 58 _ ltac:(lia)).
        apply bv_eq; vm_compute; reflexivity. }
      assert (Hrs8 : rget G3 Rs8 = G3 !!! Regidx Rs8) by (apply rget_ne; nz).
      assert (HG3s8 : G3 !!! Regidx Rs8 = m !!! Regidx Rs8)
        by exact (HG3thr Rs8 ltac:(vm_compute; reflexivity) ltac:(nz) ltac:(nz)
                         ltac:(nz) ltac:(nz) ltac:(nz) ltac:(nz)).
      iEval (rewrite -Hpa10) in "Hf10".
      iApply (wp_csdsp_s_sconf (mword_of_int (KXB + 0xa4))
                (mword_of_int 58 : mword 6) Rs8 G3 (K - 68)%nat v10 true
                with "Hcg Hpc Hi0a4 Hf10").
      iIntros (CID10 Hsq10) "Hcg Hpc Hf10".
      iEval (rewrite Hpa10 Hrs8 HG3s8) in "Hf10".
      assert (Hpp0a6 : add_vec_int (mword_of_int (KXB + 0xa4) : mword 64) 2
                       = mword_of_int (KXB + 0xa6)) by pcw.
      iEval (rewrite Hpp0a6) in "Hpc".
      assert (Hpa11 : add_vec (G3 !!! Regidx csp_rs1)
                        (zero_extend' 64 (concat_vec (mword_of_int 57 : mword 6)
                                                     ('b"000")))
                      = pa_stk sp0 11).
      { rewrite HG3sp. apply (kxc_sp_slot sp0 11 57 _ ltac:(lia)).
        apply bv_eq; vm_compute; reflexivity. }
      assert (Hrs9 : rget G3 Rs9 = G3 !!! Regidx Rs9) by (apply rget_ne; nz).
      assert (HG3s9 : G3 !!! Regidx Rs9 = m !!! Regidx Rs9)
        by exact (HG3thr Rs9 ltac:(vm_compute; reflexivity) ltac:(nz) ltac:(nz)
                         ltac:(nz) ltac:(nz) ltac:(nz) ltac:(nz)).
      iEval (rewrite -Hpa11) in "Hf11".
      iApply (wp_csdsp_s_sconf (mword_of_int (KXB + 0xa6))
                (mword_of_int 57 : mword 6) Rs9 G3 (K - 68)%nat v11 true
                with "Hcg Hpc Hi0a6 Hf11").
      iIntros (CID11 Hsq11) "Hcg Hpc Hf11".
      iEval (rewrite Hpa11 Hrs9 HG3s9) in "Hf11".
      assert (Hpp0a8 : add_vec_int (mword_of_int (KXB + 0xa6) : mword 64) 2
                       = mword_of_int (KXB + 0xa8)) by pcw.
      iEval (rewrite Hpp0a8) in "Hpc".
      assert (Hpa12 : add_vec (G3 !!! Regidx csp_rs1)
                        (zero_extend' 64 (concat_vec (mword_of_int 56 : mword 6)
                                                     ('b"000")))
                      = pa_stk sp0 12).
      { rewrite HG3sp. apply (kxc_sp_slot sp0 12 56 _ ltac:(lia)).
        apply bv_eq; vm_compute; reflexivity. }
      assert (Hrs10 : rget G3 Rs10 = G3 !!! Regidx Rs10) by (apply rget_ne; nz).
      assert (HG3s10 : G3 !!! Regidx Rs10 = m !!! Regidx Rs10)
        by exact (HG3thr Rs10 ltac:(vm_compute; reflexivity) ltac:(nz) ltac:(nz)
                         ltac:(nz) ltac:(nz) ltac:(nz) ltac:(nz)).
      iEval (rewrite -Hpa12) in "Hf12".
      iApply (wp_csdsp_s_sconf (mword_of_int (KXB + 0xa8))
                (mword_of_int 56 : mword 6) Rs10 G3 (K - 68)%nat v12 true
                with "Hcg Hpc Hi0a8 Hf12").
      iIntros (CID12 Hsq12) "Hcg Hpc Hf12".
      iEval (rewrite Hpa12 Hrs10 HG3s10) in "Hf12".
      assert (Hpp0aa : add_vec_int (mword_of_int (KXB + 0xa8) : mword 64) 2
                       = mword_of_int (KXB + 0xaa)) by pcw.
      iEval (rewrite Hpp0aa) in "Hpc".
      assert (Hpa13 : add_vec (G3 !!! Regidx csp_rs1)
                        (zero_extend' 64 (concat_vec (mword_of_int 55 : mword 6)
                                                     ('b"000")))
                      = pa_stk sp0 13).
      { rewrite HG3sp. apply (kxc_sp_slot sp0 13 55 _ ltac:(lia)).
        apply bv_eq; vm_compute; reflexivity. }
      assert (Hrs11 : rget G3 Rs11 = G3 !!! Regidx Rs11) by (apply rget_ne; nz).
      assert (HG3s11 : G3 !!! Regidx Rs11 = m !!! Regidx Rs11)
        by exact (HG3thr Rs11 ltac:(vm_compute; reflexivity) ltac:(nz) ltac:(nz)
                         ltac:(nz) ltac:(nz) ltac:(nz) ltac:(nz)).
      iEval (rewrite -Hpa13) in "Hf13".
      iApply (wp_csdsp_s_sconf (mword_of_int (KXB + 0xaa))
                (mword_of_int 55 : mword 6) Rs11 G3 (K - 68)%nat v13 true
                with "Hcg Hpc Hi0aa Hf13").
      iIntros (CID13 Hsq13) "Hcg Hpc Hf13".
      iEval (rewrite Hpa13 Hrs11 HG3s11) in "Hf13".
      assert (Hpp0ac : add_vec_int (mword_of_int (KXB + 0xaa) : mword 64) 2
                       = mword_of_int (KXB + 0xac)) by pcw.
      iEval (rewrite Hpp0ac) in "Hpc".
      (* ---- the elf carve: 64 NAMED bytes, kept named from here on ---- *)
      iDestruct (kxc_elf_take sp0 with "Helf") as "[%Hal Helfb]".
      iDestruct "Helfb" as (ef) "Helfb".
      assert (Hal47 : is_aligned_paddr (Physaddr (pa_stk sp0 47)) 8 = true)
        by (pose proof (Hal 7%nat ltac:(lia)) as Hx; cbn in Hx; exact Hx).
      assert (Hal50 : is_aligned_paddr (Physaddr (pa_stk sp0 50)) 8 = true)
        by (pose proof (Hal 4%nat ltac:(lia)) as Hx; cbn in Hx; exact Hx).
      (* ---- +0x0ac: lhu a5,-376(s0) -- elf.phnum ---- *)
      assert (Hal2 : is_aligned_paddr
                       (Physaddr (pa_add (pa_stk sp0 54) 56)) 2 = true).
      { rewrite kxc_elf_off56. apply kxc_aligned8_aligned2. exact Hal47. }
      iDestruct (kxc_win2 (pa_stk sp0 54) ef 56 6 64 ltac:(lia) Hal2
                   with "Helfb") as "[Hw2 Hbk2]".
      assert (Hpa47 : add_vec (rget G3 Rs0)
                        (sign_extend' 64 (mword_of_int 3720 : mword 12))
                      = pa_add (pa_stk sp0 54) 56).
      { rewrite (rget_ne G3 Rs0 ltac:(nz)) HG3s0 kxc_elf_off56.
        apply kxc_phnum_slot. }
      iEval (rewrite -Hpa47) in "Hw2".
      iApply (wp_lhu_s_sconf (kt := KT1) (ktd := KT1) (mword_of_int (KXB + 0xac)) Ra5 Rs0
                (mword_of_int 3720 : mword 12) G3 (K - 68)%nat
                (Z_to_bv 16 (le_at ef 56 2) : mword 16) true
                (dqm := DfracOwn 1) ltac:(nz) ltac:(rdok)
                with "Hcg Hpc Hi0ac Hw2").
      iIntros (CID14 Hsq14) "Hcg Hpc Hw2". iEval (rewrite Hpa47) in "Hw2".
      iDestruct ("Hbk2" with "Hw2") as "Helfb".
      set (G4 := <[Regidx Ra5 := regval_into_reg
                    (zero_extend' 64
                       (Z_to_bv 16 (le_at ef 56 2) : mword 16))]> G3).
      assert (HG4sp : G4 !!! Regidx csp_rs1 = pa_stk sp0 68)
        by (rewrite /G4 upd_ne; [exact HG3sp | nz]).
      assert (HG4s0 : G4 !!! Regidx Rs0 = sp0)
        by (rewrite /G4 upd_ne; [exact HG3s0 | nz]).
      assert (HG4s1 : G4 !!! Regidx Rs1 = proc_addr jp)
        by (rewrite /G4 upd_ne; [exact HG3s1 | nz]).
      assert (HG4s2 : G4 !!! Regidx Rs2 = pv)
        by (rewrite /G4 upd_ne; [exact HG3s2 | nz]).
      assert (HG4s4 : G4 !!! Regidx Rs4 = ientry kf)
        by (rewrite /G4 upd_ne; [exact HG3s4 | nz]).
      assert (HG4s6 : G4 !!! Regidx Rs6 = page_base (ud_root P))
        by (rewrite /G4 upd_ne; [exact HG3s6v | nz]).
      assert (HG4s9 : G4 !!! Regidx Rs9 = m !!! Regidx Rs9)
        by (rewrite /G4 upd_ne; [exact HG3s9 | nz]).
      assert (HG4thr : forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 ->
                r <> Rs0 -> r <> Rs1 -> r <> Rs2 -> r <> Rs4 -> r <> Rs6 ->
                G4 !!! Regidx r = m !!! Regidx r).
      { intros r Hr Nsp Ns0 Ns1 Ns2 Ns4 Ns6.
        rewrite /G4 upd_ne; [| regne].
        exact (HG3thr r Hr Nsp Ns0 Ns1 Ns2 Ns4 Ns6). }
      assert (Hpp0b0 : add_vec_int (mword_of_int (KXB + 0xac) : mword 64) 4
                       = mword_of_int (KXB + 0xb0)) by pcw.
      iEval (rewrite Hpp0b0) in "Hpc".
      (* ---- +0x0b0: beqz a5 -- a BLIND split on [elf.phnum] ---- *)
      destruct (eq_vec (rget G4 Ra5) (zero_reg : mword 64)) eqn:Ephn.
      + (* ---- phnum = 0: the loop is skipped, on to +0x1a2 ---- *)
        assert (Htgt1a2 : add_vec (mword_of_int (KXB + 0xb0) : mword 64)
                  (sign_extend' 64 (mword_of_int 242 : mword 13))
                = mword_of_int (KXB + 0x1a2)) by pcw.
        iApply (wp_beqz_x0_taken_s_sconf (mword_of_int (KXB + 0xb0))
                  (mword_of_int 242 : mword 13) Ra5 G4 (K - 68)%nat true
                  ltac:(nz) Ephn
                  ltac:(rewrite Htgt1a2; vm_compute; reflexivity)
                  with "Hcg Hpc Hi0b0").
        iIntros (CID15 Hsq15). iNext. iIntros "Hcg Hpc".
        iEval (rewrite Htgt1a2) in "Hpc".
        iDestruct ("Hpvbk" with "Htfc") as "Hpriv".
        iDestruct (cpu_own_transport CID4 CID15 0%nat true (proc_addr jp) true
                     ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
        iSpecialize ("Hcont1a2" $! CID15 with "[%]"); [wp_next_chain |].
        iDestruct (wp_next_retarget CID0 CID15 true (proc_addr jp) _
                     ltac:(wp_next_chain) with "Hcont") as "Hcont".
        iApply ("Hcont1a2" $! G4 ef P v67 with "[-Hcont] Hcont").
        rewrite /kxc_at_1a2.
        iSplitR.
        { iPureIntro. split_and!;
            [exact HG4sp | exact HG4s0 | exact HG4s1 | exact HG4s2 | exact HG4s4
            | exact HG4s6 | exact HG4thr]. }
        iSplitR.
        { iPureIntro. split_and!;
            [exact Hk | exact Hib | exact Hn2 | exact Hu2 | exact Hal]. }
        iSplitR.
        { iPureIntro. split_and!;
            [exact HPtfp
            | rewrite HPum; exact (um_below_empty _)
            | exact (um_covered_zero _)]. }
        (* [iFrame] is NOT usable here: its [Frame] search unfolds [proc_priv]
           and the goal's big-ops, and this state carries a syscall-altitude
           block (measured: >19 GB and climbing before it was replaced).
           Name every conjunct instead -- durable-notes' rule for capstone
           contexts. *)
        iSplitL "Hpc"; [iExact "Hpc" |].
        iSplitL "Hcg"; [iExact "Hcg" |].
        (* [kxc_at_1a2] names the held set as the literal [∅]; depth 0 makes
           that the same set [Hcnt] carries. *)
        iEval (rewrite Hlkempty) in "Hcnt".
        iSplitL "Hcnt"; [iExact "Hcnt" |].
        iSplitL "Hopen"; [iExact "Hopen" |].
        iSplitL "Hlog"; [iExact "Hlog" |].
        iSplitL "Hirs"; [iExact "Hirs" |].
        iSplitL "Hbm"; [iExact "Hbm" |].
        iSplitL "Hins"; [iExact "Hins" |].
        iSplitL "Hbits"; [iExact "Hbits" |].
        iSplitL "Hbs"; [iExact "Hbs" |].
        iSplitR; [iExact "Hka" |].
        iSplitL "Hpt"; [iExact "Hpt" |].
        iSplitL "Hpriv"; [iExact "Hpriv" |].
        iSplitL "Hpath"; [iExact "Hpath" |].
        iSplitL "Hargv"; [iExact "Hargv" |].
        iSplitL "Hargs"; [iExact "Hargs" |].
        iSplitL "Helfb"; [iExact "Helfb" |].
        rewrite /kxc_frameB.
        iSplitL "Hf1"; [iExact "Hf1" |].
        iSplitL "Hf2"; [iExact "Hf2" |].
        iSplitL "Hf3"; [iExact "Hf3" |].
        iSplitL "Hf4"; [iExact "Hf4" |].
        iSplitL "Hf5"; [iExact "Hf5" |].
        iSplitL "Hf6"; [iExact "Hf6" |].
        iSplitL "Hf7"; [iExact "Hf7" |].
        iSplitL "Hf8"; [iExact "Hf8" |].
        iSplitL "Hf9"; [iExact "Hf9" |].
        iSplitL "Hf10"; [iExact "Hf10" |].
        iSplitL "Hf11"; [iExact "Hf11" |].
        iSplitL "Hf12"; [iExact "Hf12" |].
        iSplitL "Hf13"; [iExact "Hf13" |].
        iSplitL "Hust"; [iExact "Hust" |].
        iSplitL "Hph"; [iExact "Hph" |].
        iSplitL "Hf64"; [iExact "Hf64" |].
        iSplitL "Hf65"; [iExact "Hf65" |].
        iSplitL "Hf66"; [iExact "Hf66" |].
        iSplitL "Hf67"; [iExact "Hf67" | iExact "Hf68"].
      + (* ---- phnum <> 0: the phdr loop's setup, +0x0b4 .. +0x0cc ---- *)
        iApply (wp_beqz_x0_fall_s_sconf (mword_of_int (KXB + 0xb0))
                  (mword_of_int 242 : mword 13) Ra5 G4 (K - 68)%nat true
                  ltac:(nz) Ephn with "Hcg Hpc Hi0b0").
        iIntros (CID15 Hsq15) "Hcg Hpc".
        assert (Hpp0b4 : add_vec_int (mword_of_int (KXB + 0xb0) : mword 64) 4
                         = mword_of_int (KXB + 0xb4)) by pcw.
        iEval (rewrite Hpp0b4) in "Hpc".
        (* ---- +0x0b4: lw a3,-400(s0) -- elf.phoff, the LOW SIGNED WORD ---- *)
        assert (Hal4 : is_aligned_paddr
                         (Physaddr (pa_add (pa_stk sp0 54) 32)) 4 = true).
        { rewrite kxc_elf_off32. apply aligned8_aligned4. exact Hal50. }
        iDestruct (kxc_win4 (pa_stk sp0 54) ef 32 28 64 ltac:(lia) Hal4
                     with "Helfb") as "[Hw4 Hbk4]".
        assert (Hpa50 : add_vec (rget G4 Rs0)
                          (sign_extend' 64 (mword_of_int 3696 : mword 12))
                        = pa_add (pa_stk sp0 54) 32).
        { rewrite (rget_ne G4 Rs0 ltac:(nz)) HG4s0 kxc_elf_off32.
          apply kxc_phoff_slot. }
        iEval (rewrite -Hpa50) in "Hw4".
        iApply (wp_lw_s_sconf (mword_of_int (KXB + 0xb4)) Ra3 Rs0
                  (mword_of_int 3696 : mword 12) G4 (K - 68)%nat
                  (Z_to_bv 32 (le_at ef 32 4) : mword 32) true
                  (dqm := DfracOwn 1) ltac:(nz) ltac:(rdok)
                  with "Hcg Hpc Hi0b4 Hw4").
        iIntros (CID16 Hsq16) "Hcg Hpc Hw4". iEval (rewrite Hpa50) in "Hw4".
        iDestruct ("Hbk4" with "Hw4") as "Helfb".
        set (G5 := <[Regidx Ra3 := regval_into_reg
                      (sign_extend' 64
                         (Z_to_bv 32 (le_at ef 32 4) : mword 32))]> G4).
        assert (Hpp0b8 : add_vec_int (mword_of_int (KXB + 0xb4) : mword 64) 4
                         = mword_of_int (KXB + 0xb8)) by pcw.
        iEval (rewrite Hpp0b8) in "Hpc".
        (* ---- +0x0b8: c.li s2,0 -- sz := 0 ---- *)
        iApply (wp_cli_s_sconf (mword_of_int (KXB + 0xb8)) Rs2
                  (mword_of_int 0 : mword 6) (mword_of_int 0 : mword 64)
                  G5 (K - 68)%nat true ltac:(nz) ltac:(rdok) ltac:(pcw)
                  with "Hcg Hpc Hi0b8").
        iIntros (CID17 Hsq17) "Hcg Hpc".
        set (G6 := <[Regidx Rs2 := regval_into_reg
                      (mword_of_int 0 : mword 64)]> G5).
        assert (Hpp0ba : add_vec_int (mword_of_int (KXB + 0xb8) : mword 64) 2
                         = mword_of_int (KXB + 0xba)) by pcw.
        iEval (rewrite Hpp0ba) in "Hpc".
        (* ---- +0x0ba: c.li s10,0 -- i := 0 ---- *)
        iApply (wp_cli_s_sconf (mword_of_int (KXB + 0xba)) Rs10
                  (mword_of_int 0 : mword 6)
                  (mword_of_int (Z.of_nat 0) : mword 64)
                  G6 (K - 68)%nat true ltac:(nz) ltac:(rdok) ltac:(pcw)
                  with "Hcg Hpc Hi0ba").
        iIntros (CID18 Hsq18) "Hcg Hpc".
        set (G7 := <[Regidx Rs10 := regval_into_reg
                      (mword_of_int (Z.of_nat 0) : mword 64)]> G6).
        assert (Hpp0bc : add_vec_int (mword_of_int (KXB + 0xba) : mword 64) 2
                         = mword_of_int (KXB + 0xbc)) by pcw.
        iEval (rewrite Hpp0bc) in "Hpc".
        (* ---- +0x0bc: li s11,56 -- sizeof(struct proghdr) ---- *)
        iApply (wp_li4_s_sconf (mword_of_int (KXB + 0xbc)) Rs11
                  (mword_of_int 56 : mword 12) (mword_of_int 56 : mword 64)
                  G7 (K - 68)%nat true ltac:(nz) ltac:(rdok) ltac:(pcw)
                  with "Hcg Hpc Hi0bc").
        iIntros (CID19 Hsq19) "Hcg Hpc".
        set (G8 := <[Regidx Rs11 := regval_into_reg
                      (mword_of_int 56 : mword 64)]> G7).
        assert (Hpp0c0 : add_vec_int (mword_of_int (KXB + 0xbc) : mword 64) 4
                         = mword_of_int (KXB + 0xc0)) by pcw.
        iEval (rewrite Hpp0c0) in "Hpc".
        (* ---- +0x0c0: c.lui s9,0x1 -- s9 := 4096 ---- *)
        iApply (wp_clui_s_sconf (mword_of_int (KXB + 0xc0)) Rs9
                  (sign_extend' 20 (mword_of_int 1 : mword 6))
                  (mword_of_int 4096 : mword 64) G8 (K - 68)%nat true
                  ltac:(nz) ltac:(rdok) ltac:(pcw)
                  with "Hcg Hpc Hi0c0").
        iIntros (CID20 Hsq20) "Hcg Hpc".
        set (G9 := <[Regidx Rs9 := regval_into_reg
                      (mword_of_int 4096 : mword 64)]> G8).
        assert (HG9s9 : G9 !!! Regidx Rs9 = (mword_of_int 4096 : mword 64))
          by (rewrite /G9; apply upd_eq).
        assert (Hpp0c2 : add_vec_int (mword_of_int (KXB + 0xc0) : mword 64) 2
                         = mword_of_int (KXB + 0xc2)) by pcw.
        iEval (rewrite Hpp0c2) in "Hpc".
        (* ---- +0x0c2: addi a5,s9,-1 -- a5 := 0xfff ---- *)
        iApply (wp_addi4_s_sconf (mword_of_int (KXB + 0xc2)) Ra5 Rs9
                  (mword_of_int 4095 : mword 12) G9 (K - 68)%nat true
                  ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi0c2").
        iIntros (CID21 Hsq21) "Hcg Hpc". iEval (rgne) in "Hcg".
        set (G10 := <[Regidx Ra5 := regval_into_reg
                       (add_vec (G9 !!! Regidx Rs9)
                          (sign_extend' 64 (mword_of_int 4095 : mword 12)))]> G9).
        assert (HG10a5 : G10 !!! Regidx Ra5 = (mword_of_int 4095 : mword 64)).
        { rewrite /G10 upd_eq HG9s9. apply bv_eq; vm_compute; reflexivity. }
        assert (Hpp0c6 : add_vec_int (mword_of_int (KXB + 0xc2) : mword 64) 4
                         = mword_of_int (KXB + 0xc6)) by pcw.
        iEval (rewrite Hpp0c6) in "Hpc".
        (* ---- the register facts the mask store and the seam both need ---- *)
        assert (HG10s0 : G10 !!! Regidx Rs0 = sp0).
        { rewrite /G10 upd_ne; [| nz]. rewrite /G9 upd_ne; [| nz].
          rewrite /G8 upd_ne; [| nz]. rewrite /G7 upd_ne; [| nz].
          rewrite /G6 upd_ne; [| nz]. rewrite /G5 upd_ne; [exact HG4s0 | nz]. }
        (* ---- +0x0c6: sd a5,-536(s0) -- the PGSIZE-1 mask into slot 67 ---- *)
        assert (Hpa67 : add_vec (rget G10 Rs0)
                          (sign_extend' 64 (mword_of_int 3560 : mword 12))
                        = pa_stk sp0 67).
        { rewrite (rget_ne G10 Rs0 ltac:(nz)) HG10s0. apply kxc_mask_slot. }
        assert (Hrga5 : rget G10 Ra5 = G10 !!! Regidx Ra5)
          by (apply rget_ne; nz).
        iEval (rewrite -Hpa67) in "Hf67".
        iApply (wp_sd_s_sconf (mword_of_int (KXB + 0xc6)) Ra5 Rs0
                  (mword_of_int 3560 : mword 12) G10 (K - 68)%nat v67 true
                  with "Hcg Hpc Hi0c6 Hf67").
        iIntros (CID22 Hsq22) "Hcg Hpc Hf67".
        iEval (rewrite Hpa67 Hrga5 HG10a5) in "Hf67".
        assert (Hpp0ca : add_vec_int (mword_of_int (KXB + 0xc6) : mword 64) 4
                         = mword_of_int (KXB + 0xca)) by pcw.
        iEval (rewrite Hpp0ca) in "Hpc".
        (* ---- +0x0ca: c.lui s5,0x1 -- s5 := 4096 ---- *)
        iApply (wp_clui_s_sconf (mword_of_int (KXB + 0xca)) Rs5
                  (sign_extend' 20 (mword_of_int 1 : mword 6))
                  (mword_of_int 4096 : mword 64) G10 (K - 68)%nat true
                  ltac:(nz) ltac:(rdok) ltac:(pcw)
                  with "Hcg Hpc Hi0ca").
        iIntros (CID23 Hsq23) "Hcg Hpc".
        set (G11 := <[Regidx Rs5 := regval_into_reg
                       (mword_of_int 4096 : mword 64)]> G10).
        assert (Hpp0cc : add_vec_int (mword_of_int (KXB + 0xca) : mword 64) 2
                         = mword_of_int (KXB + 0xcc)) by pcw.
        iEval (rewrite Hpp0cc) in "Hpc".
        (* ---- the whole register state at +0x12c ---- *)
        assert (HG11s5 : G11 !!! Regidx Rs5 = (mword_of_int 4096 : mword 64))
          by (rewrite /G11; apply upd_eq).
        assert (HG11s9 : G11 !!! Regidx Rs9 = (mword_of_int 4096 : mword 64)).
        { rewrite /G11 upd_ne; [| nz]. rewrite /G10 upd_ne; [| nz].
          exact HG9s9. }
        assert (HG11s11 : G11 !!! Regidx Rs11 = (mword_of_int 56 : mword 64)).
        { rewrite /G11 upd_ne; [| nz]. rewrite /G10 upd_ne; [| nz].
          rewrite /G9 upd_ne; [| nz]. rewrite /G8; apply upd_eq. }
        assert (HG11s10 : G11 !!! Regidx Rs10
                          = (mword_of_int (Z.of_nat 0) : mword 64)).
        { rewrite /G11 upd_ne; [| nz]. rewrite /G10 upd_ne; [| nz].
          rewrite /G9 upd_ne; [| nz]. rewrite /G8 upd_ne; [| nz].
          rewrite /G7; apply upd_eq. }
        assert (HG11s2 : G11 !!! Regidx Rs2 = (mword_of_int 0 : mword 64)).
        { rewrite /G11 upd_ne; [| nz]. rewrite /G10 upd_ne; [| nz].
          rewrite /G9 upd_ne; [| nz]. rewrite /G8 upd_ne; [| nz].
          rewrite /G7 upd_ne; [| nz]. rewrite /G6; apply upd_eq. }
        assert (HG11a3 : G11 !!! Regidx Ra3 = kxc_off ef 0).
        { rewrite /G11 upd_ne; [| nz]. rewrite /G10 upd_ne; [| nz].
          rewrite /G9 upd_ne; [| nz]. rewrite /G8 upd_ne; [| nz].
          rewrite /G7 upd_ne; [| nz]. rewrite /G6 upd_ne; [| nz].
          rewrite /G5 upd_eq kxc_off_0. reflexivity. }
        assert (HG11sp : G11 !!! Regidx csp_rs1 = pa_stk sp0 68).
        { rewrite /G11 upd_ne; [| nz]. rewrite /G10 upd_ne; [| nz].
          rewrite /G9 upd_ne; [| nz]. rewrite /G8 upd_ne; [| nz].
          rewrite /G7 upd_ne; [| nz]. rewrite /G6 upd_ne; [| nz].
          rewrite /G5 upd_ne; [exact HG4sp | nz]. }
        assert (HG11s0 : G11 !!! Regidx Rs0 = sp0).
        { rewrite /G11 upd_ne; [| nz]. rewrite /G10 upd_ne; [exact HG10s0 | nz]. }
        assert (HG11s1 : G11 !!! Regidx Rs1 = proc_addr jp).
        { rewrite /G11 upd_ne; [| nz]. rewrite /G10 upd_ne; [| nz].
          rewrite /G9 upd_ne; [| nz]. rewrite /G8 upd_ne; [| nz].
          rewrite /G7 upd_ne; [| nz]. rewrite /G6 upd_ne; [| nz].
          rewrite /G5 upd_ne; [exact HG4s1 | nz]. }
        assert (HG11s4 : G11 !!! Regidx Rs4 = ientry kf).
        { rewrite /G11 upd_ne; [| nz]. rewrite /G10 upd_ne; [| nz].
          rewrite /G9 upd_ne; [| nz]. rewrite /G8 upd_ne; [| nz].
          rewrite /G7 upd_ne; [| nz]. rewrite /G6 upd_ne; [| nz].
          rewrite /G5 upd_ne; [exact HG4s4 | nz]. }
        assert (HG11s6 : G11 !!! Regidx Rs6 = page_base (ud_root P)).
        { rewrite /G11 upd_ne; [| nz]. rewrite /G10 upd_ne; [| nz].
          rewrite /G9 upd_ne; [| nz]. rewrite /G8 upd_ne; [| nz].
          rewrite /G7 upd_ne; [| nz]. rewrite /G6 upd_ne; [| nz].
          rewrite /G5 upd_ne; [exact HG4s6 | nz]. }
        assert (HG11thr : forall r : mword 5, is_cs_idx r = true ->
                  r <> csp_rs1 -> r <> Rs0 -> r <> Rs1 -> r <> Rs2 ->
                  r <> Rs4 -> r <> Rs5 -> r <> Rs6 -> r <> Rs9 -> r <> Rs10 ->
                  r <> Rs11 -> G11 !!! Regidx r = m !!! Regidx r).
        { intros r Hr Nsp Ns0 Ns1 Ns2 Ns4 Ns5 Ns6 Ns9 Ns10 Ns11.
          rewrite /G11 upd_ne; [| congruence].
          rewrite /G10 upd_ne; [| regne].
          rewrite /G9 upd_ne; [| congruence].
          rewrite /G8 upd_ne; [| congruence].
          rewrite /G7 upd_ne; [| congruence].
          rewrite /G6 upd_ne; [| congruence].
          rewrite /G5 upd_ne; [| regne].
          exact (HG4thr r Hr Nsp Ns0 Ns1 Ns2 Ns4 Ns6). }
        (* ---- +0x0cc: c.j +0x12c -- into the phdr loop's BODY ---- *)
        assert (Htgt12c : add_vec (mword_of_int (KXB + 0xcc) : mword 64)
                  (sign_extend' 64
                     (sign_extend' 21 (concat_vec (mword_of_int 48 : mword 11)
                                                  ('b"0"))))
                = mword_of_int (KXB + 0x12c)) by pcw.
        iApply (wp_cj_s_sconf (mword_of_int (KXB + 0xcc))
                  (sign_extend' 21 (concat_vec (mword_of_int 48 : mword 11)
                                               ('b"0")))
                  G11 (K - 68)%nat true
                  ltac:(rewrite Htgt12c; vm_compute; reflexivity)
                  with "Hcg Hpc Hi0cc").
        iIntros (CID24 Hsq24). iNext. iIntros "Hcg Hpc".
        iEval (rewrite Htgt12c) in "Hpc".
        iDestruct ("Hpvbk" with "Htfc") as "Hpriv".
        iDestruct (cpu_own_transport CID4 CID24 0%nat true (proc_addr jp) true
                     ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
        iSpecialize ("Hcont12c" $! CID24 with "[%]"); [wp_next_chain |].
        iDestruct (wp_next_retarget CID0 CID24 true (proc_addr jp) _
                     ltac:(wp_next_chain) with "Hcont") as "Hcont".
        iApply ("Hcont12c" $! G11 ef P with "[-Hcont] Hcont").
        rewrite /kxc_at_12c.
        (* [kxc_at_12c] has NO threading conjunct -- see its header: by +0x12c
           no callee-saved register still holds kexec's entry value, so the
           clause would be vacuous here and FALSE on the back edge.  [HG11s1]
           and [HG11thr] are true at this ENTRY and deliberately dropped. *)
        iSplitR.
        { iPureIntro. split_and!;
            [exact HG11sp | exact HG11s0 | exact HG11s2
            | exact HG11s4 | exact HG11s5 | exact HG11s6 | exact HG11s9
            | exact HG11s10 | exact HG11s11 | exact HG11a3]. }
        iSplitR.
        { iPureIntro. split_and!;
            [exact Hk | exact Hib | exact Hn2 | exact Hu2 | exact Hal]. }
        iSplitR.
        { iPureIntro. split_and!;
            [ pose proof (eh_phnum_bound ef); lia
            | exact HPtfp
            | rewrite HPum; exact (um_below_empty _)
            | exact (um_covered_zero _) ]. }
        (* [iFrame] is NOT usable here: its [Frame] search unfolds [proc_priv]
           and the goal's big-ops, and this state carries a syscall-altitude
           block (measured: >19 GB and climbing before it was replaced).
           Name every conjunct instead -- durable-notes' rule for capstone
           contexts. *)
        iSplitL "Hpc"; [iExact "Hpc" |].
        iSplitL "Hcg"; [iExact "Hcg" |].
        (* the seam predicate names the held set as the literal [∅]. *)
        iEval (rewrite Hlkempty) in "Hcnt".
        iSplitL "Hcnt"; [iExact "Hcnt" |].
        iSplitL "Hopen"; [iExact "Hopen" |].
        iSplitL "Hlog"; [iExact "Hlog" |].
        iSplitL "Hirs"; [iExact "Hirs" |].
        iSplitL "Hbm"; [iExact "Hbm" |].
        iSplitL "Hins"; [iExact "Hins" |].
        iSplitL "Hbits"; [iExact "Hbits" |].
        iSplitL "Hbs"; [iExact "Hbs" |].
        iSplitR; [iExact "Hka" |].
        iSplitL "Hpt"; [iExact "Hpt" |].
        iSplitL "Hpriv"; [iExact "Hpriv" |].
        iSplitL "Hpath"; [iExact "Hpath" |].
        iSplitL "Hargv"; [iExact "Hargv" |].
        iSplitL "Hargs"; [iExact "Hargs" |].
        iSplitL "Helfb"; [iExact "Helfb" |].
        rewrite /kxc_frameB.
        iSplitL "Hf1"; [iExact "Hf1" |].
        iSplitL "Hf2"; [iExact "Hf2" |].
        iSplitL "Hf3"; [iExact "Hf3" |].
        iSplitL "Hf4"; [iExact "Hf4" |].
        iSplitL "Hf5"; [iExact "Hf5" |].
        iSplitL "Hf6"; [iExact "Hf6" |].
        iSplitL "Hf7"; [iExact "Hf7" |].
        iSplitL "Hf8"; [iExact "Hf8" |].
        iSplitL "Hf9"; [iExact "Hf9" |].
        iSplitL "Hf10"; [iExact "Hf10" |].
        iSplitL "Hf11"; [iExact "Hf11" |].
        iSplitL "Hf12"; [iExact "Hf12" |].
        iSplitL "Hf13"; [iExact "Hf13" |].
        iSplitL "Hust"; [iExact "Hust" |].
        iSplitL "Hph"; [iExact "Hph" |].
        iSplitL "Hf64"; [iExact "Hf64" |].
        iSplitL "Hf65"; [iExact "Hf65" |].
        iSplitL "Hf66"; [iExact "Hf66" |].
        iSplitL "Hf67"; [iExact "Hf67" | iExact "Hf68"].
    - (* ============ FAILURE: the +0x31c tail ============================
         [ppt_post]'s failure arm hands back [a0 = 0] and [kalloc_env ga None],
         and nothing was allocated -- so this exit owes nothing but the frame
         and the open inode, which phase A's [kxc_bad64] closes. ---------- *)
      assert (Hzero : eq_vec (rget G3 Ra0) (zero_reg : mword 64) = true).
      { rewrite Hrga0 HG3a0 Hptz. vm_compute; reflexivity. }
      assert (Htgt31c : add_vec (mword_of_int (KXB + 0x9a) : mword 64)
                (sign_extend' 64 (mword_of_int 642 : mword 13))
              = mword_of_int (KXB + 0x31c)) by pcw.
      iApply (wp_beqz_x0_taken_s_sconf (mword_of_int (KXB + 0x9a))
                (mword_of_int 642 : mword 13) Ra0 G3 (K - 68)%nat true
                ltac:(nz) Hzero
                ltac:(rewrite Htgt31c; vm_compute; reflexivity)
                with "Hcg Hpc Hi09a").
      iIntros (CID6 Hsq6). iNext. iIntros "Hcg Hpc".
      iEval (rewrite Htgt31c) in "Hpc".
      (* ---- +0x31c: c.ldsp s6,480(sp) -- slot 8 back into s6 ---- *)
      assert (Hpa8' : add_vec (G3 !!! Regidx csp_rs1)
                        (zero_extend' 64 (concat_vec (mword_of_int 60 : mword 6)
                                                     ('b"000")))
                      = pa_stk sp0 8).
      { rewrite HG3sp. apply (kxc_sp_slot sp0 8 60 _ ltac:(lia)).
        apply bv_eq; vm_compute; reflexivity. }
      iEval (rewrite -Hpa8') in "Hf8".
      iApply (wp_cldsp_s_sconf (mword_of_int (KXB + 0x31c))
                (mword_of_int 60 : mword 6) Rs6 G3 (K - 68)%nat
                (m !!! Regidx Rs6) true (dqm := DfracOwn 1)
                ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi31c Hf8").
      iIntros (CID7 Hsq7) "Hcg Hpc Hf8". iEval (rewrite Hpa8') in "Hf8".
      set (B1 := <[Regidx Rs6 := regval_into_reg (m !!! Regidx Rs6)]> G3).
      assert (HB1sp : B1 !!! Regidx csp_rs1 = pa_stk sp0 68)
        by (rewrite /B1 upd_ne; [exact HG3sp | nz]).
      assert (HB1s4 : B1 !!! Regidx Rs4 = ientry kf)
        by (rewrite /B1 upd_ne; [exact HG3s4 | nz]).
      assert (HB1thr : forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 ->
                r <> Rs0 -> r <> Rs1 -> r <> Rs2 -> r <> Rs4 ->
                B1 !!! Regidx r = m !!! Regidx r).
      { intros r Hr Nsp Ns0 Ns1 Ns2 Ns4.
        destruct (decide (r = Rs6)) as [-> | Ns6].
        - rewrite /B1 upd_eq. reflexivity.
        - rewrite /B1 upd_ne; [| congruence].
          exact (HG3thr r Hr Nsp Ns0 Ns1 Ns2 Ns4 Ns6). }
      assert (Hpp31e : add_vec_int (mword_of_int (KXB + 0x31c) : mword 64) 2
                       = mword_of_int (KXB + 0x31e)) by pcw.
      iEval (rewrite Hpp31e) in "Hpc".
      (* ---- +0x31e: c.j +0x64 -- into phase A's [bad:] tail ---- *)
      assert (Htgt64 : add_vec (mword_of_int (KXB + 0x31e) : mword 64)
                (sign_extend' 64
                   (sign_extend' 21 (concat_vec (mword_of_int 1699 : mword 11)
                                                ('b"0"))))
              = mword_of_int (KXB + 0x64)) by pcw.
      iApply (wp_cj_s_sconf (mword_of_int (KXB + 0x31e))
                (sign_extend' 21 (concat_vec (mword_of_int 1699 : mword 11)
                                             ('b"0")))
                B1 (K - 68)%nat true
                ltac:(rewrite Htgt64; vm_compute; reflexivity)
                with "Hcg Hpc Hi31e").
      iIntros (CID8 Hsq8). iNext. iIntros "Hcg Hpc".
      iEval (rewrite Htgt64) in "Hpc".
      iDestruct ("Hpvbk" with "Htfc") as "Hpriv".
      iDestruct (cpu_own_transport CID4 CID8 0%nat true (proc_addr jp) true
                   ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
      iDestruct "Hopen" as "(#Hslkk & Hslkd & Hslpid & Hdep & Hidev & Hiinum &
                             Hivalid & Hload & #Hity & Hkeep)".
      (* [kxc_bad64] is applied AT [CID8] (its [sie_cap_gpr] premise pins its
         own [CID0] from "Hcg"), so kexec's exit -- still anchored at the
         section's [CID0] -- has to be re-anchored there.  The crossing fact
         goes by NAME (durable-notes.md). *)
      assert (Hcr8 : true = false \/ proc_addr jp = zero_reg ->
                     (CID8 : CPU) = (CID0 : CPU)) by wp_next_chain.
      iDestruct (wp_next_retarget CID0 CID8 true (proc_addr jp) _ Hcr8
                   with "Hcont") as "Hcont".
      iApply (A.kxc_bad64 gs jp gl gu gd gk pd pav pu bn g gfs gi cn gtl
                gilf gislf ga gf cov logstart bmapstart inodestart nib size
                dev used used2 kf qf sf gyf inumf dnf bmf n2
                plen pfun na avf alen aslen afun pidv V dqb dqs dqa
                m B1 K lks sp0 ra0 s00 s10 s20 pv av
                HK Hk Hlg Hsz Hbm0 Hbmc Hbml Hins0 Hibc Hibl Hib Hcovb Hn2
                Hjp Hgs Hu2 Hsp Hra Hs0 Hs1 Hs2 HB1sp HB1s4 HB1thr
                with "Hcg Hcnt Htext Hpc Hfab Hslkk Hslkd Hslpid Hdep
                      Hidev Hiinum Hivalid Hload Hity Hkeep Hbm Hins Hbits
                      Hka Hpriv Hpath Hargv Hargs Hbs Hirs Hlog [-Hcont]
                      Hcont").
      rewrite /kxc_frameA6.
      iDestruct (kxc_mid_join sp0 with "Hust Helf Hph") as "Hmid".
      iSplitL "Hf1"; [iExact "Hf1" |].
      iSplitL "Hf2"; [iExact "Hf2" |].
      iSplitL "Hf3"; [iExact "Hf3" |].
      iSplitL "Hf4"; [iExact "Hf4" |].
      iSplitL "Hf5"; [by iExists v5 |].
      iSplitL "Hf6"; [iExact "Hf6" |].
      iSplitL "Hf7"; [by iExists v7 |].
      iSplitL "Hf8"; [by iExists (m !!! Regidx Rs6) |].
      iSplitL "Hf9"; [by iExists v9 |].
      iSplitL "Hf10"; [by iExists v10 |].
      iSplitL "Hf11"; [by iExists v11 |].
      iSplitL "Hf12"; [by iExists v12 |].
      iSplitL "Hf13"; [by iExists v13 |].
      iSplitL "Hmid"; [iExact "Hmid" |].
      iSplitL "Hf64"; [iExact "Hf64" |].
      iSplitL "Hf65"; [iExact "Hf65" |].
      iSplitL "Hf66"; [iExact "Hf66" |].
      iSplitL "Hf67"; [by iExists v67 | iExact "Hf68"].
  Qed.

End KexecBBody.

End KexecBProof.
