(* ProofKexec.v -- kexec() WHOLE: the four phases composed into
   SpecKexec.wp_kexec_sconf_body, and the only place they meet.

   Every instruction of kexec is proven elsewhere; this file does the
   plumbing and nothing else.  The chain, and where each seam is stated:

     entry            SpecKexec.wp_kexec_sconf_body      pc = kexec + 0
       PA.kxc_phaseA                                     .. +0x090
     +0x090           the eight-conjunct register block A publishes
       PB.kxc_b1                                         .. +0x0cc / +0x1a2
     +0x1a2 / +0x12c  ProofKexecSeam.kxc_at_1a2 / kxc_at_12c
       PB3.kxc_b2z / PB3.kxc_b2                          .. +0x1ae
     +0x1ae           ProofKexecSeam.kxc_at_1ae
       PC.kxc_c_setup                                    .. +0x21a / +0x272
     +0x21a           ProofKexecSeam.kxc_at_21a
       PC.kxc_argv_loop                                  .. +0x272
     +0x272           ProofKexecSeam.kxc_at_272
       PC.kxc_c_close                                    .. +0x2a6
     +0x2a6           ProofKexecSeam.kxc_at_2a6
       PD.kxd_phaseD                                     .. ret

   THE ONE THING THAT MAKES THE COMPOSITION WORK IS THAT EVERY SEAM HANDS
   THE CALLER'S EXIT BACK.  A [wp_next] continuation is LINEAR, so a block
   that owns a [bad:] path and also publishes a successor state would
   consume the single exit the caller has and leave the successor with
   none; each phase lemma therefore takes the exit once and returns it
   inside its own output (durable-notes' "CHAINING TWO HALVES").  Reading
   an [iApply] below: the exit travels as [Hcont] through every step and is
   spent exactly once, by whichever block actually returns.

   THREE PLUMBING FACTS ARE NOT FREE, and they are all this file has to
   prove for itself:

   - [used] SHRINKS ACROSS THE PHASES.  Phase A hands out a [used2] with
     [used2 ⊆ used] and phase B a [used3 ⊆ used]; the later blocks state
     their exit's bitmap clause against the CURRENT set, while the
     contract's is against the entry one.  [kxc_exit_weaken] is that one
     transport, applied once, at the point where [used3] first appears.
   - THE ARGV LOOP IS ENTERED ONLY AT [c < na].  Its own measure argument
     needs that, and the loop head cannot say it: what says it is the head's
     [avf c <> 0] against the contract's [avf na = 0].
   - [oldsz] AND THE 8192 BOUND COME OUT OF PHASE C'S SETUP, not out of the
     contract, which is why [kxc_c_setup]'s output publishes both.

   The functor arguments are kexec's sixteen callees.  [PPT] is the
   GENERAL [PROC_PAGETABLE_GEN], not [PROC_PAGETABLE]: kexec runs at
   [kalloc_env ga None] and tests proc_pagetable's result against 0, so it
   is the caller that can use the uncounted arm (projects/kexec.md, "What
   is NOT blocked"). *)
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
Require Import WpNext.
Require Import WpMmodeLeafBase.
Require Import SmodeCore.
Require Import StackOwn.
Require Import CalleeSaved.
Require Import InstrBytes.
Require Import KernelText.
Require Import IntrDefs.
Require Import CpuOwn.
Require Import WpLock.
Require Import FdSlots.
Require Export SwtchCtx.
Require Import WpUart.
Require Import FsCrash.
Require Import InodeRegion.
Require Import IcacheEscrow.
Require Import ByteBuf.
Require Import ProcGeom.
Require Import ProcInv.
Require Import DiskPtsto.
Require Import BioDefs.
Require Import FsBlocks LogInv.
Require Import BitmapInv.
Require Import InodeInv.
Require Import IrefSlots.
Require Import KallocInv.
Require Import KvmSpec.
Require Import FileInvDefs.
Require Import IrefSlots.
Require Import ProcAvail.
Require Import DiskInv.
Require Import UserPtTree.
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
Require Import SpecProcPagetable.
Require Import SpecWalkaddr.
Require Import SpecFlags2perm.
Require Import SpecUvmalloc.
Require Import SpecUvmclear.
Require Import SpecStrlen.
Require Import SpecCopyout.
Require Import SpecSafestrcpy.
Require Import ProofKexecSeam.
Require Import ProofKexecA.
Require Import ProofKexecB.
Require Import SpecPanic.
Require Import ProofKexecB2.
Require Import ProofKexecB3.
Require Import ProofKexecC.
Require Import ProofKexecD.
From Kernel Require KernelSyms.
Require Import ProcAvail.
Local Open Scope Z_scope.

(* A syscall-altitude goal carries [ProcInv.tf_page]'s 4096-conjunct big-op;
   printing one takes tens of minutes, so a one-line mistake reads as a hang.
   durable-notes.md's rule. *)
Set Printing Depth 40.

Notation KX := KernelSyms.kexec (only parsing).

Module KexecProof (Myproc : MYPROC) (BeginOp : BEGIN_OP) (Namei : NAMEI)
                  (Ilock : ILOCK) (Readi : READI) (Iunlockput : IUNLOCKPUT)
                  (EndOp : END_OP) (PPT : PROC_PAGETABLE_GEN)
                  (PFP : PROC_FREEPAGETABLE) (Walkaddr : WALKADDR)
                  (Flags2perm : FLAGS2PERM) (Uvmalloc : UVMALLOC)
                  (Uvmclear : UVMCLEAR) (Strlen : STRLEN) (Copyout : COPYOUT)
                  (SS : SAFESTRCPY) (PN : PANIC) : KEXEC.

Module PA := ProofKexecA.KexecAProof Myproc BeginOp Namei Ilock Readi
                                     Iunlockput EndOp.
Module PB := ProofKexecB.KexecBProof Myproc BeginOp Namei Ilock Readi
                                     Iunlockput EndOp PPT.
Module PB2 := ProofKexecB2.KexecB2Proof Myproc BeginOp Namei Ilock Readi
                                        Iunlockput EndOp PFP Walkaddr PN.
Module PB3 := ProofKexecB3.KexecB3Proof Myproc BeginOp Namei Ilock Readi
                                        Iunlockput EndOp PFP Walkaddr
                                        Flags2perm Uvmalloc PB2.
Module PC := ProofKexecC.KexecCProof Myproc BeginOp Namei Ilock Readi
                                     Iunlockput EndOp PFP Walkaddr Flags2perm
                                     Uvmalloc Uvmclear Strlen Copyout.
Module PD := ProofKexecD.KexecDProof PFP SS.

(* ===================================================================== *)
(*  PHASES C AND D, as one lemma over phase B's output state.             *)
(*                                                                        *)
(*  Its own section, and [CID0] a LEMMA binder rather than a section       *)
(*  variable: phase B's two paths reach +0x1ae at two different harts, a   *)
(*  dozen [wp_next]s past the entry one, and a [Local Lemma] declared      *)
(*  under a section [Context `{CID0 : CpuId}] bakes THAT hart into its own *)
(*  statement (projects/kexec.md's note at [kxc_c_exit_m1]).               *)
(* ===================================================================== *)
Section KexecTail.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !fileG Σ, !kallocG Σ,
            !bioG Σ, !diskGhostG Σ, !uartGhostG Σ, !fsLogG Σ, !logG Σ,
            !fsCrashG Σ, !irefslotG Σ, !pavG Σ, !iregG Σ}.
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

  (* ------------------------------------------------------------------ *)
  (*  THE EXIT, AT A NARROWER BITMAP SET.  Phases A/B/C-setup state the   *)
  (*  contract's own [used' ⊆ used]; the argv loop, the closing copyout   *)
  (*  and phase D state [used' ⊆ used3] against the set phase B left.     *)
  (*  Since [used3 ⊆ used] the two are the same obligation one            *)
  (*  transitivity apart -- but they are DIFFERENT propositions, so the   *)
  (*  exit has to be transported rather than framed.                      *)
  (* ------------------------------------------------------------------ *)
  Local Lemma kxc_exit_weaken `{CID0 : CpuId}
      (jp : nat) (bn : bio_names) (gfs : fs_names) (ga gf : gname)
      (cov : gset Z) (logstart bmapstart inodestart : Z) (size : Z)
      (used usedw : gset Z)
      (plen : nat) (pfun : nat -> bv 8)
      (na : nat) (avf : nat -> mword 64) (alen aslen : nat -> nat)
      (afun : nat -> nat -> bv 8)
      (pidv : mword 32) (V : pprivate) (dqb dqs dqa : dfrac)
      (m : regfile) (K : nat) (ra0 pv av : mword 64) :
    usedw ⊆ used ->
    wp_next true (proc_addr jp) (fun (CID : CpuId) =>
      ∀ (mf : regfile) (used' : gset Z) (V' : pprivate)
        (entry spv szv' : mword 64),
          ⌜callee_saved m mf⌝ -∗
          ⌜kexec_ok V V' (mf !!! Regidx Ra0) entry spv szv' na alen⌝ -∗
          sie_cap_gpr KT1 mf K true (proc_addr jp) -∗
          cpu_own 0 true (proc_addr jp) true ∅ -∗
          pc_is (ret_pc ra0) -∗
          sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
          sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
          ⌜used' ⊆ used⌝ -∗
          bitmap_res gfs bmapstart cov logstart size used' -∗
          kalloc_env ga None -∗
          proc_priv gf (proc_addr jp) pidv V' -∗
          ([∗ list] i ∈ seq 0 (S plen), pa_add pv i ↦ₘ[KT1] pfun i) -∗
          ([∗ list] i ∈ seq 0 (S na), pa_add av (8 * i) ↦₈[KT1]{dqa} avf i) -∗
          ([∗ list] i ∈ seq 0 na,
             [∗ list] j ∈ seq 0 (aslen i), pa_add (avf i) j ↦ₘ afun i j) -∗
          bslots bn 3 -∗
          iref_slots 2 -∗
          WP (Loop : expr riscv_lang)) -∗
    wp_next true (proc_addr jp) (fun (CID : CpuId) =>
      ∀ (mf : regfile) (used' : gset Z) (V' : pprivate)
        (entry spv szv' : mword 64),
          ⌜callee_saved m mf⌝ -∗
          ⌜kexec_ok V V' (mf !!! Regidx Ra0) entry spv szv' na alen⌝ -∗
          sie_cap_gpr KT1 mf K true (proc_addr jp) -∗
          cpu_own 0 true (proc_addr jp) true ∅ -∗
          pc_is (ret_pc ra0) -∗
          sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
          sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
          ⌜used' ⊆ usedw⌝ -∗
          bitmap_res gfs bmapstart cov logstart size used' -∗
          kalloc_env ga None -∗
          proc_priv gf (proc_addr jp) pidv V' -∗
          ([∗ list] i ∈ seq 0 (S plen), pa_add pv i ↦ₘ[KT1] pfun i) -∗
          ([∗ list] i ∈ seq 0 (S na), pa_add av (8 * i) ↦₈[KT1]{dqa} avf i) -∗
          ([∗ list] i ∈ seq 0 na,
             [∗ list] j ∈ seq 0 (aslen i), pa_add (avf i) j ↦ₘ afun i j) -∗
          bslots bn 3 -∗
          iref_slots 2 -∗
          WP (Loop : expr riscv_lang)).
  Proof.
    intros Hsub. iIntros "H" (CID) "%Hs".
    iIntros (mf used' V' entry spv szv')
            "%Hcs %Hok Hcg Hcnt Hpc Hbm Hins %Hu Hbits Hka Hpriv
             Hpath Hargv Hargs Hbs Hirs".
    iSpecialize ("H" $! CID with "[%]"); [exact Hs |].
    iApply ("H" $! mf used' V' entry spv szv'
              with "[%] [%] Hcg Hcnt Hpc Hbm Hins [%] Hbits Hka Hpriv
                    Hpath Hargv Hargs Hbs Hirs");
      [ exact Hcs | exact Hok | set_solver ].
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  +0x272 .. ret -- the closing copyout and the commit.                *)
  (*  Both of the argv loop's entries land here (the loop's natural exit  *)
  (*  and the [argv[0] = NULL] skip), so it is a lemma rather than two    *)
  (*  copies of the same two [iApply]s.                                   *)
  (* ------------------------------------------------------------------ *)
  Local Lemma kxc_d_tail `{CID0 : CpuId}
      (jp : nat) (bn : bio_names) (gfs : fs_names) (ga gf : gname)
      (cov : gset Z) (logstart bmapstart inodestart : Z)
      (size : Z) (used3 : gset Z)
      (plen : nat) (pfun : nat -> bv 8)
      (na : nat) (avf : nat -> mword 64) (alen aslen : nat -> nat)
      (afun : nat -> nat -> bv 8)
      (pidv : mword 32) (V : pprivate) (dqb dqs dqa : dfrac)
      (m M : regfile) (K : nat)
      (sp0 ra0 s00 s10 s20 pv av : mword 64)
      (w5 w6 w7 w8 w9 w10 w11 w12 w13 w67 : mword 64)
      (ef : nat -> bv 8) (P : uptd) (sz1 : mword 64) (c : nat) :
    (K_kexec <= K)%nat ->
    bb_cstr pfun plen ->
    (na < MAXARG)%nat ->
    (8192 <= uint sz1)%Z ->
    (forall i, (i < na)%nat -> avf i <> (mword_of_int 0 : mword 64)) ->
    (forall i, (i < 8)%nat ->
       is_aligned_paddr (Physaddr (pa_stk sp0 (54 - i))) 8 = true) ->
    m !!! Regidx csp_rs1 = sp0 -> m !!! Regidx Rra = ra0 ->
    m !!! Regidx Rs0 = s00 -> m !!! Regidx Rs1 = s10 -> m !!! Regidx Rs2 = s20 ->
    m !!! Regidx Rs3 = w5 -> m !!! Regidx Rs4 = w6 -> m !!! Regidx Rs5 = w7 ->
    m !!! Regidx Rs6 = w8 -> m !!! Regidx Rs7 = w9 -> m !!! Regidx Rs8 = w10 ->
    m !!! Regidx Rs9 = w11 -> m !!! Regidx Rs10 = w12 -> m !!! Regidx Rs11 = w13 ->
    kernel_text -∗
    kxc_at_272 jp bn gfs ga gf cov logstart bmapstart inodestart size used3
               plen pfun na avf alen aslen afun pidv V dqb dqs dqa
               M K sp0 ra0 s00 s10 s20 pv av
               w5 w6 w7 w8 w9 w10 w11 w12 w13 w67 ef P (pv_sz V) sz1 c -∗
    wp_next true (proc_addr jp) (fun (CID : CpuId) =>
      ∀ (mf : regfile) (used' : gset Z) (V' : pprivate)
        (entry spv szv' : mword 64),
          ⌜callee_saved m mf⌝ -∗
          ⌜kexec_ok V V' (mf !!! Regidx Ra0) entry spv szv' na alen⌝ -∗
          sie_cap_gpr KT1 mf K true (proc_addr jp) -∗
          cpu_own 0 true (proc_addr jp) true ∅ -∗
          pc_is (ret_pc ra0) -∗
          sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
          sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
          ⌜used' ⊆ used3⌝ -∗
          bitmap_res gfs bmapstart cov logstart size used' -∗
          kalloc_env ga None -∗
          proc_priv gf (proc_addr jp) pidv V' -∗
          ([∗ list] i ∈ seq 0 (S plen), pa_add pv i ↦ₘ[KT1] pfun i) -∗
          ([∗ list] i ∈ seq 0 (S na), pa_add av (8 * i) ↦₈[KT1]{dqa} avf i) -∗
          ([∗ list] i ∈ seq 0 na,
             [∗ list] j ∈ seq 0 (aslen i), pa_add (avf i) j ↦ₘ afun i j) -∗
          bslots bn 3 -∗
          iref_slots 2 -∗
          WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros HK Hcstr Hnamax Hsz1ge Havf_nz Hal Hmsp Hmra Hms0 Hms1 Hms2
           Hmw5 Hmw6 Hmw7 Hmw8 Hmw9 Hmw10 Hmw11 Hmw12 Hmw13.
    iIntros "#Htext Hst Hcont".
    iApply (PC.kxc_c_close (CID0 := CID0) jp bn gfs ga gf cov logstart
              bmapstart inodestart size used3 plen pfun na avf alen aslen afun
              pidv V dqb dqs dqa m M K sp0 ra0 s00 s10 s20 pv av
              w5 w6 w7 w8 w9 w10 w11 w12 w13 w67 ef P (pv_sz V) sz1 c
              HK Hsz1ge Hal Hmsp Hmra Hms0 Hms1 Hms2
              Hmw5 Hmw6 Hmw7 Hmw8 Hmw9 Hmw10 Hmw11 Hmw12 Hmw13
              with "Htext Hst Hcont []").
    iIntros (CIDd) "%Hsd". iIntros (Md Pd) "Hst2a6 Hcont".
    iApply (PD.kxd_phaseD (CID0 := CIDd) jp bn gfs ga gf cov logstart
              bmapstart inodestart size used3 plen pfun na avf alen aslen afun
              pidv V dqb dqs dqa m Md K sp0 ra0 s00 s10 s20 pv av
              w5 w6 w7 w8 w9 w10 w11 w12 w13 w67 ef Pd sz1 c
              HK Hcstr Hnamax Hsz1ge Havf_nz Hal Hmsp Hmra Hms0 Hms1 Hms2
              Hmw5 Hmw6 Hmw7 Hmw8 Hmw9 Hmw10 Hmw11 Hmw12 Hmw13
              with "Htext Hst2a6 Hcont").
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  +0x1ae .. ret -- PHASES C AND D, over phase B's output state.       *)
  (* ------------------------------------------------------------------ *)
  Local Lemma kxc_cd `{CID0 : CpuId}
      (jp : nat) (bn : bio_names) (gfs : fs_names) (ga gf : gname)
      (cov : gset Z) (logstart bmapstart inodestart : Z)
      (size : Z) (used used3 : gset Z)
      (plen : nat) (pfun : nat -> bv 8)
      (na : nat) (avf : nat -> mword 64) (alen aslen : nat -> nat)
      (afun : nat -> nat -> bv 8)
      (pidv : mword 32) (V : pprivate) (dqb dqs dqa : dfrac)
      (m M : regfile) (K : nat)
      (sp0 ra0 s00 s10 s20 pv av : mword 64)
      (w5 w6 w7 w8 w9 w10 w11 w12 w13 w67 : mword 64)
      (ef : nat -> bv 8) (P : uptd) (szv : mword 64) :
    (K_kexec <= K)%nat ->
    bb_cstr pfun plen ->
    (na < MAXARG)%nat ->
    (forall i, (i < na)%nat -> avf i <> (mword_of_int 0 : mword 64)) ->
    avf na = (mword_of_int 0 : mword 64) ->
    (forall i, (i < na)%nat -> (alen i < aslen i)%nat) ->
    (forall i, (i < na)%nat -> bb_cstr (afun i) (alen i)) ->
    (forall i, (i < na)%nat -> (Z.of_nat (alen i) < 4096)%Z) ->
    m !!! Regidx csp_rs1 = sp0 -> m !!! Regidx Rra = ra0 ->
    m !!! Regidx Rs0 = s00 -> m !!! Regidx Rs1 = s10 -> m !!! Regidx Rs2 = s20 ->
    m !!! Regidx Rs3 = w5 -> m !!! Regidx Rs4 = w6 -> m !!! Regidx Rs5 = w7 ->
    m !!! Regidx Rs6 = w8 -> m !!! Regidx Rs7 = w9 -> m !!! Regidx Rs8 = w10 ->
    m !!! Regidx Rs9 = w11 -> m !!! Regidx Rs10 = w12 -> m !!! Regidx Rs11 = w13 ->
    kernel_text -∗
    kxc_at_1ae jp bn gfs ga gf cov logstart bmapstart inodestart size
               used used3 plen pfun na avf aslen afun pidv V dqb dqs dqa
               M K sp0 ra0 s00 s10 s20 pv av
               w5 w6 w7 w8 w9 w10 w11 w12 w13 w67 ef P szv -∗
    wp_next true (proc_addr jp) (fun (CID : CpuId) =>
      ∀ (mf : regfile) (used' : gset Z) (V' : pprivate)
        (entry spv szv' : mword 64),
          ⌜callee_saved m mf⌝ -∗
          ⌜kexec_ok V V' (mf !!! Regidx Ra0) entry spv szv' na alen⌝ -∗
          sie_cap_gpr KT1 mf K true (proc_addr jp) -∗
          cpu_own 0 true (proc_addr jp) true ∅ -∗
          pc_is (ret_pc ra0) -∗
          sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
          sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
          ⌜used' ⊆ used⌝ -∗
          bitmap_res gfs bmapstart cov logstart size used' -∗
          kalloc_env ga None -∗
          proc_priv gf (proc_addr jp) pidv V' -∗
          ([∗ list] i ∈ seq 0 (S plen), pa_add pv i ↦ₘ[KT1] pfun i) -∗
          ([∗ list] i ∈ seq 0 (S na), pa_add av (8 * i) ↦₈[KT1]{dqa} avf i) -∗
          ([∗ list] i ∈ seq 0 na,
             [∗ list] j ∈ seq 0 (aslen i), pa_add (avf i) j ↦ₘ afun i j) -∗
          bslots bn 3 -∗
          iref_slots 2 -∗
          WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros HK Hcstr Hnamax Havf_nz Havf_na Halen_b Halen_c Halen_4
           Hmsp Hmra Hms0 Hms1 Hms2
           Hmw5 Hmw6 Hmw7 Hmw8 Hmw9 Hmw10 Hmw11 Hmw12 Hmw13.
    iIntros "#Htext Hst Hcont".
    (* the two pure facts the blocks past [kxc_c_setup] take as PREMISES --
       the bitmap-set inclusion and the ustack's eight-alignment -- are
       conjuncts of the entry state, so read them off and put the state
       back together.  No [iFrame]: at this altitude it does not terminate
       (projects/kexec.md). *)
    rewrite /kxc_at_1ae.
    iDestruct "Hst" as "(%Hregs & %Hpure2 & %Hpure3 & Hrest)".
    destruct Hpure2 as [Hu3 Hal].
    iAssert (kxc_at_1ae jp bn gfs ga gf cov logstart bmapstart inodestart size
               used used3 plen pfun na avf aslen afun pidv V dqb dqs dqa
               M K sp0 ra0 s00 s10 s20 pv av
               w5 w6 w7 w8 w9 w10 w11 w12 w13 w67 ef P szv)
      with "[Hrest]" as "Hst".
    { rewrite /kxc_at_1ae.
      iSplitR; [iPureIntro; exact Hregs |].
      iSplitR; [iPureIntro; exact (conj Hu3 Hal) |].
      iSplitR; [iPureIntro; exact Hpure3 |].
      iExact "Hrest". }
    iApply (PC.kxc_c_setup (CID0 := CID0) jp bn gfs ga gf cov logstart
              bmapstart inodestart size used used3 plen pfun na avf alen aslen
              afun pidv V dqb dqs dqa m M K sp0 ra0 s00 s10 s20 pv av
              w5 w6 w7 w8 w9 w10 w11 w12 w13 w67 ef P szv
              HK Hmsp Hmra Hms0 Hms1 Hms2
              Hmw5 Hmw6 Hmw7 Hmw8 Hmw9 Hmw10 Hmw11 Hmw12 Hmw13
              Halen_b Halen_c Halen_4 Havf_na
              with "Htext Hst Hcont []").
    iIntros (CID1) "%Hs1". iIntros (M1 P1 sz1) "%Hsz1ge Hdisj Hcont".
    (* from here down the exit's bitmap clause is against [used3] *)
    iDestruct (kxc_exit_weaken (CID0 := CID1) jp bn gfs ga gf cov logstart
                 bmapstart inodestart size used used3 plen pfun na avf alen
                 aslen afun pidv V dqb dqs dqa m K ra0 pv av Hu3
                 with "Hcont") as "Hcont".
    iDestruct "Hdisj" as "[Hloop | Hskip]".
    - (* argv[0] <> NULL: run the loop from c = 0 *)
      (* [0 < na] is not a conjunct of the head and cannot be: what says it
         is the head's own [avf 0 <> 0] against the contract's [avf na = 0]. *)
      rewrite /kxc_at_21a.
      iDestruct "Hloop" as "(%Hq1 & %Hq2 & %Hq3 & Hrest2)".
      assert (H0na : (0 < na)%nat).
      { destruct Hq2 as (_ & _ & Hnz & _).
        destruct (Nat.eq_dec 0 na) as [Heq | Hne];
          [ exfalso; apply Hnz; rewrite Heq; exact Havf_na | lia ]. }
      iAssert (kxc_at_21a jp bn gfs ga gf cov logstart bmapstart inodestart
                 size used3 plen pfun na avf alen aslen afun pidv V dqb dqs dqa
                 M1 K sp0 ra0 s00 s10 s20 pv av
                 w5 w6 w7 w8 w9 w10 w11 w12 w13 w67 ef P1 (pv_sz V) sz1 0)
        with "[Hrest2]" as "Hloop".
      { rewrite /kxc_at_21a.
        iSplitR; [iPureIntro; exact Hq1 |].
        iSplitR; [iPureIntro; exact Hq2 |].
        iSplitR; [iPureIntro; exact Hq3 |].
        iExact "Hrest2". }
      iApply (PC.kxc_argv_loop (CID0 := CID1) jp bn gfs ga gf cov logstart
                bmapstart inodestart size used3 plen pfun na avf alen aslen
                afun pidv V dqb dqs dqa m K sp0 ra0 s00 s10 s20 pv av
                w5 w6 w7 w8 w9 w10 w11 w12 w13 w67 ef (pv_sz V) sz1
                HK Halen_b Halen_c Halen_4 Havf_na Hsz1ge Hnamax Hal
                Hmsp Hmra Hms0 Hms1 Hms2
                Hmw5 Hmw6 Hmw7 Hmw8 Hmw9 Hmw10 Hmw11 Hmw12 Hmw13
                na M1 P1 0%nat H0na ltac:(lia)
                with "Htext Hloop Hcont []").
      iIntros (CID2) "%Hs2". iIntros (M2 P2 c2) "Hst272 Hcont".
      iApply (kxc_d_tail (CID0 := CID2) jp bn gfs ga gf cov logstart bmapstart
                inodestart size used3 plen pfun na avf alen aslen afun pidv V
                dqb dqs dqa m M2 K sp0 ra0 s00 s10 s20 pv av
                w5 w6 w7 w8 w9 w10 w11 w12 w13 w67 ef P2 sz1 c2
                HK Hcstr Hnamax Hsz1ge Havf_nz Hal Hmsp Hmra Hms0 Hms1 Hms2
                Hmw5 Hmw6 Hmw7 Hmw8 Hmw9 Hmw10 Hmw11 Hmw12 Hmw13
                with "Htext Hst272 Hcont").
    - (* argv[0] = NULL: the loop is skipped, and c = 0 *)
      iApply (kxc_d_tail (CID0 := CID1) jp bn gfs ga gf cov logstart bmapstart
                inodestart size used3 plen pfun na avf alen aslen afun pidv V
                dqb dqs dqa m M1 K sp0 ra0 s00 s10 s20 pv av
                w5 w6 w7 w8 w9 w10 w11 w12 w13 w67 ef P1 sz1 0
                HK Hcstr Hnamax Hsz1ge Havf_nz Hal Hmsp Hmra Hms0 Hms1 Hms2
                Hmw5 Hmw6 Hmw7 Hmw8 Hmw9 Hmw10 Hmw11 Hmw12 Hmw13
                with "Htext Hskip Hcont").
  Qed.

End KexecTail.

(* ===================================================================== *)
(*  THE CONTRACT.                                                         *)
(* ===================================================================== *)
Section KexecMain.
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
  Notation Ra1 := (mword_of_int 11 : mword 5).

  Lemma wp_kexec_sconf
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
      (alen aslen : nat -> nat) (afun : nat -> nat -> bv 8)
      (pidv : mword 32) (V : pprivate)
      (dqb dqs dqa : dfrac)
      (m : regfile) (K : nat) (eb : bool)
      (b : bool) (lks : gset string) :
    wp_kexec_sconf_body gs jp gl gu gd gk pd pav pu bn g gfs gi cn gtl
                        ga gf cov logstart bmapstart inodestart nib
                        size dev used plen pfun na avf alen aslen afun
                        pidv V dqb dqs dqa m K eb b lks.
  Proof.
    rewrite /wp_kexec_sconf_body.
    intros HK Hdev Hnib Htlog Htist Hroot Hnib0 Hlg Hsz Hbm0 Hbmc Hbml Hins0
           Hcovb Hiregb Hcstr Hplen Havf_nz Havf_na Hnamax
           Halen_b Halen_c Halen_4 Hjp Hgs Hb Heb.
    subst b eb.
    iIntros "Hcg Hcnt #Htext Hpc #Hfab #Hka Hbm Hins Hbits Hpriv
             Hpath Hargv Hargs Hbs Hirs Hcont".
    (* depth 0 pins the held-lock set empty, which is what every seam past
       phase A spells as the literal [∅] (SpecKexec.v's note on the
       interrupt index: once [b = true] the other three are theorems). *)
    iDestruct (cpu_own_zero_empty with "Hcnt") as "[%Hlk Hcnt]". subst lks.
    (* ---- PHASE A: +0x000 .. +0x090, and two of the eight [bad:] tails ---- *)
    iApply (PA.kxc_phaseA (CID0 := CID0) gs jp gl gu gd gk pd pav pu bn g gfs
              gi cn gtl ga gf cov logstart bmapstart inodestart nib size dev
              used plen pfun na avf alen aslen afun pidv V dqb dqs dqa
              m K true true ∅
              (m !!! Regidx csp_rs1) (m !!! Regidx Rra) (m !!! Regidx Rs0)
              (m !!! Regidx Rs1) (m !!! Regidx Rs2)
              (m !!! Regidx Ra0) (m !!! Regidx Ra1)
              HK Hdev Hnib Htlog Htist Hroot Hnib0 Hlg Hsz Hbm0 Hbmc Hbml
              Hins0 Hcovb Hiregb Hcstr Hplen Hjp Hgs eq_refl
              eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
              with "Hcg Hcnt Htext Hpc Hfab Hka Hbm Hins Hbits Hpriv
                    Hpath Hargv Hargs Hbs Hirs Hcont []").
    iIntros (CIDa) "%Hsa".
    iIntros (M90 kf qf sf inumf dnf bmf gilf gislf gyf n2 used2)
            "%Hregs90 %Hn2u Hpc Hcg Hcnt Hslk Hslked Hslpid Hdep Hidev Hiinum
             Hival Hloaded Hity Hfrz Hiref Hlog Hirs Hbm Hins Hbits Hbs #Hka2
             Hpriv
             Hpath Hargv Hargs Hframe Hcont".
    destruct Hregs90 as (HM90sp & HM90s0 & HM90s1 & HM90s2 & HM90s4 & Hkf &
                         Hinumf & HM90thr).
    destruct Hn2u as [Hn2 Hu2].
    (* the nine resources phase B threads whole and never looks inside *)
    iAssert (kxc_open gfs gi cn cov logstart dev pidv kf qf sf gyf inumf dnf
                      bmf gilf gislf)
      with "[Hslk Hslked Hslpid Hdep Hidev Hiinum Hival Hloaded Hity Hfrz
             Hiref]"
      as "Hopen".
    { rewrite /kxc_open.
      iSplitL "Hslk"; [iExact "Hslk" |].
      iSplitL "Hslked"; [iExact "Hslked" |].
      iSplitL "Hslpid"; [iExact "Hslpid" |].
      iSplitL "Hdep"; [iExact "Hdep" |].
      iSplitL "Hidev"; [iExact "Hidev" |].
      iSplitL "Hiinum"; [iExact "Hiinum" |].
      iSplitL "Hival"; [iExact "Hival" |].
      iSplitL "Hloaded"; [iExact "Hloaded" |].
      iSplitL "Hity"; [iExact "Hity" |].
      iSplitL "Hfrz"; [iExact "Hfrz" | iExact "Hiref"]. }
    (* ---- PHASE B1: +0x090 .. +0x0cc, plus the +0x31c tail ---- *)
    iApply (PB.kxc_b1 (CID0 := CIDa) gs jp gl gu gd gk pd pav pu bn g gfs gi cn
              gtl ga gf cov logstart bmapstart inodestart nib size dev
              used used2 kf qf sf gyf inumf dnf bmf gilf gislf n2
              plen pfun na avf alen aslen afun pidv V dqb dqs dqa
              m M90 K true true ∅
              (m !!! Regidx csp_rs1) (m !!! Regidx Rra) (m !!! Regidx Rs0)
              (m !!! Regidx Rs1) (m !!! Regidx Rs2)
              (m !!! Regidx Ra0) (m !!! Regidx Ra1)
              HK Hlg Hsz Hbm0 Hbmc Hbml Hins0 Hcovb Hiregb Hjp Hgs eq_refl
              Hu2 Hkf Hinumf Hn2 eq_refl eq_refl eq_refl eq_refl eq_refl
              HM90sp HM90s0 HM90s1 HM90s2 HM90s4 HM90thr
              with "Htext Hfab Hpc Hcg Hcnt Hopen Hlog Hirs Hbm Hins
                    Hbits Hbs Hka2 Hpriv Hpath Hargv Hargs Hframe Hcont [] []").
    - (* ---- OUTPUT 1: elf.phnum = 0, the phdr loop is skipped ---- *)
      iIntros (CIDz) "%Hsz1". iIntros (Mz efz Pz w67z) "Hst1a2 Hcont".
      iApply (PB3.kxc_b2z (CID0 := CIDz) gs jp gl gu gd gk pd pav pu bn g gfs
                gi cn gtl gilf gislf ga gf cov logstart bmapstart inodestart
                nib size dev used used2 kf qf sf gyf inumf dnf bmf n2
                plen pfun na avf alen aslen afun pidv V dqb dqs dqa
                m Mz K (m !!! Regidx csp_rs1) (m !!! Regidx Rra)
                (m !!! Regidx Rs0) (m !!! Regidx Rs1) (m !!! Regidx Rs2)
                (m !!! Regidx Ra0) (m !!! Regidx Ra1) w67z efz Pz
                HK Hkf Hlg Hsz Hbm0 Hbmc Hbml Hins0 Hcovb Hiregb Hjp Hgs
                with "Htext Hfab Hst1a2 [Hcont]").
      iIntros (CIDy) "%Hsy". iIntros (My used3) "Hst1ae".
      iDestruct (wp_next_retarget CIDz CIDy true (proc_addr jp) _
                   ltac:(wp_next_chain) with "Hcont") as "Hcont".
      iApply (kxc_cd (CID0 := CIDy) jp bn gfs ga gf cov logstart bmapstart
                inodestart size used used3 plen pfun na avf alen aslen afun
                pidv V dqb dqs dqa m My K
                (m !!! Regidx csp_rs1) (m !!! Regidx Rra) (m !!! Regidx Rs0)
                (m !!! Regidx Rs1) (m !!! Regidx Rs2)
                (m !!! Regidx Ra0) (m !!! Regidx Ra1)
                (m !!! Regidx Rs3) (m !!! Regidx Rs4) (m !!! Regidx Rs5)
                (m !!! Regidx Rs6) (m !!! Regidx Rs7) (m !!! Regidx Rs8)
                (m !!! Regidx Rs9) (m !!! Regidx Rs10) (m !!! Regidx Rs11)
                w67z efz Pz (mword_of_int 0 : mword 64)
                HK Hcstr Hnamax Havf_nz Havf_na Halen_b Halen_c Halen_4
                eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
                eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
                with "Htext Hst1ae Hcont").
    - (* ---- OUTPUT 2: the phdr loop's body, entered at i = 0, sz = 0 ---- *)
      iIntros (CIDl) "%Hsl". iIntros (Ml efl Pl) "Hst12c Hcont".
      iApply (PB3.kxc_b2 (CID0 := CIDl) gs jp gl gu gd gk pd pav pu bn g gfs
                gi cn gtl gilf gislf ga gf cov logstart bmapstart inodestart
                nib size dev used used2 kf qf sf gyf inumf dnf bmf n2
                plen pfun na avf alen aslen afun pidv V dqb dqs dqa
                m Ml K (m !!! Regidx csp_rs1) (m !!! Regidx Rra)
                (m !!! Regidx Rs0) (m !!! Regidx Rs1) (m !!! Regidx Rs2)
                (m !!! Regidx Ra0) (m !!! Regidx Ra1)
                (mword_of_int 4095 : mword 64) efl Pl 0%nat
                (mword_of_int 0 : mword 64)
                HK Hkf Hlg Hsz Hbm0 Hbmc Hbml Hins0 Hcovb Hiregb Hjp Hgs Hdev
                eq_refl eq_refl eq_refl eq_refl eq_refl
                with "Htext Hfab Hst12c Hcont []").
      iIntros (CIDy) "%Hsy". iIntros (My used3 Py szvy) "Hst1ae Hcont".
      iApply (kxc_cd (CID0 := CIDy) jp bn gfs ga gf cov logstart bmapstart
                inodestart size used used3 plen pfun na avf alen aslen afun
                pidv V dqb dqs dqa m My K
                (m !!! Regidx csp_rs1) (m !!! Regidx Rra) (m !!! Regidx Rs0)
                (m !!! Regidx Rs1) (m !!! Regidx Rs2)
                (m !!! Regidx Ra0) (m !!! Regidx Ra1)
                (m !!! Regidx Rs3) (m !!! Regidx Rs4) (m !!! Regidx Rs5)
                (m !!! Regidx Rs6) (m !!! Regidx Rs7) (m !!! Regidx Rs8)
                (m !!! Regidx Rs9) (m !!! Regidx Rs10) (m !!! Regidx Rs11)
                (mword_of_int 4095 : mword 64) efl Py szvy
                HK Hcstr Hnamax Havf_nz Havf_na Halen_b Halen_c Halen_4
                eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
                eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
                with "Htext Hst1ae Hcont").
  Qed.

End KexecMain.

End KexecProof.
