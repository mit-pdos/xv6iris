(* ===================================================================== *)
(*  ProofKexecAU.v -- kexec AT THE ATOMIC-UPDATE CONTRACT, ASSEMBLED.     *)
(*  (fs-syscall-specs, exec AU lane, stage S4b; SpecKexecAU.v sect. 3-4)  *)
(* ===================================================================== *)

(*  [ProofKexecPin.v]'s composition, replayed once more: the cone has been
    generic in [Q] since the exit-generic sweep, so phases B / B2 / B3 /
    C / D and all eight [bad:] tails apply UNCHANGED and the file below is
    ProofKexecPin's two sections with three differences and no fourth.

      (1) PHASE A IS THE AU ONE ([ProofKexecAUA.kxc_phaseA_au]), which
          spends the caller's walk premise and its ONE observation where
          the pinned block reads a pin.  That is the only block that is
          not the landed one.

      (2) THE ONE PAYING SITE.  [kxc_cd] takes [Q (kxq_entry ef)]; the
          pinned run discharges it from a header claim and this one from
          WHAT THE RUN BUILT -- [KexecAUBridge.exec_built_Q_intro], at
          [Q := KexecAUBridge.exec_built_Q (kxc_fb datl dnf) ef ...].

      (3) THE EXIT IS CONVERTED, TWICE, and that is the whole of the AU
          work in this file:
            * phase A's own [-1] tails close through
              [kxau_close_fail], at [Q := fun _ _ => False] -- phase A
              allocates nothing and returns nothing but [-1], so the
              success arm of [kexec_ok_q] is refuted rather than proved,
              and the caller's [exec_post_fail] rides straight into
              [exec_arms]' left disjunct;
            * everything past +0x090 closes through [kxau_close], which
              takes the RECEIPT phase A bought and answers the ONE
              question the arms are keyed on -- is the observed node a
              file [kexec_loadable] describes?  That question is decided
              CONSTRUCTIVELY ([KexecAUBridge.kexec_loadable_dec]); the
              audit stays at its thirteen axioms.

          On the [-1] side of the second conversion the cause is
          [EfNoMem] when the node IS a loadable file (its magic passed by
          [KexecAUBridge.kexec_magic_of_loadable] -- [elf_wf] tests the
          magic first) and [EfNotLoadable] otherwise, which is exactly
          [SpecKexecAU.exec_fail_ok]'s honest fold.                      *)
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
Require Import WpNext.
Require Import WpMmodeLeafBase.
Require Import RiscvExtras.
Require Import StackOwn.
Require Import CalleeSaved.
Require Import KernelText.
Require Import IntrDefs.
Require Import CpuOwn.
Require Import FdSlots.
Require Export SwtchCtx.
Require Import ByteBuf.
Require Import ProcGeom.
Require Import ProcInv.
Require Import Xv6Cameras.
Require Import BitmapInv.
Require Import IrefSlots.
Require Import UserPtTree.
Require Import FileInvDefs.
Require Import SpecKexec.
Require Import ElfFile.      (* [elf_bytes] *)
Require Import ElfBridge.    (* [file_bytes_lookup] *)
Require Import KexecBuilt.   (* the argument block's algebra + [kexec_built] *)
Require Import KexecOkQ.
Require Import KexecAUBridge. (* the pure closer: [exec_built_Q] and friends *)
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
Require Import ProofKexecTail.
Require Import ProofKexecSeam.
Require Import ProofKexecB.
Require Import SpecPanic.
Require Import ProofKexecB2.
Require Import ProofKexecB3.
Require Import ProofKexecC.
Require Import ProofKexecD.
(* ---- and the names the AU contract's body is written in ---- *)
Require Import InstrBytes.     (* [pc_is]                            *)
Require Import LogInv.
Require Import LogDefs.
Require Import IcacheRef.
Require Import IcacheInv.
Require Import KvmSpec.
Require Import BioDefs.
Require Import InodeInv.       (* [ROOTDEV], [MAXFILE]               *)
Require Import DinodeEnc.      (* [di_type] / [di_size]              *)
Require Import InodeLock.
Require Import SleepLock.
Require Import OffBox.
Require Import PathElems.      (* [SLASH], [path_elems]              *)
Require Import DirentEnc.      (* [bview]                            *)
Require Import FsTree.         (* [fname], [file_bytes], [file_byte] *)
Require FsImg.                 (* [FsImg.T_FILE_z]                   *)
Require DirView.               (* [DirView.T_DIR_z]                  *)
Require Import SpecNameiEra.   (* [NAMEI_ERA]: the functor argument  *)
Require Import UserFd.         (* [ufdG] -- the slot's descriptor leg *)
Require Import UexecSlot.
Require Import UexecRet.       (* [uslot]                            *)
Require Import ProofKexecAUA.  (* the AU phase A                     *)
Require FsBytesGamma.          (* [FsBytesGamma.fs_gamma_L]          *)
(* THE ABSTRACT SIDE.  [FsAbs] LAST of the two, per its own rule; the
   AU leaves stay QUALIFIED (their statements are all this file wants). *)
Require Import FsAbsInv.
Require Import FsAbs.
Require SpecSysOpenAU.
Require FsAbsOpenFire.
Require SpecKexecAU.           (* THE CONTRACT                       *)
From Kernel Require KernelSyms.
Require Import ProcAvail.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Require Import FsCfg.  (* [fscfg]: the fs configuration is AMBIENT *)
Require Import TsoCtx.
Local Open Scope Z_scope.

(* A syscall-altitude goal carries [ProcInv.tf_page]'s 4096-conjunct big-op;
   printing one takes tens of minutes, so a one-line mistake reads as a hang.
   durable-notes.md's rule. *)
Set Printing Depth 40.

Notation KX := KernelSyms.kexec (only parsing).

(* ===================================================================== *)
(*  THE PROOF.  [ProofKexecPin.KexecPinProof]'s functor argument for       *)
(*  argument, with [ProofKexecAUA]'s phase A in place of the pinned one.   *)
(* ===================================================================== *)
Module KexecAUProof (Myproc : MYPROC) (BeginOp : BEGIN_OP) (Namei : NAMEI)
                    (NE : NAMEI_ERA)
                    (Ilock : ILOCK) (Readi : READI) (Iunlockput : IUNLOCKPUT)
                    (EndOp : END_OP) (PPT : PROC_PAGETABLE_GEN)
                    (PFP : PROC_FREEPAGETABLE) (Walkaddr : WALKADDR)
                    (Flags2perm : FLAGS2PERM) (Uvmalloc : UVMALLOC)
                    (Uvmclear : UVMCLEAR) (Strlen : STRLEN) (Copyout : COPYOUT)
                    (SS : SAFESTRCPY) (PN : PANIC) : SpecKexecAU.KEXEC_AU.

Module PA := ProofKexecAUA.KexecAUAProof Myproc BeginOp Namei NE Ilock Readi
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
(*  PHASES C AND D, over phase B's output state -- ProofKexecPin's two     *)
(*  relays verbatim (they are [Local] there, so they are re-stated here    *)
(*  rather than shared; nothing in them is AU-specific).                   *)
(* ===================================================================== *)
Section KexecAUTail.
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

  (* ------------------------------------------------------------------ *)
  (*  +0x272 .. ret -- the closing copyout and the commit.                *)
  (* ------------------------------------------------------------------ *)
  Local Lemma kxc_d_tail `{CID0 : CpuId} `{XI : CurCtx}
      (Q : mword 64 -> ustate -> Prop)
      (jp : nat) (gf : gname)
      (plen : nat) (pfun : nat -> bv 8)
      (na : nat) (avf : nat -> mword 64) (alen aslen : nat -> nat)
      (afun : nat -> nat -> bv 8)
      (pidv : mword 32) (U : ustate) (eb : bool) (dqb dqs dqa dqpv dqas : dfrac)
      (m M : regfile) (K : nat)
      (sp0 ra0 s00 s10 s20 pv av : mword 64)
      (w5 w6 w7 w8 w9 w10 w11 w12 w13 w67 : mword 64)
      (fb : elf_bytes) (ef : nat -> bv 8) (P : uptd) (Mi : gmap Z (bv 8)) (sz1 : mword 64) (c : nat) :
    (forall U' : ustate,
       kexec_built fb ef sz1 na alen afun U' -> Q (kxq_entry ef) U') ->
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
    m !!! Regidx Rs9 = w11 -> m !!! Regidx Rs10 = w12 ->
    kernel_text -∗
    kxc_at_272 jp gf
               plen pfun na avf alen aslen afun pidv U eb dqb dqs dqa dqpv dqas
               M K sp0 ra0 s00 s10 s20 pv av
               w5 w6 w7 w8 w9 w10 w11 w12 w13 w67 fb ef P Mi (pv_sz (us_V U)) sz1 (m !!! Regidx Rs11) c -∗
    wp_next true (proc_addr jp) (fun (CID : CpuId) =>
      KexecOkQ.kexec_closer Q gf fsc_kalloc (proc_addr jp) pidv U m (ret_pc ra0) K
           eb eb ∅ dqb dqs fsc_bmapstart na alen plen pv dqpv
           pfun av dqa avf aslen dqas afun) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros HQe HK Hcstr Hnamax Hsz1ge Havf_nz Hal Hmsp Hmra Hms0 Hms1 Hms2
           Hmw5 Hmw6 Hmw7 Hmw8 Hmw9 Hmw10 Hmw11 Hmw12.
    iIntros "#Htext Hst Hcont".
    iApply (PC.kxc_c_close (CID0 := CID0) Q jp gf
 plen pfun na avf alen aslen afun
              pidv U eb dqb dqs dqa dqpv dqas m M K sp0 ra0 s00 s10 s20 pv av
              w5 w6 w7 w8 w9 w10 w11 w12 w13 w67 fb ef P Mi (pv_sz (us_V U)) sz1 c
              HK Hsz1ge Hal Hmsp Hmra Hms0 Hms1 Hms2
              Hmw5 Hmw6 Hmw7 Hmw8 Hmw9 Hmw10 Hmw11 Hmw12
              with "Htext Hst Hcont []").
    iIntros (CIDd) "%Hsd". iIntros (Md Pd Mid) "Hst2a6 Hcont".
    iApply (PD.kxd_phaseD (CID0 := CIDd) Q jp gf
 plen pfun na avf alen aslen afun
              pidv U eb dqb dqs dqa dqpv dqas m Md K sp0 ra0 s00 s10 s20 pv av
              w5 w6 w7 w8 w9 w10 w11 w12 w13 w67 fb ef Pd Mid sz1 c
              HQe HK Hcstr Hnamax Hsz1ge Havf_nz Hal Hmsp Hmra Hms0 Hms1 Hms2
              Hmw5 Hmw6 Hmw7 Hmw8 Hmw9 Hmw10 Hmw11 Hmw12
              with "Htext Hst2a6 Hcont").
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  +0x1ae .. ret -- PHASES C AND D, over phase B's output state.       *)
  (* ------------------------------------------------------------------ *)
  Local Lemma kxc_cd `{CID0 : CpuId} `{XI : CurCtx}
      (Q : mword 64 -> ustate -> Prop)
      (jp : nat) (gf : gname)
      (plen : nat) (pfun : nat -> bv 8)
      (na : nat) (avf : nat -> mword 64) (alen aslen : nat -> nat)
      (afun : nat -> nat -> bv 8)
      (pidv : mword 32) (U : ustate) (eb : bool) (dqb dqs dqa dqpv dqas : dfrac)
      (m M : regfile) (K : nat)
      (sp0 ra0 s00 s10 s20 pv av : mword 64)
      (w5 w6 w7 w8 w9 w10 w11 w12 w13 w67 : mword 64)
      (fb : elf_bytes) (ef : nat -> bv 8) (P : uptd) (Mi : gmap Z (bv 8)) (szv : mword 64) :
    (forall (szg : mword 64) (U' : ustate),
       kexec_built fb ef szg na alen afun U' -> Q (kxq_entry ef) U') ->
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
    m !!! Regidx Rs9 = w11 -> m !!! Regidx Rs10 = w12 ->
    kernel_text -∗
    kxc_at_1ae jp gf
               plen pfun na avf aslen afun pidv U eb dqb dqs dqa dqpv dqas
               M K sp0 ra0 s00 s10 s20 pv av
               w5 w6 w7 w8 w9 w10 w11 w12 w13 w67 fb ef P Mi szv (m !!! Regidx Rs11) -∗
    wp_next true (proc_addr jp) (fun (CID : CpuId) =>
      KexecOkQ.kexec_closer Q gf fsc_kalloc (proc_addr jp) pidv U m (ret_pc ra0) K
           eb eb ∅ dqb dqs fsc_bmapstart na alen plen pv dqpv
           pfun av dqa avf aslen dqas afun) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros HQe HK Hcstr Hnamax Havf_nz Havf_na Halen_b Halen_c Halen_4
           Hmsp Hmra Hms0 Hms1 Hms2
           Hmw5 Hmw6 Hmw7 Hmw8 Hmw9 Hmw10 Hmw11 Hmw12.
    iIntros "#Htext Hst Hcont".
    rewrite /kxc_at_1ae.
    iDestruct "Hst" as "(%Hregs & %Hal & %Hpure3 & Hrest)".
    iAssert (kxc_at_1ae jp gf
               plen pfun na avf aslen afun pidv U eb dqb dqs dqa dqpv dqas
               M K sp0 ra0 s00 s10 s20 pv av
               w5 w6 w7 w8 w9 w10 w11 w12 w13 w67 fb ef P Mi szv (m !!! Regidx Rs11))
      with "[Hrest]" as "Hst".
    { rewrite /kxc_at_1ae.
      iSplitR; [iPureIntro; exact Hregs |].
      iSplitR; [iPureIntro; exact Hal |].
      iSplitR; [iPureIntro; exact Hpure3 |].
      iExact "Hrest". }
    iApply (PC.kxc_c_setup (CID0 := CID0) Q jp gf
 plen pfun na avf alen aslen
              afun pidv U eb dqb dqs dqa dqpv dqas m M K sp0 ra0 s00 s10 s20 pv av
              w5 w6 w7 w8 w9 w10 w11 w12 w13 w67 fb ef P Mi szv
              HK Hmsp Hmra Hms0 Hms1 Hms2
              Hmw5 Hmw6 Hmw7 Hmw8 Hmw9 Hmw10 Hmw11 Hmw12
              Halen_b Halen_c Halen_4 Havf_na
              with "Htext Hst Hcont []").
    iIntros (CID1) "%Hs1". iIntros (M1 P1 Mim1 sz1) "%Hsz1ge Hdisj Hcont".
    iDestruct "Hdisj" as "[Hloop | Hskip]".
    - rewrite /kxc_at_21a.
      iDestruct "Hloop" as "(%Hq1 & %Hq2 & %Hq3 & %Hq4 & Hrest2)".
      assert (H0na : (0 < na)%nat).
      { destruct Hq2 as (_ & _ & Hnz & _).
        destruct (Nat.eq_dec 0 na) as [Heq | Hne];
          [ exfalso; apply Hnz; rewrite Heq; exact Havf_na | lia ]. }
      iAssert (kxc_at_21a jp gf
 plen pfun na avf alen aslen afun pidv U eb dqb dqs dqa dqpv dqas
                 M1 K sp0 ra0 s00 s10 s20 pv av
                 w5 w6 w7 w8 w9 w10 w11 w12 w13 w67 fb ef P1 Mim1 (pv_sz (us_V U)) sz1 (m !!! Regidx Rs11) 0)
        with "[Hrest2]" as "Hloop".
      { rewrite /kxc_at_21a.
        iSplitR; [iPureIntro; exact Hq1 |].
        iSplitR; [iPureIntro; exact Hq2 |].
        iSplitR; [iPureIntro; exact Hq3 |].
        iSplitR; [iPureIntro; exact Hq4 |].
        iExact "Hrest2". }
      iApply (PC.kxc_argv_loop (CID0 := CID1) Q jp gf
 plen pfun na avf alen aslen
                afun pidv U eb dqb dqs dqa dqpv dqas m K sp0 ra0 s00 s10 s20 pv av
                w5 w6 w7 w8 w9 w10 w11 w12 w13 w67 fb ef (pv_sz (us_V U)) sz1
                HK Halen_b Halen_c Halen_4 Havf_na Hsz1ge Hnamax Hal
                Hmsp Hmra Hms0 Hms1 Hms2
                Hmw5 Hmw6 Hmw7 Hmw8 Hmw9 Hmw10 Hmw11 Hmw12
                na M1 P1 Mim1 0%nat H0na ltac:(lia)
                with "Htext Hloop Hcont []").
      iIntros (CID2) "%Hs2". iIntros (M2 P2 Mim2 c2) "Hst272 Hcont".
      iApply (kxc_d_tail (CID0 := CID2) Q jp gf
 plen pfun na avf alen aslen afun pidv U eb
                dqb dqs dqa dqpv dqas m M2 K sp0 ra0 s00 s10 s20 pv av
                w5 w6 w7 w8 w9 w10 w11 w12 w13 w67 fb ef P2 Mim2 sz1 c2
                (HQe sz1) HK Hcstr Hnamax Hsz1ge Havf_nz Hal Hmsp Hmra Hms0 Hms1 Hms2
                Hmw5 Hmw6 Hmw7 Hmw8 Hmw9 Hmw10 Hmw11 Hmw12
                with "Htext Hst272 Hcont").
    - iApply (kxc_d_tail (CID0 := CID1) Q jp gf
 plen pfun na avf alen aslen afun pidv U eb
                dqb dqs dqa dqpv dqas m M1 K sp0 ra0 s00 s10 s20 pv av
                w5 w6 w7 w8 w9 w10 w11 w12 w13 w67 fb ef P1 Mim1 sz1 0
                (HQe sz1) HK Hcstr Hnamax Hsz1ge Havf_nz Hal Hmsp Hmra Hms0 Hms1 Hms2
                Hmw5 Hmw6 Hmw7 Hmw8 Hmw9 Hmw10 Hmw11 Hmw12
                with "Htext Hskip Hcont").
  Qed.

End KexecAUTail.

(* ===================================================================== *)
(*  THE EXIT CONVERSION: from the AU contract's armed continuation to the  *)
(*  cone's own [kexec_closer].                                            *)
(* ===================================================================== *)
Section KexecAUExit.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ, !ufdG Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.

  Notation Ra0 := (mword_of_int 10 : mword 5).
  Notation ΓL := (FsBytesGamma.fs_gamma_L fsc_fs).

  (* [KexecOkQ.kexec_closer]'s resource rows with the ARMED POST in place
     of the pure [kexec_ok_q] -- i.e. [SpecKexecAU.wp_kexec_au_frame]'s
     own continuation, named so the two conversions below can quote it. *)
  Definition kxau_ret `{CID : CpuId}
      (ARMS : ustate -> mword 64 -> iProp Σ)
      (gf ga : gname) (pj : mword 64) (pidv : mword 32)
      (m : regfile) (ret_tgt : mword 64) (K : nat) (b eb : bool)
      (lks : gset string) (dqb dqs : dfrac) (bmapstart : Z)
      (na : nat) (plen : nat) (pv : mword 64) (dqpv : dfrac)
      (pfun : nat -> bv 8) (av : mword 64) (dqa : dfrac)
      (avf : nat -> mword 64) (aslen : nat -> nat) (dqas : dfrac)
      (afun : nat -> nat -> bv 8) : iProp Σ :=
    (∀ (mf : regfile) (U' : ustate),
        ⌜callee_saved m mf⌝ -∗
        ARMS U' (mf !!! Regidx Ra0) -∗
        sie_cap_gpr KT1 mf K b pj -∗
        cpu_own 0 eb pj b lks -∗
        trap_csrs_ext KT1 eb -∗
        cpu_claim_ext eb pj -∗
        pc_is ret_tgt -∗
        sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
        sb_inodestart ↦₄{dqs} (mword_of_int icfg_ist : mword 32) -∗
        kalloc_env ga None -∗
        proc_priv gf pj pidv U' -∗
        ([∗ list] i ∈ seq 0 (S plen), pa_add pv i ↦ₘ[KT1]{dqpv} pfun i) -∗
        ([∗ list] i ∈ seq 0 (S na), pa_add av (8 * i) ↦₈[KT1]{dqa} avf i) -∗
        ([∗ list] i ∈ seq 0 na,
           [∗ list] j ∈ seq 0 (aslen i), pa_add (avf i) j ↦ₘ{dqas} afun i j) -∗
        bslots 3 -∗
        iref_slots 2 -∗
        WP (Loop : expr riscv_lang))%I.

  (* the linear twin of [ProofKexecA.kxc_exit_open_r]: the receipt the
     conversion spends is not persistent, so the wand is not either. *)
  Lemma kxau_exit_conv `{CIDx : CpuId} (pj : mword 64)
      (KEX E : CpuId -> iProp Σ) (R : iProp Σ) :
    (∀ CX : CpuId, KEX CX -∗ R -∗ E CX) -∗
    R -∗
    wp_next (CID0 := CIDx) true pj KEX -∗
    wp_next (CID0 := CIDx) true pj E.
  Proof.
    rewrite /wp_next. iIntros "Hw HR H" (CID Hcr).
    iSpecialize ("H" $! CID with "[%]"); [exact Hcr |].
    iApply ("Hw" with "H HR").
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  THE ONE QUESTION THE ARMS ARE KEYED ON, DECIDED.                    *)
  (*                                                                      *)
  (*  Success arm (a) vs (b), and failure cause [EfNoMem] vs              *)
  (*  [EfNotLoadable], are the SAME split: is the node the walk observed   *)
  (*  a file that [kexec_loadable] describes?  [Hrow] is the receipt's own *)
  (*  conditional file row (the oracle's instant is where [inode_ok] was   *)
  (*  in scope); everything else is [KexecAUBridge]'s decision procedure   *)
  (*  and [FsAbsOpenFire]'s two other row shapes.                          *)
  (* ------------------------------------------------------------------ *)
  Lemma kxau_classify (dn : dinode) (bm : blkmap) (data : nat -> list (bv 8)) :
    (bv_unsigned (di_type dn) = FsImg.T_FILE_z ->
       abs_of (FsStateEra.era_node dn bm data)
       = MkAnode (AFile (kxc_fb data dn))
                 (fn_nlink (FsStateEra.era_node dn bm data))) ->
    { nl : nat | abs_of (FsStateEra.era_node dn bm data)
                 = MkAnode (AFile (kxc_fb data dn)) nl
                 /\ SpecKexecAU.kexec_loadable (kxc_fb data dn) }
    + { ~ SpecKexecAU.anode_loadable (abs_of (FsStateEra.era_node dn bm data)) }.
  Proof.
    intros Hrow.
    destruct (decide (bv_unsigned (di_type dn) = FsImg.T_FILE_z)) as [Ht | Ht].
    - destruct (kexec_loadable_dec (kxc_fb data dn)) as [Hl | Hl].
      + left. exists (fn_nlink (FsStateEra.era_node dn bm data)).
        split; [exact (Hrow Ht) | exact Hl].
      + right. intros (f & nl & Heq & Hload).
        rewrite (Hrow Ht) in Heq. injection Heq as Hn _.
        apply Hl. rewrite Hn. exact Hload.
    - right. intros (f & nl & Heq & Hload).
      destruct (decide (bv_unsigned (di_type dn) = DirView.T_DIR_z)) as [Hd | Hd].
      + rewrite (FsAbsOpenFire.opf_era_dir_row dn bm data Hd) in Heq.
        injection Heq as Hn _. discriminate Hn.
      + rewrite (FsAbsOpenFire.opf_era_dev_row dn bm data Hd Ht) in Heq.
        injection Heq as Hn _. discriminate Hn.
  Qed.

  (* [EfNoMem]'s side condition, on a loadable file: [elf_wf] tests the
     magic first, so the kernel's own four-byte test passed. *)
  Lemma kxau_nomem_ok (a : anode) (f : elf_bytes) (nl : nat)
      (na : nat) (alen : nat -> nat) :
    a = MkAnode (AFile f) nl -> SpecKexecAU.kexec_loadable f ->
    SpecKexecAU.exec_fail_ok a na alen SpecKexecAU.EfNoMem.
  Proof.
    intros Ha Hl. cbn. intros f' nl' Heq.
    rewrite Ha in Heq. injection Heq as Hn _. rewrite <- Hn.
    exact (kexec_magic_of_loadable f Hl).
  Qed.

  Lemma kxau_fb_length (data : nat -> list (bv 8)) (dn : dinode) :
    length (kxc_fb data dn) = Z.to_nat (bv_unsigned (di_size dn)).
  Proof.
    unfold kxc_fb, FsTree.file_bytes. rewrite length_fmap length_seq.
    reflexivity.
  Qed.

  Lemma kxau_argc_ne_m1 (na : nat) :
    (na <= MAXARG)%nat ->
    (mword_of_int (Z.of_nat na) : mword 64) <> (mword_of_int (-1) : mword 64).
  Proof.
    intros Hna Heq.
    assert (Hsm : bv_wrap 64 (Z.of_nat na) = Z.of_nat na).
    { apply bvw64_small. unfold MAXARG in Hna.
      change (2 ^ 64)%Z with 18446744073709551616%Z. lia. }
    assert (Hm1 : bv_wrap 64 (-1) = 18446744073709551615%Z)
      by (vm_compute; reflexivity).
    apply (f_equal bv_unsigned) in Heq.
    rewrite !moi64_unsigned Hsm Hm1 in Heq.
    unfold MAXARG in Hna. lia.
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  CONVERSION 1: phase A's own [-1] tails.                             *)
  (*                                                                      *)
  (*  Phase A allocates nothing and its two tails return [-1], so the      *)
  (*  cone is run at [Q := fun _ _ => False] BELOW +0x090: the success arm *)
  (*  of [kexec_ok_q] is then refuted rather than proved, and every        *)
  (*  [bad:] tail proves the failure arm at any [Q] whatever.              *)
  (* ------------------------------------------------------------------ *)
  (* the plug below +0x090: phase A returns nothing but [-1]. *)
  Definition kxau_QF : mword 64 -> ustate -> Prop := fun _ _ => False.

  Lemma kxau_close_fail `{CIDx : CpuId}
      (P Pmiss : nat -> Z -> iProp Σ)
      (Φo : aview -> Z -> anode -> iProp Σ)
      (gf : gname) (pj : mword 64) (pidv : mword 32) (U : ustate)
      (sts : list fdstate)
      (m : regfile) (ret_tgt : mword 64) (K : nat) (b eb : bool)
      (lks : gset string) (dqb dqs : dfrac)
      (na : nat) (alen aslen : nat -> nat) (afun : nat -> nat -> bv 8)
      (plen : nat) (pv : mword 64) (dqpv : dfrac) (pfun : nat -> bv 8)
      (av : mword 64) (dqa : dfrac) (avf : nat -> mword 64) (dqas : dfrac) :
    kxau_ret (CID := CIDx)
      (SpecKexecAU.exec_arms ΓL fsc_fs P Pmiss Φo na alen afun sts U)
      gf fsc_kalloc pj pidv m ret_tgt K b eb lks dqb dqs fsc_bmapstart
      na plen pv dqpv pfun av dqa avf aslen dqas afun -∗
    SpecKexecAU.exec_post_fail ΓL fsc_fs P Pmiss Φo na alen afun sts -∗
    KexecOkQ.kexec_closer (CID := CIDx)
      kxau_QF
      gf fsc_kalloc pj pidv U m ret_tgt K b eb lks dqb dqs fsc_bmapstart
      na alen plen pv dqpv pfun av dqa avf aslen dqas afun.
  Proof.
    iIntros "Hret Hfail". rewrite /KexecOkQ.kexec_closer /kxau_QF.
    iIntros (mf U' entry spv szv') "%Hcs %Hq".
    iIntros "Hcg Hcnt Hextc Hclmc Hpc Hbm Hins Hka Hpriv Hpath Hargv Hargs Hbs Hirs".
    destruct Hq as [(Hr & HV) | (Hfalse & _)]; [| destruct Hfalse].
    rewrite /kxau_ret.
    iApply ("Hret" $! mf U' with "[%] [Hfail] Hcg Hcnt Hextc Hclmc Hpc Hbm Hins
                                  Hka Hpriv Hpath Hargv Hargs Hbs Hirs").
    { exact Hcs. }
    rewrite /SpecKexecAU.exec_arms. iLeft.
    iSplitR; [iPureIntro; split; assumption |]. iExact "Hfail".
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  CONVERSION 2: everything past +0x090, at the RECEIPT.               *)
  (* ------------------------------------------------------------------ *)
  Lemma kxau_close `{CIDx : CpuId}
      (P Pmiss : nat -> Z -> iProp Σ)
      (Φo : aview -> Z -> anode -> iProp Σ)
      (pl : list (bv 8)) (zi : Z)
      (dn : dinode) (bm : blkmap) (datl : nat -> list (bv 8))
      (ef : nat -> bv 8)
      (gf : gname) (pj : mword 64) (pidv : mword 32) (U : ustate)
      (sts : list fdstate)
      (m : regfile) (ret_tgt : mword 64) (K : nat) (b eb : bool)
      (lks : gset string) (dqb dqs : dfrac)
      (na : nat) (alen aslen : nat -> nat) (afun : nat -> nat -> bv 8)
      (plen : nat) (pv : mword 64) (dqpv : dfrac) (pfun : nat -> bv 8)
      (av : mword 64) (dqa : dfrac) (avf : nat -> mword 64) (dqas : dfrac) :
    (forall j : nat, (j < 64)%nat -> ef j = file_byte datl j) ->
    length (pv_tf (us_V U)) = TFWORDS ->
    (na <= MAXARG)%nat ->
    kxau_ret (CID := CIDx)
      (SpecKexecAU.exec_arms ΓL fsc_fs P Pmiss Φo na alen afun sts U)
      gf fsc_kalloc pj pidv m ret_tgt K b eb lks dqb dqs fsc_bmapstart
      na plen pv dqpv pfun av dqa avf aslen dqas afun -∗
    PA.kxa_receipt P Φo (length (path_elems pl)) zi na alen afun sts dn bm datl -∗
    KexecOkQ.kexec_closer (CID := CIDx)
      (KexecAUBridge.exec_built_Q (kxc_fb datl dn) ef na alen afun)
      gf fsc_kalloc pj pidv U m ret_tgt K b eb lks dqb dqs fsc_bmapstart
      na alen plen pv dqpv pfun av dqa avf aslen dqas afun.
  Proof.
    intros Hag Htflen Hnamax.
    iIntros "Hret Hrcpt". rewrite /KexecOkQ.kexec_closer.
    iIntros (mf U' entry spv szv') "%Hcs %Hq".
    iIntros "Hcg Hcnt Hextc Hclmc Hpc Hbm Hins Hka Hpriv Hpath Hargv Hargs Hbs Hirs".
    rewrite /kxau_ret.
    iApply ("Hret" $! mf U' with "[%] [Hrcpt] Hcg Hcnt Hextc Hclmc Hpc Hbm Hins
                                  Hka Hpriv Hpath Hargv Hargs Hbs Hirs").
    { exact Hcs. }
    rewrite /PA.kxa_receipt.
    iDestruct "Hrcpt" as (av0) "(%Hav & %Hrow & HΦ & HP & Hsl)".
    destruct (kxau_classify dn bm datl Hrow) as [(nl & Ha & Hload) | Hnl].
    - (* A LOADABLE FILE.  Arm (a) on success; [EfNoMem] on a failure past
         the lock -- the magic did pass, [KexecAUBridge]. *)
      rewrite Ha in Hav. rewrite Ha.
      (* the buffer readi filled IS the file's first 64 bytes *)
      assert (Hag' : forall j : nat, (j < 64)%nat -> ef j = kxc_fb datl dn !!! j).
      { intros j Hj. rewrite (Hag j Hj). symmetry.
        unfold kxc_fb. apply file_bytes_lookup.
        pose proof (kexec_loadable_len _ Hload) as H64.
        rewrite kxau_fb_length in H64. lia. }
      destruct Hq as [(Hr & HV) | Hsucc].
      + rewrite /SpecKexecAU.exec_arms. iLeft.
        iSplitR; [iPureIntro; split; assumption |].
        rewrite /SpecKexecAU.exec_post_fail. iRight. iExists pl. iRight.
        iExists zi, av0, (MkAnode (AFile (kxc_fb datl dn)) nl),
                SpecKexecAU.EfNoMem.
        iSplitL "HP"; [iExact "HP" |].
        iSplitR; [iPureIntro; exact Hav |].
        iSplitL "HΦ"; [iExact "HΦ" |].
        iSplitR; [iPureIntro;
                  exact (kxau_nomem_ok _ (kxc_fb datl dn) nl na alen eq_refl Hload) |].
        iExact "Hsl".
      + assert (Hne : (mf !!! Regidx Ra0) <> (mword_of_int (-1) : mword 64)).
        { destruct Hsucc as (_ & Hr & _). rewrite Hr.
          exact (kxau_argc_ne_m1 na Hnamax). }
        destruct (exec_image_ok_of_ok_q (kxc_fb datl dn) ef (us_V U) U' sts
                    na alen afun (mf !!! Regidx Ra0) entry spv szv'
                    Hload Hag' Htflen ltac:(by right) Hne) as (Himg & Hokx).
        rewrite /SpecKexecAU.exec_arms. iRight.
        rewrite /SpecKexecAU.exec_post_ok.
        iExists pl, zi, av0, (MkAnode (AFile (kxc_fb datl dn)) nl).
        iSplitL "HP"; [iExact "HP" |].
        iSplitR; [iPureIntro; exact Hav |].
        iLeft. iExists (kxc_fb datl dn), nl.
        iSplitR; [iPureIntro; reflexivity |].
        iSplitR; [iPureIntro; exact Hload |].
        iSplitR; [iPureIntro; exact Hokx |].
        iSplitR; [iPureIntro; exact Himg |].
        iApply ("Hsl" $! av0 zi (kxc_fb datl dn) nl
                  (SpecKexecAU.exec_key U' sts na) with "HΦ [%] [%]");
          [exact Hload | exact Himg].
    - (* NOT A LOADABLE FILE.  Arm (b) on success, [EfNotLoadable] on a
         failure past the lock. *)
      destruct Hq as [(Hr & HV) | Hsucc].
      + rewrite /SpecKexecAU.exec_arms. iLeft.
        iSplitR; [iPureIntro; split; assumption |].
        rewrite /SpecKexecAU.exec_post_fail. iRight. iExists pl. iRight.
        iExists zi, av0, (abs_of (FsStateEra.era_node dn bm datl)),
                SpecKexecAU.EfNotLoadable.
        iSplitL "HP"; [iExact "HP" |].
        iSplitR; [iPureIntro; exact Hav |].
        iSplitL "HΦ"; [iExact "HΦ" |].
        iSplitR; [iPureIntro; exact Hnl |].
        iExact "Hsl".
      + assert (Hne : (mf !!! Regidx Ra0) <> (mword_of_int (-1) : mword 64)).
        { destruct Hsucc as (_ & Hr & _). rewrite Hr.
          exact (kxau_argc_ne_m1 na Hnamax). }
        rewrite /SpecKexecAU.exec_arms. iRight.
        rewrite /SpecKexecAU.exec_post_ok.
        iExists pl, zi, av0, (abs_of (FsStateEra.era_node dn bm datl)).
        iSplitL "HP"; [iExact "HP" |].
        iSplitR; [iPureIntro; exact Hav |].
        iRight.
        iSplitR; [iPureIntro; exact Hnl |].
        iSplitR.
        { iPureIntro. exists entry, spv, szv'. split; [exact Hne |].
          apply (KexecOkQ.kexec_ok_q_weaken
                   (fun e => KexecAUBridge.exec_built_Q (kxc_fb datl dn) ef
                               na alen afun e U')).
          by right. }
        iFrame "HΦ Hsl".
  Qed.

End KexecAUExit.

(* ===================================================================== *)
(*  THE CONTRACT.                                                         *)
(* ===================================================================== *)
Section KexecAUMain.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ, !ufdG Σ}.
  Context `{GEN : GenId} `{CID0 : CpuId} `{XI : CurCtx}.

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

  Notation ΓL := (FsBytesGamma.fs_gamma_L fsc_fs).

  Lemma wp_kexec_au
      (gs : list gname) (jp : nat) (gl : gname)
      (pd pav pu : mword 64)
      (gf : gname)
      (plen : nat) (pfun : nat -> bv 8)
      (na : nat) (avf : nat -> mword 64)
      (alen aslen : nat -> nat) (afun : nat -> nat -> bv 8)
      (pidv : mword 32) (U : ustate) (sts : list fdstate)
      (dqb dqs dqa dqpv dqas : dfrac)
      (m : regfile) (K : nat) (eb : bool)
      (b : bool) (lks : gset string)
      (P Pmiss : nat -> Z -> iProp Σ)
      (Φo : aview -> Z -> anode -> iProp Σ) :
    SpecKexecAU.wp_kexec_au_body gs jp gl pd pav pu gf plen pfun na avf alen
      aslen afun pidv U sts dqb dqs dqa dqpv dqas m K eb b lks P Pmiss Φo.
  Proof.
    rewrite /SpecKexecAU.wp_kexec_au_body /SpecKexecAU.wp_kexec_au_frame.
    intros HK Hroot Hnib0 Hlg Hsz Hbm0 Hbmc Hbml Hins0
           Hcovb Hiregb Hcstr Hplen Havf_nz Havf_na Hnamax
           Halen_b Halen_c Halen_4 Hjp Hgs.
    iIntros "Hcg Hcnt Hextc Hclmc #Htext Hpc #Hfab #Hka Hbm Hins Hbits Hpriv
             Hpath Hargv Hargs Hbs Hirs Hau Hcont".
    (* ---- THE BUNDLE, OPENED (SpecKexecAU sect. 2): the walk premise,
       the one observation, and the program's WP. ---- *)
    rewrite /SpecKexecAU.exec_au_pre.
    iDestruct "Hau" as "(Hwalk & Hoc & Hsl)".
    (* the trapframe's length, read off the block ONCE: the image closer
       ([KexecAUBridge.exec_image_ok_of_ok_q]) wants it about the INCOMING
       state, and at the exit only [U'] is in hand. *)
    iDestruct (proc_priv_tf with "Hpriv") as "(Hq14 & Htfp & Hpvbk)".
    iDestruct (tf_page_length with "Htfp") as %Htflen.
    iDestruct ("Hpvbk" with "Hq14 Htfp") as "Hpriv".
    (* the index and the held-lock set, as in every kexec composition *)
    iDestruct (kxc_sie_b_agree m 0%nat K eb b (proc_addr jp) lks
                 with "Hcg Hcnt") as %Houtb.
    cbn in Houtb. subst b.
    iDestruct (cpu_own_eb_agree with "Hcg Hcnt") as %Hebb.
    iDestruct (cpu_own_zero_empty with "Hcnt") as "[%Hlk Hcnt]". subst lks.
    (* ---- THE EXIT, NAMED.  [kxau_ret] IS the contract's continuation. ---- *)
    iAssert (wp_next true (proc_addr jp) (fun CID : CpuId =>
               kxau_ret (CID := CID)
                 (SpecKexecAU.exec_arms ΓL fsc_fs P Pmiss Φo na alen afun sts U)
                 gf fsc_kalloc (proc_addr jp) pidv m
                 (ret_pc (m !!! Regidx Rra)) K eb eb ∅ dqb dqs fsc_bmapstart
                 na plen (m !!! Regidx Ra0) dqpv pfun (m !!! Regidx Ra1) dqa
                 avf aslen dqas afun))
      with "[Hcont]" as "Hcont"; [iExact "Hcont" |].
    (* ---- PHASE A: +0x000 .. +0x090, and two of the eight [bad:] tails.
       [Q := False] below +0x090: phase A allocates nothing, so its own
       tails only ever prove [kexec_ok_q]'s FAILURE arm. ---- *)
    iApply (PA.kxc_phaseA_au (CID0 := CID0) kxau_QF
              gs jp gl pd pav pu gf
              plen pfun na avf alen aslen afun pidv U sts dqb dqs dqa dqpv dqas
              m K eb eb ∅
              (m !!! Regidx csp_rs1) (m !!! Regidx Rra) (m !!! Regidx Rs0)
              (m !!! Regidx Rs1) (m !!! Regidx Rs2)
              (m !!! Regidx Ra0) (m !!! Regidx Ra1) P Pmiss Φo _
              HK Hroot Hnib0 Hlg Hsz Hbm0 Hbmc Hbml
              Hins0 Hcovb Hiregb Hcstr Hplen Hjp Hgs
              eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
              with "Hcg Hcnt Hextc Hclmc Htext Hpc Hfab Hwalk Hoc Hsl Hka Hbm
                    Hins Hbits Hpriv Hpath Hargv Hargs Hbs Hirs Hcont [] []").
    { (* arms (i) and (ii): the refund rides straight into [exec_arms] *)
      iModIntro. iIntros (CX) "HK Hfail".
      iApply (kxau_close_fail (CIDx := CX) P Pmiss Φo gf (proc_addr jp) pidv U
                sts m (ret_pc (m !!! Regidx Rra)) K eb eb ∅ dqb dqs na alen
                aslen afun plen (m !!! Regidx Ra0) dqpv pfun (m !!! Regidx Ra1)
                dqa avf dqas with "HK Hfail"). }
    iIntros (CIDa) "%Hsa".
    iIntros (M90 kf qf sf inumf dnf bmf gilf gislf gyf loyf tlyf n2 ef datl)
            "%Hregs90 %Hn2 %Hef Hpc Hcg Hcnt Hextc Hclmc Hslk Hslked %Hle90 #Hfl90 #Hclaims90 Hdep Hoffr Hidev Hiinum
             Hival Hloaded Hity Hfrz Hiref Hru Hlog Hirs Hbm Hins Hbits Hbs #Hka2
             Hpriv
             Hpath Hargv Hargs Hrcpt Hframe Hcont".
    iDestruct "Hrcpt" as (zi) "Hrcpt".
    destruct Hregs90 as (HM90sp & HM90s0 & HM90s1 & HM90s2 & HM90s4 & Hkf &
                         Hinumf & HM90thr).
    (* ---- THE EXIT, CONVERTED AT THE RECEIPT.  Below this line the file
       is ProofKexecPin's composition on the nose, at
       [Q := exec_built_Q (kxc_fb datl dnf) ef ...]. ---- *)
    iDestruct (kxau_exit_conv (CIDx := CIDa) (proc_addr jp) _
                 (fun CID : CpuId =>
                    KexecOkQ.kexec_closer
                      (KexecAUBridge.exec_built_Q (kxc_fb datl dnf) ef na alen afun)
                      gf fsc_kalloc (proc_addr jp) pidv U m
                      (ret_pc (m !!! Regidx Rra)) K eb eb ∅ dqb dqs
                      fsc_bmapstart na alen plen (m !!! Regidx Ra0) dqpv pfun
                      (m !!! Regidx Ra1) dqa avf aslen dqas afun)
                 _ with "[] Hrcpt Hcont") as "Hcont".
    { iIntros (CX) "HK HR".
      iApply (kxau_close (CIDx := CX) P Pmiss Φo (bview plen pfun) zi dnf bmf
                datl ef gf (proc_addr jp) pidv U sts m
                (ret_pc (m !!! Regidx Rra)) K eb eb ∅ dqb dqs na alen aslen afun
                plen (m !!! Regidx Ra0) dqpv pfun (m !!! Regidx Ra1) dqa avf dqas
                Hef Htflen ltac:(lia) with "HK HR"). }
    (* the nine resources phase B threads whole and never looks inside *)
    iAssert (kxc_open pidv kf qf sf gyf loyf tlyf inumf dnf
                      bmf datl gilf gislf)
      with "[Hslk Hslked Hdep Hoffr Hidev Hiinum Hival Hloaded Hity Hfrz
             Hiref Hru]"
      as "Hopen".
    { rewrite /kxc_open.
      iSplitL "Hslk"; [iExact "Hslk" |].
      iSplitL "Hslked"; [iExact "Hslked" |].
      iSplitR; [iPureIntro; exact Hle90 |].
      iSplitR; [iExact "Hfl90" |].
      iSplitR; [iExact "Hclaims90" |].
      iSplitL "Hdep"; [iExact "Hdep" |].
      iSplitL "Hoffr"; [iExact "Hoffr" |].
      iSplitL "Hidev"; [iExact "Hidev" |].
      iSplitL "Hiinum"; [iExact "Hiinum" |].
      iSplitL "Hival"; [iExact "Hival" |].
      iSplitL "Hloaded"; [iExact "Hloaded" |].
      iSplitL "Hity"; [iExact "Hity" |].
      iSplitL "Hfrz"; [iExact "Hfrz" |].
      iSplitL "Hiref"; [iExact "Hiref" | iExact "Hru"]. }
    (* ---- PHASE B1: +0x090 .. +0x0cc, plus the +0x31c tail ---- *)
    iApply (PB.kxc_b1 (CID0 := CIDa)
              (KexecAUBridge.exec_built_Q (kxc_fb datl dnf) ef na alen afun)
              gs jp gl pd pav pu gf
              kf qf sf gyf loyf tlyf inumf dnf bmf datl gilf gislf n2
              plen pfun na avf alen aslen afun pidv U dqb dqs dqa dqpv dqas
              m M90 K eb eb ∅
              (m !!! Regidx csp_rs1) (m !!! Regidx Rra) (m !!! Regidx Rs0)
              (m !!! Regidx Rs1) (m !!! Regidx Rs2)
              (m !!! Regidx Ra0) (m !!! Regidx Ra1) ef
              HK Hlg Hsz Hbm0 Hbmc Hbml Hins0 Hcovb Hiregb Hjp Hgs
              Hkf Hinumf Hn2 eq_refl eq_refl eq_refl eq_refl eq_refl
              HM90sp HM90s0 HM90s1 HM90s2 HM90s4 HM90thr
              with "Htext Hfab Hpc Hcg Hcnt Hextc Hclmc Hopen Hlog Hirs Hbm Hins
                    Hbits Hbs Hka2 Hpriv Hpath Hargv Hargs Hframe Hcont [] []").
    - (* ---- OUTPUT 1: elf.phnum = 0, the phdr loop is skipped ---- *)
      iIntros (CIDz) "%Hsz1". iIntros (Mz Pz Miz w13z w67z) "Hst1a2 Hcont".
      iApply (PB3.kxc_b2z (CID0 := CIDz) gs jp gl pd pav pu
                gilf gislf gf
 kf qf sf gyf loyf tlyf inumf dnf bmf datl n2
                plen pfun na avf alen aslen afun pidv U eb dqb dqs dqa dqpv dqas
                m Mz K (m !!! Regidx csp_rs1) (m !!! Regidx Rra)
                (m !!! Regidx Rs0) (m !!! Regidx Rs1) (m !!! Regidx Rs2)
                (m !!! Regidx Ra0) (m !!! Regidx Ra1) w13z w67z ef Pz Miz
                HK Hkf Hlg Hsz Hbm0 Hbmc Hbml Hins0 Hcovb Hiregb Hjp Hgs
                with "Htext Hfab Hst1a2 [Hcont]").
      iIntros (CIDy) "%Hsy". iIntros (My) "Hst1ae".
      iDestruct (wp_next_retarget CIDz CIDy true (proc_addr jp) _
                   ltac:(wp_next_chain) with "Hcont") as "Hcont".
      iApply (kxc_cd (CID0 := CIDy)
                (KexecAUBridge.exec_built_Q (kxc_fb datl dnf) ef na alen afun)
                jp gf
 plen pfun na avf alen aslen afun
                pidv U eb dqb dqs dqa dqpv dqas m My K
                (m !!! Regidx csp_rs1) (m !!! Regidx Rra) (m !!! Regidx Rs0)
                (m !!! Regidx Rs1) (m !!! Regidx Rs2)
                (m !!! Regidx Ra0) (m !!! Regidx Ra1)
                (m !!! Regidx Rs3) (m !!! Regidx Rs4) (m !!! Regidx Rs5)
                (m !!! Regidx Rs6) (m !!! Regidx Rs7) (m !!! Regidx Rs8)
                (m !!! Regidx Rs9) (m !!! Regidx Rs10) w13z
                w67z (kxc_fb datl dnf) ef Pz Miz (mword_of_int 0 : mword 64)
                (fun szg U' Hb =>
                   KexecAUBridge.exec_built_Q_intro (kxc_fb datl dnf) ef na alen
                     afun szg U' Hb)
                HK Hcstr Hnamax Havf_nz Havf_na Halen_b Halen_c Halen_4
                eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
                eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
                with "Htext Hst1ae Hcont").
    - (* ---- OUTPUT 2: the phdr loop's body, entered at i = 0, sz = 0 ---- *)
      iIntros (CIDl) "%Hsl". iIntros (Ml Pl Mil) "Hst12c Hcont".
      iApply (PB3.kxc_b2 (CID0 := CIDl)
                (KexecAUBridge.exec_built_Q (kxc_fb datl dnf) ef na alen afun)
                gs jp gl pd pav pu
                gilf gislf gf
 kf qf sf gyf loyf tlyf inumf dnf bmf datl n2
                plen pfun na avf alen aslen afun pidv U eb dqb dqs dqa dqpv dqas
                m Ml K (m !!! Regidx csp_rs1) (m !!! Regidx Rra)
                (m !!! Regidx Rs0) (m !!! Regidx Rs1) (m !!! Regidx Rs2)
                (m !!! Regidx Ra0) (m !!! Regidx Ra1)
                (mword_of_int 4095 : mword 64) ef Pl Mil 0%nat
                (mword_of_int 0 : mword 64)
                HK Hkf Hlg Hsz Hbm0 Hbmc Hbml Hins0 Hcovb Hiregb Hjp Hgs
                eq_refl eq_refl eq_refl eq_refl eq_refl
                with "Htext Hfab Hst12c Hcont []").
      iIntros (CIDy) "%Hsy". iIntros (My Py Miy szvy) "Hst1ae Hcont".
      iApply (kxc_cd (CID0 := CIDy)
                (KexecAUBridge.exec_built_Q (kxc_fb datl dnf) ef na alen afun)
                jp gf
 plen pfun na avf alen aslen afun
                pidv U eb dqb dqs dqa dqpv dqas m My K
                (m !!! Regidx csp_rs1) (m !!! Regidx Rra) (m !!! Regidx Rs0)
                (m !!! Regidx Rs1) (m !!! Regidx Rs2)
                (m !!! Regidx Ra0) (m !!! Regidx Ra1)
                (m !!! Regidx Rs3) (m !!! Regidx Rs4) (m !!! Regidx Rs5)
                (m !!! Regidx Rs6) (m !!! Regidx Rs7) (m !!! Regidx Rs8)
                (m !!! Regidx Rs9) (m !!! Regidx Rs10) (m !!! Regidx Rs11)
                (mword_of_int 4095 : mword 64) (kxc_fb datl dnf) ef Py Miy szvy
                (fun szg U' Hb =>
                   KexecAUBridge.exec_built_Q_intro (kxc_fb datl dnf) ef na alen
                     afun szg U' Hb)
                HK Hcstr Hnamax Havf_nz Havf_na Halen_b Halen_c Halen_4
                eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
                eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
                with "Htext Hst1ae Hcont").
  Qed.

End KexecAUMain.

End KexecAUProof.
