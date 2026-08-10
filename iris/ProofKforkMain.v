(* ProofKforkMain.v -- the capstone: gluing kfork's six proven blocks
   (ProofKforkB1..B7, ProofKfork's two exits, ProofKforkParts' epilogue)
   into SpecKfork.KFORK's [wp_kfork_sconf].

   STATUS: NOT COMPLETE, but the three earlier gaps this file's previous
   revision found (missing [cpu_own] on the allocproc-not-found arm,
   [kfk_frame]'s existential swallowing the uvmcopy-failure arm's slot-6
   value, [Hcont4a]'s missing ofile/cwd conjunct on the child block) have
   all been FIXED in [ProofKforkB6.v]/[ProofKfork.v], and the fixes are
   used below.  Every Lemma in this file is fully proved (no
   [admit]/[Admitted]/[Axiom]/[Parameter]):

     - [kfork_arm1] is a complete, HYPOTHESIS-FREE match for [Hcont10a]'s
       own body (allocproc found no slot) -- [ProofKfork.kfk_exit_alloc]
       plus [kfork_post]'s first disjunct.
     - [kfork_arm2] is a complete, HYPOTHESIS-FREE match for [Hcont7c]'s
       own body (uvmcopy failed) -- [ProofKforkB1.kfk_exit_uvmcopy] plus
       [kfork_post]'s second disjunct.
     - [kfork_arm3] closes [Hcont4a]'s own body (uvmcopy succeeded) all the
       way through [ProofKforkB2] (the trapframe copy loop), [ProofKforkB7]
       (my own block), [ProofKforkB3] (the whole 16-iteration fd scan),
       [ProofKforkB4] (idup/safestrcpy/pid), [ProofKforkB5] (the two lock
       crossings and the RUNNABLE park), and [ProofKfork.kfk_tail_succ],
       reaching [kfork_post]'s THIRD disjunct -- given exactly ONE extra
       premise, documented in its own header as a SEAM: [Hcont4a] hands
       the scheduler context as the generic [SwtchCtx.own_ctx (p_context
       npa)], but [SpecForkretPark.forkret_park] (run inside
       [ProofKforkB5.kfk_b5]) needs the RAW, SPECIFIC shape ([is_kstack] +
       [ctx_cells] at the literal [forkret_pc :: add_vec ks 4096 :: rest]),
       which a generic 14-word existential cannot supply.

   Because that one fact only becomes nameable INSIDE [Hcont4a]'s own
   binders (the child's address [npa] does not exist before then), it
   cannot be discharged by adding a top-level hypothesis to a
   [wp_kfork_sconf]-shaped lemma the way the three earlier gaps could --
   the fix has to be inside [ProofKforkB6.kfk_prologue] itself (expose
   [is_kstack npa ks ∗ ctx_cells (p_context npa) (forkret_pc ::
   add_vec ks 4096 :: rest)] in [Hcont4a] in place of [own_ctx (p_context
   npa)], exactly mirroring how the three earlier gaps were fixed).  So
   this file does NOT define [Module Kfork ... : KFORK]: doing so would
   require completing [wp_kfork_sconf], which is exactly the one step
   blocked on that fix.  [kfork_arm3] is otherwise ready to plug in
   unchanged the moment it lands. *)
From Stdlib Require Import Eqdep_dec ZArith Lia List.
From stdpp Require Import gmap list list_monad bitvector.definitions bitvector.tactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_var gen_heap invariants.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvModelBytes.
Require Import RiscvExtras.
Require Import RegFile.
Require Import WpNext.
Require Import WpMmodeLeafBase.
Require Import SmodeCore.
Require Import StackOwn.
Require Import CalleeSaved.
Require Import KernelRvcDecode.
Require Import InstrBytes.
Require Import KernelText.
Require Import WpSconfAlu WpSconfMem WpSconfCtl WpSconfBtype.
Require Import WpSmodeIntr.
Require Import IntrDefs.
Require Import CpuOwn.
Require Import HartTp.
Require Import PageGeom PageFields.
Require Import ProcGeom.
Require Import PtBuild.
Require Import UserPtTree.
Require Import ProcPtOwn.
Require Import FdSlots FileInv.
Require Import WpLock.
Require Import SwtchCtx.
Require Import ProcInv.
Require Import KallocInv.
Require Import KvmSpec.
Require Import SchedCtx.
Require Import InodeInv.
Require Import IrefSlots.
Require Import IcacheInv.
Require Import WaitInv.
Require Import SpecAllocpid.
Require Import SpecProcinit.
Require Import SpecPanic.
Require Import SpecFreeproc.
Require Import SpecMyproc.
Require Import SpecAllocproc.
Require Import SpecUvmcopy.
Require Import SpecRelease.
Require Import SpecAcquire.
Require Import SpecFiledup.
Require Import SpecIdup.
Require Import SpecSafestrcpy.
Require Import SpecForkretPark.
Require Import SpecKfork.
Require Import CodeKfork.
Require Import ProofKforkParts.
Require Import ProofKfork.
Require Import ProofKforkB1.
Require Import ProofKforkB2.
Require Import ProofKforkB3.
Require Import ProofKforkB4.
Require Import ProofKforkB5.
Require Import ProofKforkB6.
Require Import ProofKforkB7.
From Kernel Require KernelSyms.
Local Open Scope Z_scope.

(* A syscall-altitude goal carries [ProcInv.tf_page]'s 4096-conjunct big-op;
   printing one takes tens of minutes, so a one-line mistake reads as a hang.
   durable-notes.md's rule. *)
Set Printing Depth 40.

Notation KF := KernelSyms.kfork (only parsing).

Module Kfork (MP : MYPROC) (AP : ALLOCPROC_GEN) (UC : UVMCOPY)
             (FP : FREEPROC) (RL : RELEASE) (AQ : ACQUIRE)
             (FD : FILEDUP) (ID : IDUP) (SS : SAFESTRCPY)
             (FRP : FORKRET_PARK).

  Module B6 := KforkPrologue MP AP UC.
  Module B1 := KforkB1 FP RL.
  Module B3 := KforkB3 FD.
  Module B4 := KforkB4 ID SS.
  Module B5 := KforkB5 AQ RL FRP.

Section KforkArms.
  Context `{!riscvGS Σ, !lockG Σ, !sieG Σ, !kallocG Σ, !fileG Σ, !fdslotG Σ,
            !icacheG Σ, !irefslotG Σ}.
  Context `{GEN : GenId} `{CID0 : CpuId}.

  Notation Rra := (mword_of_int 1 : mword 5).
  Notation Rs0 := (mword_of_int 8 : mword 5).
  Notation Rs1 := (mword_of_int 9 : mword 5).
  Notation Ra0 := (mword_of_int 10 : mword 5).
  Notation Ra3 := (mword_of_int 13 : mword 5).
  Notation Ra4 := (mword_of_int 14 : mword 5).
  Notation Ra5 := (mword_of_int 15 : mword 5).
  Notation Rs2 := (mword_of_int 18 : mword 5).
  Notation Rs3 := (mword_of_int 19 : mword 5).
  Notation Rs4 := (mword_of_int 20 : mword 5).
  Notation Rs5 := (mword_of_int 21 : mword 5).

  (* =================================================================== *)
  (*  ARM 2 -- uvmcopy failed.  [Hcont7c] now hands the frame as           *)
  (*  [∃ w4 w5, ProofKfork.kfk_frame_at sp0 ra0 s00 s10 s50 w4 w5 (m !!!   *)
  (*  Regidx Rs4)] -- slot 6 pinned, slots 4/5 still existential -- which   *)
  (*  is exactly what [ProofKforkB1.kfk_exit_uvmcopy] needs; this is now    *)
  (*  a complete, hypothesis-free match for [Hcont7c]'s own type.           *)
  (* =================================================================== *)
  Lemma kfork_arm2
      (γa γf γi γl2 : gname) (γs : list gname)
      (m : regfile) (K lvl : nat) (eb b : bool) (pme : mword 64) (C : iProp Σ)
      (pid_p : mword 32) (Vp : pprivate) (ck : nat) (cdev cinum : mword 32)
      (sp0 ra0 s00 s10 s50 : mword 64) (npa : mword 64) (j : nat)
      (pid_c : mword 32) (ch : mword 64) (Vc : pprivate) (Mt : regfile) :
    (52 <= K)%nat ->
    (Z.of_nat lvl + 2 < 2 ^ 31)%Z ->
    match lvl with O => eb | S _ => false end = b ->
    m !!! Regidx csp_rs1 = sp0 -> m !!! Regidx Rra = ra0 -> m !!! Regidx Rs0 = s00 ->
    m !!! Regidx Rs1 = s10 -> m !!! Regidx Rs5 = s50 ->
    Mt !!! Regidx csp_rs1 = pa_stk sp0 8 -> Mt !!! Regidx Rs4 = proc_addr j ->
    npa = proc_addr j -> (j < NPROC)%nat -> γs !! j = Some γl2 ->
    pv_ofile Vc = replicate NOFILE (zero_reg : mword 64) ->
    pv_cwd Vc = (zero_reg : mword 64) ->
    (forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 ->
        r <> Rs0 -> r <> Rs1 -> r <> Rs4 -> r <> Rs5 -> Mt !!! Regidx r = m !!! Regidx r) ->
    procs_inv γs -∗
    sie_cap_gpr Mt (K - 8)%nat false pme -∗
    cpu_own (S lvl) eb pme C false -∗
    arm_pay lvl eb pme -∗
    kernel_text -∗
    pc_is (mword_of_int (KF + 0x7c) : mword 64) -∗
    (∃ w4 w5 : mword 64, ProofKfork.kfk_frame_at sp0 ra0 s00 s10 s50 w4 w5 (m !!! Regidx Rs4)) -∗
    proc_priv γf pme pid_p Vp -∗
    proc_priv γf npa pid_c Vc -∗
    SchedCtx.proc_held cpu_id j γl2 USED ch -∗
    ProcGeom.hart_at_any npa -∗
    FdSlots.fd_slots FDSPARE -∗
    SwtchCtx.own_ctx (p_context npa) -∗
    (∃ q' : Qp, inode_ref γi ck q' cdev cinum) -∗
    kalloc_env γa None -∗
    wp_next b pme (fun (CID : CpuId) =>
      ∀ mr : regfile,
        ⌜ callee_saved m mr ⌝ -∗
        pc_is (ret_pc ra0) -∗
        kfork_post γa γf γi lvl eb pme C None b pid_p Vp ck cdev cinum K mr
          (mr !!! Regidx Ra0) -∗
        WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros HK Hlvl Hbeq Hmsp Hmra Hms0 Hms1 Hms5 HMtsp HMts4 Hnpa HjN Hgamma
      Hofnull Hcwdnull HMtthr.
    subst npa.
    iIntros "#Hprocs Hcg Hcpu Hpay #Htext Hpc Hframe
             Hpv HCpriv Hheld Hhart Hfd Hctx Hiref Hkalloc Hcont".
    iDestruct "Hframe" as (w4 w5) "Hframe".
    rewrite /ProofKfork.kfk_frame_at.
    iDestruct "Hframe" as "(Hb1 & Hb2 & Hb3 & Hb4 & Hb5 & Hb6 & Hb7 & Hb8)".
    iAssert (∃ w4', word_pointsto (pa_stk sp0 4) (DfracOwn 1) w4')%I with "[Hb4]" as "Hb4x".
    { iExists w4. iExact "Hb4". }
    iAssert (∃ w5', word_pointsto (pa_stk sp0 5) (DfracOwn 1) w5')%I with "[Hb5]" as "Hb5x".
    { iExists w5. iExact "Hb5". }
    iDestruct (SchedCtx.procs_inv_lookup γs j γl2 Hgamma with "Hprocs") as "#Hislock".
    iDestruct (ProofKforkParts.kfk_of_priv γf (proc_addr j) pid_c Vc Hofnull Hcwdnull
                 with "HCpriv Hfd Hctx") as "(Hfprest & Hfppt & Hfptf)".
    iApply (B1.kfk_exit_uvmcopy γs γa γl2 j ch Vc pid_c (pv_upt Vc) (pv_tf Vc)
              m Mt K sp0 ra0 s00 s10 s50 pme eb C lvl
              HK Hlvl Hmsp Hmra Hms0 Hms1 Hms5 HMtsp HMts4 HMtthr
              with "Hcg Hcpu Hpay Htext Hpc Hb1 Hb2 Hb3 Hb4x Hb5x Hb6 Hb7 Hb8
                    Hheld Hhart Hislock Hkalloc Hfprest Hfppt Hfptf [-]").
    iIntros (CID Hcross mf) "%Hpf Hcg Hpc Hcpu2 Hkalloc2".
    destruct Hpf as [Hcsmf Hmfa0].
    iSpecialize ("Hcont" $! CID with "[%]").
    { rewrite -Hbeq. exact Hcross. }
    iApply ("Hcont" $! mf with "[%] Hpc [Hcg Hcpu2 Hpv Hiref Hkalloc2]").
    - exact Hcsmf.
    - rewrite /kfork_post.
      iEval (rewrite Hbeq) in "Hcg". iEval (rewrite Hbeq) in "Hcpu2".
      iSplitL "Hcg"; [iExact "Hcg" |].
      iSplitL "Hcpu2"; [iExact "Hcpu2" |].
      iSplitL "Hpv"; [iExact "Hpv" |].
      iSplitL "Hiref"; [iExact "Hiref" |].
      iRight. iLeft. iSplitR; [iPureIntro; rewrite Hmfa0; reflexivity | iExact "Hkalloc2"].
  Qed.

  (* =================================================================== *)
  (*  ARM 1 -- allocproc found no free slot.                             *)
  (*                                                                       *)
  (*  SEAM: [ProofKforkB6.kfk_prologue]'s [Hcont10a] does not hand back    *)
  (*  [cpu_own lvl eb pme C b] at all.  Both of its two call sites          *)
  (*  (allocproc's two "not found" sub-cases) hold "Hcpu" -- allocproc's    *)
  (*  own postcondition hands it back explicitly, e.g. destructured as      *)
  (*  [(%Hrv & Hcg & Hcpu & Henv')] right before the call -- but neither     *)
  (*  call site forwards "Hcpu" into [Hcont10a], because [Hcont10a]'s type  *)
  (*  has no slot for it; Iris's affine BI just lets it drop silently.      *)
  (*  [kfork_post] needs [cpu_own lvl eb pme C b] unconditionally (outside  *)
  (*  the 3-way arm disjunction), so [wp_kfork_sconf] cannot reconstruct    *)
  (*  it for this arm from what [Hcont10a] states.  Supplied here as an     *)
  (*  extra premise, at exactly the "b" [kfork_post] wants (arm 1 never     *)
  (*  crosses a lock, so "b" never moves from the caller's own). *)
  (* =================================================================== *)
  Lemma kfork_arm1
      (γa γf γi : gname)
      (m : regfile) (K lvl : nat) (eb b : bool) (pme : mword 64) (C : iProp Σ)
      (on : option nat) (pid_p : mword 32) (Vp : pprivate) (ck : nat) (cdev cinum : mword 32)
      (sp0 ra0 s00 s10 s50 : mword 64) (Mt : regfile) :
    (8 <= K)%nat ->
    m !!! Regidx csp_rs1 = sp0 -> m !!! Regidx Rra = ra0 -> m !!! Regidx Rs0 = s00 ->
    m !!! Regidx Rs1 = s10 -> m !!! Regidx Rs5 = s50 ->
    Mt !!! Regidx csp_rs1 = pa_stk sp0 8 ->
    (forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 ->
        r <> Rs0 -> r <> Rs1 -> r <> Rs5 -> Mt !!! Regidx r = m !!! Regidx r) ->
    sie_cap_gpr Mt (K - 8)%nat b pme -∗
    cpu_own lvl eb pme C b -∗
    kernel_text -∗
    pc_is (mword_of_int (KF + 0x10a) : mword 64) -∗
    kfk_frame sp0 ra0 s00 s10 s50 -∗
    proc_priv γf pme pid_p Vp -∗
    (∃ q' : Qp, inode_ref γi ck q' cdev cinum) -∗
    ( kalloc_env γa on
      ∨ (∃ n : nat, ⌜(n <= K_allocproc)%nat /\ avail_zero (avail_sub on n)⌝ ∗
         kalloc_env γa None) ) -∗
    wp_next b pme (fun (CID : CpuId) =>
      ∀ mr : regfile,
        ⌜ callee_saved m mr ⌝ -∗
        pc_is (ret_pc ra0) -∗
        kfork_post γa γf γi lvl eb pme C on b pid_p Vp ck cdev cinum K mr
          (mr !!! Regidx Ra0) -∗
        WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros HK8 Hmsp Hmra Hms0 Hms1 Hms5 HMtsp HMtthr.
    iIntros "Hcg Hcpu #Htext Hpc Hframe Hpv Hiref Hkalloc Hcont".
    iApply (ProofKfork.kfk_exit_alloc m Mt K sp0 ra0 s00 s10 s50 pme b
              HK8 Hmsp Hmra Hms0 Hms1 Hms5 HMtsp HMtthr
              with "Hcg Htext Hpc Hframe [-]").
    iIntros (CID Hcross mf) "%Hpf Hcg Hpc".
    destruct Hpf as [Hcsmf Hmfa0].
    iDestruct (cpu_own_transport CID0 CID lvl eb pme C b Hcross with "Hcpu") as "Hcpu".
    iSpecialize ("Hcont" $! CID with "[%]"); [exact Hcross |].
    iApply ("Hcont" $! mf with "[%] Hpc [Hcg Hcpu Hpv Hiref Hkalloc]").
    - exact Hcsmf.
    - rewrite /kfork_post.
      iSplitL "Hcg"; [iExact "Hcg" |].
      iSplitL "Hcpu"; [iExact "Hcpu" |].
      iSplitL "Hpv"; [iExact "Hpv" |].
      iSplitL "Hiref"; [iExact "Hiref" |].
      iLeft. iSplitR; [iPureIntro; rewrite Hmfa0; reflexivity | iExact "Hkalloc"].
  Qed.

  (* =================================================================== *)
  (*  ARM 3 -- uvmcopy succeeded: the trapframe copy loop (ProofKforkB2),  *)
  (*  MY OWN block (ProofKforkB7), the fd scan (ProofKforkB3), idup/       *)
  (*  safestrcpy/pid-read (ProofKforkB4), the two lock crossings and the   *)
  (*  RUNNABLE park (ProofKforkB5), and the three lazy reloads             *)
  (*  (ProofKfork.kfk_tail_succ) -- all the way to [kfork_post]'s third    *)
  (*  disjunct.  [Hcont4a]'s two previous gaps (the ofile/cwd conjunct on   *)
  (*  [Vc'], the existential frame) are both fixed now, so every register/  *)
  (*  frame premise below matches [Hcont4a] exactly.                        *)
  (*                                                                        *)
  (*  SEAM (new, found assembling this arm): [Hcont4a] hands the raw        *)
  (*  scheduler context as the GENERIC [SwtchCtx.own_ctx (p_context npa)]   *)
  (*  (14 words, contents existential, no relation to any specific value)   *)
  (*  -- exactly the form [ProofKforkParts.kfk_of_priv]/freeproc want on     *)
  (*  the uvmcopy-FAILURE arm.  But arm 3 never frees the child; +0xc2's     *)
  (*  first release instead runs [SpecForkretPark.forkret_park] (inside     *)
  (*  [ProofKforkB5.kfk_b5]), whose contract ([SpecForkretPark.v]'s own      *)
  (*  header: precisely what allocproc's own postcondition hands the        *)
  (*  caller for the context) needs the RAW, SPECIFIC shape instead:         *)
  (*    is_kstack npa ks ∗                                                  *)
  (*    ctx_cells (p_context npa) (forkret_pc :: add_vec ks 4096 :: rest)    *)
  (*  A generic 14-word [own_ctx] cannot supply this -- its contents carry   *)
  (*  no relation to [ks]/[forkret_pc] at all, and [is_kstack]/[ctx_cells]   *)
  (*  are TWO SEPARATE resources, not one own_ctx can be split into.  Both   *)
  (*  pieces genuinely exist at the point B6 dispatches to [Hcont4a] (they   *)
  (*  come straight off allocproc's own postcondition, which is what lets    *)
  (*  B6 build the SAME [own_ctx] for [Hcont7c] two lines earlier); B6's      *)
  (*  proof simply wraps them into the weaker, generic form before handing   *)
  (*  off, exactly the same pattern as the [kfk_frame]/[kfk_frame_at] and    *)
  (*  ofile/cwd gaps already fixed.  [ks]/[rest] and the two resources are   *)
  (*  therefore taken here as an explicit extra hypothesis (mirroring        *)
  (*  [Hcont7c]'s conjunct is not enough here -- unlike ofile/cwd, there is  *)
  (*  no already-generic resource to strengthen; [Hcont4a] needs a NEW        *)
  (*  disjunct/conjunct, in the same shape [own_ctx]'s definition shows:      *)
  (*  [∃ ks rest, ⌜length rest = 12⌝ ∗ is_kstack npa ks ∗ ctx_cells (p_context *)
  (*  npa) (forkret_pc :: add_vec ks 4096 :: rest)] in place of [own_ctx      *)
  (*  (p_context npa)]).  Everything else in this lemma is hypothesis-free.  *)
  (* =================================================================== *)
  Lemma kfork_arm3
      (γa γf γil γi γw γl : gname) (γs : list gname)
      (m : regfile) (K lvl : nat) (eb b : bool) (pme : mword 64) (C : iProp Σ)
      (on : option nat) (pid_p : mword 32) (Vp : pprivate)
      (ck : nat) (cdev cinum : mword 32)
      (sp0 ra0 s00 s10 s50 : mword 64)
      (Mt : regfile) (npa : mword 64) (j : nat) (γl2 : gname)
      (pid_c : mword 32) (ch : mword 64) (Vc' : pprivate) (tfsrc tfdst : mword 44)
      (ks : mword 64) (rest : list (mword 64)) :
    (56 <= K)%nat ->
    (Z.of_nat lvl + 2 < 2 ^ 31)%Z ->
    match lvl with O => eb | S _ => false end = b ->
    pv_cwd Vp = ientry ck ->
    m !!! Regidx csp_rs1 = sp0 -> m !!! Regidx Rra = ra0 -> m !!! Regidx Rs0 = s00 ->
    m !!! Regidx Rs1 = s10 -> m !!! Regidx Rs5 = s50 ->
    Mt !!! Regidx csp_rs1 = pa_stk sp0 8 ->
    Mt !!! Regidx Rs4 = npa ->
    Mt !!! Regidx Rs5 = pme ->
    Mt !!! Regidx Ra5 = a_tf_word tfsrc 0 ->
    Mt !!! Regidx Ra4 = a_tf_word tfdst 0 ->
    Mt !!! Regidx Ra3 = a_tf_word tfsrc 36 ->
    ud_tfp (pv_upt Vp) = tfsrc -> ud_tfp (pv_upt Vc') = tfdst ->
    (forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 ->
        r <> Rs0 -> r <> Rs1 -> r <> Rs4 -> r <> Rs5 -> Mt !!! Regidx r = m !!! Regidx r) ->
    npa = proc_addr j -> (j < NPROC)%nat -> γs !! j = Some γl2 ->
    pv_ofile Vc' = replicate NOFILE (zero_reg : mword 64) ->
    pv_cwd Vc' = (zero_reg : mword 64) ->
    length rest = 12%nat ->
    kernel_text -∗
    panic_wp_any -∗
    procs_inv γs -∗
    sie_cap_gpr Mt (K - 8)%nat false pme -∗
    cpu_own (S lvl) eb pme C false -∗
    pc_is (mword_of_int (KF + 0x4a) : mword 64) -∗
    kfk_frame_at sp0 ra0 s00 s10 s50
      (m !!! Regidx Rs2) (m !!! Regidx Rs3) (m !!! Regidx Rs4) -∗
    proc_priv γf pme pid_p Vp -∗
    proc_priv γf npa pid_c Vc' -∗
    SchedCtx.proc_held cpu_id j γl2 USED ch -∗
    ProcGeom.hart_at_any npa -∗
    FdSlots.fd_slots FDSPARE -∗
    SwtchCtx.own_ctx (p_context npa) -∗
    IntrDefs.arm_pay lvl eb pme -∗
    (∃ q' : Qp, inode_ref γi ck q' cdev cinum) -∗
    kalloc_env γa None -∗
    is_lock γw wait_lock_addr "wait_lock"%string wait_res -∗
    is_ftable γl γf -∗
    is_itable γil γi -∗
    itable_inv γi -∗
    iref_slot -∗
    (* SEAM (see header): the raw context, unavailable from [own_ctx] above. *)
    ProcInv.is_kstack npa ks -∗
    SwtchCtx.ctx_cells (p_context npa) (SpecForkretPark.forkret_pc :: add_vec ks (mword_of_int 4096) :: rest) -∗
    wp_next b pme (fun (CID : CpuId) =>
      ∀ mr : regfile,
        ⌜ callee_saved m mr ⌝ -∗
        pc_is (ret_pc ra0) -∗
        kfork_post γa γf γi lvl eb pme C on b pid_p Vp ck cdev cinum K mr
          (mr !!! Regidx Ra0) -∗
        WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros HK Hlvl Hbeq Hcwd Hmsp Hmra Hms0 Hms1 Hms5 HMtsp HMts4 HMts5
      HMta5 HMta4 HMta3 Htfsrc Htfdst HMtthr Hnpa HjN Hgamma
      Hofnull Hcwdnull Hrestlen.
    subst tfsrc tfdst.
    iIntros "#Htext #Hpanic #Hprocs Hcg Hcpu Hpc Hframe Hpv HCpriv
             Hheld Hhart Hfd Hctx Hpay Hiref Hkalloc Hwlock Hft
             Hitb Hitinv Hirs Hks Hkctx Hcont".
    rewrite /kfk_frame_at.
    iDestruct "Hframe" as "(Hb1 & Hb2 & Hb3 & Hb4 & Hb5 & Hb6 & Hb7 & Hb8)".
    iDestruct "Hb8" as (w8) "Hb8".
    iDestruct "Hiref" as (cq) "Hiref".
    iDestruct (ProofKforkParts.proc_priv_tfp_valid with "Hpv") as %Hpvsrc.
    iDestruct (ProofKforkParts.proc_priv_tfp_valid with "HCpriv") as %Hpvdst.
    iDestruct (ProofKforkParts.proc_priv_tf_upd with "Hpv") as "(Htf_p & Htfp_p & Hclose_p)".
    iDestruct (ProofKforkParts.proc_priv_tf_upd with "HCpriv") as "(Htf_c & Htfp_c & Hclose_c)".
    iDestruct (ProofKforkB7.kfkb7_tf_len with "Htfp_p") as %Hlenp.
    iDestruct (ProofKforkB7.kfkb7_tf_len with "Htfp_c") as %Hlenc.
    (* ---- ProofKforkB2: the trapframe copy loop ---- *)
    iApply (ProofKforkB2.kfk_tf_copy_loop Mt (ud_tfp (pv_upt Vp)) (ud_tfp (pv_upt Vc'))
              (pv_tf Vp) (pv_tf Vc') (K - 8)%nat pme
              Hpvsrc Hpvdst Hlenp Hlenc HMta5 HMta4 HMta3
              with "Hcg Htext Hpc Htfp_p Htfp_c [-]").
    iApply wp_next_off_intro.
    iIntros (mf) "%Hpf Hcg Hpc Htfp_p Htfp_c".
    destruct Hpf as (Hcsmf & Hmfa5 & Hmfa4).
    iDestruct ("Hclose_p" $! (pv_tf Vp) with "Htf_p Htfp_p") as "Hpv".
    iEval (rewrite ProofKforkParts.upd_pt_id) in "Hpv".
    iDestruct ("Hclose_c" $! (pv_tf Vp) with "Htf_c Htfp_c") as "HCpriv".
    set (V1 := upd_pt Vc' (pv_upt Vc') (pv_tf Vp)).
    change (upd_pt Vc' (pv_upt Vc') (pv_tf Vp)) with V1.
    assert (Hmfs4 : mf !!! Regidx Rs4 = npa)
      by (rewrite (callee_saved_lookup Hcsmf Rs4 ltac:(vm_compute; reflexivity)); exact HMts4).
    assert (Hmfs5 : mf !!! Regidx Rs5 = pme)
      by (rewrite (callee_saved_lookup Hcsmf Rs5 ltac:(vm_compute; reflexivity)); exact HMts5).
    (* ---- ProofKforkB7: MY OWN block ---- *)
    iApply (ProofKforkB7.kfk_b7 γf npa pme pid_c V1 mf (K - 8)%nat pme Hmfs4 Hmfs5
              with "Hcg Htext Hpc HCpriv [-]").
    iApply wp_next_off_intro.
    iIntros (Mx) "%Hpx Hcg Hpc HCpriv".
    destruct Hpx as (HMxs1 & HMxs2 & HMxs3 & HMxs4 & HMxs5 & HMxthr).
    assert (HMxsp : Mx !!! Regidx csp_rs1 = pa_stk sp0 8).
    { assert (Hcs : is_cs_idx csp_rs1 = true) by (vm_compute; reflexivity).
      assert (Hne1 : csp_rs1 <> Rs1) by (vm_compute; discriminate).
      assert (Hne2 : csp_rs1 <> Rs2) by (vm_compute; discriminate).
      assert (Hne3 : csp_rs1 <> Rs3) by (vm_compute; discriminate).
      rewrite (HMxthr csp_rs1 Hcs Hne1 Hne2 Hne3).
      rewrite (callee_saved_lookup Hcsmf csp_rs1 ltac:(vm_compute; reflexivity)).
      exact HMtsp. }
    assert (HMxs0 : Mx !!! Regidx Rs0 = Mt !!! Regidx Rs0).
    { assert (Hcs : is_cs_idx Rs0 = true) by (vm_compute; reflexivity).
      assert (Hne1 : Rs0 <> Rs1) by (vm_compute; discriminate).
      assert (Hne2 : Rs0 <> Rs2) by (vm_compute; discriminate).
      assert (Hne3 : Rs0 <> Rs3) by (vm_compute; discriminate).
      rewrite (HMxthr Rs0 Hcs Hne1 Hne2 Hne3).
      apply (callee_saved_lookup Hcsmf Rs0 ltac:(vm_compute; reflexivity)). }
    assert (HMxfull : forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 ->
                r <> Rs0 -> r <> Rs1 -> r <> Rs2 -> r <> Rs3 -> r <> Rs4 -> r <> Rs5 ->
                Mx !!! Regidx r = m !!! Regidx r).
    { intros r Hr Ncsp Ns0 Ns1 Ns2 Ns3 Ns4 Ns5.
      rewrite (HMxthr r Hr Ns1 Ns2 Ns3).
      rewrite (callee_saved_lookup Hcsmf r Hr).
      exact (HMtthr r Hr Ncsp Ns0 Ns1 Ns4 Ns5). }
    set (V2 := upd_pt V1 (pv_upt V1) (<[(14%nat) := zero_reg]> (pv_tf V1))).
    change (upd_pt V1 (pv_upt V1) (<[(14%nat) := zero_reg]> (pv_tf V1))) with V2.
    assert (HofnullV2 : pv_ofile V2 = replicate NOFILE (zero_reg : mword 64)).
    { rewrite /V2 /V1. cbn [pv_ofile upd_pt]. exact Hofnull. }
    (* ---- ProofKforkB3: the fd scan, ALL 16 iterations in one shot ---- *)
    iPoseProof (B3.kfkb3_fd_loop γl γf pme npa pid_p pid_c Vp V2 m K (S lvl) eb false C
                  (pa_stk sp0 8) (Mt !!! Regidx Rs0) ltac:(lia) ltac:(lia) HofnullV2) as "Hb3app".
    iSpecialize ("Hb3app" with "Htext Hft Hpanic").
    iSpecialize ("Hb3app" $! 0%nat Mx
      with "[%] [%] [Hb1 Hb2 Hb3 Hb4 Hb5 Hb6 Hb7 Hb8
                     Hheld Hhart Hfd Hctx Hpay Hiref Hkalloc Hwlock Hitb Hitinv Hirs Hks Hkctx Hcont]
            Hcg Hcpu Hpc Hpv [HCpriv]").
    - unfold NOFILE. lia.
    - split_and!.
      + exact HMxsp.
      + exact HMxs0.
      + exact HMxs1.
      + exact HMxs2.
      + exact HMxs3.
      + exact HMxs4.
      + exact HMxs5.
      + exact HMxfull.
    - iApply wp_next_off_intro. iIntros (Mx2) "%Hregs2 Hsc Hown Hpcx Hpvx Hpvcx".
      destruct Hregs2 as (Hd1 & Hd2 & Hd3 & Hd4 & Hd5).
      (* ---- ProofKforkB4: idup / safestrcpy / pid read ---- *)
      iApply (B4.kfk_b4 γf γil γi ck cq cdev cinum pid_p pid_c Vp
                (kfk_childV V2 (pv_ofile Vp) NOFILE) pme npa
                Mx2 K (S lvl) eb C
                ltac:(lia) ltac:(lia) Hcwd Hd4 Hd3
                with "Hsc Hown Htext Hpcx Hpanic Hitb Hitinv Hirs Hiref Hpvx Hpvcx [-]").
      iApply wp_next_off_intro.
      iIntros (mf4) "%Hp4 Hsc4 Hown4 Hpc4 Hpvx4 Hpvcx4 Hiref4".
      destruct Hp4 as (Hthr4 & Hpid4).
      iDestruct "Hpvcx4" as (Vc4) "(%HVc4 & Hpvcx4)".
      assert (Hmf4s4 : mf4 !!! Regidx Rs4 = npa).
      { rewrite (Hthr4 Rs4 ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)).
        exact Hd3. }
      assert (Hmf4s5 : mf4 !!! Regidx Rs5 = pme).
      { rewrite (Hthr4 Rs5 ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)).
        exact Hd4. }
      (* ---- convert the FEW resources B5 needs at the literal [proc_addr j] ---- *)
      rewrite Hnpa in Hmf4s4.
      iEval (rewrite Hnpa) in "Hhart".
      iEval (rewrite Hnpa) in "Hks".
      iEval (rewrite Hnpa) in "Hkctx".
      iEval (rewrite Hnpa) in "Hpvcx4".
      (* ---- ProofKforkB5: the two lock crossings, the RUNNABLE park ---- *)
      iApply (B5.kfk_b5 γs γf γw γl2 j mf4 K lvl eb (match lvl with O => eb | S _ => false end)
                pme ks pid_c Vc4 ch rest (sign_extend' 64 pid_c) C
                ltac:(lia) ltac:(lia) HjN Hgamma Hrestlen eq_refl Hmf4s4 Hmf4s5 Hpid4
                with "Hsc4 Hown4 Hpay Htext Hpc4 Hpanic Hprocs Hwlock
                      Hheld Hhart Hpvcx4 Hfd Hks Hkctx [-]").
      (* [b] is symbolic here (B5's own exit index): an ordinary crossing,
         not [wp_next_off_intro] -- the brief's correction (a). *)
      iIntros (CID5 Hcross5 mf5) "%Hcs5 Hsc5 Hown5 Hpc5".
      assert (Hmf5sp : mf5 !!! Regidx csp_rs1 = pa_stk sp0 8)
        by (rewrite (callee_saved_lookup Hcs5 csp_rs1 ltac:(vm_compute; reflexivity));
            rewrite (Hthr4 csp_rs1 ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate));
            exact Hd1).
      assert (Hmf5s1 : mf5 !!! Regidx Rs1 = sign_extend' 64 pid_c)
        by (rewrite (callee_saved_lookup Hcs5 Rs1 ltac:(vm_compute; reflexivity)); exact Hpid4).
      assert (Hmf5thr : forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 ->
                  r <> Rs0 -> r <> Rs1 -> r <> Rs2 -> r <> Rs3 -> r <> Rs4 -> r <> Rs5 ->
                  mf5 !!! Regidx r = m !!! Regidx r).
      { intros r Hr Ncsp Ns0 Ns1 Ns2 Ns3 Ns4 Ns5.
        rewrite (callee_saved_lookup Hcs5 r Hr).
        rewrite (Hthr4 r Hr Ns1).
        exact (Hd5 r Hr Ncsp Ns0 Ns1 Ns2 Ns3 Ns4 Ns5). }
      (* ---- ProofKfork.kfk_tail_succ: the three lazy reloads ---- *)
      iApply (ProofKfork.kfk_tail_succ (CID0 := CID5) m mf5 K sp0 ra0 s00 s10 s50
                (sign_extend' 64 pid_c) w8 pme (match lvl with O => eb | S _ => false end)
                ltac:(lia) Hmsp Hmra Hms0 Hms1 Hms5 Hmf5sp Hmf5s1 Hmf5thr
                with "Hsc5 Htext Hpc5 Hb1 Hb2 Hb3 Hb4 Hb5 Hb6 Hb7 Hb8 [-]").
      iIntros (CID6 Hcross6 mr) "%Hpost Hsc6 Hpc6".
      destruct Hpost as (Hcsm & Hrv).
      iDestruct (cpu_own_transport CID5 CID6 lvl eb pme C
                   (match lvl with O => eb | S _ => false end) Hcross6 with "Hown5") as "Hown5".
      iSpecialize ("Hcont" $! CID6 with "[%]").
      { rewrite -Hbeq. intros Hdisj. transitivity CID5; [exact (Hcross6 Hdisj) | exact (Hcross5 Hdisj)]. }
      iApply ("Hcont" $! mr with "[%] Hpc6 [Hsc6 Hown5 Hpvx4 Hiref4 Hkalloc]").
      + exact Hcsm.
      + rewrite /kfork_post.
        iEval (rewrite Hbeq) in "Hsc6". iEval (rewrite Hbeq) in "Hown5".
        iSplitL "Hsc6"; [iExact "Hsc6" |].
        iSplitL "Hown5"; [iExact "Hown5" |].
        iSplitL "Hpvx4"; [iExact "Hpvx4" |].
        iSplitL "Hiref4"; [iExists (cq/2)%Qp; iExact "Hiref4" |].
        iRight. iRight. iExists pid_c. iSplit; [iPureIntro; rewrite Hrv; reflexivity | iExact "Hkalloc"].
    - rewrite kfk_childV_0. iExact "HCpriv".
    - iApply "Hb3app".
  Qed.

End KforkArms.
End Kfork.
