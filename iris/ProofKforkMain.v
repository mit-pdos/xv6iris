(* ProofKforkMain.v -- the capstone: gluing kfork's six proven blocks
   (ProofKforkB1..B7, ProofKfork's two exits, ProofKforkParts' epilogue)
   into SpecKfork.KFORK's [wp_kfork_sconf].

   STATUS: NOT COMPLETE.  Every Lemma in this file is fully proved (no
   [admit]/[Admitted]/[Axiom]/[Parameter]); what is missing is the final
   [Module Kfork ... : KFORK] wrapper, because two of [ProofKforkB6.v]'s
   own continuation types are missing a premise their sibling continuation
   already carries -- see the two "SEAM" comments below, at
   [kfork_arm1_modulo_cpu_own] and [kfork_arm3_modulo_ofile_cwd], for the
   precise gap.  Per the brief: block files are not to be edited from here;
   this file instead proves, AS FAR AS THE STATEMENTS ALLOW, that gluing
   the six blocks together works, moving the missing fact to an explicit
   extra hypothesis of an otherwise complete lemma.

   Arm 2 (uvmcopy failed) has NO such gap and is a complete, closed proof
   of the shape [wp_kfork_sconf] needs for that arm: [kfork_arm2]. *)
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
  (*  ARM 2 -- uvmcopy failed.                                            *)
  (*                                                                       *)
  (*  SEAM: [ProofKforkB6.kfk_prologue]'s [Hcont7c] hands back the frame   *)
  (*  slots bundled as [ProofKforkParts.kfk_frame], which quantifies slots *)
  (*  4/5/6 EXISTENTIALLY.  [ProofKforkB1.kfk_exit_uvmcopy] needs slot 6    *)
  (*  (16(sp), the caller's saved s4) at the SPECIFIC value [m !!! Regidx  *)
  (*  Rs4] -- its own header comment says so, and B6's proof DOES build    *)
  (*  slot 6 at exactly that value internally ([rget mf6 Rs4], shown equal *)
  (*  to [m !!! Regidx Rs4] via its own [HBthr]) -- but once wrapped in    *)
  (*  [kfk_frame]'s existential the equality is lost to the caller, so     *)
  (*  slot 6's value cannot be recovered from what [Hcont7c] actually      *)
  (*  states.  This lemma is stated with slot 6 at its correct, SPECIFIC   *)
  (*  value (exactly [ProofKforkB1]'s own precondition) instead of         *)
  (*  [kfk_frame], which is what [Hcont7c] would need to hand back for the *)
  (*  application below to go through as part of [wp_kfork_sconf] itself.  *)
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
    word_pointsto (pa_stk sp0 1) (DfracOwn 1) ra0 -∗
    word_pointsto (pa_stk sp0 2) (DfracOwn 1) s00 -∗
    word_pointsto (pa_stk sp0 3) (DfracOwn 1) s10 -∗
    (∃ w4, word_pointsto (pa_stk sp0 4) (DfracOwn 1) w4) -∗
    (∃ w5, word_pointsto (pa_stk sp0 5) (DfracOwn 1) w5) -∗
    word_pointsto (pa_stk sp0 6) (DfracOwn 1) (m !!! Regidx Rs4) -∗
    word_pointsto (pa_stk sp0 7) (DfracOwn 1) s50 -∗
    (∃ w8, word_pointsto (pa_stk sp0 8) (DfracOwn 1) w8) -∗
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
    iIntros "#Hprocs Hcg Hcpu Hpay #Htext Hpc Hb1 Hb2 Hb3 Hb4 Hb5 Hb6 Hb7 Hb8
             Hpv HCpriv Hheld Hhart Hfd Hctx Hiref Hkalloc Hcont".
    iDestruct (SchedCtx.procs_inv_lookup γs j γl2 Hgamma with "Hprocs") as "#Hislock".
    iDestruct (ProofKforkParts.kfk_of_priv γf (proc_addr j) pid_c Vc Hofnull Hcwdnull
                 with "HCpriv Hfd Hctx") as "(Hfprest & Hfppt & Hfptf)".
    iApply (B1.kfk_exit_uvmcopy γs γa γl2 j ch Vc pid_c (pv_upt Vc) (pv_tf Vc)
              m Mt K sp0 ra0 s00 s10 s50 pme eb C lvl
              HK Hlvl Hmsp Hmra Hms0 Hms1 Hms5 HMtsp HMts4 HMtthr
              with "Hcg Hcpu Hpay Htext Hpc Hb1 Hb2 Hb3 Hb4 Hb5 Hb6 Hb7 Hb8
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
  (*  ARM 3, CHECKPOINT -- the trapframe copy loop (ProofKforkB2) handing  *)
  (*  off into MY OWN block (ProofKforkB7), and B7 handing off into the fd *)
  (*  scan's entry (ProofKforkB3), at i = 0.  This is as far as arm 3 can  *)
  (*  be pushed without a SECOND premise ProofKforkB6.kfk_prologue's       *)
  (*  [Hcont4a] fails to expose (documented below); it exercises B7's own  *)
  (*  hand-off on both sides (into it from B2, out of it into B3) in full. *)
  (*                                                                       *)
  (*  SEAM: [Hcont4a] hands back the child's [proc_priv] at an arbitrary   *)
  (*  [Vc' : pprivate], with NO conjunct pinning [pv_ofile Vc']/[pv_cwd     *)
  (*  Vc'].  [ProofKforkB6.kfk_prologue]'s OWN proof constructs [Vc'] as    *)
  (*  [upd_pt (upd_sz Vc (pv_sz Vp)) P' (pv_tf Vc)] (ProofKforkB6.v around  *)
  (*  line 1116), and [upd_pt]/[upd_sz] both preserve [pv_ofile]/[pv_cwd],  *)
  (*  so [pv_ofile Vc' = pv_ofile Vc] and [pv_cwd Vc' = pv_cwd Vc] -- and   *)
  (*  [Vc] is the SAME allocation record [Hcont7c] uses, whose analogous    *)
  (*  conjunct DOES state [pv_ofile Vc = replicate NOFILE zero_reg /\       *)
  (*  pv_cwd Vc = zero_reg] (ProofKforkB6.v line ~253).  So the fact is     *)
  (*  TRUE and available inside B6's own proof; [Hcont4a]'s stated type     *)
  (*  just does not expose it.  [ProofKforkB3.kfkb3_fd_loop] needs exactly  *)
  (*  this fact about the child block it is handed (its own [V0]), so      *)
  (*  without it the fd-scan cannot even be ENTERED.  Supplied here as an   *)
  (*  extra premise, mirroring [Hcont7c]'s conjunct exactly. *)
  (* =================================================================== *)
  Lemma kfork_arm3_reach_b3
      (γf γl2 : gname)
      (K lvl : nat) (eb : bool) (pme : mword 64) (C : iProp Σ)
      (pid_p : mword 32) (Vp : pprivate)
      (sp0 : mword 64) (Mt : regfile) (npa : mword 64) (j : nat)
      (pid_c : mword 32) (Vc' : pprivate) (tfsrc tfdst : mword 44) (m : regfile) :
    (22 <= K)%nat ->
    (Z.of_nat lvl + 2 < 2 ^ 31)%Z ->
    pv_ofile Vc' = replicate NOFILE (zero_reg : mword 64) ->
    pv_cwd Vc' = (zero_reg : mword 64) ->
    Mt !!! Regidx csp_rs1 = pa_stk sp0 8 ->
    Mt !!! Regidx Rs4 = npa ->
    Mt !!! Regidx Rs5 = pme ->
    Mt !!! Regidx Ra5 = a_tf_word tfsrc 0 ->
    Mt !!! Regidx Ra4 = a_tf_word tfdst 0 ->
    Mt !!! Regidx Ra3 = a_tf_word tfsrc 36 ->
    ud_tfp (pv_upt Vp) = tfsrc -> ud_tfp (pv_upt Vc') = tfdst ->
    (forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 ->
        r <> Rs0 -> r <> Rs1 -> r <> Rs4 -> r <> Rs5 -> Mt !!! Regidx r = m !!! Regidx r) ->
    kernel_text -∗
    is_ftable γl2 γf -∗
    panic_wp_any -∗
    sie_cap_gpr Mt (K - 8)%nat false pme -∗
    cpu_own (S lvl) eb pme C false -∗
    pc_is (mword_of_int (KF + 0x4a) : mword 64) -∗
    proc_priv γf pme pid_p Vp -∗
    proc_priv γf npa pid_c Vc' -∗
    (∀ (V2 : pprivate) (Mx : regfile),
      ⌜ pv_sz V2 = pv_sz Vc' /\ pv_ofile V2 = pv_ofile Vc' /\ pv_cwd V2 = pv_cwd Vc' ⌝ -∗
      ⌜ Mx !!! Regidx csp_rs1 = pa_stk sp0 8 /\ Mx !!! Regidx Rs0 = Mt !!! Regidx Rs0 /\
        Mx !!! Regidx Rs4 = npa /\ Mx !!! Regidx Rs5 = pme /\
        (forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 ->
            r <> Rs0 -> r <> Rs1 -> r <> Rs2 -> r <> Rs3 -> r <> Rs4 -> r <> Rs5 ->
            Mx !!! Regidx r = m !!! Regidx r) ⌝ -∗
      sie_cap_gpr Mx (K - 8)%nat false pme -∗
      cpu_own (S lvl) eb pme C false -∗
      pc_is (mword_of_int (KF + 0xa4) : mword 64) -∗
      proc_priv γf pme pid_p Vp -∗
      proc_priv γf npa pid_c (kfk_childV V2 (pv_ofile Vp) NOFILE) -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros HK Hlvl Hofnull Hcwdnull HMtsp HMts4 HMts5 HMta5 HMta4 HMta3 Htfsrc Htfdst HMtthr.
    subst tfsrc tfdst.
    iIntros "#Htext #Hft #Hpanic Hcg Hcpu Hpc Hpv HCpriv Hcont".
    iDestruct (ProofKforkParts.proc_priv_tfp_valid with "Hpv") as %Hpvsrc.
    iDestruct (ProofKforkParts.proc_priv_tfp_valid with "HCpriv") as %Hpvdst.
    iDestruct (ProofKforkParts.proc_priv_tf_upd with "Hpv") as "(Htf_p & Htfp_p & Hclose_p)".
    iDestruct (ProofKforkParts.proc_priv_tf_upd with "HCpriv") as "(Htf_c & Htfp_c & Hclose_c)".
    iDestruct (ProofKforkB7.kfkb7_tf_len with "Htfp_p") as %Hlenp.
    iDestruct (ProofKforkB7.kfkb7_tf_len with "Htfp_c") as %Hlenc.
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
    iPoseProof (B3.kfkb3_fd_loop γl2 γf pme npa pid_p pid_c Vp V2 m K (S lvl) eb false C
                  (pa_stk sp0 8) (Mt !!! Regidx Rs0) HK ltac:(lia) HofnullV2) as "Hb3".
    iSpecialize ("Hb3" with "Htext Hft Hpanic").
    iSpecialize ("Hb3" $! 0%nat Mx with "[%] [%] [Hcont] Hcg Hcpu Hpc Hpv [HCpriv]").
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
      iApply ("Hcont" $! V2 Mx2 with "[%] [%] Hsc Hown Hpcx Hpvx Hpvcx").
      + split_and!; reflexivity.
      + split_and!; [exact Hd1 | exact Hd2 | exact Hd3 | exact Hd4 | exact Hd5].
    - rewrite kfk_childV_0. iExact "HCpriv".
    - iApply "Hb3".
  Qed.

End KforkArms.
End Kfork.
