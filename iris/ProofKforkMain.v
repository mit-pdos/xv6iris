(* ProofKforkMain.v -- the capstone: gluing kfork's six proven blocks
   (ProofKforkB1..B7, ProofKfork's two exits, ProofKforkParts' epilogue)
   into SpecKfork.KFORK's [wp_kfork_sconf].

   STATUS: [kfork_arm1]/[kfork_arm2]/[kfork_arm3] are complete,
   HYPOTHESIS-FREE matches for [Hcont10a]/[Hcont7c]/[Hcont4a]'s own bodies
   (no [admit]/[Admitted]/[Axiom]/[Parameter] anywhere in this file), and
   all four seams the earlier rounds found (missing [cpu_own] on the
   allocproc-not-found arm; [kfk_frame]'s existential swallowing the
   uvmcopy-failure arm's slot-6 value; [Hcont4a]'s missing ofile/cwd
   conjunct on the child block; [Hcont4a]'s [own_ctx] being too weak for
   [SpecForkretPark.forkret_park]) are fixed and used below.

   [wp_kfork_sconf] ITSELF IS BLOCKED ON A FIFTH SEAM, in
   [ProofKforkB6.kfk_prologue]'s statement of [Hcont7c]/[Hcont4a] --
   documented in full where the attempt stops, right after this comment.
   Unlike the first four, this one is NOT worked around here: per the
   brief's rule ("if a goal can't be closed, STOP and report the precise
   goal/lemma/premise"), [wp_kfork_sconf] is left unproved (no attempted
   [Proof]/[Qed] below) rather than admitted, and [Module Kfork ... :
   KFORK] is not written.

   THE GAP.  [Hcont10a] (kfk_prologue's FIRST continuation, at +0x016) is
   stated directly as [wp_next b pme K1] -- the SAME [(b, pme)] pair, and
   hence the SAME implicit [CID0] (kfk_prologue's own Context variable,
   unified with this file's outer [wp_kfork_sconf]'s own entry hart), as
   [wp_kfork_sconf_body]'s own trailing continuation ("Hcont").  So
   [kfork_arm1] discharges "Hcont" trivially: destructure "Hcont10a"'s own
   [∀CID, ⌜cross⌝-*K1 CID] to get a crossing fact [Hcrossx : b=false\/
   pme=zero_reg -> CIDx=CID0] "for free", and use exactly that fact
   (plus [CpuOwn.cpu_own_transport]) to re-anchor "Hcont" at [CIDx].

   [Hcont7c]/[Hcont4a] (at +0x02c) are stated DIFFERENTLY: each is wrapped
   in an EXTRA [∀ CIDh : CpuId], and the [wp_next] INSIDE that binder is
   pinned at the LITERAL [false] (not the caller's symbolic [b]), with
   NO further premise connecting [CIDh] to anything:

     (∀ CIDh : CpuId, wp_next (CID0 := CIDh) false pme (fun CID => ...)) -∗

   Since [false = false] is trivially true, [wp_next (CID0 := CIDh) false
   pme K ⊣⊢ K CIDh] ([WpNext.wp_next_off]) FOR ANY [CIDh] -- so proving
   this antecedent is, after [iIntros (CIDh)], EXACTLY proving [K CIDh]
   for a [CIDh] that is otherwise TOTALLY UNCONSTRAINED (swap the two
   quantifiers: [∀CIDh ∀CID, ⌜CID=CIDh⌝-*K CID] ≡ [∀CID, K CID]).  [K]'s
   own body threads [sie_cap_gpr Mt (K-8) false pme] / [cpu_own (S lvl)
   eb pme C false] -- both canonically hart-indexed AT THAT SAME [CIDh]
   (WpNext.v's own "every resource inside K is about the hart we resume
   on" shadowing discipline: [sie_gname := sie_name cpu_id] with [cpu_id]
   resolved, at STATEMENT-elaboration time, to the innermost [CpuId] in
   scope, which is [CIDh]/[CID], never kfk_prologue's own outer [CID0]).
   To close [K CIDh] one eventually has to re-anchor wp_kfork_sconf's own
   "Hcont" (anchored at [CID0], via [WpNext.wp_next_trans]/
   [CpuOwn.cpu_own_transport]) at [CIDh] -- which needs EXACTLY the
   crossing fact [b = false \/ pme = zero_reg -> (CIDh:CPU) = (CID0:CPU)].
   Nothing in [Hcont7c]/[Hcont4a]'s premise list supplies it: not the pure
   register/[npa]/[γl2] facts, not [ProcGeom.hart_at_any npa]
   ([ProcGeom.v:909]), not [IntrDefs.arm_pay lvl eb pme]
   ([IntrDefs.v:848], itself just another [CIDh]-indexed resource with no
   crossing content) -- and it cannot be recovered from anything still
   held at the top of [wp_kfork_sconf], because "Hcg"/"Hown" (the only
   things that WERE at [CID0]) were already handed to [kfk_prologue] as
   its own precondition.

   THIS FACT DOES EXIST -- but only INSIDE [kfk_prologue]'s own, already
   compiled proof, as an internal, unexposed byproduct of ITS OWN
   [wp_next_chain] bookkeeping through myproc/allocproc/uvmcopy.
   Concretely, at the two call sites (ProofKforkB6.v:890-893 for
   [Hcont7c], and the identical pattern at :1172-1173 for [Hcont4a]):

     iSpecialize ("Hcont7c" $! CID11).
     iSpecialize ("Hcont7c" $! CID20 with "[%]"); [wp_next_chain|].
     assert (Hchain7c : false = false \/ pme = zero_reg -> (CID20:CPU) = (CID11:CPU))
       by wp_next_chain.

   [kfk_prologue] instantiates its own [∀CIDh] at [CID11] -- a SPECIFIC
   hart it already knows (from its own earlier, internal crossing chain,
   never surfaced in [Hcont7c]/[Hcont4a]'s TYPE) relates correctly to its
   own [CID0].  A caller constructing the antecedent, however, must supply
   a proof for [∀CIDh], i.e. for adversarial [CIDh] too -- which is where
   this gets stuck.  [Hcont10a] never has this problem because it carries
   no such extra binder at all.

   THE FIX -- for [ProofKforkB6.kfk_prologue], not this file -- is to add
   exactly the missing crossing premise to [Hcont7c]/[Hcont4a], mirroring
   [CpuOwn.cpu_own_transport]'s own shape:

     (∀ CIDh : CpuId,
        ⌜ b = false \/ pme = zero_reg -> (CIDh : CPU) = (CID0 : CPU) ⌝ -∗
        wp_next (CID0 := CIDh) false pme (fun CID => ...)) -∗

   With that premise in hand, [kfork_arm2]/[kfork_arm3]'s own continuation
   slot becomes constructible from "Hcont" exactly the way [kfork_arm1]
   already does it (destructure the new premise, then
   [WpNext.wp_next_trans]/[CpuOwn.cpu_own_transport] to re-anchor).
   [kfork_arm1], [kfork_arm2] and [kfork_arm3] below are otherwise ready
   to plug in unchanged the moment it lands; only [wp_kfork_sconf]'s own
   proof (INSIDE Section KforkCapstone) needs the three
   [iApply (kfork_armN ...)] bullets re-added. *)
From Stdlib Require Import Eqdep_dec ZArith Lia List.
From stdpp Require Import gmap list list_monad bitvector.definitions bitvector.tactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_var gen_heap invariants.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
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
Require Import ProcGeom.
Require Import UserPtTree.
Require Import FdSlots FileInv.
Require Import WpLock.
Require Import SwtchCtx.
Require Import ProcInv.
Require Import KallocInv.
Require Import KvmSpec.
Require Import SchedCtx.
Require Import IrefSlots.
Require Import DiskPtsto.
Require Import FsBlocks.
Require Import InodeRegion.
Require Import IcacheInv.
Require Import IcacheEscrow.
Require Import WaitInv.
Require Import SpecProcinit.
Require Import PanicStub.
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
Require Import ProcAvail.
Local Open Scope Z_scope.

(* A syscall-altitude goal carries [ProcInv.tf_page]'s 4096-conjunct big-op;
   printing one takes tens of minutes, so a one-line mistake reads as a hang.
   durable-notes.md's rule. *)
Set Printing Depth 40.

Notation KF := KernelSyms.kfork (only parsing).

(* ---- numeric side conditions, by name, over plain nat -- never inline
   [ltac:(lia)] under this file's heavy mword/bitvector import context
   (durable-notes.md: the zify hook answers "Cannot find witness" whenever
   a [bv_unsigned] is merely in the ambient proof context, not just the
   goal). ---- *)
Lemma wpk_K_ge8 (K : nat) : (K_kfork <= K)%nat -> (8 <= K)%nat.
Proof. lia. Qed.
Lemma wpk_K_ge52 (K : nat) : (K_kfork <= K)%nat -> (52 <= K)%nat.
Proof. lia. Qed.
Lemma wpk_K_ge56 (K : nat) : (K_kfork <= K)%nat -> (56 <= K)%nat.
Proof. lia. Qed.

(* Re-anchoring a [wp_next] FORWARD, i.e. handing the caller's exit -- which
   is anchored at the function's entry hart -- to a block that resumed
   somewhere else.  [ProofKwait.kw_next_reanchor] is the same four lines,
   but it is section-local to a file this one must not depend on. *)
Lemma kfk_reanchor `{!riscvGS Σ} `{GEN : GenId} (CIDa CIDb : CpuId)
    (b : bool) (pv : mword 64) (K : forall (CID : CpuId), iProp Σ) :
  (b = false \/ pv = zero_reg -> (CIDb : CPU) = (CIDa : CPU)) ->
  wp_next (CID0 := CIDa) b pv K -∗ wp_next (CID0 := CIDb) b pv K.
Proof.
  intros Hch. iIntros "H" (CID Hs). iApply ("H" $! CID). iPureIntro.
  intro Hb. rewrite (Hs Hb). exact (Hch Hb).
Qed.

Module KforkProof (MP : MYPROC) (AP : ALLOCPROC_GEN) (UC : UVMCOPY)
             (FP : FREEPROC) (RL : RELEASE) (AQ : ACQUIRE)
             (FD : FILEDUP) (ID : IDUP) (SS : SAFESTRCPY)
             (FRP : FORKRET_PARK) : KFORK.

  Module B6 := KforkPrologue MP AP UC.
  Module B1 := KforkB1 FP RL.
  Module B3 := KforkB3 FD.
  Module B4 := KforkB4 ID SS.
  Module B5 := KforkB5 AQ RL FRP.

Section KforkArms.
  Context `{!riscvGS Σ, !lockG Σ, !sieG Σ, !kallocG Σ, !fileG Σ, !fdslotG Σ, !irefslotG Σ, !pavG Σ,
            !diskGhostG Σ, !fsLogG Σ, !iregG Σ}.
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
      (γa γf γl2 : gname) (γs : list gname) (cn : ic_names)
      (m : regfile) (K lvl : nat) (eb b : bool) (pme : mword 64)
      (pid_p : mword 32) (Vp : pprivate)
      (sp0 ra0 s00 s10 s50 : mword 64) (npa : mword 64) (j : nat)
      (pid_c : mword 32) (ch : mword 64) (Vc : pprivate) (Mt : regfile) (lks : gset string) :
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
    (* THE FLOOR OF THIS CONE IS wait_lock (8), which kfork takes AFTER
       releasing np->lock (kernel/proc.c:295) and which ProofKforkB5 states.
       allocproc's "proc" (9) is the call the function is about and the one
       the eye goes to, but it is not the lowest; the fd scan's filedup
       ("ftable", 15) and idup ("itable", 14) sit above [proc] by the leaf
       placement in LockRank.v, and kalloc/uvmcopy's "kmem" above that.  All
       four follow from this one by [locks_below_mono]. *)
    locks_below lks "wait_lock" ->
    procs_inv γs -∗
    (* ENTRY is in-lock (allocproc returned holding np->lock: level
       [S lvl], arm [false]), so the index carries the reserve of the arm
       this block returns at, namely [b].  See ProofKforkB1/B5 -- the
       whole post-allocproc stretch of kfork runs at this index. *)
    sie_cap_gpr Mt (trap_res b + (K - 8))%nat false pme -∗
    cpu_own (S lvl) eb pme false ({["proc"]} ∪ lks) -∗
    arm_pay lvl eb pme -∗
    kernel_text -∗
    pc_is (mword_of_int (KF + 0x7c) : mword 64) -∗
    (∃ w4 w5 : mword 64, ProofKfork.kfk_frame_at sp0 ra0 s00 s10 s50 w4 w5 (m !!! Regidx Rs4)) -∗
    proc_priv γf pme pid_p Vp -∗
    proc_priv_nocwd γf npa pid_c Vc -∗
    SchedCtx.proc_held cpu_id j γl2 USED ch -∗
    ProcGeom.hart_at_any npa -∗
    FdSlots.fd_slots FDSPARE -∗
    IrefSlots.iref_slots (1 + IREFSPARE) -∗
    SwtchCtx.own_ctx (p_context npa) -∗
    kalloc_env γa None -∗
    wp_next b pme (fun (CID : CpuId) =>
      ∀ mr : regfile,
        ⌜ callee_saved m mr ⌝ -∗
        pc_is (ret_pc ra0) -∗
        kfork_post γa γf cn lvl eb pme b pid_p Vp K mr
          (mr !!! Regidx Ra0) lks -∗
        WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros HK Hlvl Hbeq Hmsp Hmra Hms0 Hms1 Hms5 HMtsp HMts4 Hnpa HjN Hgamma
      Hofnull Hcwdnull HMtthr Hbelow.
    subst npa.
    iIntros "#Hprocs Hcg Hcpu Hpay #Htext Hpc Hframe
             Hpv HCpriv Hheld Hhart Hfd Hir Hctx Hkalloc Hcont".
    iDestruct "Hframe" as (w4 w5) "Hframe".
    rewrite /ProofKfork.kfk_frame_at.
    iDestruct "Hframe" as "(Hb1 & Hb2 & Hb3 & Hb4 & Hb5 & Hb6 & Hb7 & Hb8)".
    iAssert (∃ w4', word_pointsto (pa_stk sp0 4) (DfracOwn 1) w4')%I with "[Hb4]" as "Hb4x".
    { iExists w4. iExact "Hb4". }
    iAssert (∃ w5', word_pointsto (pa_stk sp0 5) (DfracOwn 1) w5')%I with "[Hb5]" as "Hb5x".
    { iExists w5. iExact "Hb5". }
    iDestruct (SchedCtx.procs_inv_lookup γs j γl2 Hgamma with "Hprocs") as "#Hislock".
    iDestruct (ProofKforkParts.kfk_of_priv γf (proc_addr j) pid_c Vc Hofnull Hcwdnull
                 with "HCpriv Hfd Hir Hctx") as "(Hfprest & Hfppt & Hfptf)".
    iApply (B1.kfk_exit_uvmcopy γs γa γl2 j ch Vc pid_c (pv_upt Vc) (pv_tf Vc)
              m Mt K sp0 ra0 s00 s10 s50 pme eb b lvl lks
              HK Hlvl Hbeq Hmsp Hmra Hms0 Hms1 Hms5 HMtsp HMts4 HMtthr
              with "Hcg Hcpu Hpay Htext Hpc Hb1 Hb2 Hb3 Hb4x Hb5x Hb6 Hb7 Hb8
                    Hheld Hhart Hislock Hkalloc Hfprest Hfppt Hfptf").
    all: try lkbelow.
    iIntros (CID Hcross mf) "%Hpf Hcg Hpc Hcpu2 Hkalloc2".
    destruct Hpf as [Hcsmf Hmfa0].
    iSpecialize ("Hcont" $! CID with "[%]").
    { rewrite -Hbeq. exact Hcross. }
    iApply ("Hcont" $! mf with "[%] Hpc [Hcg Hcpu2 Hpv Hkalloc2]").
    - exact Hcsmf.
    - rewrite /kfork_post.
      iEval (rewrite Hbeq) in "Hcg". iEval (rewrite Hbeq) in "Hcpu2".
      iSplitL "Hcg"; [iExact "Hcg" |].
      iSplitL "Hcpu2"; [iExact "Hcpu2" |].
      iSplitL "Hpv"; [iExact "Hpv" |].
      (* ONE [-1] arm now: with no page count, "allocproc found no slot" and
         "uvmcopy failed" report exactly the same thing. *)
      iFrame "Hkalloc2". iLeft. iPureIntro. rewrite Hmfa0. reflexivity.
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
      (γa γf : gname) (cn : ic_names)
      (m : regfile) (K lvl : nat) (eb b : bool) (pme : mword 64)
      (pid_p : mword 32) (Vp : pprivate)
      (sp0 ra0 s00 s10 s50 : mword 64) (Mt : regfile) (lks : gset string) :
    (8 <= K)%nat ->
    m !!! Regidx csp_rs1 = sp0 -> m !!! Regidx Rra = ra0 -> m !!! Regidx Rs0 = s00 ->
    m !!! Regidx Rs1 = s10 -> m !!! Regidx Rs5 = s50 ->
    Mt !!! Regidx csp_rs1 = pa_stk sp0 8 ->
    (forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 ->
        r <> Rs0 -> r <> Rs1 -> r <> Rs5 -> Mt !!! Regidx r = m !!! Regidx r) ->
    sie_cap_gpr Mt (K - 8)%nat b pme -∗
    cpu_own lvl eb pme b lks -∗
    kernel_text -∗
    pc_is (mword_of_int (KF + 0x10a) : mword 64) -∗
    kfk_frame sp0 ra0 s00 s10 s50 -∗
    proc_priv γf pme pid_p Vp -∗
    (* at [on = None] allocproc's two not-found disjuncts are the SAME
       resource -- [avail_sub None n] is [None] and [avail_zero None] is
       [True], so its "ran dry after n pages" witness says nothing -- and
       the caller has already collapsed them. *)
    kalloc_env γa None -∗
    wp_next b pme (fun (CID : CpuId) =>
      ∀ mr : regfile,
        ⌜ callee_saved m mr ⌝ -∗
        pc_is (ret_pc ra0) -∗
        kfork_post γa γf cn lvl eb pme b pid_p Vp K mr
          (mr !!! Regidx Ra0) lks -∗
        WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros HK8 Hmsp Hmra Hms0 Hms1 Hms5 HMtsp HMtthr.
    iIntros "Hcg Hcpu #Htext Hpc Hframe Hpv Hkalloc Hcont".
    iApply (ProofKfork.kfk_exit_alloc m Mt K sp0 ra0 s00 s10 s50 pme b
              HK8 Hmsp Hmra Hms0 Hms1 Hms5 HMtsp HMtthr
              with "Hcg Htext Hpc Hframe").
    iIntros (CID Hcross mf) "%Hpf Hcg Hpc".
    destruct Hpf as [Hcsmf Hmfa0].
    iDestruct (cpu_own_transport CID0 CID lvl eb pme b Hcross with "Hcpu") as "Hcpu".
    iSpecialize ("Hcont" $! CID with "[%]"); [exact Hcross |].
    iApply ("Hcont" $! mf with "[%] Hpc [Hcg Hcpu Hpv Hkalloc]").
    - exact Hcsmf.
    - rewrite /kfork_post.
      iSplitL "Hcg"; [iExact "Hcg" |].
      iSplitL "Hcpu"; [iExact "Hcpu" |].
      iSplitL "Hpv"; [iExact "Hpv" |].
      iFrame "Hkalloc". iLeft. iPureIntro. rewrite Hmfa0. reflexivity.
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
      (γa γf γil γic γw γl : gname) (γs : list gname)
      (cn : ic_names) (γfs : fs_names) (cov : gset Z) (logstart : Z) (nib : nat)
      (m : regfile) (K lvl : nat) (eb b : bool) (pme : mword 64)
      (pid_p : mword 32) (Vp : pprivate)
      (sp0 ra0 s00 s10 s50 : mword 64)
      (Mt : regfile) (npa : mword 64) (j : nat) (γl2 : gname)
      (pid_c : mword 32) (ch : mword 64) (Vc' : pprivate) (tfsrc tfdst : mword 44) (lks : gset string) :
    (56 <= K)%nat ->
    (Z.of_nat lvl + 2 < 2 ^ 31)%Z ->
    match lvl with O => eb | S _ => false end = b ->
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
    (* THE FLOOR OF THIS CONE IS wait_lock (8), which kfork takes AFTER
       releasing np->lock (kernel/proc.c:295) and which ProofKforkB5 states.
       allocproc's "proc" (9) is the call the function is about and the one
       the eye goes to, but it is not the lowest; the fd scan's filedup
       ("ftable", 15) and idup ("itable", 14) sit above [proc] by the leaf
       placement in LockRank.v, and kalloc/uvmcopy's "kmem" above that.  All
       four follow from this one by [locks_below_mono]. *)
    locks_below lks "wait_lock" ->
    kernel_text -∗
    panic_wp_any -∗
    procs_inv γs -∗
    (* ENTRY is in-lock (allocproc returned holding np->lock: level
       [S lvl], arm [false]), so the index carries the reserve of the arm
       this block returns at, namely [b].  See ProofKforkB1/B5 -- the
       whole post-allocproc stretch of kfork runs at this index. *)
    sie_cap_gpr Mt (trap_res b + (K - 8))%nat false pme -∗
    cpu_own (S lvl) eb pme false ({["proc"]} ∪ lks) -∗
    pc_is (mword_of_int (KF + 0x4a) : mword 64) -∗
    kfk_frame_at sp0 ra0 s00 s10 s50
      (m !!! Regidx Rs2) (m !!! Regidx Rs3) (m !!! Regidx Rs4) -∗
    proc_priv γf pme pid_p Vp -∗
    proc_priv_nocwd γf npa pid_c Vc' -∗
    (* the slot's ALLOCATION MARKER, minted by allocproc and carried to
       whichever release finally parks the slot ([ProcAvail.v]).
       Persistent. *)
    ProcAvail.pslot_used_at npa -∗
    SchedCtx.proc_held cpu_id j γl2 USED ch -∗
    ProcGeom.hart_at_any npa -∗
    FdSlots.fd_slots FDSPARE -∗
    (∃ (ks : mword 64) (rest : list (mword 64)),
       ⌜length rest = 12%nat⌝ ∗
       ProcDefs.is_kstack npa ks ∗
       SwtchCtx.ctx_cells (p_context npa)
         (SpecAllocproc.forkret_pc :: add_vec ks (mword_of_int 4096) :: rest)) -∗
    IntrDefs.arm_pay lvl eb pme -∗
    kalloc_env γa None -∗
    is_lock γw wait_lock_addr "wait_lock"%string wait_res -∗
    is_ftable γl γf -∗
    is_itable2 γil cn γfs γic cov logstart nib icfg_dev -∗
    itable_inv -∗
    iref_slots (1 + IREFSPARE) -∗
    wp_next b pme (fun (CID : CpuId) =>
      ∀ mr : regfile,
        ⌜ callee_saved m mr ⌝ -∗
        pc_is (ret_pc ra0) -∗
        kfork_post γa γf cn lvl eb pme b pid_p Vp K mr
          (mr !!! Regidx Ra0) lks -∗
        WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros HK Hlvl Hbeq Hmsp Hmra Hms0 Hms1 Hms5 HMtsp HMts4 HMts5
      HMta5 HMta4 HMta3 Htfsrc Htfdst HMtthr Hnpa HjN Hgamma
      Hofnull Hcwdnull Hbelow.
    subst tfsrc tfdst.
    iIntros "#Htext #Hpanic #Hprocs Hcg Hcpu Hpc Hframe Hpv HCpriv #Hmk
             Hheld Hhart Hfd Hctxex Hpay Hkalloc Hwlock Hft
             Hitb Hitinv Hirs Hcont".
    iDestruct "Hctxex" as (ks rest) "(%Hrestlen & Hks & Hkctx)".
    rewrite /kfk_frame_at.
    iDestruct "Hframe" as "(Hb1 & Hb2 & Hb3 & Hb4 & Hb5 & Hb6 & Hb7 & Hb8)".
    iDestruct "Hb8" as (w8) "Hb8".
    iDestruct (ProofKforkParts.proc_priv_tfp_valid with "Hpv") as %Hpvsrc.
    iDestruct (ProofKforkParts.proc_priv_nocwd_tfp_valid with "HCpriv") as %Hpvdst.
    iDestruct (proc_priv_tf_upd with "Hpv") as "(Htf_p & Htfp_p & Hclose_p)".
    iDestruct (ProofKforkParts.proc_priv_nocwd_tf_upd with "HCpriv") as "(Htf_c & Htfp_c & Hclose_c)".
    iDestruct (ProofKforkB7.kfkb7_tf_len with "Htfp_p") as %Hlenp.
    iDestruct (ProofKforkB7.kfkb7_tf_len with "Htfp_c") as %Hlenc.
    (* [a_tf_word]-shaped (this block's own vocabulary) -> [tf_pa]-shaped
       (what the physical-native [kfk_tf_copy_loop] now wants). *)
    rewrite (a_tf_word_eq_tf_pa (ud_tfp (pv_upt Vp)) 0 ltac:(lia)) in HMta5.
    rewrite (a_tf_word_eq_tf_pa (ud_tfp (pv_upt Vc')) 0 ltac:(lia)) in HMta4.
    rewrite (a_tf_word_eq_tf_pa (ud_tfp (pv_upt Vp)) 36 ltac:(lia)) in HMta3.
    (* ---- ProofKforkB2: the trapframe copy loop ---- *)
    iApply (ProofKforkB2.kfk_tf_copy_loop Mt (ud_tfp (pv_upt Vp)) (ud_tfp (pv_upt Vc'))
              (pv_tf Vp) (pv_tf Vc') (trap_res b + (K - 8))%nat pme
              Hpvsrc Hpvdst Hlenp Hlenc HMta5 HMta4 HMta3
              with "Hcg Htext Hpc Htfp_p Htfp_c").
    iApply wp_next_off_intro.
    iIntros (mf) "%Hpf Hcg Hpc Htfp_p Htfp_c".
    destruct Hpf as (Hcsmf & Hmfa5 & Hmfa4).
    iDestruct ("Hclose_p" $! (pv_tf Vp) with "Htf_p Htfp_p") as "Hpv".
    iEval (rewrite upd_tf_id) in "Hpv".
    iDestruct ("Hclose_c" $! (pv_tf Vp) with "Htf_c Htfp_c") as "HCpriv".
    set (V1 := upd_pt Vc' (pv_upt Vc') (pv_tf Vp)).
    change (upd_pt Vc' (pv_upt Vc') (pv_tf Vp)) with V1.
    assert (Hmfs4 : mf !!! Regidx Rs4 = npa)
      by (rewrite (callee_saved_lookup Hcsmf Rs4 ltac:(vm_compute; reflexivity)); exact HMts4).
    assert (Hmfs5 : mf !!! Regidx Rs5 = pme)
      by (rewrite (callee_saved_lookup Hcsmf Rs5 ltac:(vm_compute; reflexivity)); exact HMts5).
    (* ---- ProofKforkB7: MY OWN block ---- *)
    iApply (ProofKforkB7.kfk_b7 γf npa pme pid_c V1 mf (trap_res b + (K - 8))%nat pme Hmfs4 Hmfs5
              with "Hcg Htext Hpc HCpriv").
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
    (* [trap_res b] is the RESERVE the in-lock window is carrying; B3 is
       arm-generic and instantiated at [b := false], so it cannot compute the
       reserve itself -- it takes it as the opaque [rsv] parameter. *)
    iPoseProof (B3.kfkb3_fd_loop γl γf pme npa pid_p pid_c Vp V2 m (trap_res b) K (S lvl) eb false
                  (pa_stk sp0 8) (Mt !!! Regidx Rs0) ({["proc"]} ∪ lks)
                  ltac:(lia) ltac:(lia) HofnullV2 ltac:(lkbelow)) as "Hb3app".
    iSpecialize ("Hb3app" with "Htext Hft Hpanic").
    iSpecialize ("Hb3app" $! 0%nat Mx
      with "[%] [%] [Hb1 Hb2 Hb3 Hb4 Hb5 Hb6 Hb7 Hb8
                     Hheld Hhart Hfd Hpay Hkalloc Hwlock Hitb Hitinv Hirs Hks Hkctx Hcont]
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
      iApply (B4.kfk_b4 γf γil γic cn γfs cov logstart nib pid_p pid_c Vp
                (kfk_childV V2 (pv_ofile Vp) NOFILE) pme npa
                Mx2 (trap_res b) K (S lvl) eb ({["proc"]} ∪ lks)
                ltac:(lia) ltac:(lia) Hd4 Hd3
                with "Hsc Hown Htext Hpcx Hpanic Hitb Hitinv Hirs Hpvx Hpvcx").
      all: try lkbelow.
      iApply wp_next_off_intro.
      iIntros (mf4) "%Hp4 Hsc4 Hown4 Hpc4 Hpvx4 Hpvcx4 Hirsp".
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
      iEval (rewrite Hnpa) in "Hmk".
      (* ---- ProofKforkB5: the two lock crossings, the RUNNABLE park ---- *)
      (* pass B5's exit arm as THIS proof's [b] (with [eq_sym Hbeq] for B5's
         own [b = match lvl ...] premise) rather than as the [match] itself:
         the in-lock index we are handing it is spelled [trap_res b + (K - 8)],
         and B5's entry index has to be syntactically that. *)
      iApply (B5.kfk_b5 γs γf γw γl2 j mf4 K lvl eb b
                pme ks pid_c Vc4 ch rest (sign_extend' 64 pid_c) lks
                ltac:(lia) ltac:(lia) HjN Hgamma Hrestlen (eq_sym Hbeq) Hmf4s4 Hmf4s5 Hpid4
                with "Hsc4 Hown4 Hpay Htext Hpc4 Hpanic Hprocs Hwlock
                      Hheld Hhart Hpvcx4 Hmk Hfd Hirsp Hks Hkctx").
      all: try lkbelow.
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
      (* B5 now exits at THIS proof's [b] (see the call above), so the tail and
         the [cpu_own] transport are instantiated at [b] too -- and none of the
         [Hbeq] re-spellings that used to bridge [b] and [match lvl ...] here
         are needed any more. *)
      iApply (ProofKfork.kfk_tail_succ (CID0 := CID5) m mf5 K sp0 ra0 s00 s10 s50
                (sign_extend' 64 pid_c) w8 pme b
                ltac:(lia) Hmsp Hmra Hms0 Hms1 Hms5 Hmf5sp Hmf5s1 Hmf5thr
                with "Hsc5 Htext Hpc5 Hb1 Hb2 Hb3 Hb4 Hb5 Hb6 Hb7 Hb8").
      iIntros (CID6 Hcross6 mr) "%Hpost Hsc6 Hpc6".
      destruct Hpost as (Hcsm & Hrv).
      iDestruct (cpu_own_transport CID5 CID6 lvl eb pme b Hcross6 with "Hown5") as "Hown5".
      iSpecialize ("Hcont" $! CID6 with "[%]").
      { intros Hdisj. transitivity CID5; [exact (Hcross6 Hdisj) | exact (Hcross5 Hdisj)]. }
      iApply ("Hcont" $! mr with "[%] Hpc6 [Hsc6 Hown5 Hpvx4 Hkalloc]").
      + exact Hcsm.
      + rewrite /kfork_post.
        iSplitL "Hsc6"; [iExact "Hsc6" |].
        iSplitL "Hown5"; [iExact "Hown5" |].
        iSplitL "Hpvx4"; [iExact "Hpvx4" |].
        iFrame "Hkalloc". iRight. iExists pid_c. iPureIntro.
        rewrite Hrv. reflexivity.
    - rewrite kfk_childV_0. iExact "HCpriv".
    - iApply "Hb3app".
  Qed.

End KforkArms.

(* =================================================================== *)
(*  THE CAPSTONE.                                                       *)
(*                                                                      *)
(*  A FRESH SECTION, deliberately: [kfork_arm1/2/3] must be applied with *)
(*  [(CID0 := ...)] overridden per call site, and a still-open section's *)
(*  [Context CID0] is one fixed shared variable, not a per-use argument  *)
(*  -- it rejects the override with "Wrong argument name CID0".          *)
(*                                                                      *)
(*  [B6.kfk_prologue] takes the caller's exit as an abstract [R] and     *)
(*  hands it back to whichever of its three continuations runs, so the   *)
(*  single linear [Hcont] is supplied ONCE here and each closure         *)
(*  RECEIVES it rather than capturing a copy.                            *)
(* =================================================================== *)
Section KforkMain.
  Context `{!riscvGS Σ, !lockG Σ, !sieG Σ, !kallocG Σ, !fileG Σ, !fdslotG Σ, !irefslotG Σ, !pavG Σ,
            !diskGhostG Σ, !fsLogG Σ, !iregG Σ}.
  Context `{GEN : GenId} `{CID0 : CpuId}.

  Notation Rra := (mword_of_int 1 : mword 5).
  Notation Rs0 := (mword_of_int 8 : mword 5).
  Notation Rs1 := (mword_of_int 9 : mword 5).
  Notation Ra0 := (mword_of_int 10 : mword 5).
  Notation Rs5 := (mword_of_int 21 : mword 5).

  Lemma wp_kfork_sconf
      (γa γp γw γl γf γil γic : gname) (γs : list gname)
      (cn : ic_names) (γfs : fs_names) (cov : gset Z) (logstart : Z) (nib : nat)
      (m : regfile) (lvl K : nat) (eb : bool) (pme : mword 64)
      (b : bool) (pid_p : mword 32) (Vp : pprivate) (lks : gset string)
 :
    wp_kfork_sconf_body γa γp γw γl γf γil γic γs cn γfs cov logstart nib
      m lvl K eb pme b pid_p Vp lks.
  Proof.
    cbv beta delta [wp_kfork_sconf_body]. cbn zeta.
    intros HK Hlvl Hbelow.
    iIntros "Hcg Hcpu #Htext Hpc #Hpanic #Hprocs #Hplock #Hwlock #Hftbl
             #Hitbl #Hitinv Henv #Hpav Hpv Hcont".
    (* the SIE index the two lock-holding exits come back at *)
    iDestruct (cpu_own_eb_agree with "Hcg Hcpu") as %Hbeq.
    (* [B6.kfk_prologue] is still generic in the allocator's count; kfork
       pins it at [None] here, which is what collapses its Hcont10a
       disjunction and, with it, two of [kfork_post]'s three arms. *)
    iApply (B6.kfk_prologue γa γp γw γl γf γil γic γs cn γfs cov logstart nib
              m lvl K eb pme None b
              pid_p Vp
              (wp_next b pme (fun (CID : CpuId) =>
                 (∀ mr : regfile,
                    ⌜ callee_saved m mr ⌝ -∗
                    pc_is (ret_pc (m !!! Regidx Rra)) -∗
                    kfork_post γa γf cn lvl eb pme b pid_p Vp
                      K mr (mr !!! Regidx Ra0) lks -∗
                    WP (Loop : expr riscv_lang))%I)) lks
              HK Hlvl
              with "Hcg Hcpu Htext Hpc Hpanic Hprocs Hplock Hwlock Hftbl
                    Hitbl Hitinv Henv Hpav Hpv Hcont [] [] []").
    all: try lkbelow.
    - (* ---- arm 1: allocproc found no free slot, +0x10a ---- *)
      iIntros (CID1 Hx1 Mt) "%HMtsp %HMtthr Hcg Hcpu #Ht Hpc Hframe Hpv Hke HR".
      (* THE COLLAPSE.  allocproc's two not-found disjuncts are the same
         resource at [None]: [avail_sub None n] is [None] and
         [avail_zero None] is [True], so the second arm's "ran dry after n
         pages" witness carries no information.  This is what lets
         [kfork_post] state [kalloc_env] once instead of per-arm. *)
      iAssert (kalloc_env γa None) with "[Hke]" as "Hke".
      { iDestruct "Hke" as "[$ | (% & _ & $)]". }
      iApply (kfork_arm1 (CID0 := CID1) γa γf cn m K lvl eb b pme pid_p Vp
                (m !!! Regidx csp_rs1) (m !!! Regidx Rra)
                (m !!! Regidx Rs0) (m !!! Regidx Rs1) (m !!! Regidx Rs5) Mt lks
                (wpk_K_ge8 K HK) eq_refl eq_refl eq_refl eq_refl eq_refl
                HMtsp HMtthr
                with "Hcg Hcpu Ht Hpc Hframe Hpv Hke [HR]").
      iApply (kfk_reanchor CID0 CID1 b pme _ Hx1 with "HR").
    - (* ---- arm 2: uvmcopy failed, +0x7c ---- *)
      iIntros (CIDh Hxh). iIntros (CID2 Hx2 Mt npa j γl2 pid_c ch Vc).
      iIntros "%HMtsp %HMts4 %HMts5 %HMta0 %HMtthr %Hpures".
      iIntros "Hcg #Ht Hpc Hframe Hpv HCp Hheld Hhart Hfd Hir Hctx Hpay Hcpu Hke HR".
      destruct Hpures as (Hnpa & HjN & Hgamma & Hofn & Hcwdn).
      iApply (kfork_arm2 (CID0 := CID2) γa γf γl2 γs cn m K lvl eb b pme
                pid_p Vp (m !!! Regidx csp_rs1) (m !!! Regidx Rra)
                (m !!! Regidx Rs0) (m !!! Regidx Rs1) (m !!! Regidx Rs5)
                npa j pid_c ch Vc Mt lks
                (wpk_K_ge52 K HK) Hlvl Hbeq
                eq_refl eq_refl eq_refl eq_refl eq_refl
                HMtsp ltac:(rewrite HMts4 Hnpa; reflexivity) Hnpa HjN Hgamma
                Hofn Hcwdn HMtthr ltac:(lkbelow)
                with "Hprocs Hcg Hcpu Hpay Ht Hpc Hframe Hpv HCp Hheld Hhart
                      Hfd Hir Hctx Hke [HR]").
      (* the crossing fact by NAME, never as an inline [ltac:] in argument
         position: the hole's expected type is still an evar there, which is
         durable-notes' diverging-ltac trap. *)
      assert (Hcr2 : b = false \/ pme = zero_reg -> (CID2 : CPU) = (CID0 : CPU)).
      { intro Hd. rewrite (Hx2 (or_introl eq_refl)). exact (Hxh Hd). }
      iApply (kfk_reanchor CID0 CID2 b pme _ Hcr2 with "HR").
    - (* ---- arm 3: uvmcopy succeeded, the copy loop's head at +0x4a ---- *)
      iIntros (CIDh Hxh). iIntros (CID3 Hx3 Mt npa j γl2 pid_c ch Vc' tfsrc tfdst).
      iIntros "%HMtsp %HMts4 %HMts5 %HMta5 %HMta4 %HMta3 %Htfs %HMtthr %Hpures".
      iIntros "Hcg #Ht Hpc Hframe Hpv HCp #Hmk Hheld Hhart Hfd Hirs Hctx Hpay Hcpu
               Hke #Hwl #Hft #Hit #Hiti HR".
      destruct Hpures as (Hnpa & HjN & Hgamma & Hofn & Hcwdn).
      destruct Htfs as (Htfsrc & Htfdst).
      iApply (kfork_arm3 (CID0 := CID3) γa γf γil γic γw γl γs
                cn γfs cov logstart nib m K lvl eb b pme
                pid_p Vp (m !!! Regidx csp_rs1) (m !!! Regidx Rra)
                (m !!! Regidx Rs0) (m !!! Regidx Rs1) (m !!! Regidx Rs5)
                Mt npa j γl2 pid_c ch Vc' tfsrc tfdst lks
                (wpk_K_ge56 K HK) Hlvl Hbeq
                eq_refl eq_refl eq_refl eq_refl eq_refl
                HMtsp HMts4 HMts5 HMta5 HMta4 HMta3 Htfsrc Htfdst HMtthr
                Hnpa HjN Hgamma Hofn Hcwdn ltac:(lkbelow)
                with "Ht Hpanic Hprocs Hcg Hcpu Hpc Hframe Hpv HCp Hmk Hheld Hhart
                      Hfd Hctx Hpay Hke Hwl Hft Hit Hiti Hirs [HR]").
      (* the crossing fact by NAME, never as an inline [ltac:] in argument
         position: the hole's expected type is still an evar there, which is
         durable-notes' diverging-ltac trap. *)
      assert (Hcr3 : b = false \/ pme = zero_reg -> (CID3 : CPU) = (CID0 : CPU)).
      { intro Hd. rewrite (Hx3 (or_introl eq_refl)). exact (Hxh Hd). }
      iApply (kfk_reanchor CID0 CID3 b pme _ Hcr3 with "HR").
  Qed.

End KforkMain.

End KforkProof.
