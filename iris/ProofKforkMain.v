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
Require Import RegFile.
Require Import WpNext.
Require Import WpMmodeLeafBase.
Require Import RiscvExtras.
Require Import StackOwn.
Require Import CalleeSaved.
Require Import InstrBytes.
Require Import KernelText.
Require Import IntrDefs.
Require Import CpuOwn.
Require Import ProcGeom.
Require Import UserPtTree.
Require Import UserPerm.   (* [perm_of] -- the child's permission view, in the run key *)
Require Import FdSlots FileInv.
Require Import WpLock.
Require Import SwtchCtx.
Require Import ProcInv.
Require Import FirstTok.  (* [first_done] / [first_tok_of_done] *)
Require Import KvmSpec.
Require Import SchedCtx.
Require Import IrefSlots.
Require Import Xv6Cameras.
Require Import InodeRegion.
Require Import IcacheInv.
Require Import IcacheEscrow.
Require Import WaitInv.
Require Import SpecProcinit.
Require Import SpecFreeproc.
Require Import PidLock.
Require Import SpecMyproc.
Require Import SpecAllocproc.
Require Import SpecUvmcopy.
Require Import SpecRelease.
Require Import SpecAcquire.
Require Import SpecFiledup.
Require Import SpecIdup.
Require Import SpecSafestrcpy.
Require Import SyscParkEnv ParkCap.
Require Import UexecSlot. (* [uvis] *)
Require Import UexecRet.  (* [uslot] / [urun_eq] -- the child's single slot
                             and its run key, threaded to [B5] beside the
                             WP.  Required DIRECTLY. *)
Require Import SpecKfork.
Require Import ProofKforkParts.
Require Import KforkChild.  (* [kfork_child] / [urun_eq_kfork_child] *)
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
Require Import LogInv.  (* [logG]: [ireg_inv]'s own instance argument *)
Require Import ChildTok.  (* [gen_set] / [gen_split] -- fork's mint *)
Local Open Scope Z_scope.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Require Import FsCfg.   (* [fscfg]: the fs configuration is AMBIENT *)

(* A syscall-altitude goal carries [ProcInv.tf_page]'s 4096-conjunct big-op;
   printing one takes tens of minutes, so a one-line mistake reads as a hang.
   durable-notes.md's rule. *)
Require Import TsoCtx.
Require Import UserFd.   (* [ufdG] -- MUST precede the first `{!ufdG Σ}:
                            an unbound name inside `{ } is auto-generalized
                            into a fresh opaque class instead. *)

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
Lemma kfk_reanchor `{!riscvGS Σ, FSC : fscfg} `{!ufdG Σ} `{GEN : GenId} (CIDa CIDb : CpuId)
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
             : KFORK.

  Module B6 := KforkPrologue MP AP UC.
  Module B1 := KforkB1 FP RL.
  Module B3 := KforkB3 FD.
  Module B4 := KforkB4 ID SS.
  Module B5 := KforkB5 AQ RL.

Section KforkArms.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fileG Σ, !fdslotG Σ, !irefslotG Σ, !pavG Σ, !wchG Σ}.
  Context `{!ufdG Σ}.
  Context `{GEN : GenId} `{CID0 : CpuId} `{XI : CurCtx}.
  (* NO [Context {SG : uexecSG Σ}]: this file sits ABOVE
     [UexecExecInst], so the deposit class it speaks is that file's
     INSTANCE, and so is the one the specs it inhabits were stated at.  A
     section variable here would be a SECOND class of the same type, and the
     two [UexecRet.uslot]s print identically -- the unifier does not stop. *)

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
 (γp γf γl2 : gname) (γs : list gname) 
      (m : regfile) (K lvl : nat) (eb b : bool) (pme : mword 64)
      (pid_p : mword 32) (Up : ustate)
      (sp0 ra0 s00 s10 s50 : mword 64) (npa : mword 64) (j : nat)
      (pid_c : mword 32) (ch : mword 64) (Uc : ustate) (stsP : list fdstate)
      (* the caller's children set: this arm moves nothing into it (no child
         was made), so [kfork_post]'s [-1] arm hands the row back at it *)
      (csP : gset gname)
      (* the payload, threaded to [kfork_post] and read by nothing on this
         arm: fork FAILED here, so no generation was split *)
      (Q : Z -> iProp Σ)
      (Mt : regfile) (lks : gset string) :
    (52 <= K)%nat ->
    (Z.of_nat lvl + 2 < 2 ^ 31)%Z ->
    match lvl with O => eb | S _ => false end = b ->
    m !!! Regidx csp_rs1 = sp0 -> m !!! Regidx Rra = ra0 -> m !!! Regidx Rs0 = s00 ->
    m !!! Regidx Rs1 = s10 -> m !!! Regidx Rs5 = s50 ->
    Mt !!! Regidx csp_rs1 = pa_stk sp0 8 -> Mt !!! Regidx Rs4 = proc_addr j ->
    npa = proc_addr j -> (j < NPROC)%nat -> γs !! j = Some γl2 ->
    pv_ofile (us_V Uc) = replicate NOFILE (zero_reg : mword 64) ->
    pv_cwd (us_V Uc) = (zero_reg : mword 64) ->
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
    is_lock γp alp_pid_lock "nextpid"%string nextpid_res_at -∗
    (* ENTRY is in-lock (allocproc returned holding np->lock: level
       [S lvl], arm [false]), so the index carries the reserve of the arm
       this block returns at, namely [b].  See ProofKforkB1/B5 -- the
       whole post-allocproc stretch of kfork runs at this index. *)
    sie_cap_gpr KT1 Mt (trap_res b + (K - 8))%nat false pme -∗
    cpu_own (S lvl) eb pme false ({["proc"]} ∪ lks) -∗
    arm_pay KT1 lvl eb pme -∗
    kernel_text -∗
    pc_is (mword_of_int (KF + 0x7c) : mword 64) -∗
    (∃ w4 w5 : mword 64, ProofKfork.kfk_frame_at sp0 ra0 s00 s10 s50 w4 w5 (m !!! Regidx Rs4)) -∗
    proc_priv γf pme pid_p Up -∗
    (* ...and its descriptor states, which [kfork_post] hands back verbatim
       beside the block: this arm touches neither. *)
    FdSlots.fd_frags (ProcDefs.pv_fdg (us_V Up)) stsP -∗
    (* ...and the caller's children row, which this arm hands straight back
       ([kfork_post]'s [-1] arm): nothing was forked, so nothing moved. *)
    WaitInv.ch_frag (ProcDefs.pv_chg (us_V Up)) pme csP -∗
    proc_priv_nocwd γf npa pid_c Uc -∗
    (* ...AND THE CHILD'S ROW, which freeproc puts back into the slot's
       UNUSED block ([SpecFreeproc]).  It is at [∅] -- allocproc handed it
       out at [∅] and this arm never reached the fork that would move it. *)
    WaitInv.ch_frag (ProcDefs.pv_chg (us_V Uc)) npa ∅ -∗
    (* ...AND THE CHILD'S TWO EXCLUSIVE GHOSTS, BOTH WHOLE, beside the row:
       this arm frees the slot, and freeproc is what puts the generation
       back into the UNUSED block and deletes the pid's registration
       ([SpecFreeproc]).  Nothing was split off them -- the split is at the
       block assembly, which this arm never reaches. *)
    SlotGen.slot_gen npa (DfracOwn 1) (pv_gen (us_V Uc)) -∗
    SlotGen.pid_reg pid_c (DfracOwn 1) (pv_gen (us_V Uc)) -∗
    (* ...and the child slot's half of [p->xstate], which goes back into the
       UNUSED block with the row ([SpecFreeproc]) *)
    (∃ xsv : mword 32, p_xstate npa ↦₄{DfracOwn (1/2)} xsv) -∗
    SchedCtx.proc_held cpu_id j γl2 USED ch -∗
    ProcGeom.hart_at_any npa -∗
    FdSlots.fd_slots FDSPARE -∗
    IrefSlots.iref_slots (1 + IREFSPARE) -∗
    (* the child's bio allowance, as allocproc handed it out: this arm frees
       the slot, so the three units go back into freeproc's block with the
       stack below ([ProcDefs.proc_dormant] owns three at every state). *)
    bslots 3 -∗
    SwtchCtx.own_ctx (p_context npa) -∗
    (* the child's kernel stack, as allocproc handed it out: this arm frees
       the slot, so it goes straight back into freeproc's block. *)
    ProcDefs.kstack_free npa -∗
    kalloc_env_at fsc_kalloc fsc_kpages None -∗
    wp_next b pme (fun (CID : CpuId) =>
      ∀ mr : regfile,
        ⌜ callee_saved m mr ⌝ -∗
        pc_is (ret_pc ra0) -∗
        kfork_post γf lvl eb pme b pid_p Up stsP csP Q K mr
          (mr !!! Regidx Ra0) lks -∗
        WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros HK Hlvl Hbeq Hmsp Hmra Hms0 Hms1 Hms5 HMtsp HMts4 Hnpa HjN Hgamma
      Hofnull Hcwdnull HMtthr Hbelow.
    subst npa.
    iIntros "#Hprocs #Hplock Hcg Hcpu Hpay #Htext Hpc Hframe
             Hpv Hpfrag Hprow HCpriv Hcrow Hcsg Hcpr Hcxb Hheld Hhart Hfd Hir Hbsl Hctx Hkst Hkalloc Hcont".
    iDestruct "Hframe" as (w4 w5) "Hframe".
    rewrite /ProofKfork.kfk_frame_at.
    iDestruct "Hframe" as "(Hb1 & Hb2 & Hb3 & Hb4 & Hb5 & Hb6 & Hb7 & Hb8)".
    iAssert (∃ w4', ctx_word_pointsto (KTR := KT1) cur_ctx (pa_stk sp0 4) (DfracOwn 1) w4')%I with "[Hb4]" as "Hb4x".
    { iExists w4. iExact "Hb4". }
    iAssert (∃ w5', ctx_word_pointsto (KTR := KT1) cur_ctx (pa_stk sp0 5) (DfracOwn 1) w5')%I with "[Hb5]" as "Hb5x".
    { iExists w5. iExact "Hb5". }
    iDestruct (SchedCtx.procs_inv_lookup γs j γl2 Hgamma with "Hprocs") as "#Hislock".
    iDestruct (ProofKforkParts.kfk_of_priv γf (proc_addr j) pid_c Uc Hofnull Hcwdnull
                 with "HCpriv Hfd Hir Hbsl Hctx Hkst") as "(Hfprest & Hfppt & Hfptf)".
    iApply (B1.kfk_exit_uvmcopy γs fsc_kalloc γp fsc_kpages γl2 j ch (us_V Uc) (pv_gen (us_V Uc)) pid_c (pv_upt (us_V Uc)) (pv_tf (us_V Uc))
              m Mt K sp0 ra0 s00 s10 s50 pme eb b lvl lks
              HK Hlvl HjN Hbeq Hmsp Hmra Hms0 Hms1 Hms5 HMtsp HMts4 HMtthr
              with "Hcg Hcpu Hpay Htext Hpc Hb1 Hb2 Hb3 Hb4x Hb5x Hb6 Hb7 Hb8
                    Hheld Hhart Hislock Hplock Hkalloc Hfprest Hcrow Hcxb Hcsg Hcpr Hfppt Hfptf").
    all: try lkbelow.
    iIntros (CID Hcross mf) "%Hpf Hcg Hpc Hcpu2 Hkalloc2".
    destruct Hpf as [Hcsmf Hmfa0].
    iSpecialize ("Hcont" $! CID with "[%]").
    { rewrite -Hbeq. exact Hcross. }
    iApply ("Hcont" $! mf with "[%] Hpc [Hcg Hcpu2 Hpv Hpfrag Hkalloc2 Hprow]").
    - exact Hcsmf.
    - rewrite /kfork_post.
      iEval (rewrite Hbeq) in "Hcg". iEval (rewrite Hbeq) in "Hcpu2".
      iSplitL "Hcg"; [iExact "Hcg" |].
      iSplitL "Hcpu2"; [iExact "Hcpu2" |].
      iSplitL "Hpv"; [iExact "Hpv" |].
      iSplitL "Hpfrag"; [iExact "Hpfrag" |].
      (* ONE [-1] arm now: with no page count, "allocproc found no slot" and
         "uvmcopy failed" report exactly the same thing. *)
      iFrame "Hkalloc2". iLeft.
      iSplitR; [iPureIntro; rewrite Hmfa0; reflexivity |]. iExact "Hprow".
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
 (γf : gname) 
      (m : regfile) (K lvl : nat) (eb b : bool) (pme : mword 64)
      (pid_p : mword 32) (Up : ustate) (stsP : list fdstate)
      (* the caller's children set -- see [kfork_arm2]: nothing moved *)
      (csP : gset gname)
      (* the payload -- see [kfork_arm2]: nothing on this arm reads it *)
      (Q : Z -> iProp Σ)
      (sp0 ra0 s00 s10 s50 : mword 64) (Mt : regfile) (lks : gset string) :
    (8 <= K)%nat ->
    m !!! Regidx csp_rs1 = sp0 -> m !!! Regidx Rra = ra0 -> m !!! Regidx Rs0 = s00 ->
    m !!! Regidx Rs1 = s10 -> m !!! Regidx Rs5 = s50 ->
    Mt !!! Regidx csp_rs1 = pa_stk sp0 8 ->
    (forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 ->
        r <> Rs0 -> r <> Rs1 -> r <> Rs5 -> Mt !!! Regidx r = m !!! Regidx r) ->
    sie_cap_gpr KT1 Mt (K - 8)%nat b pme -∗
    cpu_own lvl eb pme b lks -∗
    kernel_text -∗
    pc_is (mword_of_int (KF + 0x10a) : mword 64) -∗
    kfk_frame sp0 ra0 s00 s10 s50 -∗
    proc_priv γf pme pid_p Up -∗
    (* ...and its descriptor states, which [kfork_post] hands back verbatim
       beside the block: this arm touches neither. *)
    FdSlots.fd_frags (ProcDefs.pv_fdg (us_V Up)) stsP -∗
    (* ...and the caller's children row, handed straight back
       ([kfork_post]'s [-1] arm): no child was made. *)
    WaitInv.ch_frag (ProcDefs.pv_chg (us_V Up)) pme csP -∗
    (* at [on = None] allocproc's two not-found disjuncts are the SAME
       resource -- [avail_sub None n] is [None] and [avail_zero None] is
       [True], so its "ran dry after n pages" witness says nothing -- and
       the caller has already collapsed them. *)
    kalloc_env_at fsc_kalloc fsc_kpages None -∗
    wp_next b pme (fun (CID : CpuId) =>
      ∀ mr : regfile,
        ⌜ callee_saved m mr ⌝ -∗
        pc_is (ret_pc ra0) -∗
        kfork_post γf lvl eb pme b pid_p Up stsP csP Q K mr
          (mr !!! Regidx Ra0) lks -∗
        WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros HK8 Hmsp Hmra Hms0 Hms1 Hms5 HMtsp HMtthr.
    iIntros "Hcg Hcpu #Htext Hpc Hframe Hpv Hpfrag Hprow Hkalloc Hcont".
    iApply (ProofKfork.kfk_exit_alloc m Mt K sp0 ra0 s00 s10 s50 pme b
              HK8 Hmsp Hmra Hms0 Hms1 Hms5 HMtsp HMtthr
              with "Hcg Htext Hpc Hframe").
    iIntros (CID Hcross mf) "%Hpf Hcg Hpc".
    destruct Hpf as [Hcsmf Hmfa0].
    iDestruct (cpu_own_transport CID0 CID lvl eb pme b Hcross with "Hcpu") as "Hcpu".
    iSpecialize ("Hcont" $! CID with "[%]"); [exact Hcross |].
    iApply ("Hcont" $! mf with "[%] Hpc [Hcg Hcpu Hpv Hpfrag Hkalloc Hprow]").
    - exact Hcsmf.
    - rewrite /kfork_post.
      iSplitL "Hcg"; [iExact "Hcg" |].
      iSplitL "Hcpu"; [iExact "Hcpu" |].
      iSplitL "Hpv"; [iExact "Hpv" |].
      iSplitL "Hpfrag"; [iExact "Hpfrag" |].
      iFrame "Hkalloc". iLeft.
      iSplitR; [iPureIntro; rewrite Hmfa0; reflexivity |]. iExact "Hprow".
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
 (γf γw γl : gname) (γs : list gname)
      (m : regfile) (K lvl : nat) (eb b : bool) (pme : mword 64)
      (pid_p : mword 32) (Up : ustate)
      (sp0 ra0 s00 s10 s50 : mword 64)
      (Mt : regfile) (npa : mword 64) (j : nat) (γl2 : gname)
      (pid_c : mword 32) (ch : mword 64) (Uc' : ustate) (stsP : list fdstate)
      (* THE CALLER'S CHILDREN SET, going in: this arm is where fork MOVES
         it -- the child's generation joins it under <wait_lock>
         ([ProofKforkB5.kfk_b5]) -- and [kfork_post]'s pid arm hands the row
         back at [csP ∪ {[γ]}]. *)
      (csP : gset gname)
      (* THE CHILD'S EXIT PAYLOAD, the depositing process's choice
         ([UexecSG.sfork_pay]): this arm writes it onto the generation
         allocproc minted and splits ([ChildTok.gen_split]). *)
      (Q : Z -> iProp Σ)
      (tfsrc tfdst : mword 44) (lks : gset string) :
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
    ud_tfp (pv_upt (us_V Up)) = tfsrc -> ud_tfp (pv_upt (us_V Uc')) = tfdst ->
    (forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 ->
        r <> Rs0 -> r <> Rs1 -> r <> Rs4 -> r <> Rs5 -> Mt !!! Regidx r = m !!! Regidx r) ->
    npa = proc_addr j -> (j < NPROC)%nat -> γs !! j = Some γl2 ->
    pv_ofile (us_V Uc') = replicate NOFILE (zero_reg : mword 64) ->
    pv_cwd (us_V Uc') = (zero_reg : mword 64) ->
    (* THE CHILD'S PID IS IN [1, PIDMAX] ([SpecAllocproc.allocproc_post],
       relayed by [ProofKforkB6]'s exit clause).  It is what this arm owes
       [SpecKfork.kfork_post]'s pid disjunct, and hence what makes fork's
       return to the PARENT nonzero. *)
    (1 <= bv_unsigned pid_c <= PIDMAX)%Z ->
    (* WHAT THE CHILD ALREADY SHARES WITH THE PARENT ([ProofKforkB6]'s exit
       clause of the same name): the size uvmcopy was run at, the image it
       copied and the permission view it rebuilt.  With the trapframe the
       loop below copies and the cwd inum B4 duplicates, these ARE the
       child's run key, which is what lets the slot premise be a single
       slot ([KforkChild.urun_eq_kfork_child]). *)
    pv_sz (us_V Uc') = pv_sz (us_V Up) ->
    us_M Uc' = us_M Up ->
    perm_of (ud_um (pv_upt (us_V Uc'))) (uint (pv_sz (us_V Up)))
      = perm_of (ud_um (pv_upt (us_V Up))) (uint (pv_sz (us_V Up))) ->
    (* THE FLOOR OF THIS CONE IS wait_lock (8), which kfork takes AFTER
       releasing np->lock (kernel/proc.c:295) and which ProofKforkB5 states.
       allocproc's "proc" (9) is the call the function is about and the one
       the eye goes to, but it is not the lowest; the fd scan's filedup
       ("ftable", 15) and idup ("itable", 14) sit above [proc] by the leaf
       placement in LockRank.v, and kalloc/uvmcopy's "kmem" above that.  All
       four follow from this one by [locks_below_mono]. *)
    locks_below lks "wait_lock" ->
    kernel_text -∗
    procs_inv γs -∗
    (* ENTRY is in-lock (allocproc returned holding np->lock: level
       [S lvl], arm [false]), so the index carries the reserve of the arm
       this block returns at, namely [b].  See ProofKforkB1/B5 -- the
       whole post-allocproc stretch of kfork runs at this index. *)
    sie_cap_gpr KT1 Mt (trap_res b + (K - 8))%nat false pme -∗
    cpu_own (S lvl) eb pme false ({["proc"]} ∪ lks) -∗
    pc_is (mword_of_int (KF + 0x4a) : mword 64) -∗
    kfk_frame_at sp0 ra0 s00 s10 s50
      (m !!! Regidx Rs2) (m !!! Regidx Rs3) (m !!! Regidx Rs4) -∗
    proc_priv γf pme pid_p Up -∗
    (* ...AND ITS DESCRIPTOR STATES, which are what the copy is a copy OF:
       the scan reads this list at every slot it duplicates, changes none of
       it, and hands it back with the block. *)
    FdSlots.fd_frags (ProcDefs.pv_fdg (us_V Up)) stsP -∗
    (* ...AND THE CALLER'S CHILDREN ROW, which this arm MOVES: it rides the
       forking process's residue in, [ProofKforkB5.kfk_b5] adds the child's
       generation to the set under the <wait_lock> it takes to write
       [np->parent], and [kfork_post]'s pid arm hands it back moved. *)
    WaitInv.ch_frag (ProcDefs.pv_chg (us_V Up)) pme csP -∗
    proc_priv_nocwd γf npa pid_c Uc' -∗
    (* THE CHILD'S GENERATION, WHOLE -- allocproc minted it, and this arm
       is where the forking process's choice of payload is written onto it
       and the three pieces cut ([ChildTok.gen_set] / [gen_split]). *)
    ChildTok.gen_own (pv_gen (us_V Uc')) (DfracOwn 1) npa pid_c
      (fun _ => True)%I -∗
    (* ...AND THE CHILD SLOT'S TWO EXCLUSIVE GHOSTS, BOTH WHOLE, cut at the
       same point and 3/4 : 1/4 ([SlotGen.slot_gen_quarters]): the quarters
       close the child's block, the three quarters are the deposit
       [ProofKforkB5.kfk_b5] makes under <wait_lock>. *)
    SlotGen.slot_gen npa (DfracOwn 1) (pv_gen (us_V Uc')) -∗
    SlotGen.pid_reg pid_c (DfracOwn 1) (pv_gen (us_V Uc')) -∗
    (* the child's descriptor-state fragments, minted with its block by
       allocproc AT [fdt0]: the scan retypes them one at a time, at the
       parent's own entries, and the whole table goes into the child's
       residue at the park. *)
    FdSlots.fd_frags (ProcDefs.pv_fdg (us_V Uc')) fdt0 -∗
    (* ...and the child's OWN children row, out of the slot's dormant block
       with them ([SpecAllocproc.allocproc_post]) and parked with the child
       ([ParkCap.park_token_park_steady]).  At [∅]: a fresh child has no
       children of its own. *)
    WaitInv.ch_frag (ProcDefs.pv_chg (us_V Uc')) npa ∅ -∗
    (* ...and the child slot's half of [p->xstate], out of the dormant block
       with the row: the block B4 closes carries it ([ProcInv.proc_priv_core]) *)
    (∃ xsv : mword 32, p_xstate npa ↦₄{DfracOwn (1/2)} xsv) -∗
    (* the slot's ALLOCATION MARKER, minted by allocproc and carried to
       whichever release finally parks the slot ([ProcAvail.v]).
       Persistent. *)
    ProcAvail.pslot_used_at npa -∗
    SchedCtx.proc_held cpu_id j γl2 USED ch -∗
    ProcGeom.hart_at_any npa -∗
    FdSlots.fd_slots FDSPARE -∗
    (* the child's bio units and free kernel stack, for the paid park *)
    bslots 3 -∗
    ProcDefs.kstack_free npa -∗
    (∃ (ks : mword 64) (rest : list (mword 64)),
       ⌜length rest = 12%nat⌝ ∗
       ProcDefs.is_kstack npa ks ∗
       SwtchCtx.ctx_cells (p_context npa)
         (SpecAllocproc.forkret_pc :: add_vec ks (mword_of_int 4096) :: rest)) -∗
    IntrDefs.arm_pay KT1 lvl eb pme -∗
    kalloc_env_at fsc_kalloc fsc_kpages None -∗
    is_lock γw wait_lock_addr "wait_lock"%string (wait_res_at) -∗
    is_ftable γl γf -∗
    is_itable2 fsc_itlock fsc_ic fsc_fs fsc_ireg fsc_cov fsc_logst icfg_nib icfg_dev -∗
    itable_inv -∗
    (* the region handle, straight through to [B4.kfk_b4]'s [idup]
       (iclaim-ledger.md §3.19); persistent, and this arm reads no dinode *)
    ireg_inv fsc_ireg fsc_fs icfg_ist icfg_nib -∗
    iref_slots (1 + IREFSPARE) -∗
    (* the child's token's source, straight through to [B4.kfk_b4] *)
    first_done -∗
    (* ...and the world its park needs, and the park itself, straight
       through to [B5.kfk_b5] *)
    park_world γs -∗
    park_token γs -∗
    (* ...and the child's SLOT, also straight through to [B5.kfk_b5], where
       the park captures it -- at the record kfork STATES from the parent,
       which this proof re-keys onto the record the child is actually parked
       at.  LINEAR, unlike the two rows above it: see [SpecKfork]'s premise
       of the same name. *)
    (∀ (γ : gname) (pidc : mword 32),
       my_pay γ Q -∗ uslot (uvis_of (kfork_child Up) stsP γ ∅ pidc)) -∗
    wp_next b pme (fun (CID : CpuId) =>
      ∀ mr : regfile,
        ⌜ callee_saved m mr ⌝ -∗
        pc_is (ret_pc ra0) -∗
        kfork_post γf lvl eb pme b pid_p Up stsP csP Q K mr
          (mr !!! Regidx Ra0) lks -∗
        WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros HK Hlvl Hbeq Hmsp Hmra Hms0 Hms1 Hms5 HMtsp HMts4 HMts5
      HMta5 HMta4 HMta3 Htfsrc Htfdst HMtthr Hnpa HjN Hgamma
      Hofnull Hcwdnull Hpidc Hshsz Hshimg Hshperm Hbelow.
    subst tfsrc tfdst.
    iIntros "#Htext #Hprocs Hcg Hcpu Hpc Hframe Hpv Hpfrag Hprow HCpriv Hcgen Hcsg Hcpr Hcfrag Hcrow Hcxb #Hmk
             Hheld Hhart Hfd Hbsl Hkst Hctxex Hpay Hkalloc #Hwlock #Hft
             Hitb Hitinv #Hireg Hirs #Hfdone #Hworld #Htoken Hjslot Hcont".
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
    rewrite (a_tf_word_eq_tf_pa (ud_tfp (pv_upt (us_V Up))) 0 ltac:(lia)) in HMta5.
    rewrite (a_tf_word_eq_tf_pa (ud_tfp (pv_upt (us_V Uc'))) 0 ltac:(lia)) in HMta4.
    rewrite (a_tf_word_eq_tf_pa (ud_tfp (pv_upt (us_V Up))) 36 ltac:(lia)) in HMta3.
    (* ---- ProofKforkB2: the trapframe copy loop ---- *)
    iApply (ProofKforkB2.kfk_tf_copy_loop Mt (ud_tfp (pv_upt (us_V Up))) (ud_tfp (pv_upt (us_V Uc')))
              (pv_tf (us_V Up)) (pv_tf (us_V Uc')) (trap_res b + (K - 8))%nat pme
              Hpvsrc Hpvdst Hlenp Hlenc HMta5 HMta4 HMta3
              with "Hcg Htext Hpc Htfp_p Htfp_c").
    iApply wp_next_off_intro.
    iIntros (mf) "%Hpf Hcg Hpc Htfp_p Htfp_c".
    destruct Hpf as (Hcsmf & Hmfa5 & Hmfa4).
    iDestruct ("Hclose_p" $! (pv_tf (us_V Up)) with "Htf_p Htfp_p") as "Hpv".
    iEval (rewrite us_tf_id) in "Hpv".
    iDestruct ("Hclose_c" $! (pv_tf (us_V Up)) with "Htf_c Htfp_c") as "HCpriv".
    set (V1 := upd_pt (us_V Uc') (pv_upt (us_V Uc')) (pv_tf (us_V Up))).
    change (upd_pt (us_V Uc') (pv_upt (us_V Uc')) (pv_tf (us_V Up))) with V1.
    assert (Hmfs4 : mf !!! Regidx Rs4 = npa)
      by (rewrite (callee_saved_lookup Hcsmf Rs4 ltac:(vm_compute; reflexivity)); exact HMts4).
    assert (Hmfs5 : mf !!! Regidx Rs5 = pme)
      by (rewrite (callee_saved_lookup Hcsmf Rs5 ltac:(vm_compute; reflexivity)); exact HMts5).
    (* ---- ProofKforkB7: MY OWN block ---- *)
    iApply (ProofKforkB7.kfk_b7 γf npa pme pid_c (MkUstate V1 ((us_M Uc'))) mf (trap_res b + (K - 8))%nat pme Hmfs4 Hmfs5
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
    { rewrite /V2 /V1. cbn [pv_ofile upd_pt pv_fdg]. exact Hofnull. }
    (* ---- ProofKforkB3: the fd scan, ALL 16 iterations in one shot ---- *)
    (* [trap_res b] is the RESERVE the in-lock window is carrying; B3 is
       arm-generic and instantiated at [b := false], so it cannot compute the
       reserve itself -- it takes it as the opaque [rsv] parameter. *)
    iPoseProof (B3.kfkb3_fd_loop γl γf pme npa pid_p pid_c Up (MkUstate V2 (us_M Uc')) stsP m (trap_res b) K (S lvl) eb false
                  (pa_stk sp0 8) (Mt !!! Regidx Rs0) ({["proc"]} ∪ lks)
                  ltac:(lia) ltac:(lia) HofnullV2 ltac:(lkbelow)) as "Hb3app".
    iSpecialize ("Hb3app" with "Htext Hft").
    iSpecialize ("Hb3app" $! 0%nat Mx
      with "[%] [%] [Hb1 Hb2 Hb3 Hb4 Hb5 Hb6 Hb7 Hb8
                     Hheld Hhart Hfd Hbsl Hkst Hpay Hkalloc Hwlock Hitb Hitinv Hirs Hks Hkctx Hjslot Hcgen Hcont
                     Hprow Hcrow Hcxb Hcsg Hcpr]
            Hcg Hcpu Hpc Hpv [HCpriv] Hpfrag Hcfrag").
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
    - iApply wp_next_off_intro.
      iIntros (Mx2) "%Hregs2 Hsc Hown Hpcx Hpvx Hpvcx Hpfrag Hcfrag".
      destruct Hregs2 as (Hd1 & Hd2 & Hd3 & Hd4 & Hd5).
      (* FORK'S CHOICE, AND THE SPLIT, BEFORE THE CHILD'S BLOCK IS CLOSED.
         The payload is the depositing process's ([UexecSG.sfork_pay],
         relayed here as [Q]); the generation allocproc minted is set to it
         and cut in three -- the PARENT's quarter goes back in
         [kfork_post]'s pid arm, the CHILD's persistent [ChildTok.my_pay]
         pays the slot premise, and the KERNEL's quarter goes INTO THE
         CHILD'S BLOCK, which is where kexit finds it when the child
         eventually exits ([ProcInv.proc_priv_core]).  It has to happen
         here, before [B4]'s [sd a0,336(s4)]: that store is what closes the
         block, and a block cannot be closed without the pair. *)
      iApply fupd_wp.
      iMod (gen_set (pv_gen (us_V Uc')) npa pid_c (fun _ => True)%I Q
              with "Hcgen") as "Hcgen".
      iMod (gen_split with "Hcgen") as "(Htok & Hkq & #Hmp)".
      iModIntro.
      (* ...AND THE TWO EXCLUSIVE GHOSTS, CUT THE SAME WAY AND AT THE SAME
         POINT, 3/4 : 1/4 ([SlotGen.slot_gen_quarters]).  The QUARTERS go
         into the child's block with the kernel's quarter of the generation
         (B4's store closes it); the THREE QUARTERS are the deposit B5 makes
         under <wait_lock> at the store that fills the child's parent cell
         ([WaitInv.gen_halves]).  The split is uneven so that B5 can REFUTE
         a pre-existing entry for the slot ([gen_halves_no_entry]) -- by
         then the child's block is closed and kfork no longer holds the
         whole. *)
      iEval (rewrite slot_gen_quarters) in "Hcsg".
      iDestruct "Hcsg" as "[Hsg34 Hsg14]".
      iEval (rewrite pid_reg_quarters) in "Hcpr".
      iDestruct "Hcpr" as "[Hpr34 Hpr14]".
      (* the generation's two persistent readings, off the discarded half
         and the kernel quarter: the deposit carries them so that a reaper
         can read an entry as -- this slot, this pid. *)
      iAssert (ChildTok.gen_slot (pv_gen (us_V Uc')) npa ∗
               ChildTok.gen_pid (pv_gen (us_V Uc')) pid_c)%I as "#Hgsp".
      { iDestruct "Hmp" as (pa0 pid0) "#Hmo".
        iDestruct (gen_agree_pure with "Hmo Hkq") as %[-> ->].
        iSplit; [iExists pid_c, Q; iExact "Hmo" | iExists npa, Q; iExact "Hmo"]. }
      iDestruct "Hgsp" as "[#Hgslot #Hgpid]".
      (* ---- ProofKforkB4: idup / safestrcpy / pid read ---- *)
      iApply (B4.kfk_b4 γf
                pid_p pid_c Up
                (MkUstate (kfk_childV V2 (pv_ofile (us_V Up)) NOFILE) (us_M Uc')) pme npa
                Mx2 (trap_res b) K (S lvl) eb ({["proc"]} ∪ lks)
                ltac:(lia) ltac:(lia) Hd4 Hd3
                with "Hsc Hown Htext Hpcx Hitb Hitinv Hireg Hirs Hpvx Hfdone
                      Hpvcx [Hkq] Hcxb [Hsg14 Hpr14]").
      all: try lkbelow.
      { (* the pair, at the child block's own generation: [kfk_childV] is an
           [upd_*] chain that preserves [pv_gen] *)
        iExists Q. cbn [us_V]. rewrite /kfk_childV /V2 /V1. iFrame "Hkq Hmp". }
      { (* ...and the two quarters, at that same field *)
        rewrite /SlotGen.gen_halves_priv. cbn [us_V].
        rewrite /kfk_childV /V2 /V1. iFrame "Hsg14 Hpr14". }
      iApply wp_next_off_intro.
      iIntros (mf4) "%Hp4 Hsc4 Hown4 Hpc4 Hpvx4 Hpvcx4 Hirsp".
      destruct Hp4 as (Hthr4 & Hpid4).
      iDestruct "Hpvcx4" as (Vc4) "(%HVc4 & Hpvcx4)".
      (* B4 moved only [cwd] and [name]; the child's fd-state ghost name is
         the one allocproc chose, which is what the park is keyed on. *)
      assert (Hcfg4 : pv_fdg Vc4 = pv_fdg (kfk_childV V2 (pv_ofile (us_V Up)) NOFILE))
        by (destruct HVc4 as (_ & _ & _ & _ & _ & Hg & _); exact Hg).
      iEval (rewrite -Hcfg4) in "Hcfrag".
      (* ...and the child's children row travels the same way: B4 moves the
         cwd and the name and nothing else, so the row allocproc handed out
         is a row of THIS block. *)
      assert (Hcchg4 : pv_chg Vc4 = pv_chg (us_V Uc')).
      { destruct HVc4 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hg).
        rewrite Hg. rewrite /kfk_childV /V2 /V1. reflexivity. }
      iEval (rewrite -Hcchg4) in "Hcrow".
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
      iEval (rewrite Hnpa) in "Hcrow".
      iEval (rewrite Hnpa) in "Hmk".
      iEval (rewrite Hnpa) in "Hkst".
      (* the deposit B5 makes is keyed at the slot's address and at the
         block's own generation, so both spellings are converted here with
         the rest *)
      iEval (rewrite Hnpa) in "Hsg34".
      iEval (rewrite Hnpa) in "Hgslot".
      (* THE RUN KEY.  The slot arrived at [uvis_of (kfork_child Up) stsP],
         the record [SpecKfork] states from the parent; the child is parked
         at [MkUstate Vc4 (us_M Uc')].  The two agree on every projection a
         slot reads: the trapframe is the parent's with a0 := 0 (B2's copy
         loop through [V1], B7's store through [V2], both preserved by the
         fd scan and by B4), the image, the size and the permission view are
         B6's exit clause, and the cwd inum is B4's post.  So the park may
         take the ONE slot ([ParkCap.park_token_park_steady], via
         [UexecRet.uslot_of_urun_eq] inside [B5.kfk_b5]). *)
      assert (Hshperm' : perm_of (ud_um (pv_upt (us_V Uc'))) (uint (pv_sz (us_V Uc')))
                         = perm_of (ud_um (pv_upt (us_V Up))) (uint (pv_sz (us_V Up))))
        by (rewrite Hshsz; exact Hshperm).
      (* THE CHILD'S GENERATION IS THE ONE ALLOCPROC MINTED, and the key is
         built at the BLOCK's field: every step between allocproc and here
         is an [upd_*] that preserves it, so the park -- which keys the
         child's slot at [ProcDefs.pv_gen] ([ParkCap.park_cap]) -- and the
         caller's deposit meet at this one name. *)
      assert (Hcgn4 : pv_gen Vc4 = pv_gen (us_V Uc')).
      { destruct HVc4 as (_ & _ & _ & _ & _ & _ & _ & _ & Hg & _).
        rewrite Hg. rewrite /kfk_childV /V2 /V1. reflexivity. }
      assert (Hurun : urun_eq
                        (uvis_of (kfork_child Up) stsP (pv_gen Vc4) ∅ pid_c)
                        (MkUstate Vc4 ((us_M Uc')))).
      { destruct HVc4 as (Hs & Hu & Ht & _ & _ & _ & _ & Hc & _ & _).
        apply urun_eq_kfork_child.
        - exact Ht.
        - exact Hshimg.
        - cbn [us_V]. rewrite Hu Hs. exact Hshperm'.
        - cbn [us_V]. rewrite Hs. exact Hshsz.
        - cbn [us_V]. exact Hc. }
      (* ---- ProofKforkB5: the two lock crossings, the RUNNABLE park ---- *)
      (* pass B5's exit arm as THIS proof's [b] (with [eq_sym Hbeq] for B5's
         own [b = match lvl ...] premise) rather than as the [match] itself:
         the in-lock index we are handing it is spelled [trap_res b + (K - 8)],
         and B5's entry index has to be syntactically that. *)
      iEval (rewrite -Hcgn4) in "Hmp".
      iEval (rewrite -Hcgn4) in "Hsg34".
      iEval (rewrite -Hcgn4) in "Hpr34".
      iEval (rewrite -Hcgn4) in "Hgslot".
      iEval (rewrite -Hcgn4) in "Hgpid".
      (* THE CHILD'S PID IS ALLOCPROC'S, and this is where fork's ∀-bound
         one is instantiated: [pid_c] is the number <allocpid> chose, the
         one [kfork_post]'s success arm returns and the one the park keys
         the child's slot at ([ParkCap.park_cap] passes [un_pid N]). *)
      iSpecialize ("Hjslot" $! (pv_gen Vc4) pid_c with "Hmp").
      iApply (B5.kfk_b5 γs γf γw γl γl2 j mf4 K lvl eb b
                pme ks pid_c (MkUstate Vc4 ((us_M Uc'))) stsP
                ∅
                (uvis_of (kfork_child Up) stsP (pv_gen Vc4) ∅ pid_c)
                (pv_chg (us_V Up)) csP ch rest
                (sign_extend' 64 pid_c) lks
                ltac:(lia) ltac:(lia) HjN Hgamma Hrestlen (eq_sym Hbeq) Hmf4s4 Hmf4s5 Hpid4
                Hurun eq_refl eq_refl eq_refl eq_refl
                with "Hsc4 Hown4 Hpay Htext Hpc4 Hprocs Hwlock Hft Hworld Htoken Hfdone
                      Hheld Hhart Hpvcx4 Hcfrag Hcrow Hprow Hsg34 Hpr34 Hgslot Hgpid Hjslot Hmk Hfd Hirsp Hbsl Hkst Hks Hkctx").
      all: try lkbelow.
      (* [b] is symbolic here (B5's own exit index): an ordinary crossing,
         not [wp_next_off_intro] -- the brief's correction (a). *)
      iIntros (CID5 Hcross5 mf5) "%Hcs5 Hsc5 Hown5 Hpc5 Hprow".
      (* the row comes back MOVED, at the generation the block records;
         [kfork_post]'s pid arm names it at [Uc']'s field.  The equation is
         restated at the literal spelling the row carries, so the rewrite
         has something to match. *)
      assert (Hgeq4 : pv_gen (us_V (MkUstate Vc4 (us_M Uc'))) = pv_gen (us_V Uc'))
        by exact Hcgn4.
      iEval (rewrite Hgeq4) in "Hprow".
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
      iApply ("Hcont" $! mr with "[%] Hpc6 [Hsc6 Hown5 Hpvx4 Hpfrag Hkalloc Htok Hprow]").
      + exact Hcsm.
      + rewrite /kfork_post.
        iSplitL "Hsc6"; [iExact "Hsc6" |].
        iSplitL "Hown5"; [iExact "Hown5" |].
        iSplitL "Hpvx4"; [iExact "Hpvx4" |].
        iSplitL "Hpfrag"; [iExact "Hpfrag" |].
        iFrame "Hkalloc". iRight. iExists pid_c, (pv_gen (us_V Uc')).
        iSplitR; [iPureIntro; rewrite Hrv; reflexivity |].
        iSplitR; [iPureIntro; exact Hpidc |].
        iSplitL "Htok"; [iExact "Htok" |]. iExact "Hprow".
    - rewrite kfk_childU_0. iExact "HCpriv".
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
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fileG Σ, !fdslotG Σ, !irefslotG Σ, !pavG Σ, !wchG Σ}.
  Context `{!ufdG Σ}.
  Context `{GEN : GenId} `{CID0 : CpuId} `{XI : CurCtx}.

  Notation Rra := (mword_of_int 1 : mword 5).
  Notation Rs0 := (mword_of_int 8 : mword 5).
  Notation Rs1 := (mword_of_int 9 : mword 5).
  Notation Ra0 := (mword_of_int 10 : mword 5).
  Notation Rs5 := (mword_of_int 21 : mword 5).

  (* [γk], the allocator's count/seal pair, is threaded universally: kfork
     runs UNCOUNTED and its only caller ([sys_fork]) holds a generic
     allocator gname, so nothing here may pin the pair at [fsc_kpages]. *)
  Lemma wp_kfork_sconf
 (γp γw γl γf : gname) (γs : list gname)
      (m : regfile) (lvl K : nat) (eb : bool) (pme : mword 64)
      (b : bool) (pid_p : mword 32) (Up : ustate) (stsP : list fdstate)
      (csP : gset gname)
      (Q : Z -> iProp Σ)
      (lks : gset string)
 :
    wp_kfork_sconf_body γp γw γl γf γs
 m lvl K eb pme b pid_p Up stsP csP Q lks.
  Proof.
    cbv beta delta [wp_kfork_sconf_body]. cbn zeta.
    intros HK Hlvl Hbelow.
    iIntros "Hcg Hcpu #Htext Hpc #Hprocs #Hplock #Hwlock #Hftbl
             #Hitbl #Hitinv #Hireg Henv #Hpav #Hworld #Htoken Hjslot #Hfdone Hpv Hpfrag Hrow Hcont".
    (* the SIE index the two lock-holding exits come back at *)
    iDestruct (cpu_own_eb_agree with "Hcg Hcpu") as %Hbeq.
    (* [B6.kfk_prologue] is still generic in the allocator's count; kfork
       pins it at [None] here, which is what collapses its Hcont10a
       disjunction and, with it, two of [kfork_post]'s three arms. *)
    (* the pair the three exits share, built ONCE -- see the [R] below *)
    iCombine "Hrow Hcont" as "HR0".
    iApply (B6.kfk_prologue γp γw γl γf γs
              m lvl K eb pme None b
              pid_p Up stsP
              (* THE CALLER'S EXIT AND ITS CHILDREN ROW TRAVEL AS ONE
                 ABSTRACT [R].  The prologue's three continuations are three
                 closures of which exactly one runs, and both of these are
                 LINEAR, so neither can be captured per closure -- the
                 prologue's own note says why.  Every arm splits the pair
                 back apart. *)
              (WaitInv.ch_frag (ProcDefs.pv_chg (us_V Up)) pme csP ∗
               wp_next b pme (fun (CID : CpuId) =>
                 (∀ mr : regfile,
                    ⌜ callee_saved m mr ⌝ -∗
                    pc_is (ret_pc (m !!! Regidx Rra)) -∗
                    kfork_post γf lvl eb pme b pid_p Up stsP csP Q
                      K mr (mr !!! Regidx Ra0) lks -∗
                    WP (Loop : expr riscv_lang))%I))%I lks
              HK Hlvl
              with "Hcg Hcpu Htext Hpc Hprocs Hplock Hwlock Hftbl
                    Hitbl Hitinv Henv Hpav Hpv Hpfrag HR0 [] [] [Hjslot]").
    all: try lkbelow.
    - (* ---- arm 1: allocproc found no free slot, +0x10a ---- *)
      iIntros (CID1 Hx1 Mt) "%HMtsp %HMtthr Hcg Hcpu #Ht Hpc Hframe Hpv Hpfrag Hke HR".
      iDestruct "HR" as "[Hrow HR]".
      (* THE COLLAPSE.  allocproc's two not-found disjuncts are the same
         resource at [None]: [avail_sub None n] is [None] and
         [avail_zero None] is [True], so the second arm's "ran dry after n
         pages" witness carries no information.  This is what lets
         [kfork_post] state [kalloc_env_at] once instead of per-arm. *)
      iAssert (kalloc_env_at fsc_kalloc fsc_kpages None) with "[Hke]" as "Hke".
      { iDestruct "Hke" as "[$ | (% & _ & $)]". }
      iApply (kfork_arm1 (CID0 := CID1) γf m K lvl eb b pme pid_p Up stsP csP Q
                (m !!! Regidx csp_rs1) (m !!! Regidx Rra)
                (m !!! Regidx Rs0) (m !!! Regidx Rs1) (m !!! Regidx Rs5) Mt lks
                (wpk_K_ge8 K HK) eq_refl eq_refl eq_refl eq_refl eq_refl
                HMtsp HMtthr
                with "Hcg Hcpu Ht Hpc Hframe Hpv Hpfrag Hrow Hke [HR]").
      iApply (kfk_reanchor CID0 CID1 b pme _ Hx1 with "HR").
    - (* ---- arm 2: uvmcopy failed, +0x7c ---- *)
      (* the child's image, as uvmcopy left it -- [kfk_pro_exit2]'s own ∀ *)
      iIntros (CIDh Hxh). iIntros (CID2 Hx2 Mt npa j γl2 pid_c ch Uc).
      destruct Uc as [Vc Mc].
      iIntros "%HMtsp %HMts4 %HMts5 %HMta0 %HMtthr %Hpures".
      iIntros "Hcg #Ht Hpc Hframe Hpv Hpfrag HCp Hcrow Hcsg Hcpr Hcxb Hheld Hhart Hfd Hir Hbslp Hctx Hkstk Hpay Hcpu Hke HR".
      iDestruct "HR" as "[Hrow HR]".
      destruct Hpures as (Hnpa & HjN & Hgamma & Hofn & Hcwdn).
      iApply (kfork_arm2 (CID0 := CID2) γp γf γl2 γs m K lvl eb b pme
                pid_p Up (m !!! Regidx csp_rs1) (m !!! Regidx Rra)
                (m !!! Regidx Rs0) (m !!! Regidx Rs1) (m !!! Regidx Rs5)
                npa j pid_c ch (MkUstate Vc Mc) stsP csP Q Mt lks
                (wpk_K_ge52 K HK) Hlvl Hbeq
                eq_refl eq_refl eq_refl eq_refl eq_refl
                HMtsp ltac:(rewrite HMts4 Hnpa; reflexivity) Hnpa HjN Hgamma
                Hofn Hcwdn HMtthr ltac:(lkbelow)
                with "Hprocs Hplock Hcg Hcpu Hpay Ht Hpc Hframe Hpv Hpfrag Hrow HCp Hcrow Hcsg Hcpr Hcxb Hheld Hhart
                      Hfd Hir Hbslp Hctx Hkstk Hke [HR]").
      (* the crossing fact by NAME, never as an inline [ltac:] in argument
         position: the hole's expected type is still an evar there, which is
         durable-notes' diverging-ltac trap. *)
      assert (Hcr2 : b = false \/ pme = zero_reg -> (CID2 : CPU) = (CID0 : CPU)).
      { intro Hd. rewrite (Hx2 (or_introl eq_refl)). exact (Hxh Hd). }
      iApply (kfk_reanchor CID0 CID2 b pme _ Hcr2 with "HR").
    - (* ---- arm 3: uvmcopy succeeded, the copy loop's head at +0x4a ---- *)
      iIntros (CIDh Hxh). iIntros (CID3 Hx3 Mt npa j γl2 pid_c ch Uc' tfsrc tfdst).
      destruct Uc' as [Vc' Mc].
      iIntros "%HMtsp %HMts4 %HMts5 %HMta5 %HMta4 %HMta3 %Htfs %HMtthr %Hpures %Hshare".
      iIntros "Hcg #Ht Hpc Hframe Hpv Hpfrag HCp Hcgen Hcsg Hcpr Hcfrag Hcrow Hcxb #Hmk Hheld Hhart Hfd Hirs Hbsl Hkst Hctx Hpay Hcpu
               Hke #Hwl #Hft #Hit #Hiti HR".
      iDestruct "HR" as "[Hrow HR]".
      destruct Hpures as (Hnpa & HjN & Hgamma & Hofn & Hcwdn & Hpidc).
      destruct Hshare as (Hshsz & Hshimg & Hshperm).
      destruct Htfs as (Htfsrc & Htfdst).
      iApply (kfork_arm3 (CID0 := CID3) γf γw γl γs
 m K lvl eb b pme
                pid_p Up (m !!! Regidx csp_rs1) (m !!! Regidx Rra)
                (m !!! Regidx Rs0) (m !!! Regidx Rs1) (m !!! Regidx Rs5)
                Mt npa j γl2 pid_c ch (MkUstate Vc' Mc) stsP csP Q tfsrc tfdst lks
                (wpk_K_ge56 K HK) Hlvl Hbeq
                eq_refl eq_refl eq_refl eq_refl eq_refl
                HMtsp HMts4 HMts5 HMta5 HMta4 HMta3 Htfsrc Htfdst HMtthr
                Hnpa HjN Hgamma Hofn Hcwdn Hpidc Hshsz Hshimg Hshperm ltac:(lkbelow)
                with "Ht Hprocs Hcg Hcpu Hpc Hframe Hpv Hpfrag Hrow HCp Hcgen Hcsg Hcpr Hcfrag Hcrow Hcxb Hmk Hheld Hhart
                      Hfd Hbsl Hkst Hctx Hpay Hke Hwl Hft Hit Hiti Hireg Hirs Hfdone Hworld Htoken Hjslot
                      [HR]").
      (* the crossing fact by NAME, never as an inline [ltac:] in argument
         position: the hole's expected type is still an evar there, which is
         durable-notes' diverging-ltac trap. *)
      assert (Hcr3 : b = false \/ pme = zero_reg -> (CID3 : CPU) = (CID0 : CPU)).
      { intro Hd. rewrite (Hx3 (or_introl eq_refl)). exact (Hxh Hd). }
      iApply (kfk_reanchor CID0 CID3 b pme _ Hcr3 with "HR").
  Qed.

End KforkMain.

End KforkProof.
