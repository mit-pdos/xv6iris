(* ProofKforkB6.v -- kfork's PROLOGUE: myproc, allocproc, the three-way
   dispatch (allocproc found no slot / uvmcopy failed / uvmcopy succeeded),
   and the uvmcopy call itself, +0x000 .. +0x046.

   This is the TOP of kfork (kernel/proc.c), so this block's statement IS
   kfork's own precondition (SpecKfork.v's [wp_kfork_sconf_body]).  It hands
   off to THREE further blocks, each proved elsewhere, taken here as
   abstract continuations:

     - [Hcont10a] -- allocproc found no free slot (+0x016 taken).  Reaches
       exactly [ProofKfork.kfk_exit_alloc]'s precondition, plus the ghost
       resources (the parent's [proc_priv], the cwd [inode_ref], and
       allocproc's own "no slot" disjunction on [kalloc_env]) that
       [kfork_post]'s first disjunct needs.

     - [Hcont7c] -- uvmcopy failed (+0x02c taken).  Reaches the
       uvmcopy-failure tail's precondition: both proc_privs closed back up
       UNCHANGED (uvmcopy's failure arm restores [proc_pt Pnew] to exactly
       what it was given), plus everything [ProofKforkParts.kfk_of_priv]
       needs to hand freeproc its three pieces.

     - [Hcont4a] -- uvmcopy succeeded (+0x02c fall-through, through the
       [np->sz := p->sz] store and the trapframe-copy loop's setup).
       Reaches the copy loop's precondition at pc = +0x04a: the child's
       [proc_priv] with its size/table already advanced to uvmcopy's
       result, the parent's [proc_priv] untouched, and the four copy-loop
       registers (a3/a4/a5, plus s4/s5) at their [a_tf_word] addresses.

   Functorized over [MYPROC], [ALLOCPROC_GEN] and [UVMCOPY] -- the three
   callees this block makes, each taken as an abstract module so this file
   never depends on their own whole-function proofs. *)
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
Require Import HartTp.
Require Import IntrDefs.
Require Import ProcGeom.
Require Import PageGeom.
Require Import PtBuild.
Require Import UserPtTree.
Require Import ProcPtOwn.
Require Import FdSlots FileInv.
Require Import WpLock.
Require Import SwtchCtx.
Require Import ProcInv.
Require Import KallocInv.
Require Import SchedCtx.
Require Import KvmSpec.
Require Import DiskPtsto.
Require Import FsBlocks.
Require Import InodeRegion.
Require Import IrefSlots.
Require Import IcacheInv.
Require Import IcacheEscrow.
Require Import SpecAllocpid.
Require Import WaitInv.
Require Import SpecProcinit.
Require Import PanicStub.
Require Import SpecMyproc.
Require Import SpecAllocproc.
Require Import SpecUvmcopy.
Require Import SpecKfork.
Require Import CpuOwn.
Require Import CodeKfork.
Require Import ProofKforkParts.
Require Import ProofKfork.
From Kernel Require KernelSyms.
Local Open Scope Z_scope.

(* A syscall-altitude goal carries [ProcInv.tf_page]'s 4096-conjunct big-op;
   printing one takes tens of minutes, so a one-line mistake reads as a hang. *)
Set Printing Depth 40.

Notation KF := KernelSyms.kfork (only parsing).

Module KforkPrologue (Myproc : MYPROC) (Allocproc : ALLOCPROC_GEN) (Uvmcopy : UVMCOPY).

Section KforkPrologue.
  Context `{!riscvGS Σ, !lockG Σ, !sieG Σ, !kallocG Σ, !fileG Σ, !fdslotG Σ, !irefslotG Σ,
            !diskGhostG Σ, !fsLogG Σ, !iregG Σ}.
  Context `{GEN : GenId} `{CID0 : CpuId}.

  Notation Rra := (mword_of_int 1 : mword 5).
  Notation Rs0 := (mword_of_int 8 : mword 5).
  Notation Rs1 := (mword_of_int 9 : mword 5).
  Notation Ra0 := (mword_of_int 10 : mword 5).
  Notation Ra1 := (mword_of_int 11 : mword 5).
  Notation Ra2 := (mword_of_int 12 : mword 5).
  Notation Ra3 := (mword_of_int 13 : mword 5).
  Notation Ra4 := (mword_of_int 14 : mword 5).
  Notation Ra5 := (mword_of_int 15 : mword 5).
  Notation Rs2 := (mword_of_int 18 : mword 5).
  Notation Rs3 := (mword_of_int 19 : mword 5).
  Notation Rs4 := (mword_of_int 20 : mword 5).
  Notation Rs5 := (mword_of_int 21 : mword 5).

  Local Ltac regne := reg_ne_side.

  Local Ltac reg_neq :=
    lazymatch goal with |- ?a <> ?b =>
      tryif unify a b then fail else (vm_compute; discriminate) end.

  (* ===================================================================
     THE CHILD/PARENT PROC_PRIV ACCESSOR, generalized over the size, the
     descriptor AND the trapframe contents together -- [ProcInv]'s own
     [proc_priv_addrspace] leaves the trapframe bundled inside its wand's
     closure (so it cannot be read out concurrently), and
     [proc_priv_tf]'s wand can only hand back the SAME content it was
     given (so it cannot serve the write side of the copy loop).  This
     opens all three axes at once: sz/pagetable/table are handed out
     loose (as [proc_priv_addrspace] does) and the trapframe pointer is
     handed out at FULL ownership (as [SpecFreeproc.fp_tf]'s [Some] arm
     wants it, and as [ProcPtOwn.proc_pt_at] already holds it -- no
     [word_split14] fraction-splitting needed, that Local lemma is not
     ours to use anyway).
     =================================================================== *)
  Lemma kfk_priv_open (γf : gname) (pa : mword 64) (pid : mword 32) (V : pprivate) :
    proc_priv γf pa pid V -∗
    ⌜uint (pv_sz V) <= uvm_maxsz⌝ ∗
    ⌜um_below (pv_sz V) (ud_um (pv_upt V))⌝ ∗
    p_sz pa ↦₈ pv_sz V ∗
    p_pagetable pa ↦₈ page_base (ud_root (pv_upt V)) ∗
    proc_pt (pv_upt V) ∗
    p_trapframe pa ↦₈ page_base (ud_tfp (pv_upt V)) ∗
    tf_page (ud_tfp (pv_upt V)) (pv_tf V) ∗
    (∀ (P' : uptd) (szv : mword 64) (ws' : list (mword 64)),
       ⌜ud_root P' = ud_root (pv_upt V)⌝ -∗
       ⌜ud_tfp P' = ud_tfp (pv_upt V)⌝ -∗
       ⌜uint szv <= uvm_maxsz⌝ -∗
       ⌜um_below szv (ud_um P')⌝ -∗
       p_sz pa ↦₈ szv -∗
       p_pagetable pa ↦₈ page_base (ud_root (pv_upt V)) -∗
       proc_pt P' -∗
       p_trapframe pa ↦₈ page_base (ud_tfp (pv_upt V)) -∗
       tf_page (ud_tfp (pv_upt V)) ws' -∗
       proc_priv γf pa pid (upd_pt (upd_sz V szv) P' ws')).
  Proof.
    iIntros "Hpv".
    iDestruct (proc_priv_sz_maxsz with "Hpv") as "#Hszb".
    iDestruct (proc_priv_um_below with "Hpv") as "#Hbel".
    iDestruct "Hpv" as "[(%Hszb & %Hbel & Hpid & Hf & Hpt & Htfp & Hc) Ho]".
    rewrite /proc_fields /proc_pt_at.
    iDestruct "Hf" as "(Hsz & Hcwd & %Hnl & Hnm)".
    iDestruct "Hpt" as "(Hpg & Htfc & Hptt)".
    iSplitR; [done|]. iSplitR; [done|].
    iFrame "Hsz Hpg Hptt Htfc Htfp".
    iIntros (P' szv ws') "%Hroot %Htf %Hszb' %Hbel' Hsz Hpg Hptt Htfc Htfp".
    rewrite /proc_priv /proc_priv_core /proc_fields /proc_pt_at.
    cbn [upd_pt upd_sz pv_sz pv_upt pv_tf pv_ofile pv_cwd pv_name].
    rewrite Hroot Htf.
    iSplitR "Ho"; [|iFrame "Ho"].
    iSplitR; [iPureIntro; exact Hszb'|].
    iSplitR; [iPureIntro; exact Hbel'|].
    iFrame "Hpid".
    iSplitL "Hsz Hcwd Hnm".
    { iFrame "Hsz Hcwd Hnm". iPureIntro. exact Hnl. }
    iFrame "Hpg Htfc Hptt Htfp Hc".
  Qed.

  (* the same, on the DEFICIT block: the CHILD is still in the construction
     window here -- allocproc left [np->cwd] at 0 -- so uvmcopy's
     destination side opens a [proc_priv_nocwd].  Neither this nor its
     [proc_priv] twin touches [p->cwd]. *)
  Lemma kfk_priv_open_nocwd (γf : gname) (pa : mword 64) (pid : mword 32) (V : pprivate) :
    proc_priv_nocwd γf pa pid V -∗
    ⌜uint (pv_sz V) <= uvm_maxsz⌝ ∗
    ⌜um_below (pv_sz V) (ud_um (pv_upt V))⌝ ∗
    p_sz pa ↦₈ pv_sz V ∗
    p_pagetable pa ↦₈ page_base (ud_root (pv_upt V)) ∗
    proc_pt (pv_upt V) ∗
    p_trapframe pa ↦₈ page_base (ud_tfp (pv_upt V)) ∗
    tf_page (ud_tfp (pv_upt V)) (pv_tf V) ∗
    (∀ (P' : uptd) (szv : mword 64) (ws' : list (mword 64)),
       ⌜ud_root P' = ud_root (pv_upt V)⌝ -∗
       ⌜ud_tfp P' = ud_tfp (pv_upt V)⌝ -∗
       ⌜uint szv <= uvm_maxsz⌝ -∗
       ⌜um_below szv (ud_um P')⌝ -∗
       p_sz pa ↦₈ szv -∗
       p_pagetable pa ↦₈ page_base (ud_root (pv_upt V)) -∗
       proc_pt P' -∗
       p_trapframe pa ↦₈ page_base (ud_tfp (pv_upt V)) -∗
       tf_page (ud_tfp (pv_upt V)) ws' -∗
       proc_priv_nocwd γf pa pid (upd_pt (upd_sz V szv) P' ws')).
  Proof.
    iIntros "Hpv".
    iDestruct (proc_priv_nocwd_sz_maxsz with "Hpv") as "#Hszb".
    iDestruct (proc_priv_nocwd_um_below with "Hpv") as "#Hbel".
    iDestruct "Hpv" as "(%Hszb & %Hbel & Hpid & Hf & Hpt & Htfp & Ho)".
    rewrite /proc_fields /proc_pt_at.
    iDestruct "Hf" as "(Hsz & Hcwd & %Hnl & Hnm)".
    iDestruct "Hpt" as "(Hpg & Htfc & Hptt)".
    iSplitR; [done|]. iSplitR; [done|].
    iFrame "Hsz Hpg Hptt Htfc Htfp".
    iIntros (P' szv ws') "%Hroot %Htf %Hszb' %Hbel' Hsz Hpg Hptt Htfc Htfp".
    rewrite /proc_priv_nocwd /proc_fields /proc_pt_at.
    cbn [upd_pt upd_sz pv_sz pv_upt pv_tf pv_ofile pv_cwd pv_name].
    rewrite Hroot Htf.
    iSplitR; [iPureIntro; exact Hszb'|].
    iSplitR; [iPureIntro; exact Hbel'|].
    iFrame "Hpid".
    iSplitL "Hsz Hcwd Hnm".
    { iFrame "Hsz Hcwd Hnm". iPureIntro. exact Hnl. }
    iFrame "Hpg Htfc Hptt Htfp Ho".
  Qed.

  (* closing [kfk_priv_open]'s wand with NOTHING changed is the identity. *)
  Lemma kfk_priv_close_id (V : pprivate) :
    upd_pt (upd_sz V (pv_sz V)) (pv_upt V) (pv_tf V) = V.
  Proof. destruct V; reflexivity. Qed.

  (* =================================================================== *)
  (*  THE BLOCK.                                                          *)
  (* =================================================================== *)
  Lemma kfk_prologue
      (γa γp γw γl γf γil γic : gname) (γs : list gname)
      (cn : ic_names) (γfs : fs_names) (cov : gset Z) (logstart : Z) (nib : nat)
      (m : regfile) (lvl K : nat) (eb : bool) (pme : mword 64) (C : iProp Σ)
      (on : option nat) (b : bool) (pid_p : mword 32) (Vp : pprivate)
      (R : iProp Σ) (lks : gset nat) :
    let sp0 : mword 64 := m !!! Regidx csp_rs1 in
    let ra0 : mword 64 := m !!! Regidx Rra in
    let s00 : mword 64 := m !!! Regidx Rs0 in
    let s10 : mword 64 := m !!! Regidx Rs1 in
    let s50 : mword 64 := m !!! Regidx Rs5 in
    (K_kfork <= K)%nat ->
    (Z.of_nat lvl + 2 < 2 ^ 31)%Z ->
    (* this block's only lock-touching callee is allocproc, whose own bound
       is at "proc" (11) -- uvmcopy's kalloc calls run while np->lock is
       already held, but rank above "proc" follows by [locks_below_mono]
       and its own contract does not yet expose the premise. *)
    locks_below lks (lock_rank "proc") ->
    sie_cap_gpr m K b pme -∗
    cpu_own lvl eb pme C b lks -∗
    kernel_text -∗
    pc_is (mword_of_int KF : mword 64) -∗
    panic_wp_any -∗
    procs_inv γs -∗
    is_lock γp alp_pid_lock "nextpid"%string nextpid_res -∗
    is_lock γw wait_lock_addr "wait_lock"%string wait_res -∗
    is_ftable γl γf -∗
    is_itable2 γil cn γfs γic cov logstart nib icfg_dev -∗
    itable_inv -∗
    kalloc_env γa on -∗
    proc_priv γf pme pid_p Vp -∗
    (* THE CALLER'S EXIT, THREADED -- kwait's [kw_exit_fn] recipe.  The three
       continuations below are three DIFFERENT closures and exactly one of
       them runs, but a caller has only ONE exit and it is linear, so making
       each closure capture its own copy is unsound by typing (claude-notes,
       S10: "splitting it into two closures instead is unsound-by-typing:
       whichever arm does not run would have to drop one").  So the exit
       rides through as an abstract [R] and each continuation receives it
       back as its LAST argument. *)
    R -∗
    (* ---- Hcont10a : allocproc found no free slot ---- *)
    wp_next b pme (fun (CID : CpuId) =>
      ∀ (Mt : regfile),
        ⌜ Mt !!! Regidx csp_rs1 = pa_stk sp0 8 ⌝ -∗
        ⌜ forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 ->
            r <> Rs0 -> r <> Rs1 -> r <> Rs5 -> Mt !!! Regidx r = m !!! Regidx r ⌝ -∗
        sie_cap_gpr Mt (K - 8)%nat b pme -∗
        (* [cpu_own] is handed on, not dropped.  Both of allocproc_post's
           not-found arms return it at the CALLER's level and index, and
           [SpecKfork.kfork_post] needs it unconditionally -- an affine BI
           lets a proof drop it silently, which is exactly how it went
           missing from this continuation the first time. *)
        cpu_own lvl eb pme C b lks -∗
        kernel_text -∗
        pc_is (mword_of_int (KF + 0x10a) : mword 64) -∗
        kfk_frame sp0 ra0 s00 s10 s50 -∗
        proc_priv γf pme pid_p Vp -∗
        ( kalloc_env γa on
          ∨ (∃ n : nat, ⌜(n <= K_allocproc)%nat /\ avail_zero (avail_sub on n)⌝ ∗
             kalloc_env γa None) ) -∗
        R -∗
        WP (Loop : expr riscv_lang)) -∗
    (* ---- Hcont7c : uvmcopy failed ---- *)
    (* [wp_next]'s own reference hart is bound EXPLICITLY (rather than left to
       resolve at this Section's [CID0]): once allocproc's found arm commits
       to [b = false] the hart is pinned from THAT hart on, which need not be
       [CID0] if the entry [b] was [true] and a migration happened inside
       myproc/allocproc.  The caller instantiates [CIDh] at whichever hart is
       ambient the moment it reaches this exit. *)
    (* THE CROSSING PREMISE IS NOT OPTIONAL.  Without it this antecedent is
       "prove the continuation at a hart nobody has said anything about":
       [wp_next _ false _ K] is [K CIDh] ([WpNext.wp_next_off]), so supplying
       it means proving [K CIDh] for an ADVERSARIAL [CIDh], and the caller's
       own exit continuation is anchored at [CID0] with no way to re-anchor.
       The fact is true and this proof already has it -- [wp_next_chain] over
       the leaves run so far -- it was simply never surfaced. *)
    (∀ CIDh : CpuId,
       ⌜ b = false \/ pme = zero_reg -> (CIDh : CPU) = (CID0 : CPU) ⌝ -∗
       wp_next (CID0 := CIDh) false pme (fun (CID : CpuId) =>
      ∀ (Mt : regfile) (npa : mword 64) (j : nat) (γl2 : gname)
        (pid_c : mword 32) (ch : mword 64) (Vc : pprivate),
        ⌜ Mt !!! Regidx csp_rs1 = pa_stk sp0 8 ⌝ -∗
        ⌜ Mt !!! Regidx Rs4 = npa ⌝ -∗
        ⌜ Mt !!! Regidx Rs5 = pme ⌝ -∗
        ⌜ Mt !!! Regidx Ra0 = (mword_of_int (-1) : mword 64) ⌝ -∗
        ⌜ forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 ->
            r <> Rs0 -> r <> Rs1 -> r <> Rs4 -> r <> Rs5 -> Mt !!! Regidx r = m !!! Regidx r ⌝ -∗
        (* [npa = proc_addr j] is what lets the caller apply a block stated
           over [proc_addr j] (ProofKforkB1) to the [npa] this hands out.
           Inside, [npa] IS [proc_addr j] by [set]; the binder is free, so
           without this equation the caller has an opaque pointer. *)
        ⌜ npa = proc_addr j /\ (j < NPROC)%nat /\ γs !! j = Some γl2 /\
          pv_ofile Vc = replicate NOFILE (zero_reg : mword 64) /\
          pv_cwd Vc = (zero_reg : mword 64) ⌝ -∗
        (* IN-LOCK EXIT: allocproc returned holding np->lock, so the index
           carries the trap reserve of the arm the caller will eventually
           return at ([trap_res b]) -- exactly [SpecAllocproc]'s found-arm
           index, propagated. *)
        sie_cap_gpr Mt (trap_res b + (K - 8))%nat false pme -∗
        kernel_text -∗
        pc_is (mword_of_int (KF + 0x7c) : mword 64) -∗
        (* slot 6 PINNED: s4 was spilled at +0x1a and the uvmcopy-failure
           tail reloads it at +0x8a, so that exit has to know which value it
           gets back.  Slots 4/5 stay existential -- s2/s3 are spilled only
           at +0x30/+0x32, i.e. after uvmcopy has already SUCCEEDED, so on
           this path they were never written. *)
        (∃ w4 w5 : mword 64,
           kfk_frame_at sp0 ra0 s00 s10 s50 w4 w5 (m !!! Regidx Rs4)) -∗
        proc_priv γf pme pid_p Vp -∗
        proc_priv_nocwd γf npa pid_c Vc -∗
        SchedCtx.proc_held cpu_id j γl2 USED ch -∗
        ProcGeom.hart_at_any npa -∗
        FdSlots.fd_slots FDSPARE -∗
        IrefSlots.iref_slots (1 + IREFSPARE) -∗
        SwtchCtx.own_ctx (p_context npa) -∗
        IntrDefs.arm_pay lvl eb pme -∗
        cpu_own (S lvl) eb pme C false ({[lock_rank "proc"]} ∪ lks) -∗
        kalloc_env γa None -∗
        R -∗
        WP (Loop : expr riscv_lang))) -∗
    (* ---- Hcont4a : uvmcopy succeeded -- the trapframe copy loop's head --- *)
    (* THE CROSSING PREMISE IS NOT OPTIONAL.  Without it this antecedent is
       "prove the continuation at a hart nobody has said anything about":
       [wp_next _ false _ K] is [K CIDh] ([WpNext.wp_next_off]), so supplying
       it means proving [K CIDh] for an ADVERSARIAL [CIDh], and the caller's
       own exit continuation is anchored at [CID0] with no way to re-anchor.
       The fact is true and this proof already has it -- [wp_next_chain] over
       the leaves run so far -- it was simply never surfaced. *)
    (∀ CIDh : CpuId,
       ⌜ b = false \/ pme = zero_reg -> (CIDh : CPU) = (CID0 : CPU) ⌝ -∗
       wp_next (CID0 := CIDh) false pme (fun (CID : CpuId) =>
      ∀ (Mt : regfile) (npa : mword 64) (j : nat) (γl2 : gname)
        (pid_c : mword 32) (ch : mword 64) (Vc' : pprivate)
        (tfsrc tfdst : mword 44),
        ⌜ Mt !!! Regidx csp_rs1 = pa_stk sp0 8 ⌝ -∗
        ⌜ Mt !!! Regidx Rs4 = npa ⌝ -∗
        ⌜ Mt !!! Regidx Rs5 = pme ⌝ -∗
        ⌜ Mt !!! Regidx Ra5 = a_tf_word tfsrc 0 ⌝ -∗
        ⌜ Mt !!! Regidx Ra4 = a_tf_word tfdst 0 ⌝ -∗
        ⌜ Mt !!! Regidx Ra3 = a_tf_word tfsrc 36 ⌝ -∗
        ⌜ ud_tfp (pv_upt Vp) = tfsrc /\ ud_tfp (pv_upt Vc') = tfdst ⌝ -∗
        ⌜ forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 ->
            r <> Rs0 -> r <> Rs1 -> r <> Rs4 -> r <> Rs5 -> Mt !!! Regidx r = m !!! Regidx r ⌝ -∗
        (* the child is still FRESH: uvmcopy touched only its page table, and
           [upd_pt]/[upd_sz] preserve both of these.  The uvmcopy-failure
           continuation states the same two facts about [Vc]; the success
           one has to state them about [Vc'] or the fd scan cannot start. *)
        ⌜ npa = proc_addr j /\ (j < NPROC)%nat /\ γs !! j = Some γl2 /\
          pv_ofile Vc' = replicate NOFILE (zero_reg : mword 64) /\
          pv_cwd Vc' = (zero_reg : mword 64) ⌝ -∗
        (* IN-LOCK EXIT: allocproc returned holding np->lock, so the index
           carries the trap reserve of the arm the caller will eventually
           return at ([trap_res b]) -- exactly [SpecAllocproc]'s found-arm
           index, propagated. *)
        sie_cap_gpr Mt (trap_res b + (K - 8))%nat false pme -∗
        kernel_text -∗
        pc_is (mword_of_int (KF + 0x4a) : mword 64) -∗
        (* all three lazy slots PINNED here: by +0x4a s2, s3 and s4 have all
           been spilled, and [ProofKfork.kfk_tail_succ] reloads all three. *)
        kfk_frame_at sp0 ra0 s00 s10 s50
          (m !!! Regidx Rs2) (m !!! Regidx Rs3) (m !!! Regidx Rs4) -∗
        proc_priv γf pme pid_p Vp -∗
        proc_priv_nocwd γf npa pid_c Vc' -∗
        SchedCtx.proc_held cpu_id j γl2 USED ch -∗
        ProcGeom.hart_at_any npa -∗
        FdSlots.fd_slots FDSPARE -∗
        (* the child's iref units, out of the dormant block allocproc took
           the slot from: the [1] is the cwd unit ProofKforkB4 spends on
           [idup], [IREFSPARE] is the allowance that parks with the child. *)
        IrefSlots.iref_slots (1 + IREFSPARE) -∗
        (* THE RAW CONTEXT, not [own_ctx].  The success path's park
           ([SpecForkretPark.forkret_park], run inside ProofKforkB5 at
           kfork's FIRST release) needs the kstack and the saved context at
           their literal head values -- ra = forkret, sp = kstack + PGSIZE --
           and a generic 14-word existential cannot be split back into those.
           The uvmcopy-FAILURE continuation above keeps [own_ctx], because
           freeproc's [fp_rest] wants exactly that and nothing sharper. *)
        (∃ (ks : mword 64) (rest : list (mword 64)),
           ⌜length rest = 12%nat⌝ ∗
           ProcInv.is_kstack npa ks ∗
           SwtchCtx.ctx_cells (p_context npa)
             (* [SpecAllocproc.forkret_pc]; [SpecForkretPark.v] duplicates the
                constant rather than importing it, so B5's premise names the
                other copy.  The two are [mword_of_int KernelSyms.forkret]
                either way, hence convertible, and [iApply] bridges them. *)
             (forkret_pc :: add_vec ks (mword_of_int 4096) :: rest)) -∗
        IntrDefs.arm_pay lvl eb pme -∗
        cpu_own (S lvl) eb pme C false ({[lock_rank "proc"]} ∪ lks) -∗
        kalloc_env γa None -∗
        is_lock γw wait_lock_addr "wait_lock"%string wait_res -∗
        is_ftable γl γf -∗
        is_itable2 γil cn γfs γic cov logstart nib icfg_dev -∗
        itable_inv -∗
        R -∗
        WP (Loop : expr riscv_lang))) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros sp0 ra0 s00 s10 s50 HK Hlvl Hbelow.
    unfold K_kfork in HK.
    iIntros "Hcg Hcpu #Htext Hpc #Hpanic #Hprocs #Hplock #Hwlock #Hftbl #Hitbl
             #Hitinv Henv Hpv HR Hcont10a Hcont7c Hcont4a".
    set (K1 := (K - 8)%nat).
    iPoseProof (kfk_000 with "Htext") as "Hi000".
    iPoseProof (kfk_002 with "Htext") as "Hi002".
    iPoseProof (kfk_004 with "Htext") as "Hi004".
    iPoseProof (kfk_006 with "Htext") as "Hi006".
    iPoseProof (kfk_008 with "Htext") as "Hi008".
    iPoseProof (kfk_00a with "Htext") as "Hi00a".
    iPoseProof (kfk_00c with "Htext") as "Hi00c".
    iPoseProof (kfk_010 with "Htext") as "Hi010".
    iPoseProof (kfk_012 with "Htext") as "Hi012".
    iPoseProof (kfk_016 with "Htext") as "Hi016".
    iPoseProof (kfk_01a with "Htext") as "Hi01a".
    iPoseProof (kfk_01c with "Htext") as "Hi01c".
    iPoseProof (kfk_01e with "Htext") as "Hi01e".
    iPoseProof (kfk_022 with "Htext") as "Hi022".
    iPoseProof (kfk_024 with "Htext") as "Hi024".
    iPoseProof (kfk_028 with "Htext") as "Hi028".
    iPoseProof (kfk_02c with "Htext") as "Hi02c".
    iPoseProof (kfk_030 with "Htext") as "Hi030".
    iPoseProof (kfk_032 with "Htext") as "Hi032".
    iPoseProof (kfk_034 with "Htext") as "Hi034".
    iPoseProof (kfk_038 with "Htext") as "Hi038".
    iPoseProof (kfk_03c with "Htext") as "Hi03c".
    iPoseProof (kfk_040 with "Htext") as "Hi040".
    iPoseProof (kfk_042 with "Htext") as "Hi042".
    iPoseProof (kfk_046 with "Htext") as "Hi046".
    (* =================================================================
       PROLOGUE: push 8 slots, spill ra/s0/s1/s5, set the frame pointer.
       ================================================================= *)
    assert (Hpush : add_vec sp0 (sign_extend' 64 (caddi16sp_imm (mword_of_int 60 : mword 6)))
                    = pa_stk sp0 8).
    { unfold pa_stk, add_vec_int. apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    iApply (wp_caddi16sp_push_s_sconf (mword_of_int KF) (mword_of_int 60 : mword 6) m K 8 b
              ltac:(lia) Hpush with "Hcg Hpc Hi000").
    iIntros (CID1 Hs1) "Hcg Hframe Hpc".
    fold K1.
    set (M0' := <[Regidx csp_rs1 := regval_into_reg (pa_stk sp0 8)]> m).
    change (<[Regidx csp_rs1 := regval_into_reg (add_vec sp0
              (sign_extend' 64 (caddi16sp_imm (mword_of_int 60 : mword 6))))]> m) with M0'.
    assert (HM0sp : M0' !!! Regidx csp_rs1 = pa_stk sp0 8) by (rewrite /M0' upd_eq; reflexivity).
    iEval (rewrite stack_own_slots; cbn [seq]) in "Hframe".
    iDestruct "Hframe" as "(S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8 & _)".
    iDestruct "S1" as (u1) "Hb1". iDestruct "S2" as (u2) "Hb2".
    iDestruct "S3" as (u3) "Hb3". iDestruct "S4" as (u4) "Hb4".
    iDestruct "S5" as (u5) "Hb5". iDestruct "S6" as (u6) "Hb6".
    iDestruct "S7" as (u7) "Hb7". iDestruct "S8" as (u8) "Hb8".
    assert (Hf1 : add_vec (M0' !!! Regidx csp_rs1)
                    (zero_extend' 64 (concat_vec (mword_of_int 7 : mword 6) ('b"000")))
                  = pa_stk sp0 1) by (rewrite HM0sp; apply kfk_frm1).
    assert (Hf2 : add_vec (M0' !!! Regidx csp_rs1)
                    (zero_extend' 64 (concat_vec (mword_of_int 6 : mword 6) ('b"000")))
                  = pa_stk sp0 2) by (rewrite HM0sp; apply kfk_frm2).
    assert (Hf3 : add_vec (M0' !!! Regidx csp_rs1)
                    (zero_extend' 64 (concat_vec (mword_of_int 5 : mword 6) ('b"000")))
                  = pa_stk sp0 3) by (rewrite HM0sp; apply kfk_frm3).
    assert (Hf7 : add_vec (M0' !!! Regidx csp_rs1)
                    (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000")))
                  = pa_stk sp0 7) by (rewrite HM0sp; apply kfk_frm7).
    iEval (rewrite -Hf1) in "Hb1". iEval (rewrite -Hf2) in "Hb2".
    iEval (rewrite -Hf3) in "Hb3". iEval (rewrite -Hf7) in "Hb7".
    assert (Hpp002 : add_vec_int (mword_of_int KF : mword 64) 2 = mword_of_int (KF + 0x2))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp002) in "Hpc".
    (* +0x002 c.sdsp ra,56(sp) *)
    iApply (wp_csdsp_s_sconf (mword_of_int (KF + 0x2)) (mword_of_int 7 : mword 6) Rra
              M0' K1 u1 b with "Hcg Hpc Hi002 Hb1").
    iIntros (CID2 Hs2) "Hcg Hpc Hb1". iEval (rgne) in "Hb1". iEval (rewrite Hf1) in "Hb1".
    assert (HM0ra : M0' !!! Regidx Rra = ra0)
      by (rewrite /M0' upd_ne; [reflexivity | vm_compute; discriminate]).
    iEval (rewrite HM0ra) in "Hb1".
    assert (Hpp004 : add_vec_int (mword_of_int (KF + 0x2) : mword 64) 2 = mword_of_int (KF + 0x4))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp004) in "Hpc".
    (* +0x004 c.sdsp s0,48(sp) *)
    iApply (wp_csdsp_s_sconf (mword_of_int (KF + 0x4)) (mword_of_int 6 : mword 6) Rs0
              M0' K1 u2 b with "Hcg Hpc Hi004 Hb2").
    iIntros (CID3 Hs3) "Hcg Hpc Hb2". iEval (rgne) in "Hb2". iEval (rewrite Hf2) in "Hb2".
    assert (HM0s0 : M0' !!! Regidx Rs0 = s00)
      by (rewrite /M0' upd_ne; [reflexivity | vm_compute; discriminate]).
    iEval (rewrite HM0s0) in "Hb2".
    assert (Hpp006 : add_vec_int (mword_of_int (KF + 0x4) : mword 64) 2 = mword_of_int (KF + 0x6))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp006) in "Hpc".
    (* +0x006 c.sdsp s1,40(sp) *)
    iApply (wp_csdsp_s_sconf (mword_of_int (KF + 0x6)) (mword_of_int 5 : mword 6) Rs1
              M0' K1 u3 b with "Hcg Hpc Hi006 Hb3").
    iIntros (CID4 Hs4) "Hcg Hpc Hb3". iEval (rgne) in "Hb3". iEval (rewrite Hf3) in "Hb3".
    assert (HM0s1 : M0' !!! Regidx Rs1 = s10)
      by (rewrite /M0' upd_ne; [reflexivity | vm_compute; discriminate]).
    iEval (rewrite HM0s1) in "Hb3".
    assert (Hpp008 : add_vec_int (mword_of_int (KF + 0x6) : mword 64) 2 = mword_of_int (KF + 0x8))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp008) in "Hpc".
    (* +0x008 c.sdsp s5,8(sp) *)
    iApply (wp_csdsp_s_sconf (mword_of_int (KF + 0x8)) (mword_of_int 1 : mword 6) Rs5
              M0' K1 u7 b with "Hcg Hpc Hi008 Hb7").
    iIntros (CID5 Hs5) "Hcg Hpc Hb7". iEval (rgne) in "Hb7". iEval (rewrite Hf7) in "Hb7".
    assert (HM0s5 : M0' !!! Regidx Rs5 = s50)
      by (rewrite /M0' upd_ne; [reflexivity | vm_compute; discriminate]).
    iEval (rewrite HM0s5) in "Hb7".
    assert (Hpp00a : add_vec_int (mword_of_int (KF + 0x8) : mword 64) 2 = mword_of_int (KF + 0xa))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp00a) in "Hpc".
    (* +0x00a c.addi4spn s0,sp,64 *)
    iApply (wp_caddi4spn_s_sconf (mword_of_int (KF + 0xa)) (Cregidx (mword_of_int 0))
              (mword_of_int 16 : mword 8) Rs0 M0' K1 b
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi00a").
    iIntros (CID6 Hs6) "Hcg Hpc".
    set (M1 := <[Regidx Rs0 := regval_into_reg
                  (add_vec (M0' !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm (mword_of_int 16 : mword 8))))]> M0').
    assert (HM1s0 : M1 !!! Regidx Rs0 = sp0).
    { rewrite /M1 upd_eq HM0sp. apply stk_fp_64. }
    assert (HM1sp : M1 !!! Regidx csp_rs1 = pa_stk sp0 8)
      by (rewrite /M1 upd_ne; [exact HM0sp | vm_compute; discriminate]).
    assert (HM1ra : M1 !!! Regidx Rra = ra0)
      by (rewrite /M1 upd_ne; [exact HM0ra | vm_compute; discriminate]).
    assert (HM1s1 : M1 !!! Regidx Rs1 = s10)
      by (rewrite /M1 upd_ne; [exact HM0s1 | vm_compute; discriminate]).
    assert (HM1s5 : M1 !!! Regidx Rs5 = s50)
      by (rewrite /M1 upd_ne; [exact HM0s5 | vm_compute; discriminate]).
    assert (Hpp00c : add_vec_int (mword_of_int (KF + 0xa) : mword 64) 2 = mword_of_int (KF + 0xc))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp00c) in "Hpc".
    (* =================================================================
       +0x00c: jal ra, myproc
       ================================================================= *)
    iApply (wp_jal_s_sconf (mword_of_int (KF + 0xc)) Rra (mword_of_int 2096260 : mword 21)
              M1 K1 b ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi00c").
    iIntros (CID7 Hs7) "Hcg Hpc".
    set (M2 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (KF + 0xc) : mword 64) 4)]> M1).
    assert (Hjmyp : add_vec (mword_of_int (KF + 0xc) : mword 64)
                     (sign_extend' 64 (mword_of_int 2096260 : mword 21)) = mword_of_int KernelSyms.myproc)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hjmyp) in "Hpc".
    assert (HM2sp : M2 !!! Regidx csp_rs1 = pa_stk sp0 8)
      by (rewrite /M2 upd_ne; [exact HM1sp | vm_compute; discriminate]).
    assert (HM2s0 : M2 !!! Regidx Rs0 = sp0)
      by (rewrite /M2 upd_ne; [exact HM1s0 | vm_compute; discriminate]).
    assert (HM2s1 : M2 !!! Regidx Rs1 = s10)
      by (rewrite /M2 upd_ne; [exact HM1s1 | vm_compute; discriminate]).
    assert (HM2s5 : M2 !!! Regidx Rs5 = s50)
      by (rewrite /M2 upd_ne; [exact HM1s5 | vm_compute; discriminate]).
    assert (HM2ra : M2 !!! Regidx Rra = add_vec_int (mword_of_int (KF + 0xc) : mword 64) 4)
      by (rewrite /M2 upd_eq; reflexivity).
    (* ---- myproc(): a0 = pme ---- *)
    iDestruct (cpu_own_transport CID0 CID7 lvl eb pme C b ltac:(wp_next_chain) with "Hcpu") as "Hcpu".
    iApply (Myproc.wp_myproc_sconf M2 K1 lvl eb pme C b _
              ltac:(lia) ltac:(lia)
              with "Hcg Hcpu Htext Hpc").
    iIntros (CID8 Hs8 ms A) "%Hms Hcg Hcpu Hpc %HcsA".
    destruct HcsA as [HcsA HAa0].
    assert (Hpc10 : ret_pc (M2 !!! Regidx Rra) = mword_of_int (KF + 0x10))
      by (rewrite HM2ra; apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc10) in "Hpc".
    assert (HAsp : A !!! Regidx csp_rs1 = pa_stk sp0 8)
      by (rewrite (callee_saved_lookup HcsA csp_rs1 ltac:(vm_compute; reflexivity)); exact HM2sp).
    assert (HAs0 : A !!! Regidx Rs0 = sp0)
      by (rewrite (callee_saved_lookup HcsA (mword_of_int 8) ltac:(vm_compute; reflexivity)); exact HM2s0).
    assert (HAs1 : A !!! Regidx Rs1 = s10)
      by (rewrite (callee_saved_lookup HcsA (mword_of_int 9) ltac:(vm_compute; reflexivity)); exact HM2s1).
    assert (HAs5 : A !!! Regidx Rs5 = s50)
      by (rewrite (callee_saved_lookup HcsA (mword_of_int 21) ltac:(vm_compute; reflexivity)); exact HM2s5).
    assert (HAthr : forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 ->
              r <> Rs0 -> r <> Rs1 -> r <> Rs5 -> A !!! Regidx r = m !!! Regidx r).
    { intros r Hr Ncsp N8 N9 N21.
      rewrite (callee_saved_lookup HcsA r Hr).
      rewrite /M2 upd_ne; [| regne]. rewrite /M1 upd_ne; [| regne].
      rewrite /M0' upd_ne; [| regne]. reflexivity. }
    (* +0x010 c.mv s5,a0 -- s5 := pme *)
    iApply (wp_cmv_s_sconf (mword_of_int (KF + 0x10)) Rs5 Ra0 A K1 b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi010").
    iIntros (CID9 Hs9) "Hcg Hpc". iEval (rgne) in "Hcg".
    set (M4 := <[Regidx Rs5 := regval_into_reg (add_vec zero_reg (A !!! Regidx Ra0))]> A).
    assert (HM4s5 : M4 !!! Regidx Rs5 = pme)
      by (rewrite /M4 upd_eq HAa0; apply add_vec_zero_l).
    assert (HM4sp : M4 !!! Regidx csp_rs1 = pa_stk sp0 8)
      by (rewrite /M4 upd_ne; [exact HAsp | vm_compute; discriminate]).
    assert (HM4s0 : M4 !!! Regidx Rs0 = sp0)
      by (rewrite /M4 upd_ne; [exact HAs0 | vm_compute; discriminate]).
    assert (HM4s1 : M4 !!! Regidx Rs1 = s10)
      by (rewrite /M4 upd_ne; [exact HAs1 | vm_compute; discriminate]).
    assert (HM4thr : forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 ->
              r <> Rs0 -> r <> Rs1 -> r <> Rs5 -> M4 !!! Regidx r = m !!! Regidx r).
    { intros r Hr Ncsp N8 N9 N21.
      rewrite /M4 upd_ne; [| regne]. apply HAthr; assumption. }
    assert (Hpp012 : add_vec_int (mword_of_int (KF + 0x10) : mword 64) 2 = mword_of_int (KF + 0x12))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp012) in "Hpc".
    (* =================================================================
       +0x012: jal ra, allocproc
       ================================================================= *)
    iApply (wp_jal_s_sconf (mword_of_int (KF + 0x12)) Rra (mword_of_int 2096810 : mword 21)
              M4 K1 b ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi012").
    iIntros (CID10 Hs10) "Hcg Hpc".
    set (M5 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (KF + 0x12) : mword 64) 4)]> M4).
    assert (Hjalp : add_vec (mword_of_int (KF + 0x12) : mword 64)
                     (sign_extend' 64 (mword_of_int 2096810 : mword 21)) = mword_of_int KernelSyms.allocproc)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hjalp) in "Hpc".
    assert (HM5sp : M5 !!! Regidx csp_rs1 = pa_stk sp0 8)
      by (rewrite /M5 upd_ne; [exact HM4sp | vm_compute; discriminate]).
    assert (HM5s0 : M5 !!! Regidx Rs0 = sp0)
      by (rewrite /M5 upd_ne; [exact HM4s0 | vm_compute; discriminate]).
    assert (HM5s1 : M5 !!! Regidx Rs1 = s10)
      by (rewrite /M5 upd_ne; [exact HM4s1 | vm_compute; discriminate]).
    assert (HM5s5 : M5 !!! Regidx Rs5 = pme)
      by (rewrite /M5 upd_ne; [exact HM4s5 | vm_compute; discriminate]).
    assert (HM5ra : M5 !!! Regidx Rra = add_vec_int (mword_of_int (KF + 0x12) : mword 64) 4)
      by (rewrite /M5 upd_eq; reflexivity).
    iDestruct (cpu_own_transport CID8 CID10 lvl eb pme C b ltac:(wp_next_chain) with "Hcpu") as "Hcpu".
    iApply (Allocproc.wp_allocproc_core γa γp γf γs M5 lvl K1 eb pme C on b lks
              ltac:(lia) ltac:(lia) Hbelow
              with "Hcg Hcpu Htext Hpc Hpanic Hprocs Hplock Henv").
    all: try lkbelow.
    iIntros (CID11 Hs11 mf6) "%HcsB Hpc Hpost".
    assert (Hpc16 : ret_pc (M5 !!! Regidx Rra) = mword_of_int (KF + 0x16))
      by (rewrite HM5ra; apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc16) in "Hpc".
    assert (HBsp : mf6 !!! Regidx csp_rs1 = pa_stk sp0 8)
      by (rewrite (callee_saved_lookup HcsB csp_rs1 ltac:(vm_compute; reflexivity)); exact HM5sp).
    assert (HBs0 : mf6 !!! Regidx Rs0 = sp0)
      by (rewrite (callee_saved_lookup HcsB (mword_of_int 8) ltac:(vm_compute; reflexivity)); exact HM5s0).
    assert (HBs1 : mf6 !!! Regidx Rs1 = s10)
      by (rewrite (callee_saved_lookup HcsB (mword_of_int 9) ltac:(vm_compute; reflexivity)); exact HM5s1).
    assert (HBs5 : mf6 !!! Regidx Rs5 = pme)
      by (rewrite (callee_saved_lookup HcsB (mword_of_int 21) ltac:(vm_compute; reflexivity)); exact HM5s5).
    assert (HBthr : forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 ->
              r <> Rs0 -> r <> Rs1 -> r <> Rs5 -> mf6 !!! Regidx r = m !!! Regidx r).
    { intros r Hr Ncsp N8 N9 N21.
      rewrite (callee_saved_lookup HcsB r Hr).
      rewrite /M5 upd_ne; [| regne]. apply HM4thr; assumption. }
    (* ===================================================================
       THE THREE-WAY DISPATCH.  [allocproc_post] is a 2-way split (found /
       not found) at the assembly's own [c.beqz]; the "not found" side
       covers BOTH of allocproc_post's own not-found disjuncts (arm 1 and
       arm 3), which is exactly what [Hcont10a] takes as a disjunction too.
       =================================================================== *)
    assert (Hrget_mf6_a0 : rget mf6 Ra0 = mf6 !!! Regidx Ra0).
    { apply rget_ne. intro He. injection He as He2. vm_compute in He2. discriminate. }
    rewrite /allocproc_post.
    iDestruct "Hpost" as "[Hp1 | [Hp2 | Hp3]]".
    - (* ---- arm 1: no free slot, budget untouched ---- *)
      iDestruct "Hp1" as "(%Hrv & Hcg & Hcpu & Henv')".
      assert (HBa0 : mf6 !!! Regidx Ra0 = (zero_reg : mword 64)) by exact Hrv.
      iApply (wp_beqz_x0_taken_s_sconf (mword_of_int (KF + 0x16)) (mword_of_int 244 : mword 13)
                Ra0 mf6 K1 b
                ltac:(vm_compute; discriminate)
                ltac:(rewrite Hrget_mf6_a0 HBa0; vm_compute; reflexivity)
                ltac:(vm_compute; reflexivity)
                with "Hcg Hpc Hi016").
      iNext. iIntros (CID12 Hs12) "Hcg Hpc".
      (* [cpu_own] is the one bundle no leaf re-anchors: it came out of
         [allocproc_post] at CID11 and the continuation is at CID12, and the
         two print IDENTICALLY.  durable-notes' rule. *)
      iDestruct (cpu_own_transport CID11 CID12 lvl eb pme C b
                   ltac:(wp_next_chain) with "Hcpu") as "Hcpu".
      iAssert (kfk_frame sp0 ra0 s00 s10 s50) with "[Hb1 Hb2 Hb3 Hb4 Hb5 Hb6 Hb7 Hb8]" as "Hframe_alloc".
      { rewrite /kfk_frame. iFrame "Hb1 Hb2 Hb3 Hb7".
        iSplitL "Hb4"; [iExists u4; iExact "Hb4"|].
        iSplitL "Hb5"; [iExists u5; iExact "Hb5"|].
        iSplitL "Hb6"; [iExists u6; iExact "Hb6"|].
        iExists u8; iExact "Hb8". }
      iSpecialize ("Hcont10a" $! CID12 with "[%]"); [wp_next_chain|].
      iApply ("Hcont10a" $! mf6 with "[%] [%] Hcg Hcpu Htext Hpc Hframe_alloc Hpv [Henv'] HR").
      + exact HBsp.
      + intros r Hr Ncsp N8 N9 N21. apply HBthr; assumption.
      + iLeft. iExact "Henv'".
    - (* ===================================================================
         arm 2 -- FOUND.  Destructure the found-arm's whole bundle.
         =================================================================== *)
      iDestruct "Hp2" as (j γl2 ch pid_c Vc root tfp ks rest nc)
        "(%Hpures & Hheld & Hhart & Hcpriv & Hfdsp & Hirsp & Hks & Hctx & Hcg & Hcpu & Harmpay & Henv')".
      destruct Hpures as (Hrv & HjN & Hgamma & HVcupt & HVcof & HVccwd & Hrestlen & Hncle).
      assert (HBa0 : mf6 !!! Regidx Ra0 = proc_addr j) by exact Hrv.
      set (npa := proc_addr j).
      assert (Hnpanz : npa <> (zero_reg : mword 64)) by (apply proc_addr_nonzero; exact HjN).
      iApply (wp_beqz_x0_fall_s_sconf (mword_of_int (KF + 0x16)) (mword_of_int 244 : mword 13)
                Ra0 mf6 (trap_res b + K1)%nat false
                ltac:(vm_compute; discriminate)
                ltac:(rewrite Hrget_mf6_a0 HBa0; apply eq_vec_false_iff; exact Hnpanz)
                with "Hcg Hpc Hi016").
      iIntros (CID12 Hs12) "Hcg Hpc".
      assert (Hpp01a : add_vec_int (mword_of_int (KF + 0x16) : mword 64) 4 = mword_of_int (KF + 0x1a))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp01a) in "Hpc".
      (* +0x01a c.sdsp s4,16(sp) -- saves the CALLER's s4; no register write *)
      assert (Hf6 : add_vec (mf6 !!! Regidx csp_rs1)
                      (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000")))
                    = pa_stk sp0 6) by (rewrite HBsp; apply kfk_frm6).
      iEval (rewrite -Hf6) in "Hb6".
      iApply (wp_csdsp_s_sconf (mword_of_int (KF + 0x1a)) (mword_of_int 2 : mword 6) Rs4
                mf6 (trap_res b + K1)%nat u6 false with "Hcg Hpc Hi01a Hb6").
      iIntros (CID13 Hs13) "Hcg Hpc Hb6". iEval (rewrite Hf6) in "Hb6".
      assert (Hpp01c : add_vec_int (mword_of_int (KF + 0x1a) : mword 64) 2 = mword_of_int (KF + 0x1c))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp01c) in "Hpc".
      (* +0x01c c.mv s4,a0 -- s4 := npa *)
      iApply (wp_cmv_s_sconf (mword_of_int (KF + 0x1c)) Rs4 Ra0 mf6 (trap_res b + K1)%nat false
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi01c").
      iIntros (CID14 Hs14) "Hcg Hpc". iEval (rgne) in "Hcg".
      set (N1 := <[Regidx Rs4 := regval_into_reg (add_vec zero_reg (mf6 !!! Regidx Ra0))]> mf6).
      assert (HN1s4 : N1 !!! Regidx Rs4 = npa)
        by (rewrite /N1 upd_eq HBa0; apply add_vec_zero_l).
      assert (HN1sp : N1 !!! Regidx csp_rs1 = pa_stk sp0 8)
        by (rewrite /N1 upd_ne; [exact HBsp | vm_compute; discriminate]).
      assert (HN1s0 : N1 !!! Regidx Rs0 = sp0)
        by (rewrite /N1 upd_ne; [exact HBs0 | vm_compute; discriminate]).
      assert (HN1s1 : N1 !!! Regidx Rs1 = s10)
        by (rewrite /N1 upd_ne; [exact HBs1 | vm_compute; discriminate]).
      assert (HN1s5 : N1 !!! Regidx Rs5 = pme)
        by (rewrite /N1 upd_ne; [exact HBs5 | vm_compute; discriminate]).
      assert (HN1thr : forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 ->
                r <> Rs0 -> r <> Rs1 -> r <> Rs4 -> r <> Rs5 -> N1 !!! Regidx r = m !!! Regidx r).
      { intros r Hr Ncsp N8 N9 N20 N21.
        rewrite /N1 upd_ne; [| regne]. apply HBthr; assumption. }
      assert (Hpp01e : add_vec_int (mword_of_int (KF + 0x1c) : mword 64) 2 = mword_of_int (KF + 0x1e))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp01e) in "Hpc".
      (* ---- open the parent's and the child's proc_priv, all five pieces
             at once, held through the whole rest of this block. ---- *)
      iDestruct (kfk_priv_open with "Hpv") as
        "(%HszbP & %HbelP & HPsz & HPpg & HPpt & HPtf & HPtfpg & HPwand)".
      iDestruct (kfk_priv_open_nocwd with "Hcpriv") as
        "(%HszbC & %HbelC & HCsz & HCpg & HCpt & HCtf & HCtfpg & HCwand)".
      (* +0x01e ld a2,72(s5) -- a2 := p->sz *)
      assert (Hszaddr_p : add_vec (N1 !!! Regidx Rs5) (sign_extend' 64 (mword_of_int 72 : mword 12))
                          = p_sz pme) by (rewrite HN1s5; reflexivity).
      iApply (wp_ld_s_sconf (mword_of_int (KF + 0x1e)) Ra2 Rs5 (mword_of_int 72 : mword 12)
                N1 (trap_res b + K1)%nat (pv_sz Vp) false (dqm := DfracOwn 1)
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi01e [HPsz]").
      { iEval (rewrite Hszaddr_p). iExact "HPsz". }
      iIntros (CID15 Hs15) "Hcg Hpc HPsz". iEval (rewrite Hszaddr_p) in "HPsz".
      set (N2 := <[Regidx Ra2 := regval_into_reg (pv_sz Vp)]> N1).
      assert (HN2a2 : N2 !!! Regidx Ra2 = pv_sz Vp) by (rewrite /N2 upd_eq; reflexivity).
      assert (HN2sp : N2 !!! Regidx csp_rs1 = pa_stk sp0 8)
        by (rewrite /N2 upd_ne; [exact HN1sp | vm_compute; discriminate]).
      assert (HN2s0 : N2 !!! Regidx Rs0 = sp0)
        by (rewrite /N2 upd_ne; [exact HN1s0 | vm_compute; discriminate]).
      assert (HN2s1 : N2 !!! Regidx Rs1 = s10)
        by (rewrite /N2 upd_ne; [exact HN1s1 | vm_compute; discriminate]).
      assert (HN2s4 : N2 !!! Regidx Rs4 = npa)
        by (rewrite /N2 upd_ne; [exact HN1s4 | vm_compute; discriminate]).
      assert (HN2s5 : N2 !!! Regidx Rs5 = pme)
        by (rewrite /N2 upd_ne; [exact HN1s5 | vm_compute; discriminate]).
      assert (HN2a0 : N2 !!! Regidx Ra0 = npa)
        by (rewrite /N2 upd_ne; [exact HBa0 | vm_compute; discriminate]).
      assert (HN2thr : forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 ->
                r <> Rs0 -> r <> Rs1 -> r <> Rs4 -> r <> Rs5 -> N2 !!! Regidx r = m !!! Regidx r).
      { intros r Hr Ncsp N8 N9 N20 N21.
        rewrite /N2 upd_ne; [| regne]. apply HN1thr; assumption. }
      assert (Hpp022 : add_vec_int (mword_of_int (KF + 0x1e) : mword 64) 4 = mword_of_int (KF + 0x22))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp022) in "Hpc".
      (* +0x022 c.ld a1,80(a0) -- a1 := np->pagetable *)
      assert (Hpgaddr_c : add_vec (N2 !!! Regidx Ra0) (sign_extend' 64 (mword_of_int 80 : mword 12))
                          = p_pagetable npa) by (rewrite HN2a0; reflexivity).
      iApply (wp_cld_s_sconf (mword_of_int (KF + 0x22)) Ra1 Ra0 (mword_of_int 80 : mword 12)
                N2 (trap_res b + K1)%nat (page_base (ud_root (pv_upt Vc))) false (dqm := DfracOwn 1)
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi022 [HCpg]").
      { iEval (rewrite Hpgaddr_c). iExact "HCpg". }
      iIntros (CID16 Hs16) "Hcg Hpc HCpg". iEval (rewrite Hpgaddr_c) in "HCpg".
      set (N3 := <[Regidx Ra1 := regval_into_reg (page_base (ud_root (pv_upt Vc)))]> N2).
      assert (HN3sp : N3 !!! Regidx csp_rs1 = pa_stk sp0 8)
        by (rewrite /N3 upd_ne; [exact HN2sp | vm_compute; discriminate]).
      assert (HN3s0 : N3 !!! Regidx Rs0 = sp0)
        by (rewrite /N3 upd_ne; [exact HN2s0 | vm_compute; discriminate]).
      assert (HN3s1 : N3 !!! Regidx Rs1 = s10)
        by (rewrite /N3 upd_ne; [exact HN2s1 | vm_compute; discriminate]).
      assert (HN3s4 : N3 !!! Regidx Rs4 = npa)
        by (rewrite /N3 upd_ne; [exact HN2s4 | vm_compute; discriminate]).
      assert (HN3s5 : N3 !!! Regidx Rs5 = pme)
        by (rewrite /N3 upd_ne; [exact HN2s5 | vm_compute; discriminate]).
      assert (HN3thr : forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 ->
                r <> Rs0 -> r <> Rs1 -> r <> Rs4 -> r <> Rs5 -> N3 !!! Regidx r = m !!! Regidx r).
      { intros r Hr Ncsp N8 N9 N20 N21.
        rewrite /N3 upd_ne; [| regne]. apply HN2thr; assumption. }
      assert (HN3a2 : N3 !!! Regidx Ra2 = pv_sz Vp)
        by (rewrite /N3 upd_ne; [exact HN2a2 | vm_compute; discriminate]).
      assert (Hpp024 : add_vec_int (mword_of_int (KF + 0x22) : mword 64) 2 = mword_of_int (KF + 0x24))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp024) in "Hpc".
      (* +0x024 ld a0,80(s5) -- a0 := p->pagetable *)
      assert (Hpgaddr_p : add_vec (N3 !!! Regidx Rs5) (sign_extend' 64 (mword_of_int 80 : mword 12))
                          = p_pagetable pme) by (rewrite HN3s5; reflexivity).
      iApply (wp_ld_s_sconf (mword_of_int (KF + 0x24)) Ra0 Rs5 (mword_of_int 80 : mword 12)
                N3 (trap_res b + K1)%nat (page_base (ud_root (pv_upt Vp))) false (dqm := DfracOwn 1)
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi024 [HPpg]").
      { iEval (rewrite Hpgaddr_p). iExact "HPpg". }
      iIntros (CID17 Hs17) "Hcg Hpc HPpg". iEval (rewrite Hpgaddr_p) in "HPpg".
      set (N4 := <[Regidx Ra0 := regval_into_reg (page_base (ud_root (pv_upt Vp)))]> N3).
      assert (HN4sp : N4 !!! Regidx csp_rs1 = pa_stk sp0 8)
        by (rewrite /N4 upd_ne; [exact HN3sp | vm_compute; discriminate]).
      assert (HN4s0 : N4 !!! Regidx Rs0 = sp0)
        by (rewrite /N4 upd_ne; [exact HN3s0 | vm_compute; discriminate]).
      assert (HN4s1 : N4 !!! Regidx Rs1 = s10)
        by (rewrite /N4 upd_ne; [exact HN3s1 | vm_compute; discriminate]).
      assert (HN4s4 : N4 !!! Regidx Rs4 = npa)
        by (rewrite /N4 upd_ne; [exact HN3s4 | vm_compute; discriminate]).
      assert (HN4s5 : N4 !!! Regidx Rs5 = pme)
        by (rewrite /N4 upd_ne; [exact HN3s5 | vm_compute; discriminate]).
      assert (HN4a1 : N4 !!! Regidx Ra1 = page_base (ud_root (pv_upt Vc))).
      { rewrite /N4 upd_ne; [| vm_compute; discriminate]. rewrite /N3 upd_eq. reflexivity. }
      assert (HN4thr : forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 ->
                r <> Rs0 -> r <> Rs1 -> r <> Rs4 -> r <> Rs5 -> N4 !!! Regidx r = m !!! Regidx r).
      { intros r Hr Ncsp N8 N9 N20 N21.
        rewrite /N4 upd_ne; [| regne]. apply HN3thr; assumption. }
      assert (HN4a2 : N4 !!! Regidx Ra2 = pv_sz Vp)
        by (rewrite /N4 upd_ne; [exact HN3a2 | vm_compute; discriminate]).
      assert (Hpp028 : add_vec_int (mword_of_int (KF + 0x24) : mword 64) 4 = mword_of_int (KF + 0x28))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp028) in "Hpc".
      (* =================================================================
         +0x028: jal ra, uvmcopy
         ================================================================= *)
      iApply (wp_jal_s_sconf (mword_of_int (KF + 0x28)) Rra (mword_of_int 2094918 : mword 21)
                N4 (trap_res b + K1)%nat false ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(vm_compute; reflexivity)
                with "Hcg Hpc Hi028").
      iIntros (CID18 Hs18) "Hcg Hpc".
      set (N5 := <[Regidx Rra := regval_into_reg
                    (add_vec_int (mword_of_int (KF + 0x28) : mword 64) 4)]> N4).
      assert (Hjuvc : add_vec (mword_of_int (KF + 0x28) : mword 64)
                       (sign_extend' 64 (mword_of_int 2094918 : mword 21)) = mword_of_int KernelSyms.uvmcopy)
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hjuvc) in "Hpc".
      assert (HN5sp : N5 !!! Regidx csp_rs1 = pa_stk sp0 8)
        by (rewrite /N5 upd_ne; [exact HN4sp | vm_compute; discriminate]).
      assert (HN5s0 : N5 !!! Regidx Rs0 = sp0)
        by (rewrite /N5 upd_ne; [exact HN4s0 | vm_compute; discriminate]).
      assert (HN5s1 : N5 !!! Regidx Rs1 = s10)
        by (rewrite /N5 upd_ne; [exact HN4s1 | vm_compute; discriminate]).
      assert (HN5s4 : N5 !!! Regidx Rs4 = npa)
        by (rewrite /N5 upd_ne; [exact HN4s4 | vm_compute; discriminate]).
      assert (HN5s5 : N5 !!! Regidx Rs5 = pme)
        by (rewrite /N5 upd_ne; [exact HN4s5 | vm_compute; discriminate]).
      assert (HN5a0 : N5 !!! Regidx Ra0 = page_base (ud_root (pv_upt Vp))).
      { rewrite /N5 upd_ne; [| vm_compute; discriminate]. rewrite /N4 upd_eq. reflexivity. }
      assert (HN5a1 : N5 !!! Regidx Ra1 = page_base (ud_root (pv_upt Vc))).
      { rewrite /N5 upd_ne; [| vm_compute; discriminate]. exact HN4a1. }
      assert (HN5a2 : N5 !!! Regidx Ra2 = pv_sz Vp)
        by (rewrite /N5 upd_ne; [exact HN4a2 | vm_compute; discriminate]).
      assert (HN5ra : N5 !!! Regidx Rra = add_vec_int (mword_of_int (KF + 0x28) : mword 64) 4)
        by (rewrite /N5 upd_eq; reflexivity).
      assert (HN5thr : forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 ->
                r <> Rs0 -> r <> Rs1 -> r <> Rs4 -> r <> Rs5 -> N5 !!! Regidx r = m !!! Regidx r).
      { intros r Hr Ncsp N8 N9 N20 N21.
        assert (N1' : r <> mword_of_int 1) by
          (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
        rewrite /N5 upd_ne; [| congruence]. apply HN4thr; assumption. }
      (* [tp_pin] recipe: uvmcopy demands the raw entry map's tp slot. *)
      set (N5p := tp_pin N5).
      assert (Hpinid5 : tp_pin N5p = tp_pin N5) by (rewrite /N5p; apply (tp_pin_id (tp_pin N5) (rget_tp N5))).
      assert (Hn5psp : N5p !!! Regidx csp_rs1 = N5 !!! Regidx csp_rs1)
        by (rewrite /N5p; exact (tp_pin_sp N5)).
      assert (Hgpreq5 : sie_cap_gpr N5 (trap_res b + K1)%nat false pme = sie_cap_gpr N5p (trap_res b + K1)%nat false pme)
        by (unfold sie_cap_gpr, sie_cap; rewrite Hn5psp Hpinid5; reflexivity).
      iEval (rewrite Hgpreq5) in "Hcg".
      assert (HN5pne : forall r : mword 5, r <> Rtp -> N5p !!! Regidx r = N5 !!! Regidx r).
      { intros r Hr. rewrite /N5p. apply (rget_ne N5 r).
        intro He. injection He as He2. congruence. }
      assert (HN5ptp : N5p !!! Regidx Rtp = cid_word) by (rewrite /N5p upd_eq; reflexivity).
      assert (HN5pa0 : N5p !!! Regidx Ra0 = page_base (ud_root (pv_upt Vp)))
        by (rewrite (HN5pne Ra0 ltac:(reg_neq)); exact HN5a0).
      assert (HN5pa1 : N5p !!! Regidx Ra1 = page_base (ud_root (pv_upt Vc)))
        by (rewrite (HN5pne Ra1 ltac:(reg_neq)); exact HN5a1).
      assert (HN5pa2 : N5p !!! Regidx Ra2 = pv_sz Vp)
        by (rewrite (HN5pne Ra2 ltac:(reg_neq)); exact HN5a2).
      assert (HN5psp : N5p !!! Regidx csp_rs1 = pa_stk sp0 8)
        by (rewrite Hn5psp; exact HN5sp).
      assert (HN5ps0 : N5p !!! Regidx Rs0 = sp0)
        by (rewrite (HN5pne Rs0 ltac:(reg_neq)); exact HN5s0).
      assert (HN5ps1 : N5p !!! Regidx Rs1 = s10)
        by (rewrite (HN5pne Rs1 ltac:(reg_neq)); exact HN5s1).
      assert (HN5ps4 : N5p !!! Regidx Rs4 = npa)
        by (rewrite (HN5pne Rs4 ltac:(reg_neq)); exact HN5s4).
      assert (HN5ps5 : N5p !!! Regidx Rs5 = pme)
        by (rewrite (HN5pne Rs5 ltac:(reg_neq)); exact HN5s5).
      assert (HN5pra : N5p !!! Regidx Rra = add_vec_int (mword_of_int (KF + 0x28) : mword 64) 4)
        by (rewrite (HN5pne Rra ltac:(reg_neq)); exact HN5ra).
      assert (HthrN5p : forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 ->
                r <> Rs0 -> r <> Rs1 -> r <> Rs4 -> r <> Rs5 -> N5p !!! Regidx r = m !!! Regidx r).
      { intros r Hr Ncsp N8 N9 N20 N21.
        assert (N4' : r <> Rtp) by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
        rewrite (HN5pne r N4'). apply HN5thr; assumption. }
      (* the freshness premise: the child's map is EMPTY (allocproc's own
         invariant), so uvmcopy's "child map free over the run" is
         [lookup_empty]. *)
      assert (HCempty : ud_um (pv_upt Vc) = ∅) by (rewrite HVcupt; reflexivity).
      iDestruct (cpu_own_transport CID11 CID18 (S lvl) eb pme C false ltac:(wp_next_chain) with "Hcpu") as "Hcpu".
      iApply fupd_wp.
      iMod (kalloc_env_seal with "Henv'") as "Henv'".
      iModIntro.
      iDestruct "Henv'" as "#Henv'".
      iApply (Uvmcopy.wp_uvmcopy_sconf γa N5p (pv_upt Vp) (pv_upt Vc) (trap_res b + K1)%nat eb pme C (S lvl) false
                ({[lock_rank "proc"]} ∪ lks)
                ltac:(lia) ltac:(lia) HN5ptp HN5pa0 HN5pa1 HszbP
                ltac:(intros i _; rewrite HCempty; apply lookup_empty)
                with "Hcg Hcpu Htext Hpc HPpt HCpt Henv'").
      all: try lkbelow.
      iIntros (CID19 Hs19 mf9) "Hcg Hcpu Hpc %HcsD HPpt Hpost9".
      assert (Hpc2c : ret_pc (N5p !!! Regidx Rra) = mword_of_int (KF + 0x2c))
        by (rewrite HN5pra; apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpc2c) in "Hpc".
      assert (HDsp : mf9 !!! Regidx csp_rs1 = pa_stk sp0 8)
        by (rewrite (callee_saved_lookup HcsD csp_rs1 ltac:(vm_compute; reflexivity)); exact HN5psp).
      assert (HDs0 : mf9 !!! Regidx Rs0 = sp0)
        by (rewrite (callee_saved_lookup HcsD (mword_of_int 8) ltac:(vm_compute; reflexivity)); exact HN5ps0).
      assert (HDs1 : mf9 !!! Regidx Rs1 = s10)
        by (rewrite (callee_saved_lookup HcsD (mword_of_int 9) ltac:(vm_compute; reflexivity)); exact HN5ps1).
      assert (HDs4 : mf9 !!! Regidx Rs4 = npa)
        by (rewrite (callee_saved_lookup HcsD (mword_of_int 20) ltac:(vm_compute; reflexivity)); exact HN5ps4).
      assert (HDs5 : mf9 !!! Regidx Rs5 = pme)
        by (rewrite (callee_saved_lookup HcsD (mword_of_int 21) ltac:(vm_compute; reflexivity)); exact HN5ps5).
      assert (HDthr : forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 ->
                r <> Rs0 -> r <> Rs1 -> r <> Rs4 -> r <> Rs5 -> mf9 !!! Regidx r = m !!! Regidx r).
      { intros r Hr Ncsp N8 N9 N20 N21.
        rewrite (callee_saved_lookup HcsD r Hr). apply HthrN5p; assumption. }
      assert (Hrget_mf9_a0 : rget mf9 Ra0 = mf9 !!! Regidx Ra0).
      { apply rget_ne. intro He. injection He as He2. vm_compute in He2. discriminate. }
      (* ---- uvmcopy's own 2-way disjunction: failed, or succeeded ---- *)
      iDestruct "Hpost9" as "[[%HDa0 HCpt] | Hsucc]".
      + (* =============================================================
           uvmcopy FAILED -- +0x02c taken, straight to Hcont7c.
           ============================================================= *)
        iApply (wp_blt_x0_taken_s_sconf (mword_of_int (KF + 0x2c)) (mword_of_int 80 : mword 13)
                  Ra0 mf9 (trap_res b + K1)%nat false
                  ltac:(vm_compute; discriminate)
                  ltac:(rewrite Hrget_mf9_a0 HDa0; vm_compute; reflexivity)
                  ltac:(vm_compute; reflexivity)
                  with "Hcg Hpc Hi02c").
        iNext. iIntros (CID20 Hs20) "Hcg Hpc".
        (* [proc_held]/[arm_pay] name the AMBIENT hart explicitly ([cpu_id]),
           unlike [sie_cap_gpr]/[pc_is]/etc which are re-quantified fresh by
           every leaf: bring them from CID11 (where allocproc's found arm
           left them) up to the current hart. *)
        iDestruct (cpu_own_transport CID19 CID20 (S lvl) eb pme C false ltac:(wp_next_chain) with "Hcpu") as "Hcpu".
        assert (Hchain7c : false = false \/ pme = zero_reg -> (CID20 : CPU) = (CID11 : CPU))
          by wp_next_chain.
        assert (HCIDeq7c : (CID11 : CPU) = (CID20 : CPU))
          by (symmetry; exact (Hchain7c (or_introl eq_refl))).
        iEval (rewrite HCIDeq7c) in "Hheld".
        iEval (rewrite HCIDeq7c) in "Harmpay".
        (* close both proc_privs back up UNCHANGED *)
        iDestruct ("HPwand" $! (pv_upt Vp) (pv_sz Vp) (pv_tf Vp)
                     with "[%] [%] [%] [%] HPsz HPpg HPpt HPtf HPtfpg") as "HPpriv".
        { reflexivity. } { reflexivity. } { exact HszbP. } { exact HbelP. }
        iDestruct ("HCwand" $! (pv_upt Vc) (pv_sz Vc) (pv_tf Vc)
                     with "[%] [%] [%] [%] HCsz HCpg HCpt HCtf HCtfpg") as "HCpriv".
        { reflexivity. } { reflexivity. } { exact HszbC. } { exact HbelC. }
        iEval (rewrite (kfk_priv_close_id Vp)) in "HPpriv".
        iEval (rewrite (kfk_priv_close_id Vc)) in "HCpriv".
        (* [rget] is indexed by the AMBIENT [CpuId], so a fact stated with
           [rget] here does not rewrite into a hypothesis the store leaf
           produced at an earlier hart -- the two print identically.
           durable-notes' rule: normalise with [rgne] and state the fact in
           the [!!!] form. *)
        assert (Hslot6 : mf6 !!! Regidx Rs4 = m !!! Regidx Rs4)
          by (apply HBthr; vm_compute; first [reflexivity | discriminate]).
        iAssert (∃ w4 w5 : mword 64,
                   kfk_frame_at sp0 ra0 s00 s10 s50 w4 w5 (m !!! Regidx Rs4))%I
          with "[Hb1 Hb2 Hb3 Hb4 Hb5 Hb6 Hb7 Hb8]" as "Hframe_alloc".
        { iExists u4, u5. rewrite /kfk_frame_at.
          iEval (rgne) in "Hb6". iEval (rewrite Hslot6) in "Hb6".
          iFrame "Hb1 Hb2 Hb3 Hb4 Hb5 Hb6 Hb7".
          iExists u8; iExact "Hb8". }
        iSpecialize ("Hcont7c" $! CID11 with "[%]"); [wp_next_chain|].
        iSpecialize ("Hcont7c" $! CID20 with "[%]"); [wp_next_chain|].
        iSpecialize ("Hcont7c" $! mf9 npa j γl2 pid_c ch Vc
                  with "[%] [%] [%] [%] [%] [%]").
        { exact HDsp. } { exact HDs4. } { exact HDs5. } { exact HDa0. }
        { intros r Hr Ncsp N8 N9 N20 N21. apply HDthr; assumption. }
        { split_and!; [reflexivity | exact HjN | exact Hgamma | exact HVcof | exact HVccwd]. }
        iSpecialize ("Hcont7c" with "Hcg").
        iSpecialize ("Hcont7c" with "Htext").
        iSpecialize ("Hcont7c" with "Hpc").
        iSpecialize ("Hcont7c" with "Hframe_alloc").
        iSpecialize ("Hcont7c" with "HPpriv").
        iSpecialize ("Hcont7c" with "HCpriv").
        iSpecialize ("Hcont7c" with "Hheld").
        iSpecialize ("Hcont7c" with "Hhart").
        iSpecialize ("Hcont7c" with "Hfdsp").
        iSpecialize ("Hcont7c" with "Hirsp").
        iSpecialize ("Hcont7c" with "[Hctx]").
        { iExists (forkret_pc :: add_vec ks (mword_of_int 4096) :: rest).
          iSplitR; [iPureIntro; rewrite -Hrestlen; reflexivity | iExact "Hctx"]. }
        iSpecialize ("Hcont7c" with "Harmpay").
        iSpecialize ("Hcont7c" with "Hcpu").
        iSpecialize ("Hcont7c" with "Henv'").
        iApply ("Hcont7c" with "HR").
      + (* =============================================================
           uvmcopy SUCCEEDED -- +0x02c falls through.
           ============================================================= *)
        iDestruct "Hsucc" as (P') "(%HDa0 & %Hext & %Hout & %Hin & HCpt)".
        iApply (wp_blt_x0_fall_s_sconf (mword_of_int (KF + 0x2c)) (mword_of_int 80 : mword 13)
                  Ra0 mf9 (trap_res b + K1)%nat false
                  ltac:(vm_compute; discriminate)
                  ltac:(rewrite Hrget_mf9_a0 HDa0; vm_compute; reflexivity)
                  with "Hcg Hpc Hi02c").
        iIntros (CID20 Hs20) "Hcg Hpc".
        assert (Hpp030 : add_vec_int (mword_of_int (KF + 0x2c) : mword 64) 4 = mword_of_int (KF + 0x30))
          by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hpp030) in "Hpc".
        assert (Hf4 : add_vec (mf9 !!! Regidx csp_rs1)
                        (zero_extend' 64 (concat_vec (mword_of_int 4 : mword 6) ('b"000")))
                      = pa_stk sp0 4) by (rewrite HDsp; apply kfk_frm4).
        iEval (rewrite -Hf4) in "Hb4".
        (* +0x030 c.sdsp s2,32(sp) -- no register write *)
        iApply (wp_csdsp_s_sconf (mword_of_int (KF + 0x30)) (mword_of_int 4 : mword 6) Rs2
                  mf9 (trap_res b + K1)%nat u4 false with "Hcg Hpc Hi030 Hb4").
        iIntros (CID21 Hs21) "Hcg Hpc Hb4". iEval (rewrite Hf4) in "Hb4".
        assert (Hpp032 : add_vec_int (mword_of_int (KF + 0x30) : mword 64) 2 = mword_of_int (KF + 0x32))
          by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hpp032) in "Hpc".
        assert (Hf5 : add_vec (mf9 !!! Regidx csp_rs1)
                        (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000")))
                      = pa_stk sp0 5) by (rewrite HDsp; apply kfk_frm5).
        iEval (rewrite -Hf5) in "Hb5".
        (* +0x032 c.sdsp s3,24(sp) -- no register write *)
        iApply (wp_csdsp_s_sconf (mword_of_int (KF + 0x32)) (mword_of_int 3 : mword 6) Rs3
                  mf9 (trap_res b + K1)%nat u5 false with "Hcg Hpc Hi032 Hb5").
        iIntros (CID22 Hs22) "Hcg Hpc Hb5". iEval (rewrite Hf5) in "Hb5".
        assert (Hpp034 : add_vec_int (mword_of_int (KF + 0x32) : mword 64) 2 = mword_of_int (KF + 0x34))
          by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hpp034) in "Hpc".
        (* +0x034 ld a5,72(s5) -- a5 := p->sz (again) *)
        assert (Hszaddr_p2 : add_vec (mf9 !!! Regidx Rs5) (sign_extend' 64 (mword_of_int 72 : mword 12))
                            = p_sz pme) by (rewrite HDs5; reflexivity).
        iApply (wp_ld_s_sconf (mword_of_int (KF + 0x34)) Ra5 Rs5 (mword_of_int 72 : mword 12)
                  mf9 (trap_res b + K1)%nat (pv_sz Vp) false (dqm := DfracOwn 1)
                  ltac:(vm_compute; discriminate) ltac:(rdok)
                  with "Hcg Hpc Hi034 [HPsz]").
        { iEval (rewrite Hszaddr_p2). iExact "HPsz". }
        iIntros (CID23 Hs23) "Hcg Hpc HPsz". iEval (rewrite Hszaddr_p2) in "HPsz".
        set (N6 := <[Regidx Ra5 := regval_into_reg (pv_sz Vp)]> mf9).
        assert (HN6sp : N6 !!! Regidx csp_rs1 = pa_stk sp0 8)
          by (rewrite /N6 upd_ne; [exact HDsp | vm_compute; discriminate]).
        assert (HN6s4 : N6 !!! Regidx Rs4 = npa)
          by (rewrite /N6 upd_ne; [exact HDs4 | vm_compute; discriminate]).
        assert (HN6s5 : N6 !!! Regidx Rs5 = pme)
          by (rewrite /N6 upd_ne; [exact HDs5 | vm_compute; discriminate]).
        assert (HN6a5 : N6 !!! Regidx Ra5 = pv_sz Vp) by (rewrite /N6 upd_eq; reflexivity).
        assert (Hpp038 : add_vec_int (mword_of_int (KF + 0x34) : mword 64) 4 = mword_of_int (KF + 0x38))
          by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hpp038) in "Hpc".
        (* +0x038 sd a5,72(s4) -- np->sz := a5 *)
        assert (Hszaddr_c : add_vec (N6 !!! Regidx Rs4) (sign_extend' 64 (mword_of_int 72 : mword 12))
                            = p_sz npa) by (rewrite HN6s4; reflexivity).
        iApply (wp_sd_s_sconf (mword_of_int (KF + 0x38)) Ra5 Rs4 (mword_of_int 72 : mword 12)
                  N6 (trap_res b + K1)%nat (pv_sz Vc) false
                  with "Hcg Hpc Hi038 [HCsz]").
        { iEval (rewrite Hszaddr_c). iExact "HCsz". }
        iIntros (CID24 Hs24) "Hcg Hpc HCsz". iEval (rewrite Hszaddr_c) in "HCsz".
        iEval (rgne) in "HCsz". iEval (rewrite HN6a5) in "HCsz".
        assert (Hpp03c : add_vec_int (mword_of_int (KF + 0x38) : mword 64) 4 = mword_of_int (KF + 0x3c))
          by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hpp03c) in "Hpc".
        (* +0x03c ld a3,88(s5) -- a3 := p->trapframe *)
        assert (Htfaddr_p : add_vec (N6 !!! Regidx Rs5) (sign_extend' 64 (mword_of_int 88 : mword 12))
                            = p_trapframe pme) by (rewrite HN6s5; reflexivity).
        iApply (wp_ld_s_sconf (mword_of_int (KF + 0x3c)) Ra3 Rs5 (mword_of_int 88 : mword 12)
                  N6 (trap_res b + K1)%nat (page_base (ud_tfp (pv_upt Vp))) false (dqm := DfracOwn 1)
                  ltac:(vm_compute; discriminate) ltac:(rdok)
                  with "Hcg Hpc Hi03c [HPtf]").
        { iEval (rewrite Htfaddr_p). iExact "HPtf". }
        iIntros (CID25 Hs25) "Hcg Hpc HPtf". iEval (rewrite Htfaddr_p) in "HPtf".
        set (N7 := <[Regidx Ra3 := regval_into_reg (page_base (ud_tfp (pv_upt Vp)))]> N6).
        assert (HN7sp : N7 !!! Regidx csp_rs1 = pa_stk sp0 8)
          by (rewrite /N7 upd_ne; [exact HN6sp | vm_compute; discriminate]).
        assert (HN7s4 : N7 !!! Regidx Rs4 = npa)
          by (rewrite /N7 upd_ne; [exact HN6s4 | vm_compute; discriminate]).
        assert (HN7s5 : N7 !!! Regidx Rs5 = pme)
          by (rewrite /N7 upd_ne; [exact HN6s5 | vm_compute; discriminate]).
        assert (HN7a3 : N7 !!! Regidx Ra3 = page_base (ud_tfp (pv_upt Vp)))
          by (rewrite /N7 upd_eq; reflexivity).
        assert (Hpp040 : add_vec_int (mword_of_int (KF + 0x3c) : mword 64) 4 = mword_of_int (KF + 0x40))
          by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hpp040) in "Hpc".
        (* +0x040 c.mv a5,a3 -- a5 := a3 (the SOURCE cursor) *)
        iApply (wp_cmv_s_sconf (mword_of_int (KF + 0x40)) Ra5 Ra3 N7 (trap_res b + K1)%nat false
                  ltac:(vm_compute; discriminate) ltac:(rdok)
                  with "Hcg Hpc Hi040").
        iIntros (CID26 Hs26) "Hcg Hpc". iEval (rgne) in "Hcg".
        set (N8 := <[Regidx Ra5 := regval_into_reg (add_vec zero_reg (N7 !!! Regidx Ra3))]> N7).
        assert (HN8a5 : N8 !!! Regidx Ra5 = page_base (ud_tfp (pv_upt Vp))).
        { rewrite /N8 upd_eq HN7a3. apply add_vec_zero_l. }
        assert (HN8sp : N8 !!! Regidx csp_rs1 = pa_stk sp0 8)
          by (rewrite /N8 upd_ne; [exact HN7sp | vm_compute; discriminate]).
        assert (HN8s4 : N8 !!! Regidx Rs4 = npa)
          by (rewrite /N8 upd_ne; [exact HN7s4 | vm_compute; discriminate]).
        assert (HN8s5 : N8 !!! Regidx Rs5 = pme)
          by (rewrite /N8 upd_ne; [exact HN7s5 | vm_compute; discriminate]).
        assert (HN8a3 : N8 !!! Regidx Ra3 = page_base (ud_tfp (pv_upt Vp)))
          by (rewrite /N8 upd_ne; [exact HN7a3 | vm_compute; discriminate]).
        assert (Hpp042 : add_vec_int (mword_of_int (KF + 0x40) : mword 64) 2 = mword_of_int (KF + 0x42))
          by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hpp042) in "Hpc".
        (* +0x042 ld a4,88(s4) -- a4 := np->trapframe (the DEST cursor) *)
        assert (Htfaddr_c : add_vec (N8 !!! Regidx Rs4) (sign_extend' 64 (mword_of_int 88 : mword 12))
                            = p_trapframe npa) by (rewrite HN8s4; reflexivity).
        iApply (wp_ld_s_sconf (mword_of_int (KF + 0x42)) Ra4 Rs4 (mword_of_int 88 : mword 12)
                  N8 (trap_res b + K1)%nat (page_base (ud_tfp (pv_upt Vc))) false (dqm := DfracOwn 1)
                  ltac:(vm_compute; discriminate) ltac:(rdok)
                  with "Hcg Hpc Hi042 [HCtf]").
        { iEval (rewrite Htfaddr_c). iExact "HCtf". }
        iIntros (CID27 Hs27) "Hcg Hpc HCtf". iEval (rewrite Htfaddr_c) in "HCtf".
        set (N9 := <[Regidx Ra4 := regval_into_reg (page_base (ud_tfp (pv_upt Vc)))]> N8).
        assert (HN9sp : N9 !!! Regidx csp_rs1 = pa_stk sp0 8)
          by (rewrite /N9 upd_ne; [exact HN8sp | vm_compute; discriminate]).
        assert (HN9s4 : N9 !!! Regidx Rs4 = npa)
          by (rewrite /N9 upd_ne; [exact HN8s4 | vm_compute; discriminate]).
        assert (HN9s5 : N9 !!! Regidx Rs5 = pme)
          by (rewrite /N9 upd_ne; [exact HN8s5 | vm_compute; discriminate]).
        assert (HN9a3 : N9 !!! Regidx Ra3 = page_base (ud_tfp (pv_upt Vp)))
          by (rewrite /N9 upd_ne; [exact HN8a3 | vm_compute; discriminate]).
        assert (HN9a4 : N9 !!! Regidx Ra4 = page_base (ud_tfp (pv_upt Vc)))
          by (rewrite /N9 upd_eq; reflexivity).
        assert (HN9a5 : N9 !!! Regidx Ra5 = page_base (ud_tfp (pv_upt Vp))).
        { rewrite /N9 upd_ne; [exact HN8a5 | vm_compute; discriminate]. }
        assert (Hpp046 : add_vec_int (mword_of_int (KF + 0x42) : mword 64) 4 = mword_of_int (KF + 0x46))
          by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hpp046) in "Hpc".
        (* +0x046 addi a3,a3,288 -- a3 := the loop's END pointer *)
        iApply (wp_addi4_s_sconf (mword_of_int (KF + 0x46)) Ra3 Ra3 (mword_of_int 288 : mword 12)
                  N9 (trap_res b + K1)%nat false ltac:(vm_compute; discriminate) ltac:(rdok)
                  with "Hcg Hpc Hi046").
        iIntros (CID28 Hs28) "Hcg Hpc".
        iDestruct (cpu_own_transport CID19 CID28 (S lvl) eb pme C false ltac:(wp_next_chain) with "Hcpu") as "Hcpu".
        assert (Hchain4a : false = false \/ pme = zero_reg -> (CID28 : CPU) = (CID11 : CPU))
          by wp_next_chain.
        assert (HCIDeq4a : (CID11 : CPU) = (CID28 : CPU))
          by (symmetry; exact (Hchain4a (or_introl eq_refl))).
        iEval (rewrite HCIDeq4a) in "Hheld".
        iEval (rewrite HCIDeq4a) in "Harmpay".
        set (N10 := <[Regidx Ra3 := regval_into_reg
                       (add_vec (N9 !!! Regidx Ra3) (sign_extend' 64 (mword_of_int 288 : mword 12)))]> N9).
        assert (HN10sp : N10 !!! Regidx csp_rs1 = pa_stk sp0 8)
          by (rewrite /N10 upd_ne; [exact HN9sp | vm_compute; discriminate]).
        assert (HN10s4 : N10 !!! Regidx Rs4 = npa)
          by (rewrite /N10 upd_ne; [exact HN9s4 | vm_compute; discriminate]).
        assert (HN10s5 : N10 !!! Regidx Rs5 = pme)
          by (rewrite /N10 upd_ne; [exact HN9s5 | vm_compute; discriminate]).
        assert (HN10a4 : N10 !!! Regidx Ra4 = page_base (ud_tfp (pv_upt Vc)))
          by (rewrite /N10 upd_ne; [exact HN9a4 | vm_compute; discriminate]).
        assert (HN10a5 : N10 !!! Regidx Ra5 = page_base (ud_tfp (pv_upt Vp)))
          by (rewrite /N10 upd_ne; [exact HN9a5 | vm_compute; discriminate]).
        assert (Hstep36 : add_vec (page_base (ud_tfp (pv_upt Vp)))
                            (sign_extend' 64 (mword_of_int 288 : mword 12))
                          = a_tf_word (ud_tfp (pv_upt Vp)) 36).
        { assert (Hs288 : (sign_extend' 64 (mword_of_int 288 : mword 12) : mword 64) = mword_of_int 288)
            by (apply bv_eq; vm_compute; reflexivity).
          rewrite Hs288. rewrite /a_tf_word /pa_add.
          change (add_vec (page_base (ud_tfp (pv_upt Vp))) (mword_of_int 288))
            with (add_vec_int (page_base (ud_tfp (pv_upt Vp))) 288).
          first [ reflexivity | f_equal; lia ]. }
        assert (HN10a3 : N10 !!! Regidx Ra3 = a_tf_word (ud_tfp (pv_upt Vp)) 36).
        { rewrite /N10 upd_eq HN9a3. exact Hstep36. }
        assert (HN10thr : forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 ->
                  r <> Rs0 -> r <> Rs1 -> r <> Rs4 -> r <> Rs5 -> N10 !!! Regidx r = m !!! Regidx r).
        { intros r Hr Ncsp N8' N9' N20 N21.
          assert (Na3 : r <> mword_of_int 13) by
            (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
          assert (Na4 : r <> mword_of_int 14) by
            (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
          assert (Na5 : r <> mword_of_int 15) by
            (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
          rewrite /N10 upd_ne; [| congruence].
          rewrite /N9 upd_ne; [| congruence].
          rewrite /N8 upd_ne; [| congruence].
          rewrite /N7 upd_ne; [| congruence].
          rewrite /N6 upd_ne; [| congruence]. apply HDthr; assumption. }
        assert (HN10a0 : a_tf_word (ud_tfp (pv_upt Vp)) 0 = page_base (ud_tfp (pv_upt Vp)))
          by (rewrite /a_tf_word pa_add_0; reflexivity).
        assert (HN10a4' : a_tf_word (ud_tfp (pv_upt Vc)) 0 = page_base (ud_tfp (pv_upt Vc)))
          by (rewrite /a_tf_word pa_add_0; reflexivity).
        (* ---- close both proc_privs, the parent unchanged and the child
               with its size/table advanced to uvmcopy's result. ---- *)
        pose proof (proj1 Hext) as Hroot2.
        assert (Htf2 : ud_tfp P' = ud_tfp (pv_upt Vc))
          by exact (proj1 (proj2 Hext)).
        rewrite HN5pa2 in Hout Hin.
        assert (Hin' : forall i : nat, (i < uvm_np (pv_sz Vp))%nat ->
                  match ud_um (pv_upt Vp) !! vpn_at (svpn_of (mword_of_int 0 : mword 64)) i with
                  | None => ud_um P' !! vpn_at (svpn_of (mword_of_int 0 : mword 64)) i
                            = ud_um (pv_upt Vc) !! vpn_at (svpn_of (mword_of_int 0 : mword 64)) i
                  | Some _ => exists w' : mword 64,
                      ud_um P' !! vpn_at (svpn_of (mword_of_int 0 : mword 64)) i = Some w'
                  end).
        { intros i Hi. specialize (Hin i Hi).
          destruct (ud_um (pv_upt Vp) !! vpn_at (svpn_of (mword_of_int 0 : mword 64)) i)
            as [w0 |] eqn:Heqw0.
          - destruct Hin as (r & w' & a & d & Hpv & Heqw' & Hpte). exists w'. exact Heqw'.
          - exact Hin. }
        assert (HbelC' : um_below (pv_sz Vp) (ud_um P')).
        { apply (kfk_um_below_child (pv_sz Vp) (svpn_of (mword_of_int 0 : mword 64))
                   (pv_upt Vp) (pv_upt Vc) P' HCempty HbelP Hout Hin'). }
        iDestruct ("HPwand" $! (pv_upt Vp) (pv_sz Vp) (pv_tf Vp)
                     with "[%] [%] [%] [%] HPsz HPpg HPpt HPtf HPtfpg") as "HPpriv".
        { reflexivity. } { reflexivity. } { exact HszbP. } { exact HbelP. }
        iDestruct ("HCwand" $! P' (pv_sz Vp) (pv_tf Vc)
                     with "[%] [%] [%] [%] HCsz HCpg HCpt HCtf HCtfpg") as "HCpriv".
        { exact Hroot2. } { exact Htf2. } { exact HszbP. } { exact HbelC'. }
        iEval (rewrite (kfk_priv_close_id Vp)) in "HPpriv".
        (* same [rget]/[!!!] normalisation as the failure arm above *)
        assert (Hslot6' : mf6 !!! Regidx Rs4 = m !!! Regidx Rs4)
          by (apply HBthr; vm_compute; first [reflexivity | discriminate]).
        assert (Hslot4' : mf9 !!! Regidx Rs2 = m !!! Regidx Rs2)
          by (apply HDthr; vm_compute; first [reflexivity | discriminate]).
        assert (Hslot5' : mf9 !!! Regidx Rs3 = m !!! Regidx Rs3)
          by (apply HDthr; vm_compute; first [reflexivity | discriminate]).
        iAssert (kfk_frame_at sp0 ra0 s00 s10 s50
                   (m !!! Regidx Rs2) (m !!! Regidx Rs3) (m !!! Regidx Rs4))
          with "[Hb1 Hb2 Hb3 Hb4 Hb5 Hb6 Hb7 Hb8]" as "Hframe_alloc".
        { rewrite /kfk_frame_at.
          iEval (rgne) in "Hb4". iEval (rewrite Hslot4') in "Hb4".
          iEval (rgne) in "Hb5". iEval (rewrite Hslot5') in "Hb5".
          iEval (rgne) in "Hb6". iEval (rewrite Hslot6') in "Hb6".
          iFrame "Hb1 Hb2 Hb3 Hb4 Hb5 Hb6 Hb7".
          iExists u8; iExact "Hb8". }
        iSpecialize ("Hcont4a" $! CID11 with "[%]"); [wp_next_chain|].
        iSpecialize ("Hcont4a" $! CID28 with "[%]"); [wp_next_chain|].
        iApply ("Hcont4a" $! N10 npa j γl2 pid_c ch
                  (upd_pt (upd_sz Vc (pv_sz Vp)) P' (pv_tf Vc))
                  (ud_tfp (pv_upt Vp)) (ud_tfp (pv_upt Vc))
                  with "[%] [%] [%] [%] [%] [%] [%] [%] [%] Hcg Htext Hpc Hframe_alloc HPpriv HCpriv
                        Hheld Hhart Hfdsp Hirsp [Hks Hctx] Harmpay Hcpu [Henv'] Hwlock Hftbl Hitbl Hitinv HR").
        * exact HN10sp.
        * exact HN10s4.
        * exact HN10s5.
        * rewrite HN10a5. exact (eq_sym HN10a0).
        * rewrite HN10a4. exact (eq_sym HN10a4').
        * exact HN10a3.
        * split; [reflexivity | cbn [upd_pt pv_upt]; exact Htf2].
        * intros r Hr Ncsp N8' N9' N20 N21. apply HN10thr; assumption.
        * split_and!; [reflexivity | exact HjN | exact Hgamma
                      | cbn [upd_pt upd_sz pv_ofile]; exact HVcof
                      | cbn [upd_pt upd_sz pv_cwd]; exact HVccwd].
        * iExists ks, rest. iSplitR; [iPureIntro; exact Hrestlen|].
          iFrame "Hks Hctx".
        * iExact "Henv'".
    - (* ---- arm 3: a failure tail ran, budget resealed ---- *)
      iDestruct "Hp3" as "(%Hrv & %Hwit & Hcg & Hcpu & Henv')".
      assert (HBa0 : mf6 !!! Regidx Ra0 = (zero_reg : mword 64)) by exact Hrv.
      iApply (wp_beqz_x0_taken_s_sconf (mword_of_int (KF + 0x16)) (mword_of_int 244 : mword 13)
                Ra0 mf6 K1 b
                ltac:(vm_compute; discriminate)
                ltac:(rewrite Hrget_mf6_a0 HBa0; vm_compute; reflexivity)
                ltac:(vm_compute; reflexivity)
                with "Hcg Hpc Hi016").
      iNext. iIntros (CID12 Hs12) "Hcg Hpc".
      (* [cpu_own] is the one bundle no leaf re-anchors: it came out of
         [allocproc_post] at CID11 and the continuation is at CID12, and the
         two print IDENTICALLY.  durable-notes' rule. *)
      iDestruct (cpu_own_transport CID11 CID12 lvl eb pme C b
                   ltac:(wp_next_chain) with "Hcpu") as "Hcpu".
      iAssert (kfk_frame sp0 ra0 s00 s10 s50) with "[Hb1 Hb2 Hb3 Hb4 Hb5 Hb6 Hb7 Hb8]" as "Hframe_alloc".
      { rewrite /kfk_frame. iFrame "Hb1 Hb2 Hb3 Hb7".
        iSplitL "Hb4"; [iExists u4; iExact "Hb4"|].
        iSplitL "Hb5"; [iExists u5; iExact "Hb5"|].
        iSplitL "Hb6"; [iExists u6; iExact "Hb6"|].
        iExists u8; iExact "Hb8". }
      iSpecialize ("Hcont10a" $! CID12 with "[%]"); [wp_next_chain|].
      iApply ("Hcont10a" $! mf6 with "[%] [%] Hcg Hcpu Htext Hpc Hframe_alloc Hpv [Henv'] HR").
      + exact HBsp.
      + intros r Hr Ncsp N8 N9 N21. apply HBthr; assumption.
      + destruct Hwit as (n & Hn1 & Hn2). iRight. iExists n. iSplitR; [iPureIntro; split; assumption|]. iExact "Henv'".
  Qed.

End KforkPrologue.

End KforkPrologue.
