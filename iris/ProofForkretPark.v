(* ProofForkretPark.v -- PARKING A FRESH PROCESS, PROVED, out of forkret.

   [SchedCtx.proc_ctx pa] -- membership in the scheduler's swtch chain -- is
   a guarded fixpoint whose obligation reads "prove a WP for the code that
   runs when this context is resumed".  For a process allocproc has just
   built, that code is [forkret], so the record is exactly forkret's
   contract turned inside out, and this file is the turn.

   THE ARGUMENT IN ONE PARAGRAPH.  Unfold [SwtchCtx.valid_context] once.
   Its owned half is what allocproc already handed the caller (the fourteen
   context cells, with ra = forkret and sp = the kstack top) plus the free
   kernel stack; its resume wand hands in a register file whose callee-saved
   image IS those cells, the resuming hart's [sie_cap_gpr] / [cpu_own] at
   level 1 with interrupts off, a pc at [ret_pc] of the saved ra, the cells
   back, and the chain payload.  Read the payload at its DISPATCH disjunct
   ([SchedCtx.p_sched_at_proc], which is also what refutes the parking one)
   and it delivers the trap
   CSRs, p->lock held at RUNNING, the hart tag, and -- the piece the whole
   protocol turns on -- the resumER's record, i.e. THAT hart's parked
   scheduler, which is precisely what [SchedCtx.run_slot] wants back inside
   the lock forkret is about to release.  So:

     record's ra              -> forkret's [pc_is]
     record's sp / stack      -> forkret's calling convention + [sie_cap_gpr]
     payload's [proc_held]    -> [locked] + [Rlk] + [cpu_claim]
     payload's ▷ scheduler    -> [run_slot], inside [Rlk]
     [procs_inv]              -> the [is_lock] that [Rlk] is the resource of

   and the conclusion of forkret's contract, [WP Loop] at the resuming hart,
   is the fixpoint's obligation verbatim.

   TWO THINGS THIS FILE IS NOT.

   * It is not a Löb argument.  Nothing here recurses: the NEXT park is
     inside the trap loop's own theorem ([SpecUserretClosed]), and what this
     file provides is only the ENTRY into it.  The guardedness that makes
     the fixpoint well-defined is [SwtchCtx]'s, and the ▷ this file's
     conclusion carries is the one the caller's lock invariant wants anyway.

   * It does not close the gap [LinkForkretPark.v] still assumes.  It is a
     functor over [FORKRET_NF] -- forkret WITHOUT the [first] premise, which
     is what a fresh process can honestly be given (see [LinkForkretNF.v])
     -- and it proves [FORKRET_PARK_PAID], whose precondition
     [SpecForkretParkPaid.forkret_park_pkg] names what a creator owes: the
     child's free kernel stack and the closer that produces the trap loop's
     kernel-side bundle.  kfork cannot pay either today.  That is the whole
     remaining distance between this theorem and the Axiom, and it is a
     statement about kfork's environment, not about forkret. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language weakestpre lifting.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExtras.
Require Import RegFile.
Require Import SmodeCore.
Require Import IntrDefs.
Require Import WpLock.
Require Import ProcGeom.
Require Import ProcDefs.
Require Import SwtchCtx.
Require Import FdSlots.
Require Import FileInvDefs.
Require Import IrefSlots InodeRegion.
Require Import DiskPtsto WpUart FsBlocks LogInv FsCrash KallocInv BioDefs.
Require Import ProcAvail.
Require Import ProcInv.
Require Import SchedCtx.
Require Import SpecPrepareReturn.
Require Import SpecForkret.
Require Import SpecForkretPark SpecForkretParkPaid.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Local Open Scope Z_scope.

Module ForkretParkProof (FR : FORKRET_NF) : FORKRET_PARK_PAID.

Section Res.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !fileG Σ, !bioG Σ,
            !diskGhostG Σ, !uartGhostG Σ, !fsLogG Σ, !logG Σ, !fsCrashG Σ,
            !kallocG Σ, !irefslotG Σ, !pavG Σ, !iregG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  (* the residue is forkret's, re-exported unchanged *)
  Definition usertrap_res := FR.usertrap_res.
  Definition usertrap_res_parked := FR.usertrap_res_parked.
  Definition usertrap_res_tlb_close := FR.usertrap_res_tlb_close.
  Definition usertrap_res_tlb_open := FR.usertrap_res_tlb_open.
  Definition usertrap_res_bare := FR.usertrap_res_bare.
  Definition usertrap_res_pt_close := FR.usertrap_res_pt_close.
  Definition usertrap_res_pt_open := FR.usertrap_res_pt_open.
  Definition usertrap_res_bare_norm := FR.usertrap_res_bare_norm.
  Definition usertrap_res_csrs_open := FR.usertrap_res_csrs_open.
  Definition usertrap_res_sstc := FR.usertrap_res_sstc.
  Definition usertrap_res_tf_csrs_open := FR.usertrap_res_tf_csrs_open.
  Definition usertrap_res_tf_open := FR.usertrap_res_tf_open.
End Res.

(* the two register slots of the saved image the park has to read: field 0
   is ra (the resume pc) and field 1 is sp (the kernel stack top).  Proved
   against an ABSTRACT [m] and by [cbn] restricted to the list combinators,
   for [ProofSwtch.callee_img_nth1]'s measured reason. *)
Lemma fkp_img_nth0 (m : regfile) (d : mword 64) :
  nth 0 (callee_img m) d = m !!! Regidx (mword_of_int 1 : mword 5).
Proof. unfold callee_img, ctx_regs. cbn [map nth]. reflexivity. Qed.

Lemma fkp_img_nth1 (m : regfile) (d : mword 64) :
  nth 1 (callee_img m) d = m !!! Regidx (mword_of_int 2 : mword 5).
Proof. unfold callee_img, ctx_regs. cbn [map nth]. reflexivity. Qed.

(* forkret's entry is 2-aligned, so the [c.ret]/[jalr] masking the resume pc
   goes through is the identity on it. *)
Lemma fkp_ret_pc : ret_pc forkret_pc = forkret_pc.
Proof. rewrite /forkret_pc. apply bv_eq. vm_compute. reflexivity. Qed.

(* the disabled arm never owes more reserve than the enabled one -- what
   makes ONE parked depth serve the record's [∀ eb'] resume wand. *)
Lemma fkp_trap_res_le (b : bool) : (trap_res b <= trap_res true)%nat.
Proof. destruct b; rewrite /trap_res; lia. Qed.

(* the state mirror of a proc a scheduler has just dispatched: RUNNING is a
   CLAIMED state, so what the lock holder carries splits into the lock's
   own half #1 and the claimant's half #2 -- the guard resolved once, here,
   rather than as an [if] the proofmode would have to reduce under. *)
Lemma fkp_pstate_split `{!riscvGS Σ} (pa : mword 64) :
  pstate_whole pa RUNNING ⊣⊢ pstate_lock pa RUNNING ∗ pstate_at_hlf pa RUNNING.
Proof. rewrite pstate_whole_split unclaimed_RUNNING. reflexivity. Qed.

Theorem forkret_park_paid
    `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !fileG Σ, !bioG Σ,
      !diskGhostG Σ, !uartGhostG Σ, !fsLogG Σ, !logG Σ, !fsCrashG Σ,
      !kallocG Σ, !irefslotG Σ, !pavG Σ, !iregG Σ}
    `{GEN : GenId} `{CID : CpuId}
    (γs : list gname) (γf : gname) (pa ks : mword 64) (rest : list (mword 64))
    (pid : mword 32) (V : pprivate) (av : nat) :
    forkret_park_paid_body (fun h : CpuId => FR.usertrap_res_bare (CID := h))
      γs γf pa ks rest pid V av.
Proof.
  cbv beta delta [forkret_park_paid_body].
  intros Hrest [j [Hpa Hj]] Hut Hav Hnorm Hptwf Hgap Hkw.
  subst pa.
  iIntros "Hpkg #Hks Hctx Hpriv Hfd Hirsp".
  iEval (rewrite /forkret_park_pkg) in "Hpkg".
  iDestruct "Hpkg" as "(#Htext & #Hwire & #Hkmap & #Hpinv & #Hmk & Hstk & Hclose)".
  iModIntro. iNext.
  (* ---- the record: the cells allocproc left, and the free stack ---- *)
  rewrite /proc_ctx
          (valid_context_unfold (p_sched γs) None (p_context (proc_addr j)) (proc_addr j))
          /valid_context_pre.
  iExists (forkret_pc :: add_vec ks (mword_of_int 4096) :: rest), av.
  iSplit; [iPureIntro; cbn [length]; lia |].
  iSplit; [iPureIntro; apply ret_pc_aligned |].
  iFrame "Hctx".
  iSplitL "Hstk"; [cbn [nth]; iExact "Hstk" |].
  (* ================================================================== *)
  (* THE RESUME WAND -- forkret's precondition, assembled.               *)
  (* ================================================================== *)
  (* the child's two allowances are captured HERE, at the build, and fed
     to the closer at the resume: they are the record's, not the resuming
     hart's, and forkret itself never sees them. *)
  iAssert (∀ (h : CpuId) (V' : pprivate),
             ⌜pv_upt V' = pv_upt V⌝ -∗
             forkret_yield (CID := h) γf (proc_addr j)
               (add_vec ks (mword_of_int 4096)) pid av V' -∗
             FR.usertrap_res_bare (CID := h) (pv_upt V)
               (add_vec ks (mword_of_int 4096)))%I
    with "[Hclose Hfd Hirsp]" as "Hclose".
  { iIntros (h V') "%HV Hy". iApply ("Hclose" with "[] Hy Hfd Hirsp"). done. }
  iIntros (h m eb') "%Hadm %Himg Hcg Hcpu Hpc Hcells Hpay".
  iDestruct "Hpay" as (A' cret backr) "[Hrec Hpay]".
  (* the payload can only be the DISPATCH one -- the parking disjunct would
     make this record [cpus[h].context], which proc[]/cpus[] adjacency
     refutes ([p_sched_at_proc] does that refutation).  What it delivers:
     the resumer WAS hart [h]'s scheduler, p->lock is held at RUNNING, and
     the resumer's own record ("Hrec") is that hart's parked scheduler --
     and a dispatching scheduler always leaves one, so [backr] is [true] and
     "Hrec" is a record rather than bare cells. *)
  iDestruct (p_sched_at_proc γs h A' j cret _ (proc_addr j) backr Hj with "Hpay")
    as "(%Htp & %Hcret & %Hpj & %HA & %Hbackr & Htc & Hrest)".
  iDestruct "Hrest" as (γl ch) "(%Hgl & Hheld & Htag)".
  subst cret A' backr.
  (* ---- the lock this process's release will give back to ---- *)
  iDestruct (procs_inv_lookup γs j γl Hgl with "Hpinv") as "#Hlk".
  (* ---- what holding p->lock at RUNNING is made of ---- *)
  iDestruct "Hheld" as "(Hlocked & Hstate & Hwhole & Hchan & Hpub)".
  iEval (rewrite fkp_pstate_split) in "Hwhole".
  iDestruct "Hwhole" as "[Hplock Hhlf2]".
  iEval (rewrite hart_split) in "Htag".
  iDestruct "Htag" as "[Htag1 Htag2]".
  (* ---- the running claim: half #2 of the state mirror + the hart tag ---- *)
  iDestruct (pstate_at_elim j (1/2) RUNNING Hj with "Hhlf2") as "Hhlf2".
  iDestruct (cpu_claim_proc (CID := h) j Hj with "Hhlf2 Htag1") as "Hclm".
  (* ---- the lock resource: the raw context cells the wand handed back,
         and THAT hart's parked scheduler, which is [run_slot] ---- *)
  iAssert (own_ctx (p_context (proc_addr j))) with "[Hcells]" as "Hown".
  { iExists (forkret_pc :: add_vec ks (mword_of_int 4096) :: rest).
    iFrame "Hcells". iPureIntro. cbn [length]. lia. }
  iDestruct (proc_slots_running_intro γs j h Hj with "Htag2 Hown Hrec Hmk")
    as "Hslots".
  iDestruct (proc_lock_res_intro γs γl (proc_addr j) RUNNING ch
               with "Hstate Hplock Hchan Hpub Hslots") as "HR".
  (* ---- the two register facts, off the saved image ---- *)
  assert (Hra : m !!! Regidx (mword_of_int 1 : mword 5) = forkret_pc).
  { rewrite -(fkp_img_nth0 m (mword_of_int 0)) Himg. reflexivity. }
  assert (Hsp : m !!! Regidx (mword_of_int 2 : mword 5)
                = add_vec ks (mword_of_int 4096)).
  { rewrite -(fkp_img_nth1 m (mword_of_int 0)) Himg. reflexivity. }
  iEval (rewrite Hra fkp_ret_pc) in "Hpc".
  (* ---- the budget: one parked depth, both arms ---- *)
  pose proof (fkp_trap_res_le eb') as Htr.
  assert (Hbud : (trap_res eb' + (av - 6 - trap_res eb'))%nat = (av - 6)%nat)
    by lia.
  assert (Hpr : (K_prepare_return <= av - 6 - trap_res eb')%nat) by lia.
  (* ================================================================== *)
  (* forkret, at the resuming hart.                                      *)
  (* ================================================================== *)
  iApply (FR.wp_forkret_nf (CID := h) (pv_upt V) j γl γf "proc"%string
            (proc_lock_res γs γl (proc_addr j)) pid V ks m av
            (av - 6 - trap_res eb')%nat eb'
            Hj Hbud Hpr Hut Hsp eq_refl Hnorm Hptwf Hgap Hkw
          with "Htext Hwire Hkmap Hpc [] Hcg Hcpu Htc Hclm Hlk Hlocked HR Hks Hpriv Hclose").
  done.
Qed.

End ForkretParkProof.
