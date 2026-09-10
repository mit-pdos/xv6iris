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

   * It does not close the gap [LinkForkretPark.v] still assumes.  It proves
     [FORKRET_PARK_PAID], whose precondition
     [SpecForkretParkPaid.forkret_park_pkg] names what a CREATOR owes; the
     two callers still take the assumed [FORKRET_PARK].  Closing that is
     Step E of projects/forkret-park.md and is a statement about kfork's and
     userinit's environments, not about forkret.

   WHAT CHANGED SINCE THE VERSION DELETED AT 4bbc418f.  That one was a
   functor over [FORKRET_NF] -- forkret's contract MINUS a [first] premise,
   itself an [Axiom] in [LinkForkretNF.v].  Forkret is PROVED now, boot arm
   and all, so this is a functor over [SpecForkret.FORKRET] and its cone
   carries no first-related axiom at all.  Item by item:

     - no [Pfirst] premise, no [pt] parameter, no [is_lock γl p s Rlk]
       triple -- forkret takes [procs_inv γs] and [γs !! j = Some γl] and
       derives its own lock, so the string and the resource stopped being
       parameters and the [procs_inv_lookup] step moved into forkret;

     - [Hnorm] and [Hptwf] left this contract's premises: the closer is
       [∀ pt'] and forkret proves the two page-table facts of the descriptor
       it actually ends on, so they are HANDED to the wand rather than fixed
       here.  [V] left [forkret_park_pkg] for the same reason;

     - the depth obligation is kexec's, not prepare_return's, and it is not
       a premise: [6 + trap_res true + K_kexec = 280] and [K_usertrap = 342],
       so [Hut] gives it by [lia];

     - the closer takes [FirstTok.first_done] (SpecForkret.v's last header
       section), which this file threads through unchanged. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language weakestpre lifting.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto.
Require Import RegFile.
Require Import RiscvExtras.
Require Import IntrDefs.
Require Import ProcGeom.
Require Import ProcDefs.
Require Import SwtchCtx.
Require Import FdSlots.
Require Import FileInvDefs.
Require Import IrefSlots.
Require Import WpUart LogInv.
Require Import ProcAvail.
Require Import ProcInv.
Require Import SchedCtx CtxMorphTac.
Require Import UsertrapRes.  (* [ut_park_intro_body] -- the park's producer entry *)
Require Import StackOwn.   (* [stack_own] -- the kernel stack moves into the twin (L8) *)
Require Import KexecDefs.   (* [K_kexec] -- forkret's deepest callee, on the boot arm *)
Require Import SpecForkret.
Require Import FirstTok.
Require Import UserPtTree ProcPtOwn.
Require Import SpecForkretPark SpecForkretParkPaid ParkCap.
Require Import InitBoot.  (* [init_boot_bundle] -- the BOOT mode's payload *)
Require Import UexecSlot. (* [uvis_of] *)
Require Import UexecRet.  (* [uslot] -- in the proofmode context below, so
                             required DIRECTLY (durable-notes) *)
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Local Open Scope Z_scope.
Require Import TsoCtx.   (* [own_context_twin] / [ctx_move] -- the child's own context (A6.129) *)

(* ===================================================================== *)
(* THE CHILD-RECORD PRODUCER.                                            *)
(*                                                                       *)
(* [own_context_twin] mints the child's identity [XIc] as a RUNNING copy  *)
(* of the parker's bound and watermark; every row of the record then      *)
(* moves into it by [TsoCtx.ctx_move] while both contexts run -- the      *)
(* context cells, the kernel stack, the kstack handle, the process-table  *)
(* handle, the park globals and [proc_priv].  The twin is then PARKED     *)
(* UNDER THE PARENT ([TsoCtx.ctx_park XIc cur_ctx]), which is what        *)
(* [SchedCtx.proc_ctx] holds beside the record, and the parker's release  *)
(* of p->lock deposits the slot as an ordinary payload.  No stamp, no     *)
(* box: a context is filled while it RUNS, because there is no deposit    *)
(* into a parked child (claude-notes/design/contexts.md §2, §4).          *)
(* ===================================================================== *)

Require Import UserFd.   (* [ufdG] -- the class a minted user slot needs *)

Module ForkretParkProof (FR : FORKRET) : FORKRET_PARK_PAID.

Section Res.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ, !irefslotG Σ, !pavG Σ}.
  Context `{!ufdG Σ}.
  Context `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}.
  (* NO [Context `{SG : uexecSG Σ}]: this file sits ABOVE
     [UexecExecInst], so the deposit class it speaks is that file's
     INSTANCE, and so is the one the specs it inhabits were stated at.  A
     section variable here would be a SECOND class of the same type, and the
     two [UexecRet.uslot]s print identically -- the unifier does not stop. *)

  (* the residue is forkret's, re-exported unchanged *)
  Definition usertrap_res := FR.usertrap_res.
  Definition usertrap_res_parked := FR.usertrap_res_parked.
  Definition usertrap_res_tlb_close := FR.usertrap_res_tlb_close.
  Definition usertrap_res_tlb_open := FR.usertrap_res_tlb_open.
  Definition usertrap_res_bare := FR.usertrap_res_bare.
  Definition usertrap_res_pt_close := FR.usertrap_res_pt_close.
  Definition usertrap_res_pt_open := FR.usertrap_res_pt_open.
  Definition usertrap_res_ptm_close := FR.usertrap_res_ptm_close.
  Definition usertrap_res_ptm_open := FR.usertrap_res_ptm_open.
  Definition usertrap_res_bare_norm := FR.usertrap_res_bare_norm.
  Definition usertrap_res_bare_fd_open := FR.usertrap_res_bare_fd_open.
  Definition usertrap_res_bare_fd_tf_open := FR.usertrap_res_bare_fd_tf_open.
  Definition usertrap_res_csrs_open := FR.usertrap_res_csrs_open.
  Definition usertrap_res_sstc := FR.usertrap_res_sstc.
  Definition usertrap_res_bare_sz := FR.usertrap_res_bare_sz.
  Definition usertrap_res_bare_fsabs := FR.usertrap_res_bare_fsabs.
  Definition usertrap_res_tf_csrs_open := FR.usertrap_res_tf_csrs_open.
  Definition usertrap_res_tf_open := FR.usertrap_res_tf_open.
  (* ...and the park's one producer-side entry, threaded like the rest.
     A file that merely passes the residue through has nothing to say about
     it; the entry exists so that whoever PARKS a never-run process can
     build one (UsertrapRes.v, "THE PARK'S CHANNEL THROUGH THE MODULE
     TYPES"). *)
  Definition usertrap_res_bare_park
      (N : ut_names) (av : nat)
    : ut_park_intro_body
        (fun (h : CpuId) (Xc : CurCtx) => FR.usertrap_res_bare (CID := h) (XI := Xc))
        (park_token (un_s N)) N av
    := FR.usertrap_res_bare_park N av.
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
Lemma fkp_pstate_split `{!riscvGS Σ} `{!ufdG Σ} (pa : mword 64) :
  pstate_whole pa RUNNING ⊣⊢ pstate_lock pa RUNNING ∗ pstate_at_hlf pa RUNNING.
Proof. rewrite pstate_whole_split unclaimed_RUNNING. reflexivity. Qed.

(* A6.128: the kstack pointer row is deposited into the child's record too *)
Global Instance fkp_is_kstack_morph `{!riscvGS Σ} `{GEN : GenId} `{CID : CpuId} (pa ks : mword 64) :
  CtxMorph (λ ξ, is_kstack (XI := ξ) pa ks).
Proof. rewrite /is_kstack. ctx_morph_solve. Qed.

(* THE BLOCK'S DEPOSIT ROW, AT BOTH MODES.  The boot mode's is three rows
   under one [if] ([ParkCap.park_child]); the composite goes through the
   structural instances by name, because plain search does not always
   decompose a [sep] (CtxMorphTac.v's header). *)
Global Instance fkp_park_block_morph
    `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ, !irefslotG Σ}
    `{GEN : GenId}
    (steady : bool) (γf : gname) (pa : mword 64) (pid : mword 32) (U : ustate) :
  CtxMorph (λ ξ, (if steady then proc_priv (XI := ξ) γf pa pid U
                  else proc_priv_nocwd (XI := ξ) γf pa pid U
                       ∗ cwd_ref_at (XI := ξ) (pv_cwd (us_V U)) (pv_cwi (us_V U))
                       ∗ FirstTok.first_boot (XI := ξ))%I).
(* the last conjunct of a [sep] comes back ETA-REDUCED, so the solver's
   head-symbol dispatch does not see it as a λ; [first_boot_morph] by name
   closes it (CtxMorphTac.v's two spellings of [ctx_parked_morph] are the
   same effect). *)
Proof. ctx_morph_solve; first [apply _ | apply FirstTok.first_boot_morph]. Qed.

Theorem forkret_park_paid
    `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ, !irefslotG Σ, !pavG Σ} `{!ufdG Σ} `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}
    (W : iProp Σ)
    (γs : list gname) (γw γc γft γf γtl : gname) (pa ks : mword 64) (rest : list (mword 64))
    (pid : mword 32) (U : ustate) (sts : list fdstate) (gn : gname)
    (cs : gset gname) (av : nat) (steady : bool) :
    forkret_park_paid_body
      (fun (h : CpuId) (Xc : CurCtx) => FR.usertrap_res_bare (CID := h) (XI := Xc)) W
      γs γw γc γft γf γtl pa ks rest pid U sts gn cs av steady.
Proof.
  cbv beta delta [forkret_park_paid_body].
  intros Hrest [j [Hpa Hj]] Hut.
  subst pa.
  iIntros "Hrun Hpkg HW #Hks Hctx Hpriv Hfd Hirsp".
  (* THE CHILD'S OWN CONTEXT: twin the parker's running token, move every
     row of the record across while both are running, then park the twin
     under the parker. *)
  iMod (own_context_twin cur_ctx with "Hrun") as "[Hrun (%XIc & Hthr)]".
  iEval (rewrite /forkret_park_pkg) in "Hpkg".
  iDestruct "Hpkg" as "(#Htext & #Hwire & #Hkmap & #Hpinv & #Hglobp & #Hmk & Hstk
                       & Hmode & Hclose)".
  (* THE MODE ROW, at the shape the [ctx_move] combinator takes: the package
     spells it as a [match] on the run key it carries, and the key is
     [steady]'s own [if], so the two agree by iota on each arm. *)
  iAssert (if steady then FirstTok.first_done
           else init_boot_bundle (pv_cwi (us_V U)) sts)%I with "[Hmode]" as "Hmode".
  { destruct steady; [iExact "Hmode" | iExact "Hmode"]. }
  iMod (ctx_move (R := λ ξ, ctx_cells (XI := ξ) (p_context (proc_addr j))
                              (forkret_pc :: add_vec ks (mword_of_int 4096) :: rest))
          cur_ctx XIc with "Hrun Hthr Hctx") as "(Hrun & Hthr & Hctx)".
  iMod (ctx_move (R := λ ξ, stack_own (KTR := KT1) (XI := ξ) (add_vec ks (mword_of_int 4096)) av)
          cur_ctx XIc with "Hrun Hthr Hstk") as "(Hrun & Hthr & Hstk)".
  iMod (ctx_move (R := λ ξ, is_kstack (XI := ξ) (proc_addr j) ks)
          cur_ctx XIc with "Hrun Hthr Hks") as "(Hrun & Hthr & #Hksc)".
  iMod (ctx_move (R := λ ξ, procs_inv (XI := ξ) γs)
          cur_ctx XIc with "Hrun Hthr Hpinv") as "(Hrun & Hthr & #Hpinvc)".
  iMod (ctx_move (R := λ ξ, UsertrapRes.park_globals ξ γs γw γc γft γf γtl)
          cur_ctx XIc with "Hrun Hthr Hglobp") as "(Hrun & Hthr & #Hglobc)".
  (* THE BLOCK, AT THE MODE'S SHAPE ([ParkCap.park_child]): whole on the
     steady mode, and on the boot mode the deficit block, the cwd reference
     and [FirstTok.first_boot]'s rows -- three transports under one [if],
     which [ctx_morph_if] takes apart. *)
  iMod (ctx_move (R := λ ξ, (if steady then proc_priv (XI := ξ) γf (proc_addr j) pid U
                             else proc_priv_nocwd (XI := ξ) γf (proc_addr j) pid U
                                  ∗ cwd_ref_at (XI := ξ) (pv_cwd (us_V U)) (pv_cwi (us_V U))
                                  ∗ FirstTok.first_boot (XI := ξ))%I)
          cur_ctx XIc with "Hrun Hthr Hpriv") as "(Hrun & Hthr & Hpriv)".
  (* ...and the mode row, which forkret reads at ITS context: the boot arm's
     [first_addr ↦₄ 1] comes out of the block that was just moved, so the
     [↦₄□ 0] that refutes it has to be at the same identity. *)
  iMod (ctx_move (R := λ ξ, (if steady then FirstTok.first_done (XI := ξ)
                             else init_boot_bundle (pv_cwi (us_V U)) sts)%I)
          cur_ctx XIc with "Hrun Hthr Hmode") as "(Hrun & Hthr & Hmode)".
  iMod (ctx_park XIc cur_ctx with "Hrun Hthr") as "[Hrun Hpk]".
  iModIntro. iFrame "Hrun".
  rewrite /proc_ctx /proc_ctx_at. iExists XIc. iFrame "Hpk".
  iNext.
  rewrite (valid_context_unfold (p_sched γs) None (p_context (proc_addr j))
             (proc_addr j) XIc)
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
  iAssert (∀ (h : CpuId) (Xc : CurCtx) (pt' : uptd) (U' : ustate),
             ⌜pv_upt (us_V U') = pt'⌝ -∗
             ⌜ud_data pt' = ud_pas pt'⌝ -∗
             ⌜proc_pt_wf pt'⌝ -∗
             (* the resumed record names the same fd-state ghost the parked
                one did -- see [SpecForkretParkPaid.forkret_park_pkg] *)
             ⌜pv_fdg (us_V U') = pv_fdg (us_V U)⌝ -∗
             ⌜pv_cwi (us_V U') = pv_cwi (us_V U)⌝ -∗
             (* ...and, on the steady mode, the parked run key -- passed
                straight through to the package's own closer *)
             ⌜match (if steady then Some (uvis_of U [] gn cs) else None) with
               | Some W0 => urun_eq W0 U' | None => True end⌝ -∗
             (* ...and the resumer's globals, at ITS context (L8, A12.19) *)
             UsertrapRes.park_globals Xc γs γw γc γft γf γtl -∗
             UsertrapRes.ut_tfk (CID := h) (add_vec ks (mword_of_int 4096)) (us_V U') -∗
             first_done (XI := Xc) -∗
             W -∗
             TimerCap.timer_cap (CID := h) -∗
             forkret_yield (CID := h) (XI := Xc) γf (proc_addr j)
               (add_vec ks (mword_of_int 4096)) pid av (us_V U') -∗
             (FR.usertrap_res_bare (CID := h) (XI := Xc) pt'
                (add_vec ks (mword_of_int 4096)) U' sts
              ∗ match (if steady then Some (uvis_of U [] gn cs) else None) with
                | Some _ => uslot (uvis_of U' sts gn cs)
                | None => emp
                end))%I
    with "[Hclose Hfd Hirsp]" as "Hclose".
  { iIntros (h Xc pt' U') "%HV %Hnorm %Hptwf %Hfg %Hcwi %Hrk #Hglob #Htfk Hdone HW #Htc Hy".
    iApply ("Hclose" $! h Xc pt' U'
              with "[%] [%] [%] [%] [%] [%] Hglob Htfk Hdone HW Htc Hy Hfd Hirsp");
      [exact HV | exact Hnorm | exact Hptwf | exact Hfg | exact Hcwi | exact Hrk]. }
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
  iAssert (own_ctx (XI := XIc) (p_context (proc_addr j))) with "[Hcells]" as "Hown".
  { iExists (forkret_pc :: add_vec ks (mword_of_int 4096) :: rest).
    iFrame "Hcells". iPureIntro. cbn [length]. lia. }
  (* the dispatching scheduler's record came back with its RUNNING token
     beside it ([SwtchCtx.park_tok_at (Some h)]); fold it back under the later
     the running slot holds it beneath (A6.127 §6). *)
  iDestruct "Hrec" as (XIo) "[Htok Hrec]".
  iEval (rewrite /park_tok_at) in "Htok".
  iDestruct (sched_vc_at_intro γs h _ _ XIo with "Htok Hrec") as "Hrec".
  iDestruct (proc_slots_running_intro (XI := XIc) γs j h Hj with "Htag2 Hown Hrec Hmk")
    as "Hslots".
  iDestruct (proc_lock_res_intro (XI := XIc) γs γl (proc_addr j) RUNNING ch
               with "Hstate Hplock Hchan Hpub Hslots") as "HR".
  (* ---- the two register facts, off the saved image ---- *)
  assert (Hra : m !!! Regidx (mword_of_int 1 : mword 5) = forkret_pc).
  { rewrite -(fkp_img_nth0 m (mword_of_int 0)) Himg. reflexivity. }
  assert (Hsp : m !!! Regidx (mword_of_int 2 : mword 5)
                = add_vec ks (mword_of_int 4096)).
  { rewrite -(fkp_img_nth1 m (mword_of_int 0)) Himg. reflexivity. }
  iEval (rewrite Hra fkp_ret_pc) in "Hpc".
  (* ---- the budget: one parked depth, both arms ----
     [trap_res] is a Definition, not a Notation, so [lia] needs the enabled
     arm's value spelled out; the two K's ARE literals and it sees them.
     [6 + trap_res true + K_kexec = 280 <= 342 = K_usertrap], so forkret's
     deepest callee is covered by [Hut] and is not a premise of this park. *)
  pose proof (fkp_trap_res_le eb') as Htr.
  assert (Htrue : trap_res true = kv_frame_slots) by reflexivity.
  assert (Hbud : (trap_res eb' + (av - 6 - trap_res eb'))%nat = (av - 6)%nat)
    by lia.
  assert (Hkx : (K_kexec <= av - 6 - trap_res eb')%nat) by lia.
  (* ================================================================== *)
  (* forkret, at the resuming hart.                                      *)
  (* ================================================================== *)
  iApply (FR.wp_forkret (CID := h) (XI := XIc) W j γs γl γw γc γft γf γtl pid U sts
            gn cs ks m av
            (av - 6 - trap_res eb')%nat eb' steady
            Hj Hgl Hbud Hkx Hut Hsp
          with "Htext Hwire Hkmap Hpc [] [] Hcg Hcpu Htc Hclm
                Hlocked HR Hksc [Hpriv] HW Hmode Hclose").
  (* THE THREE MOVED ROWS -- [procs_inv], [park_globals]'s handles and the
     child's private block through [BioInv.buf_escrow] -- are at the
     record's identity [XIc], so each closes by [iExact].  Bracketed rather
     than framed: a ξ mismatch fails HERE, fast, instead of sending
     [iApply]'s unifier through the bodies. *)
  { iExact "Hpinvc". }
  { iExact "Hglobc". }
  iExact "Hpriv".
Qed.

(* ===================================================================== *)
(* THE TOKEN.  The cap above at [W := park_token γs], and the residue's     *)
(* channel at the same [W] (forkret's [usertrap_res_bare_park]), tied      *)
(* into [ParkCap.park_token]'s fixpoint by [park_token_intro_of].  The     *)
(* [▷ package] of the cap and the [▷ closer] of the channel are what make  *)
(* the knot well-founded: see ParkCap.v.                                   *)
(* ===================================================================== *)
Theorem park_token_intro
    `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ, !irefslotG Σ, !pavG Σ} `{!ufdG Σ} `{GEN : GenId} `{XI : CurCtx}
    (γs : list gname) :
    ⊢ park_token γs.
Proof.
  iApply (park_token_intro_of
            (fun (h : CpuId) (Xc : CurCtx) => FR.usertrap_res_bare (CID := h) (XI := Xc)) γs).
  { intros N av. exact (FR.usertrap_res_bare_park N av). }
  rewrite /park_cap. iModIntro.
  iIntros (hp ξp γw γc γft γf γtl pa ks rest pid U sts gn cs av steady)
    "%Hrest %Hj %Hav Hrun Hpkg HW Hchild".
  destruct U as [V M].
  iDestruct "Hchild" as "(#Hks & Hctx & Hpriv & Hfd & Hirsp)".
  iApply (forkret_park_paid (CID := hp) (XI := ξp) (park_token γs) γs γw γc γft γf γtl pa ks rest pid
            (MkUstate V M) sts gn cs av steady Hrest Hj Hav
          with "Hrun [Hpkg] HW Hks Hctx Hpriv Hfd Hirsp").
  iEval (rewrite /park_pkg) in "Hpkg". iEval (rewrite /forkret_park_pkg).
  iDestruct "Hpkg" as "(#Htext & #Hwire & #Hkmap & #Hpinv & #Hglobp & #Hmk & Hstk
                       & Hmode & Hclose)".
  iFrame "Htext Hwire Hkmap Hmk Hstk".
  (* [procs_inv] and the globals by [iExact]: the persistent [Hpinv] would
     otherwise be framed INTO the transparent globals bundle's first row *)
  iSplitR; [iExact "Hpinv"|].
  iSplitR; [iExact "Hglobp"|].
  (* the mode row: the two packages are the same proposition, so this is the
     one hypothesis, on either arm *)
  iSplitL "Hmode"; [iExact "Hmode"|].
  iNext.
  iIntros (h Xc pt' U') "%HV %Hnorm %Hptwf %Hfg %Hcwi %Hrk #Hglob #Htfk Hdone HW #Htc [Htrap Hpv] Hfd Hirsp".
  iApply ("Hclose" $! h Xc pt' U'
            with "[%] [%] [%] [%] [%] [%] Hglob Htfk Hdone HW Htc Htrap Hpv Hfd Hirsp");
    [exact HV | exact Hnorm | exact Hptwf | exact Hfg | exact Hcwi | exact Hrk].
Qed.

End ForkretParkProof.
