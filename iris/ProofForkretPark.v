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
Require Import SchedCtx.
Require Import UsertrapRes.  (* [ut_park_intro_body] -- the park's producer entry *)
Require Import SpecKexec.   (* [K_kexec] -- forkret's deepest callee, on the boot arm *)
Require Import SpecForkret.
Require Import FirstTok.
Require Import UserPtTree ProcPtOwn.
Require Import SpecForkretPark SpecForkretParkPaid ParkCap.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Require Import TsoCtx.   (* [CurCtx]: the residue owns a thread token *)
Local Open Scope Z_scope.

Module ForkretParkProof (FR : FORKRET) : FORKRET_PARK_PAID.

Section Res.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ, !irefslotG Σ, !pavG Σ}.
  Context `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}.

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
  (* ...and the park's one producer-side entry, threaded like the rest.
     A file that merely passes the residue through has nothing to say about
     it; the entry exists so that whoever PARKS a never-run process can
     build one (UsertrapRes.v, "THE PARK'S CHANNEL THROUGH THE MODULE
     TYPES"). *)
  Definition usertrap_res_bare_park
      `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ, !irefslotG Σ, !pavG Σ} `{GEN : GenId}
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
Lemma fkp_pstate_split `{!riscvGS Σ} (pa : mword 64) :
  pstate_whole pa RUNNING ⊣⊢ pstate_lock pa RUNNING ∗ pstate_at_hlf pa RUNNING.
Proof. rewrite pstate_whole_split unclaimed_RUNNING. reflexivity. Qed.

Theorem forkret_park_paid
    `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ, !irefslotG Σ, !pavG Σ} `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}
    (W : iProp Σ)
    (γs : list gname) (γw γft γf γtl : gname) (pa ks : mword 64) (rest : list (mword 64))
    (pid : mword 32) (V : pprivate) (av : nat) :
    forkret_park_paid_body (fun (h : CpuId) (Xc : CurCtx) => FR.usertrap_res_bare (CID := h) (XI := Xc)) W
      γs γw γft γf γtl pa ks rest pid V av.
Proof.
  cbv beta delta [forkret_park_paid_body].
  intros Hrest [j [Hpa Hj]] Hut.
  subst pa.
  iIntros "Hrun Hpkg HW #Hks Hctx Hpriv Hfd Hirsp".
  (* THE CHILD'S THREAD OF CONTROL IS BORN HERE -- PARKED (tso-port ruling
     2d.4.1, realized by the checkpoint-0.5 repair).  A forked process's
     kernel thread is a NEW thread that has never run, so its mint is the
     PURE parked allocation ([TsoCtx.ctx_parked_alloc]) -- it claims no
     hart and no visibility, which is why no machine evidence appears
     here.  The token goes straight into the record it is building; the
     dispatcher's resume ([TsoCtx.ctx_resume], via the p->lock acquire's
     view receipt) is what first ties it to a hart.  From there it moves
     only by the swtch exchange, until a zombie park drops it.  The mint
     must precede the [iModIntro] below: that is the only update this
     proof has. *)
  iMod (ctx_parked_alloc) as (XIc) "Hthr".
  (* THE PACKAGE IS NOT UNDER A LATER ANY MORE -- its CLOSER ROW is, and
     that is the whole of what the fixpoint ever needed (tso-port.md §0.16′
     step (ii)).  THE PARKER'S OWN THREAD-OF-CONTROL TOKEN is borrowed and
     handed straight back here.  ON MAIN this is where the six-row
     [TsoCtx.ctx_deposit] into [XIc] runs; IN THIS TREE IT CANNOT, and the
     reason is measured rather than a matter of effort: the deposit's
     obligation is [CtxMorph] on each row, and four of the rows
     ([procs_inv], [park_globals]'s wait/ftable/console/ticks/nextpid
     handles, [proc_priv] through [BioInv.buf_escrow]) are constant
     embeddings [<{ P }>] of ξ-INDEXED payloads -- an [inv] over a
     ξ-indexed body, the ONE shape [CtxMorph] cannot cross.  They become
     transportable exactly when the M3 λ-payload sweep and the bcache
     escrow's parked-record form land here (they have on main: tso-port.md
     §0.14′/§0.16′/§0.17′).  Until then the record's rows stay at the
     PARKER's ξ -- which is what [SwtchCtx.valid_context_pre] still reads
     them at in this tree, so the two agree and nothing is unsound; what is
     missing is the [XIp] reshape, not a law. *)
  iModIntro. iFrame "Hrun". iNext.
  iEval (rewrite /forkret_park_pkg) in "Hpkg".
  iDestruct "Hpkg" as "(#Htext & #Hwire & #Hkmap & #Hpinv & #Hglobp & #Hmk & Hstk & Hclose)".
  (* ---- the record: the cells allocproc left, and the free stack ---- *)
  rewrite /proc_ctx
          (valid_context_unfold (p_sched γs) None (p_context (proc_addr j)) (proc_addr j))
          /valid_context_pre.
  iExists (forkret_pc :: add_vec ks (mword_of_int 4096) :: rest), av, XIc,
    0%nat.
  iSplit; [iPureIntro; cbn [length]; lia |].
  iSplit; [iPureIntro; apply ret_pc_aligned |].
  iFrame "Hctx".
  iSplitL "Hstk"; [cbn [nth]; iExact "Hstk" |].
  iSplitL "Hthr"; [iExact "Hthr" |].
  (* ================================================================== *)
  (* THE RESUME WAND -- forkret's precondition, assembled.               *)
  (* ================================================================== *)
  (* the child's two allowances are captured HERE, at the build, and fed
     to the closer at the resume: they are the record's, not the resuming
     hart's, and forkret itself never sees them. *)
  (* the closer describes the CHILD, so its identity is quantified beside
     its hart -- the resumer instantiates both (tso-port.md, the standing
     principle). *)
  iAssert (∀ (h : CpuId) (Xc : CurCtx) (pt' : uptd) (V' : pprivate),
             ⌜pv_upt V' = pt'⌝ -∗
             ⌜ud_data pt' = ud_pas pt'⌝ -∗
             ⌜proc_pt_wf pt'⌝ -∗
             UsertrapRes.park_globals Xc γs γw γft γf γtl -∗
             UsertrapRes.ut_tfk (CID := h) (add_vec ks (mword_of_int 4096)) V' -∗
             first_done (XI := Xc) -∗
             W -∗
             TimerCap.timer_cap (CID := h) -∗
             forkret_yield (CID := h) (XI := Xc) γf (proc_addr j)
               (add_vec ks (mword_of_int 4096)) pid av V' -∗
             FR.usertrap_res_bare (CID := h) (XI := Xc) pt'
               (add_vec ks (mword_of_int 4096)))%I
    with "[Hclose Hfd Hirsp]" as "Hclose".
  { iIntros (h Xc pt' V') "%HV %Hnorm %Hptwf #Hglob #Htfk Hdone HW #Htc Hy".
    iApply ("Hclose" $! h Xc pt' V'
              with "[%] [%] [%] Hglob Htfk Hdone HW Htc Hy Hfd Hirsp");
      [exact HV | exact Hnorm | exact Hptwf]. }
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
  iApply (FR.wp_forkret (CID := h) W j γs γl γw γft γf γtl pid V ks m av
            (av - 6 - trap_res eb')%nat eb'
            Hj Hgl Hbud Hkx Hut Hsp
          with "Htext Hwire Hkmap Hpc Hpinv Hglobp Hcg Hcpu Htc Hclm
                Hlocked HR Hks Hpriv HW Hclose").
Qed.

(* ===================================================================== *)
(* THE TOKEN.  The cap above at [W := park_token γs], and the residue's     *)
(* channel at the same [W] (forkret's [usertrap_res_bare_park]), tied      *)
(* into [ParkCap.park_token]'s fixpoint by [park_token_intro_of].  The     *)
(* [▷ package] of the cap and the [▷ closer] of the channel are what make  *)
(* the knot well-founded: see ParkCap.v.                                   *)
(* ===================================================================== *)
Theorem park_token_intro
    `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ, !irefslotG Σ, !pavG Σ} `{GEN : GenId} `{XI : CurCtx}
    (γs : list gname) :
    ⊢ park_token γs.
Proof.
  iApply (park_token_intro_of (fun (h : CpuId) (Xc : CurCtx) => FR.usertrap_res_bare (CID := h) (XI := Xc)) γs).
  { intros N av. exact (FR.usertrap_res_bare_park N av). }
  rewrite /park_cap. iModIntro.
  iIntros (hp ξp γw γft γf γtl pa ks rest pid V av) "%Hrest %Hj %Hav Hrun Hpkg HW Hchild".
  iDestruct "Hchild" as "(#Hks & Hctx & Hpriv & Hfd & Hirsp)".
  (* THE AMBIENT HART AND CONTEXT ARE BOTH ∀-BOUND HERE -- and the hart is
     now bound for a REASON rather than for symmetry.  [park_cap] describes
     a process that is NOT running, so neither [park_pkg] nor [park_token]
     names a hart or a ξ; but the cap consumes the PARKER's [own_context],
     which is hart-ambient by construction ([TsoCtx.own_context]'s tie is to
     the hart the thread runs on).  Quantifying [hp] beside [ξp] keeps the
     TOKEN hart-free (and hence [SpecSyscall.syscall_env] hart-free) while
     letting the cap run at the parker's real identity. *)
  iApply (forkret_park_paid (CID := hp) (XI := ξp)
            (park_token γs) γs γw γft γf γtl pa ks rest pid V av
            Hrest Hj Hav with "Hrun [Hpkg] HW Hks Hctx Hpriv Hfd Hirsp").
  iEval (rewrite /park_pkg) in "Hpkg". iEval (rewrite /forkret_park_pkg).
  iDestruct "Hpkg" as "(#Htext & #Hwire & #Hkmap & #Hpinv & #Hglobp & #Hmk & Hstk & Hclose)".
  (* row by row, not one [iFrame]: the globals row is an ∃ over a discarded
     cell and a named frame will not match it (ParkCap.park_token_park makes
     the same move for the same reason). *)
  iSplitR; [iExact "Htext"|].
  iSplitR; [iExact "Hwire"|].
  iSplitR; [iExact "Hkmap"|].
  iSplitR; [iExact "Hpinv"|].
  iSplitR; [iExact "Hglobp"|].
  iSplitR; [iExact "Hmk"|].
  iSplitL "Hstk"; [iExact "Hstk"|].
  (* the closer describes the CHILD, so its identity is ∀-quantified beside
     its hart on BOTH sides -- [park_pkg]'s wand and [forkret_park_pkg]'s --
     and this hand-over just passes it through.  It is the one row still
     under a [▷] on both sides (§0.16′ step (ii)). *)
  iNext.
  iIntros (h Xc pt' V') "%HV %Hnorm %Hptwf #Hglob #Htfk Hdone HW #Htc [Htrap Hpv] Hfd Hirsp".
  iApply ("Hclose" $! h Xc pt' V'
            with "[%] [%] [%] Hglob Htfk Hdone HW Htc Htrap Hpv Hfd Hirsp");
    [exact HV | exact Hnorm | exact Hptwf].
Qed.

End ForkretParkProof.
