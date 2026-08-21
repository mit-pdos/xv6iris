(* SpecForkretParkPaid.v -- forkret_park, stated at the premises a caller
   must PAY.  The park turns a freshly-allocated process's raw saved context
   (ra = forkret, sp = kstack + PGSIZE, twelve don't-care callee-saved slots)
   into a member of the scheduler's swtch chain, [SchedCtx.proc_ctx] -- so
   that kfork and userinit can release the process at RUNNABLE.

   [SpecForkretPark.FORKRET_PARK] is the same park ASSUMED, in the form the
   two callers use today; this file is what a proof of it is stated against.
   The difference between the two is exactly the bundle below, and that
   difference -- not anything about forkret -- is what keeps the axiom alive.

   HISTORY, because this file was deleted and rewritten.  An earlier version
   (last green at 4bbc418f) was a functor over [FORKRET_NF]: forkret's
   contract MINUS a [first] premise, assumed in [LinkForkretNF.v].  Forkret
   is now PROVED outright -- boot arm, kexec, panic tail and all
   (ProofForkret.fkr_boot) -- and its contract has moved with it, so that
   whole scaffold is gone: no [FORKRET_NF], no [LinkForkretNF.v], no
   [Pfirst], no [pt] parameter, no [is_lock γl p s Rlk] triple.  A park
   proved against THIS statement is functor over [SpecForkret.FORKRET] and
   is instantiated with [LinkForkret.Forkret], so its cone carries no
   first-related axiom at all.

   WHAT MOVED, ITEM BY ITEM, relative to that earlier statement:

     - THE [first] PREMISE IS GONE and nothing replaces it here.  The branch
       is decided by [FirstTok.first_tok], a conjunct of [ProcInv.proc_priv]
       -- which this contract already takes and passes through untouched.
       The caller owes a [proc_priv] whose token is (after boot) the steady
       arm, and [FirstTok.first_done] is persistent and is already the last
       conjunct of [ProofSyscall.syscall_env], which the closer needs anyway.

     - THE DESCRIPTOR IS NOT PINNED.  forkret's residue closer is now
       [∀ pt'], because the boot arm's kexec REPLACES the address space:
       the table userret runs on is not the one forkret was entered with, so
       no [pt] fixed on entry can name both.  The closer below is quantified
       the same way and is handed the two page-table facts rather than
       taking them as premises of the park.  Consequently [V] left
       [forkret_park_pkg]'s signature entirely -- it occurred only inside
       [pv_upt V].

     - THE DEPTH PREMISE IS GONE, not merely restated.  It used to read
       [6 + trap_res true + K_prepare_return <= av]; forkret's deepest
       callee is now kexec's, so the obligation is [K_kexec <= av2] at
       [av2 = av - 6 - trap_res eb'].  With [K_kexec = 184],
       [trap_res true = kv_frame_slots = 90] and [K_usertrap = 342], that is
       [280 <= av] -- implied by the [K_usertrap <= av] this file already
       carries, so it is [lia]'s job and not a caller's.

   ====================================================================== *)
(* WHAT THE CALLER PAYS, AND WHAT IS ACTUALLY MISSING                     *)
(*                                                                        *)
(* A record must be paid for at the moment it is BUILT, and the thread it  *)
(* promises has not run yet, so its creator owes what the first trap round *)
(* will consume.  Of the seven conjuncts below, six are payable TODAY:     *)
(*                                                                        *)
(*   - [kernel_text], [wire_inv], the trampoline's kernel mapping,         *)
(*     [procs_inv γs], [pslot_used_at pa] -- all PERSISTENT, free for any  *)
(*     caller, but they have to be NAMED, because the record's             *)
(*     continuation is a closure and a closure captures what it uses.      *)
(*     [pslot_used_at] is already in [SpecAllocproc]'s postcondition.      *)
(*                                                                        *)
(*   - [stack_own ksp av] -- the child's KERNEL STACK, free below its top. *)
(*     A running thread carries its stack inside [sie_cap_gpr] and a       *)
(*     parked one inside its record ([SwtchCtx.valid_context_pre] has it   *)
(*     as a conjunct); a never-run one has it nowhere, so the park must    *)
(*     own it.  THIS IS NO LONGER A HOLE, and the older comment here       *)
(*     saying it was is wrong: [ProcDefs.kstack_free] (= [is_kstack] plus  *)
(*     exactly these words at KSTACK_AV) is a conjunct of [proc_dormant],  *)
(*     and [SpecAllocproc]'s postcondition ALREADY hands it back beside    *)
(*     the [is_kstack] one line above it.  [ProcDefs.kstack_free_at]       *)
(*     recovers the words at the caller's concrete [ks].  And the arithmetic*)
(*     lands exactly: [KSTACK_AV = 342 = K_usertrap], so [av := KSTACK_AV] *)
(*     satisfies the depth premise on the nose, at either [eb'].           *)
(*                                                                        *)
(*   - THE RESIDUE CLOSER -- the wand that turns what forkret's tail       *)
(*     yields into the trap loop's kernel-side bundle.  It reads worse     *)
(*     than it is: [forkret_yield] hands it [ut_trap_parked] and           *)
(*     [proc_priv_nopt], its own two arguments hand it the allowances,     *)
(*     and [ut_caps] and [ProofSyscall.syscall_env] are both entirely      *)
(*     PERSISTENT, so a second process's copy of either costs nothing.     *)
(*     It takes [fd_slots FDSPARE] / [iref_slots IREFSPARE] as ARGUMENTS   *)
(*     because those are the child's and live INSIDE                      *)
(*     [UsertrapRes.ut_own_nopt] rather than beside it -- a closer that    *)
(*     did not take them would leave the park holding two resources with   *)
(*     nowhere to put them and its supplier owing two it does not have.    *)
(*                                                                        *)
(* SO EXACTLY ONE ROW HAS NO SOURCE: [bslots 3], the first       *)
(* conjunct of [UsertrapRes.ut_own_nopt].  (The [initproc] share that used *)
(* to sit beside it is DONE: userint discards the cell right after its     *)
(* store, so every later reader takes it persistently.)  The pool has room *)
(* -- [BSLOTS = 1024] against [3 * NPROC = 192] plus main's 35 -- but the  *)
(* authority [BioInv.bslots_auth] lives inside [bcache_res], behind the    *)
(* bcache lock, so a bystander cannot mint fragments from persistent facts.*)
(* THE NATURAL FIX IS NOT A WP STEP: [ProcDefs.proc_dormant] already parks *)
(* [fd_slots FDSPARE] and [iref_slots (1 + IREFSPARE)] per slot, and three *)
(* bio slots belong in exactly the same place, carved once at procinit --  *)
(* whereupon allocproc hands them out with everything else and BOTH        *)
(* callers can pay this contract in full.                                  *)
(* ====================================================================== *)

From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language weakestpre lifting.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto.
Require Import KernelText WireInv.
Require Import KptExecMap.
Require Import StackOwn.
Require Import IntrDefs.
Require Import UserPtTree UserExec.
Require Import ProcGeom.
Require Import ProcDefs.
Require Import ProcPtOwn.
Require Import SwtchCtx.
Require Import FdSlots.
Require Import FileInvDefs.
Require Import IrefSlots.
Require Import ProcAvail.
Require Import ProcInv.
Require Import SchedCtx.
Require Import UsertrapRes.
Require Import FsReady.
Require Import FirstTok.
Require Import SpecUsertrap.
Require Import SpecForkret.
Require Import SpecForkretPark.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Local Open Scope Z_scope.

Definition forkret_park_pkg
    `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ, !irefslotG Σ, !pavG Σ} `{GEN : GenId}
    (* the trap loop's kernel-side bundle, abstract exactly as [SpecForkret]
       takes it *)
    (URes : CpuId -> uptd -> mword 64 -> iProp Σ)
    (γs : list gname) (γf : gname) (pa ks : mword 64)
    (pid : mword 32) (av : nat) : iProp Σ :=
  (* [ksp] is spelled out rather than [let]-bound: this bundle is DESTRUCTED
     by its consumer, and a [let] survives [rewrite /forkret_park_pkg]. *)
  ((* ---- the persistent world the parked closure captures ---- *)
   kernel_text ∗
   wire_inv ∗
   kmap_at tramp_vpn tramp_ppn KP_rx ∗
   procs_inv γs ∗
   pslot_used_at pa ∗
   (* ---- the child's kernel stack, free below its top ---- *)
   stack_own (KTR := KT1) (add_vec ks (mword_of_int 4096)) av ∗
   (* ---- the residue closer, at every hart the record may resume on.
          It takes the two ALLOWANCES the park's own arguments carry
          ([fd_slots FDSPARE] / [iref_slots IREFSPARE]): those are the
          child's, they are inside the trap loop's bundle
          ([UsertrapRes.ut_own_nopt]) rather than beside it, and the record
          is where they get captured -- so a closer that did not take them
          would leave the park holding two resources with nowhere to put
          them and its supplier owing two it does not have. ---- *)
   (* QUANTIFIED OVER THE DESCRIPTOR, exactly as forkret's own closer is
          (SpecForkret.v, "THE RESIDUE IS A CLOSER"): the boot arm's kexec
          replaces the address space, so the table userret runs on is not
          the one forkret was entered with.  The two page-table facts are
          HANDED to this wand rather than taken as premises of the park --
          forkret proves them of the descriptor it actually ends on. *)
   (* ...AND IT IS HANDED [FirstTok.first_done], which is the whole reason
          this package is payable at all.  [UsertrapRes.ut_caps] carries
          [fs_ready] as a conjunct, the syscall environment is derived from
          it, and that environment's LAST conjunct is [first_done] -- whose
          discarded [first_addr ↦₄□ 0] half is minted by exactly one
          instruction in the kernel, the release store on forkret's own boot
          arm.  So a closer that had to OWN either could not be built by
          userinit, which parks the very process that runs that store.
          forkret pays both instead (SpecForkret.v, "...AND THE CLOSER IS
          HANDED [first_done]") and the builder here owes only the
          persistent rows neither supplies. *)
   (∀ (h : CpuId) (pt' : uptd) (V' : pprivate),
      ⌜pv_upt V' = pt'⌝ -∗
      ⌜ud_data pt' = ud_pas pt'⌝ -∗
      ⌜proc_pt_wf pt'⌝ -∗
      FirstTok.first_done -∗
      forkret_yield (CID := h) γf pa (add_vec ks (mword_of_int 4096)) pid av V' -∗
      fd_slots FDSPARE -∗
      iref_slots IREFSPARE -∗
      URes h pt' (add_vec ks (mword_of_int 4096))))%I.

Definition forkret_park_paid_body
    `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ, !irefslotG Σ, !pavG Σ} `{GEN : GenId} `{CID : CpuId}
    (URes : CpuId -> uptd -> mword 64 -> iProp Σ)
    (γs : list gname) (γf : gname) (pa ks : mword 64) (rest : list (mword 64))
    (pid : mword 32) (V : pprivate) (av : nat) : Prop :=
  (length rest = 12%nat) ->
  (* the record is stored in [procs_inv]'s slot for [pa], so [pa] is one of
     the NPROC slots -- [SpecAllocproc]'s postcondition says which.  It is
     what identifies the dispatch payload's existential process with this
     one; the assumed form gets the same fact out of the payload itself,
     which it can afford to because it never has to USE the [j]. *)
  (exists j : nat, pa = proc_addr j /\ (j < NPROC)%nat) ->
  (* THE PARKED DEPTH, and it is ONE premise now.  A resumption is always
     at level 1 with interrupts off, but the record's resume wand is
     [∀ eb'] -- the RESUMER's base enable -- and forkret's budget equation
     is stated over that [eb'], so the depth must cover the ENABLED arm's
     reserve as well as forkret's own frame and its deepest callee's.  That
     callee is now KEXEC, not prepare_return: [6 + trap_res true + K_kexec
     = 6 + 90 + 184 = 280], which [K_usertrap = 342] already dominates.  So
     the second premise this used to carry is [lia]'s job, not a caller's.
       [KSTACK_AV = 342] too, which is not a coincidence: a caller that
     hands over a whole free kernel stack satisfies this exactly. *)
  (K_usertrap <= av)%nat ->
  (* ---- SpecUservec's two gaps, passed through one more tier ---- *)
  (forall ms_v : mword 64, trap_mstatus_ok ms_v ->
     sconf_ms_facts ms_v /\ _get_Mstatus_SPIE ms_v = ('b"1" : mword 1)) ->
  (forall (h : CpuId) (kr : mword 44) (ksp' : mword 64) (ws : list (mword 64)),
     length ws = TFWORDS -> tf_kernel_words_ok (CID := h) kr ksp' ws) ->
  ⊢ forkret_park_pkg URes γs γf pa ks pid av -∗
    is_kstack pa ks -∗
    ctx_cells (p_context pa) (forkret_pc :: add_vec ks (mword_of_int 4096) :: rest) -∗
    proc_priv γf pa pid V -∗
    fd_slots FDSPARE -∗
    iref_slots IREFSPARE -∗
    |==> ▷ proc_ctx γs pa.

Module Type FORKRET_PARK_PAID.
  (* the residue is the module-type parameter it is everywhere else *)
  (* ...AND THE PARK'S ONE PRODUCER-SIDE ENTRY, threaded with the rest.
     [UsertrapRes.USERTRAP_RES_PARK] is [USERTRAP_RES] plus
     [usertrap_res_bare_park]: the residue stays opaque to every CONSUMER,
     and the one party that has to BUILD one -- whoever parks a process that
     has never trapped -- gets a closer instead.  See that file's "THE
     PARK'S CHANNEL THROUGH THE MODULE TYPES". *)
  Include UsertrapRes.USERTRAP_RES_PARK.
  Parameter forkret_park_paid :
    forall `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ, !irefslotG Σ, !pavG Σ} `{GEN : GenId} `{CID : CpuId}
      (γs : list gname) (γf : gname) (pa ks : mword 64) (rest : list (mword 64))
      (pid : mword 32) (V : pprivate) (av : nat),
      forkret_park_paid_body (fun h : CpuId => usertrap_res_bare (CID := h))
        γs γf pa ks rest pid V av.
End FORKRET_PARK_PAID.
