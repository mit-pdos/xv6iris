(* SpecForkretParkPaid.v -- the PARK, WITH ITS PREMISES PAID: the same
   statement [SpecForkretPark.v] assumes, in the form that is a THEOREM
   ([ProofForkretPark.v], out of forkret's own contract).

   A separate file rather than more of [SpecForkretPark.v] for the reason
   durable-notes.md gives for any additive change to a shared file: the
   assumed contract sits under the whole kfork cone and must stay light,
   while this one names the trap loop's residue and therefore drags in
   [SpecForkret] / [UsertrapRes] / the five cones behind them.  Nothing in
   the kfork cone should recompile because this statement moved. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language weakestpre lifting.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto.
Require Import RegFile.
Require Import SmodeCore.
Require Import KernelText WireInv.
Require Import KptExecMap.
Require Import StackOwn.
Require Import IntrDefs.
Require Import UserPtTree UserExec.
Require Import WpLock.
Require Import ProcGeom.
Require Import ProcDefs.
Require Import ProcPtOwn.
Require Import SwtchCtx.
Require Import FdSlots.
Require Import FileInvDefs.
Require Import IrefSlots InodeRegion.
Require Import DiskPtsto WpUart FsBlocks LogInv FsCrash KallocInv BioDefs.
Require Import ProcAvail.
Require Import ProcInv.
Require Import SchedCtx.
Require Import SpecPrepareReturn.
Require Import UsertrapRes.
Require Import SpecUsertrap.
Require Import SpecForkret.
Require Import SpecForkretPark.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Local Open Scope Z_scope.

(* ====================================================================== *)
(* THE SAME PARK WITH ITS PREMISES PAID -- i.e. PROVED, from forkret.      *)
(*                                                                        *)
(* [ProofForkretPark.v] discharges the statement below out of              *)
(* [SpecForkret.wp_forkret_nf_body] (forkret's contract minus the [first]  *)
(* premise, assumed in [LinkForkretNF.v]): unfold the [valid_context]      *)
(* fixpoint, and its resume wand IS forkret's precondition, once the       *)
(* scheduler's dispatch payload ([SchedCtx.p_sched]'s second disjunct) is  *)
(* read for the pieces the C code's [release(&p->lock)] gives back.        *)
(*                                                                        *)
(* WHAT THE PARK COSTS BEYOND [SpecForkretPark.forkret_park_body], and why *)
(* that difference is exactly why the assumed form is still what           *)
(* [ProofKfork.v] uses.  A record must be paid for at the moment it is     *)
(* BUILT, and the thread it promises has not run yet, so its creator owes  *)
(* everything the first trap round will consume:                           *)
(*                                                                        *)
(*   - [stack_own ksp av] -- the child's KERNEL STACK, free.  A running    *)
(*     thread carries its stack inside [sie_cap_gpr] and a parked one      *)
(*     inside its record ([SwtchCtx.valid_context_pre]); a never-run one   *)
(*     has it nowhere.  procinit maps the NPROC KSTACK pages and           *)
(*     [SpecAllocproc]'s postcondition hands out [is_kstack] (the          *)
(*     persistent [p->kstack] agreement) but not the words, so this is a   *)
(*     real hole in the chain and not bookkeeping.                         *)
(*   - THE RESIDUE CLOSER -- the wand that turns what forkret's tail       *)
(*     yields into the trap loop's kernel-side bundle.  It is forkret's    *)
(*     own premise, verbatim (SpecForkret.v's THE RESIDUE IS A CLOSER,     *)
(*     NOT A PREMISE section), and it is where the child's share of the    *)
(*     five cones' environment has to come from.  LESS OF THAT IS MISSING  *)
(*     THAN IT LOOKS: [ut_caps] and [ProofSyscall.syscall_env] are both    *)
(*     entirely PERSISTENT, so a second process's copy of either costs     *)
(*     nothing, and [fd_slots]/[iref_slots]/[proc_priv] are arguments of   *)
(*     the park already.  What has no source today is [bslots bn 3] (a     *)
(*     draw from the finite BSLOTS pool), [fileclose_bm], and the          *)
(*     [initproc] share.                                                   *)
(*   - the persistent world ([kernel_text], [wire_inv], the trampoline's   *)
(*     kernel mapping, [procs_inv], the slot's allocation marker) -- free  *)
(*     for any caller, but it has to be NAMED, because the record's        *)
(*     continuation is a closure and a closure captures what it uses.      *)
(*   - the two pure gaps [SpecUservec] still passes through, and the two   *)
(*     page-table facts [SpecUserretClosed]'s switch needs.                *)
(*                                                                        *)
(* So the honest statement of "a fresh process can be parked" is this one, *)
(* and it is a THEOREM.  What is not yet available is a CALLER that can    *)
(* pay [forkret_park_pkg]; until kfork's own contract carries the child's  *)
(* half of the trap environment, [SpecForkretPark.FORKRET_PARK] stays      *)
(* assumed.                                                               *)
(* ====================================================================== *)

Definition forkret_park_pkg
    `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !fileG Σ, !bioG Σ,
      !diskGhostG Σ, !uartGhostG Σ, !fsLogG Σ, !logG Σ, !fsCrashG Σ,
      !kallocG Σ, !irefslotG Σ, !pavG Σ, !iregG Σ}
    `{GEN : GenId}
    (* the trap loop's kernel-side bundle, abstract exactly as [SpecForkret]
       takes it *)
    (URes : CpuId -> uptd -> mword 64 -> iProp Σ)
    (γs : list gname) (γf : gname) (pa ks : mword 64)
    (pid : mword 32) (V : pprivate) (av : nat) : iProp Σ :=
  (* [ksp] is spelled out rather than [let]-bound: this bundle is DESTRUCTED
     by its consumer, and a [let] survives [rewrite /forkret_park_pkg]. *)
  ((* ---- the persistent world the parked closure captures ---- *)
   kernel_text ∗
   wire_inv ∗
   kmap_at tramp_vpn tramp_ppn KP_rx ∗
   procs_inv γs ∗
   pslot_used_at pa ∗
   (* ---- the child's kernel stack, free below its top ---- *)
   stack_own (add_vec ks (mword_of_int 4096)) av ∗
   (* ---- the residue closer, at every hart the record may resume on.
          It takes the two ALLOWANCES the park's own arguments carry
          ([fd_slots FDSPARE] / [iref_slots IREFSPARE]): those are the
          child's, they are inside the trap loop's bundle
          ([UsertrapRes.ut_own_nopt]) rather than beside it, and the record
          is where they get captured -- so a closer that did not take them
          would leave the park holding two resources with nowhere to put
          them and its supplier owing two it does not have. ---- *)
   (∀ (h : CpuId) (V' : pprivate),
      ⌜pv_upt V' = pv_upt V⌝ -∗
      forkret_yield (CID := h) γf pa (add_vec ks (mword_of_int 4096)) pid av V' -∗
      fd_slots FDSPARE -∗
      iref_slots IREFSPARE -∗
      URes h (pv_upt V) (add_vec ks (mword_of_int 4096))))%I.

Definition forkret_park_paid_body
    `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !fileG Σ, !bioG Σ,
      !diskGhostG Σ, !uartGhostG Σ, !fsLogG Σ, !logG Σ, !fsCrashG Σ,
      !kallocG Σ, !irefslotG Σ, !pavG Σ, !iregG Σ}
    `{GEN : GenId} `{CID : CpuId}
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
  (* THE PARKED DEPTH.  A resumption is always at level 1 with interrupts
     off, but the record's resume wand is [∀ eb'] -- the RESUMER's base
     enable -- and forkret's budget equation is stated over that [eb'], so
     the depth has to cover the ENABLED arm's reserve as well as forkret's
     own frame and prepare_return's; and the loop it hands off to wants
     [K_usertrap]. *)
  (K_usertrap <= av)%nat ->
  (6 + trap_res true + K_prepare_return <= av)%nat ->
  (* the two page-table facts userret's switch needs -- [SpecForkret]'s, and
     stated here at [pv_upt V] because the record fixes the process *)
  ud_data (pv_upt V) = ud_pas (pv_upt V) ->
  proc_pt_wf (pv_upt V) ->
  (* ---- SpecUservec's two gaps, passed through one more tier ---- *)
  (forall ms_v : mword 64, trap_mstatus_ok ms_v ->
     sconf_ms_facts ms_v /\ _get_Mstatus_SPIE ms_v = ('b"1" : mword 1)) ->
  (forall (h : CpuId) (kr : mword 44) (ksp' : mword 64) (ws : list (mword 64)),
     length ws = TFWORDS -> tf_kernel_words_ok (CID := h) kr ksp' ws) ->
  ⊢ forkret_park_pkg URes γs γf pa ks pid V av -∗
    is_kstack pa ks -∗
    ctx_cells (p_context pa) (forkret_pc :: add_vec ks (mword_of_int 4096) :: rest) -∗
    proc_priv γf pa pid V -∗
    fd_slots FDSPARE -∗
    iref_slots IREFSPARE -∗
    |==> ▷ proc_ctx γs pa.

Module Type FORKRET_PARK_PAID.
  (* the residue is the module-type parameter it is everywhere else *)
  Include SpecUsertrap.USERTRAP_RES.
  Parameter forkret_park_paid :
    forall `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !fileG Σ, !bioG Σ,
             !diskGhostG Σ, !uartGhostG Σ, !fsLogG Σ, !logG Σ, !fsCrashG Σ,
             !kallocG Σ, !irefslotG Σ, !pavG Σ, !iregG Σ}
      `{GEN : GenId} `{CID : CpuId}
      (γs : list gname) (γf : gname) (pa ks : mword 64) (rest : list (mword 64))
      (pid : mword 32) (V : pprivate) (av : nat),
      forkret_park_paid_body (fun h : CpuId => usertrap_res_bare (CID := h))
        γs γf pa ks rest pid V av.
End FORKRET_PARK_PAID.
