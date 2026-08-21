(* SpecForkret.v -- forkret()'s contract (proc.c).  THE EXPERIMENTAL FIRST
   VERSION: the [first] branch is assumed away, not proved.

     void forkret(void) {
       extern char userret[];
       static int first = 1;
       struct proc *p = myproc();
       release(&p->lock);                      // still held from scheduler()
       if (__atomic_load_n(&first, __ATOMIC_ACQUIRE)) {
         fsinit(ROOTDEV); ...; kexec("/init", ...); ...
       }
       prepare_return();
       uint64 satp = MAKE_SATP(p->pagetable);
       ((void ( * )(uint64))(TRAMPOLINE + (userret - trampoline)))(satp);
     }


   @ KernelSyms.forkret, 166 bytes / 45 instructions (CodeForkret.v).

   ==== THE [first] BRANCH IS DECIDED BY A RESOURCE ======================

   This contract takes NO premise about [first] at all.  The branch at
   +0x24 is decided by [FirstTok.first_tok], which rides inside
   [ProcInv.proc_priv] -- so the process that runs forkret carries, in its
   own block, which arm of the [if] it is entitled to:

     - the BOOT arm ([first_addr ↦₄ 1] beside main's persistent rows, the
       sealed page count and fsinit's whole premise pile) reads 1, falls
       through, and runs fsinit / the release store / kexec("/init");

     - the STEADY arm ([first_addr ↦₄□ 0] beside [FsReady.fs_ready]) reads
       0, takes the [c.beqz], and the boot arm is dead.

   The two arms are incompatible at one address, so "at most one process
   ever boots the file system" is a theorem about ownership rather than a
   claim about scheduling.  [FirstTok.v]'s header is the design; nothing
   about it is visible here beyond the fact that [proc_priv] is enough.

   WHAT THE BOOT ARM COSTS THIS CONTRACT is [procs_inv γs] and
   [γs !! j = Some γl] -- fsinit's and kexec's cones reach sleep/wakeup,
   whose contracts take the process table.  Those two SUBSUME the
   [is_lock γl p s Rlk] this contract used to take: the lock forkret
   releases is the table's own slot [j], so [SchedCtx.procs_inv_lookup]
   produces it and the string and the resource stop being parameters.

   Everything else the boot arm spends -- the file system's whole premise
   pile, the allocator, the log's raw cells -- rides inside the token, not
   in this precondition.

   ==== THE BOOT ARM RUNS WITH INTERRUPTS OFF ============================

   AND THAT IS WHY IT IS NOT PROVED YET.  [eb] is NOT [true] here.  This
   revision's scheduler is

       intr_on();  intr_off();  ...  acquire(&p->lock);  swtch(...)

   so [push_off] reads SIE = 0 at [noff = 0] and leaves [cpus[h].intena = 0]
   -- and forkret's own [release] at +0x10 therefore does NOT re-enable
   interrupts.  fsinit, kexec and everything under them run at [eb = false].
   (Upstream xv6 has no [intr_off()] there and does boot with the base
   enable on; the [intr_on(); intr_off()] pair is this revision's wfi-race
   fix, and it moves forkret to the disabled index.)

   The consequence is a callee-side one, and it is exactly the case
   claude-notes/completed/eb-generic-sweep.md's last section anticipated:
   fsinit, initlog, ireclaim, kexec, namei, namex and dirlookup all still
   carry [eb = true ->], on the recorded grounds that every caller reaches
   them "from a syscall or from boot with an enabled base".  forkret's boot
   arm is the caller that does not.  Generalizing those seven -- drop the
   premise, thread [trap_csrs_ext eb] / [cpu_claim_ext eb pj] in and out --
   is the prerequisite, and that file is the recipe.

   THIS CONTRACT IS ALREADY RIGHT FOR IT.  forkret holds the complement:
   [arm_pay_ext_split] turns the caller's [trap_csrs ∗ cpu_claim] into
   release's [arm_pay 0 eb p] and the [_ext] pair, and the pair is live
   across exactly the stretch the boot arm occupies.  So nothing in this
   precondition has to change when the sweep lands -- which is why it takes
   no [eb] premise now.

   ==== forkret DOES NOT RETURN ==========================================

   The [c.jalr a5] at +0x8e enters userret at [TRAMPOLINE + 0x9c] with
   a0 = MAKE_SATP(p->pagetable), and userret sret's to user mode.  So the
   contract concludes in [WP Loop] directly, via
   [SpecUserretClosed.wp_userret_closed] -- the CLOSED trap loop, entered
   where the kernel first enters it.  Its two undischarged gaps (the
   mstatus one and the trapframe kernel-words one) are passed through
   verbatim; they are the same obligations one tier down, not new ones.

   THE KERNEL PAGE TABLE'S ROOT IS AN EXISTENTIAL HERE, which is why the
   kernel-words gap is quantified over it.  forkret reaches the table
   through [IntrDefs.strans_inv]'s KPT arm, whose root is existential (the
   sconf tier is deliberately root-free -- SpecPrepareReturn.v says the same
   about [kernel_satp]), and nothing else in this contract names it.

   ==== THE ENTRY IS THE SCHEDULER'S HAND-OFF ============================

   swtch lands here with p->lock STILL HELD from scheduler(), i.e. at
   push_off level 1 with interrupts off and "proc" in the held set -- which
   is exactly what [SwtchCtx.valid_context]'s resume wand delivers
   ([sie_cap_gpr m av false p], [cpu_own 1 eb p false {["proc"]}]) plus
   [SchedCtx.p_sched]'s own [trap_csrs].  [release] is forkret's first act
   and the whole of the index bookkeeping: [arm_pay_ext_split] turns the
   caller's [trap_csrs ∗ cpu_claim p] into release's [arm_pay 0 eb p] and
   prepare_return's [trap_csrs_ext eb ∗ cpu_claim_ext eb p], so the contract
   is generic in the base-enable [eb] and no arm needs a case split.

   ==== THE RESIDUE IS A CLOSER, NOT A PREMISE ===========================

   The trap loop runs on [SpecUsertrap]'s kernel-side bundle [URes] (=
   [usertrap_res_bare]), and forkret cannot BUILD one: the bundle is the
   union of five cones' environments (the file table, the log, the device
   caps, the syscall environment...) and forkret touches none of them.
   What forkret DOES hold is the running state of a kernel thread -- the
   stack, the per-cpu bundle, the trap ghosts, the process block -- and
   those are the bundle's OTHER half, so a contract taking [URes] beside
   them would claim each of them twice and be unsatisfiable.

   The premise is therefore the WAND: hand back what forkret's tail can
   produce ([UsertrapRes.ut_trap_parked] and the process block minus its
   page table) and get the bundle.  It is quantified over the hart because
   prepare_return parks, over the process record because prepare_return
   moves the trapframe, and OVER THE DESCRIPTOR because the boot arm's
   kexec REPLACES the address space -- the table userret runs on is not the
   one forkret was entered with, so no [pt] fixed on entry can name both.
   The two facts the switch inside userret needs of that descriptor
   ([SpecUserretClosed.loop_ok]'s pt-side conjuncts) are HANDED to the
   closer rather than taken as premises: [proc_pt_wf] is a conjunct of
   [ProcPtOwn.proc_pt] and so already inside [proc_priv], and the
   normalisation equation is discharged here with [ProcPtOwn.ud_norm], the
   same renormalisation every round of the trap loop performs.  When
   [SpecForkretPark]'s axiom is finally discharged, the caller that parks
   the process is the one that proves this wand.

   The address space itself is NOT in the wand: forkret splits [proc_pt]
   off the block ([ProcInv.proc_priv_split_pt]) and hands it to the user
   tier the way uservec's tail does, which is why the bare residue is the
   right target. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import RiscvLang RiscvPtsto.
Require Import RegFile.
Require Import InstrBytes WireInv.
Require Import KernelText.
Require Import KptExecMap.
Require Import UserPtTree UserExec.
Require Import IntrDefs.
Require Import WpLock.
Require Import CpuOwn.
Require Import ProcGeom.
Require Import FdSlots FileInvDefs.
Require Import ProcInv ProcPtOwn.
Require Import SchedCtx.   (* [procs_inv] / [proc_lock_res] -- p->lock is the table's slot [j] *)
Require Import IrefSlots ProcAvail.
Require Import SpecPrepareReturn.
Require Import SpecKexec.
Require Import SpecUsertrap.
Require Import UsertrapRes.
From Kernel Require KernelSyms.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Local Open Scope Z_scope.
Import Defs.

(* forkret's own 48-byte frame is 6 slots; below it the deepest callee is
   kexec's (the boot arm's), which subsumes prepare_return's 12, myproc's
   and release's 10.  Written as an expression so a change to a callee's
   budget cannot silently leave this one behind. *)
Notation K_forkret := ((6 + K_kexec)%nat) (only parsing).
Section SpecForkret.
  Context `{!riscvGS Σ, !xv6G Σ, !fdslotG Σ, !fileG Σ, !irefslotG Σ, !pavG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  (* WHAT forkret'S TAIL HANDS THE TRAP LOOP.  [ut_trap_parked] is the
     trap-side residue with the translation slot dropped (the switch inside
     userret takes it) and the address space still to come; the process
     block arrives WITHOUT its page table, which forkret has already given
     to the user tier.  Together they are everything
     [UsertrapRes.ut_res_bare] wants except the five cones' environment --
     which is the caller's to supply, and the reason this is a wand. *)
  Definition forkret_yield (γf : gname) (p ksp : mword 64) (pid : mword 32)
      (av : nat) (V : pprivate) : iProp Σ :=
    (ut_trap_parked p ksp av ∅ ∗ proc_priv_nopt γf p pid V)%I.

End SpecForkret.

(* THE CONTRACT.  One statement, no [first] premise and no [first] reading:
   the branch is decided by [FirstTok.first_tok] inside [proc_priv].  See
   the header for the three premises the boot arm costs and for why the
   descriptor is not a parameter. *)
Definition wp_forkret_gen_body
    `{!riscvGS Σ, !xv6G Σ, !fdslotG Σ, !fileG Σ, !irefslotG Σ, !pavG Σ} `{GEN : GenId} `{CID : CpuId}
    (* the trap loop's kernel-side bundle, abstract exactly as
       [SpecUserretClosed] takes it *)
    (URes : CpuId -> uptd -> mword 64 -> iProp Σ)
    (j : nat) (γs : list gname) (γl γf : gname)
    (pid : mword 32) (V : pprivate)
    (ks : mword 64) (m : regfile) (av av2 : nat) (eb : bool) :=
  let pcE : mword 64 := mword_of_int KernelSyms.forkret in
  let p   : mword 64 := proc_addr j in
  let ksp : mword 64 := add_vec ks (mword_of_int 4096) in
  (j < NPROC)%nat ->
  (* the slot this process's lock is, which is what makes [procs_inv] below
     name p->lock rather than merely some lock *)
  γs !! j = Some γl ->
  (* THE BUDGET.  The 6-slot frame comes off the top; what is left has to
     cover prepare_return, and what the whole function leaves behind (the
     frame merged back in, since forkret never runs its epilogue) has to
     cover a trap round -- which is the loop's own requirement, not
     forkret's.  Stated as an equation on [av2] rather than a subtraction so
     the index arithmetic below is syntactic. *)
  (trap_res eb + av2)%nat = (av - 6)%nat ->
  (* THE DEEPEST CALLEE IS kexec'S, on the boot arm -- which is what
     [K_forkret = 6 + K_kexec] above has always said.  prepare_return's 12 is
     subsumed. *)
  (K_kexec <= av2)%nat ->
  (K_usertrap <= av)%nat ->
  (* calling convention: swtch restored sp to the kernel stack TOP *)
  m !!! Regidx (mword_of_int 2 : mword 5) = ksp ->
  (* ---- SpecUservec's two gaps, passed through -- see the header on why
         the kernel root is quantified here ---- *)
  (forall ms_v : mword 64, trap_mstatus_ok ms_v ->
     sconf_ms_facts ms_v /\ _get_Mstatus_SPIE ms_v = ('b"1" : mword 1)) ->
  (forall (h : CpuId) (kr : mword 44) (ksp' : mword 64) (ws : list (mword 64)),
     length ws = TFWORDS -> tf_kernel_words_ok (CID := h) kr ksp' ws) ->
  kernel_text -∗
  wire_inv -∗
  kmap_at tramp_vpn tramp_ppn KP_rx -∗
  pc_is pcE -∗
  (* the process table: [is_lock] for the lock released at +0x10, and what
     fsinit's and kexec's cones take for sleep/wakeup *)
  procs_inv γs -∗
  (* ---- the running kernel thread, as swtch left it ---- *)
  sie_cap_gpr KT1 m av false p -∗
  cpu_own 1%nat eb p false {["proc"%string]} -∗
  trap_csrs KT1 -∗
  cpu_claim p -∗
  (* ---- p->lock, still held from scheduler() ---- *)
  locked γl cpu_id -∗
  proc_lock_res γs γl p -∗
  (* ---- the process ---- *)
  is_kstack p ks -∗
  proc_priv γf p pid V -∗
  (* ---- the residue closer -- see the header ---- *)
  (∀ (h : CpuId) (pt' : uptd) (V' : pprivate),
     ⌜pv_upt V' = pt'⌝ -∗
     ⌜ud_data pt' = ud_pas pt'⌝ -∗
     ⌜proc_pt_wf pt'⌝ -∗
     forkret_yield (CID := h) γf p ksp pid av V' -∗
     URes h pt' ksp) -∗
  WP (Loop : expr riscv_lang).

(* The residue is the module-type parameter it is everywhere else: forkret's
   tail runs [SpecUserretClosed]'s theorem, which is stated at
   [usertrap_res_bare] and at nothing else, so this contract is too. *)
Module Type FORKRET.
  Include SpecUsertrap.USERTRAP_RES.
  Parameter wp_forkret :
    forall `{!riscvGS Σ, !xv6G Σ, !fdslotG Σ, !fileG Σ, !irefslotG Σ, !pavG Σ} `{GEN : GenId} `{CID : CpuId}
      (j : nat) (γs : list gname) (γl γf : gname)
      (pid : mword 32) (V : pprivate)
      (ks : mword 64) (m : regfile) (av av2 : nat) (eb : bool),
      wp_forkret_gen_body (fun h : CpuId => usertrap_res_bare (CID := h))
        j γs γl γf pid V ks m av av2 eb.
End FORKRET.
