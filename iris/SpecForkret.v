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
   +0x24 is decided by [FirstTok]'s two arms, which the process that runs
   forkret carries -- so it holds, as a resource, which arm of the [if] it
   is entitled to:

     - the BOOT arm ([FirstTok.first_boot]: [first_addr ↦₄ 1] beside
       main's persistent rows, the sealed page count and fsinit's whole
       premise pile) reads 1, falls through, and runs fsinit / the release
       store / kexec("/init");

     - the STEADY arm ([first_addr ↦₄□ 0] beside [FsReady.fs_ready]) reads
       0, takes the [c.beqz], and the boot arm is dead.

   The two arms are incompatible at one address, so "at most one process
   ever boots the file system" is a theorem about ownership rather than a
   claim about scheduling.  [FirstTok.v]'s header is the design.  WHICH ARM
   IS THE PACKAGE'S MODE: a boot-mode record carries [first_boot] as rows
   of its own beside the block minus its token, and a steady-mode one
   carries the block whole plus [FirstTok.first_done] -- the block premise
   below is that [if], and it is what makes the two modes' arms decidable
   here.

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
   right target.

   ==== ...AND THE CLOSER IS HANDED [first_done] =========================

   THE CLOSER'S BODY NEEDS THE FILE SYSTEM AND ITS BUILDER CANNOT HAVE IT.
   [UsertrapRes.ut_caps] carries [FsReady.fs_ready] as a conjunct, and the
   syscall environment the residue's other half needs is derived from it
   too -- so whoever proves this wand has to produce [fs_ready].  The two
   places a process is parked from scratch are userinit and kfork, and AT
   USERINIT'S PARK [fs_ready] DOES NOT EXIST YET: forkret's boot arm is
   what establishes it (fsinit, then [FsReady.fs_ready_establish]), and
   that runs strictly after userinit has parked the first process.  So the
   obligation is unprovable at the site that owes it.

   That is an ordering fact, not a plumbing gap, and the fix is to move the
   resource rather than the proof: the closer takes it as an ARGUMENT.
   forkret is exactly the place that can pay, on both arms and for the same
   reason the branch exists at all --

     - the STEADY arm reads it straight out of [FirstTok.first_tok]'s
       steady disjunct, which IS this resource, persistent, so putting the
       token back into the block costs nothing;
     - the BOOT arm mints it itself -- [fs_ready_establish] at the release
       store at +0x38, beside the [first_addr ↦₄□ 0] that same store
       discards -- and holds it to the [c.jalr].

   THE ARGUMENT IS [FirstTok.first_done], NOT [fs_ready], and the extra
   half is load-bearing rather than convenient.  [ProofSyscall.syscall_env]
   has FOUR conjuncts and its last is [first_done] itself -- the steady arm
   of proc.c's [static int first], which fork hands to every child.  Its
   [first_addr ↦₄□ 0] half is minted by exactly one instruction in the
   kernel, the release store on forkret's boot arm, so a closer given only
   [fs_ready] would still be missing a row that userinit -- which parks the
   very process that will run that store -- could not possibly supply.
   [first_done] is what both arms hold and is what closes the environment.

   So the wand's builder owes only what it can have: the persistent rows
   [first_done] does NOT supply ([is_ftable], the [wait_lock], the ticks
   lock, [devintr_caps_any], [procs_avail], [console_ready], the nextpid
   lock), all of which main creates before userinit runs and all of which
   kfork's parent already holds.

   ==== THE PARK HAS TWO MODES, AND forkret DECIDES WHICH IS LIVE ========

   The closer hands back a slot for the record forkret resumes with, and
   the party that has to OWN that slot is the parker.  What it can own
   depends on whether the boot arm can still run:

     - [steady = false] -- THE BOOT MODE.  It can, and it does: this record
       IS the first process, which the package says by carrying
       [FirstTok.first_boot]'s rows beside a block without them.
       kexec("/init") replaces the address space between the park and the
       resume, so no key captured at the park is still the resume's; what
       the parker owns instead is the EXEC BUNDLE that arm spends
       ([InitBoot.init_boot_bundle]), whose slot piece answers at the key
       kexec builds.  The closer owes no slot, and the kernel mints none
       (userinit).

     - [steady = true] -- THE STEADY MODE.  The boot arm cannot run, and the
       parker proves it by handing over [FirstTok.first_done].  Then the
       resume is the steady arm, which lands on a record carrying the parked
       one's RUN KEY -- the resume register file, the resume pc, the image,
       the permission view, the size and the cwd ([UexecRet.urun_eq]) -- so
       ONE slot at the parked record suffices and the closer's pure premise
       re-keys it (kfork).

   forkret is where the promise is cashed, and it cases on the MODE: at
   [true] its steady arm PROVES the run key of the record it ends on and
   its boot arm is REFUTED, because [first_done]'s [first_addr ↦₄□ 0]
   cannot coexist with the block token's boot disjunct
   ([FirstTok.first_tok_boot_excl]); at [false] it walks the boot arm on
   the rows the package handed it.  That is why the bit, the block's shape
   and the mode's resource are premises HERE and not in the closer. *)
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
Require Import UserPtTree.
Require Import IntrDefs.
Require Import WpLock.
Require Import CpuOwn.
Require Import ProcGeom.
Require Import FdSlots FileInvDefs.
Require Import ProcInv ProcPtOwn.
Require Import SchedCtx.   (* [procs_inv] / [proc_lock_res] -- p->lock is the table's slot [j] *)
Require Import IrefSlots ProcAvail.
Require Import KexecDefs.
Require Import UsertrapRes UtResFits.
Require Import FirstTok.   (* [first_done] -- the one thing the closer takes, see the header *)
Require Import UexecSlot.  (* [uvis] / [uvis_of] *)
Require Import InitBoot.   (* [init_boot_bundle] -- the first process's exec
                              bundle, which the boot arm spends *)
Require Import UexecRet.   (* [uslot] -- the closer's new second output.
                              Required DIRECTLY: the seal does not travel. *)
From Kernel Require KernelSyms.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Local Open Scope Z_scope.
Require Import TsoCtx.
Import Defs.

(* forkret's own 48-byte frame is 6 slots; below it the deepest callee is
   kexec's (the boot arm's), which subsumes prepare_return's 12, myproc's
   and release's 10.  Written as an expression so a change to a callee's
   budget cannot silently leave this one behind. *)
Notation K_forkret := ((6 + K_kexec)%nat) (only parsing).
Require Import UserFd.   (* [ufdG] -- the class a minted user slot needs *)
Require Import UexecSG.   (* [uexecSG] / [uprogSG]: the ARM deposit class *)

Section SpecForkret.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ, !irefslotG Σ, !pavG Σ}.
  Context `{!ufdG Σ}.
  Context `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}.
  Context `{SG : uexecSG Σ}.

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

(* THE RESIDUE CLOSER, SEALED IN A NAME.  Spelled inline it is ~13 % of
   the Iris context of every step of ProofForkret's three walks -- and a
   proofmode step's term mentions the whole context twice, so an inline
   20-line wand is paid ~1300 times over.  It is one [Definition] and
   stays TRANSPARENT: [fkr_tail] applies it with [iDestruct ("Hyield" $!
   ...)], which unifies through a transparent constant and fails through
   an opaque one (claude-notes/optimization.md, "Fold block continuations
   into named definitions"). *)
Definition forkret_closer
    `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ, !irefslotG Σ, !pavG Σ} `{GEN : GenId} `{XI : CurCtx}
    (URes : CpuId -> CurCtx -> uptd -> mword 64 -> ustate -> list fdstate -> iProp Σ)
    (W : iProp Σ) (γs : list gname) (γw γft γf γtl : gname) (p ksp : mword 64)
    (* the parked process's fd-state ghost name *)
    (g : gname)
    (* ...and its cwd's inum -- see [ParkCap.park_pkg] *)
    (cw : Z)
    (* ...and its descriptor states: ONE list for the residue the closer
       yields and for the key it yields it at -- see [ParkCap.park_pkg],
       whose parameter this is *)
    (sts : list fdstate)
    (* ...AND THE PARKED RUN KEY, WHEN THERE IS ONE.  [None] is the BOOT
       mode: the resume runs the boot arm's kexec("/init"), no key captured
       at the park survives that, and the record's slot comes out of exec
       instead -- so this closer yields none.  [Some Wk]: the parker holds
       [FirstTok.first_done], the boot arm is dead, and what it captured is
       ONE slot at [Wk] -- so the closer's pure premise below asks the
       resumer to say that the record it resumes with carries that run key.
       [ParkCap.park_pkg] is the package this closer is a row of. *)
    (Wk : option uvis)
    (pid : mword 32) (av : nat) : iProp Σ :=
  (∀ (h : CpuId) (Xc : CurCtx) (pt' : uptd) (U' : ustate),
     ⌜pv_upt (us_V U') = pt'⌝ -∗
     ⌜ud_data pt' = ud_pas pt'⌝ -∗
     ⌜proc_pt_wf pt'⌝ -∗
     (* ...and the fd-state ghost name the resumed record carries.  The
        closer's builder captured the process's fragment bundle at the
        PARKED record's name, so it needs to know the resumed one agrees --
        no step between park and resume reassigns a live process's
        descriptor ghost.  See [SpecForkretParkPaid.forkret_park_pkg]. *)
     ⌜pv_fdg (us_V U') = g⌝ -∗
     (* ...and the resumed record is at the parked process's working
        directory: the slot row the parker captured is restricted to it *)
     ⌜pv_cwi (us_V U') = cw⌝ -∗
     (* ...AND, ON THE STEADY MODE, THAT THE RESUMED RECORD CARRIES THE
        PARKED RUN KEY: the resume register file, the resume pc, the image,
        the permission view, the size and the working directory
        ([UexecRet.urun_eq]) -- everything the slot reads of its key but the
        descriptor view, which the closer's own existential names.  forkret
        proves it of the record it ends on: prepare_return moves only the
        four kernel trapframe words ([TfUser.tf_ueq]), [us_M] does not move,
        [ud_um (ud_norm P) = ud_um P], and neither the size nor the cwd is
        touched.  [None] asks nothing -- that mode's closer instantiates a
        family. *)
     ⌜match Wk with Some W0 => urun_eq W0 U' | None => True end⌝ -∗
     (* THE RESUMER'S OWN GLOBALS, at ITS context -- forkret holds them and
        hands them in, exactly as it does [first_done] and [timer_cap]
        (UsertrapRes.v, the park half; L8, A12.19). *)
     UsertrapRes.park_globals Xc γs γw γft γf γtl -∗
     (* THE TRAPFRAME'S KERNEL WORDS, at the resuming hart: prepare_return
        wrote them there and [V'] is the descriptor it handed back, so this
        is forkret's to pay -- see [UsertrapRes.ut_tfk]. *)
     UsertrapRes.ut_tfk (CID := h) ksp (us_V U') -∗
     (* THE FILE SYSTEM AND THE SEALED [first] CELL, HANDED TO THE CLOSER
        RATHER THAN HELD BY IT.  [FirstTok.first_done] is exactly
        [first_addr ↦₄□ 0 ∗ fs_ready] -- see the header's last section for
        why the closer's builder cannot own either half. *)
     FirstTok.first_done (XI := Xc) -∗
     W -∗
     (* THE RESUMING HART'S TIMER CAPABILITY.  It is a conjunct of
        [IntrDefs.sie_cap] now (see the note there), so the residue cannot
        assemble the kernel bundle at the trap without one -- and it must be
        THIS hart's, which is why it is supplied PER APPLICATION rather than
        owned by the closer: a record parked before that hart ever booted
        could not hold it.  forkret has one, out of the very capability it
        is about to hand back. *)
     TimerCap.timer_cap (CID := h) -∗
     forkret_yield (CID := h) (XI := Xc) γf p ksp pid av (us_V U') -∗
     (* THE RESIDUE, AND -- ON THE STEADY MODE -- THE SLOT FOR THE RECORD
        THIS RESUME LANDS ON.  At [Wk = Some _] the parker captured ONE
        slot and the run-key premise above re-keys it onto this record.  At
        [Wk = None] the closer yields no slot at all: the boot arm's kexec
        moves the key (projects/user-wp-slot.md SS4c, R-b) and the slot
        that record runs on is exec's own receipt, paid by the exec bundle
        the package handed that arm.  See [ParkCap.park_pkg], of which this
        is the forkret-side spelling; one [sts] for the residue's fragments
        and the slot's key, and it is the package's argument. *)
     (URes h Xc pt' ksp U' sts
      ∗ match Wk with
        | Some _ => uslot (uvis_of U' sts)
        | None => emp
        end))%I.


(* THE CONTRACT.  One statement, no [first] premise and no [first] reading:
   the branch is decided by [FirstTok.first_tok] inside [proc_priv].  See
   the header for the three premises the boot arm costs and for why the
   descriptor is not a parameter. *)
Definition wp_forkret_gen_body
    `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ, !irefslotG Σ, !pavG Σ} `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}
    (* the trap loop's kernel-side bundle, abstract exactly as
       [SpecUserretClosed] takes it *)
    (URes : CpuId -> CurCtx -> uptd -> mword 64 -> ustate -> list fdstate -> iProp Σ)
    (* WHAT THE RESIDUE CLOSER IS HANDED BESIDE [first_done] -- the park
       token ([ParkCap.park_token]) in practice, abstract here: forkret
       holds it ([W -∗] below), reads nothing off it, and hands it to the
       closer at its tail.  The parker holds it only under a later, so the
       package cannot carry it outright; see ParkCap.v. *)
    (W : iProp Σ)
    (j : nat) (γs : list gname) (γl γw γft γf γtl : gname)
    (pid : mword 32) (U : ustate)
    (* THE PARKED DESCRIPTOR STATES: the closer's, and -- on the boot arm --
       the list kexec builds its resume key at.  [ParkCap.park_pkg]'s
       argument. *)
    (sts : list fdstate)
    (ks : mword 64) (m : regfile) (av av2 : nat) (eb : bool)
    (* WHICH OF THE PARK'S TWO MODES built this record.  [true]: the parker
       held [FirstTok.first_done] and captured ONE slot, at the parked
       record's run key -- so it owes forkret that resource (the row below)
       and forkret owes the closer the run key of the record it resumes
       with.  The key is [uvis_of U []]: the projection of the very record
       forkret is entered at, at a placeholder descriptor view, since
       [UexecRet.urun_eq] does not read one.  [false]: the parker captured a
       slot family and owes nothing extra; the closer asks nothing.
       FORKRET DECIDES THE MODE'S FATE, which is why the bit is here: the
       steady arm proves the run key it is asked for, and the BOOT arm --
       whose kexec("/init") would make the key false -- is REFUTED, because
       [first_done]'s [first_addr ↦₄□ 0] is incompatible with the boot arm's
       own [first_addr ↦₄ 1] ([FirstTok.first_tok_boot_excl]). *)
    (steady : bool) :=
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
  kernel_text -∗
  wire_inv -∗
  kmap_at tramp_vpn tramp_ppn KP_rx -∗
  pc_is pcE -∗
  (* the process table: [is_lock] for the lock released at +0x10, and what
     fsinit's and kexec's cones take for sleep/wakeup *)
  procs_inv γs -∗
  (* ...AND THE REST OF THE RESUMER'S GLOBALS, which forkret hands to the
     residue closer at its tail (UsertrapRes.park_globals). *)
  UsertrapRes.park_globals cur_ctx γs γw γft γf γtl -∗
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
  (* ---- THE PROCESS BLOCK, AT THE PACKAGE'S MODE.  On the steady mode it
     comes over whole and its [FirstTok.first_tok] may be on either arm --
     the boot one is refuted below, by the [first_done] the same package
     carries.  On the BOOT mode the park hands it SPLIT: the deficit block,
     the working-directory reference, and [FirstTok.first_boot]'s four rows
     as rows of their own.  That is what makes the mode a FACT about the
     record: forkret's steady arm reads [first] as 0 and the boot rows'
     [first_addr ↦₄ 1] refutes that reading
     ([FirstTok.first_boot_done_excl]), so a boot-mode record can only be
     resumed on the boot arm -- the arm that spends the exec bundle below.
     [ParkCap.park_child] carries the same shape. ---- *)
  (if steady then proc_priv γf p pid U
   else proc_priv_nocwd γf p pid U
        ∗ cwd_ref_at (pv_cwd (us_V U)) (pv_cwi (us_V U))
        ∗ FirstTok.first_boot) -∗
  W -∗
  (* ---- THE STEADY PARK'S EVIDENCE THAT THE BOOT ARM IS DEAD, and nothing
     on the other mode.  A parker that promises the resume lands on the
     parked run key is promising that nothing runs kexec("/init") in
     between, and this is the resource that makes that true: forkret reads
     [first] on the arm it takes, and the boot arm's [first_addr ↦₄ 1] --
     out of its own [FirstTok.first_tok] -- is incompatible with the
     [first_addr ↦₄□ 0] here.  So the boot arm is refuted rather than owing
     a key it cannot have.  Persistent, so the parker pays nothing.
     [SpecForkretParkPaid.forkret_park_pkg] carries the same row.
     ---- ...AND, ON THE BOOT MODE, THE FIRST PROCESS'S EXEC BUNDLE, which
     is what the boot arm's kexec("/init") is called with and where that
     record's user-execution slot comes from: the slot piece answers at the
     key kexec built ([SpecKexec.exec_post_ok]'s success arms hand back
     [Fs.(pf_recv) (exec_key U' sts na)]), and the tail re-keys it exactly
     as the steady arm's closer output is re-keyed.  LINEAR -- the kernel
     mints nothing.  [InitBoot.init_boot_bundle], [ParkCap.park_pkg]'s row.
     ---- *)
  (if steady then FirstTok.first_done
   else init_boot_bundle (pv_cwi (us_V U)) sts) -∗
  (* ---- the residue closer -- see the header, and [forkret_closer] above
     for why it is a name rather than the wand spelled out ---- *)
  forkret_closer URes W γs γw γft γf γtl p ksp (pv_fdg (us_V U)) (pv_cwi (us_V U))
    sts (if steady then Some (uvis_of U []) else None) pid av -∗
  WP (Loop : expr riscv_lang).

(* The residue is the module-type parameter it is everywhere else: forkret's
   tail runs [SpecUserretClosed]'s theorem, which is stated at
   [usertrap_res_bare] and at nothing else, so this contract is too. *)
Module Type FORKRET.
  (* ...AND THE PARK'S ONE PRODUCER-SIDE ENTRY, threaded with the rest.
     [UtResFits.USERTRAP_RES_PARK] is [USERTRAP_RES] plus
     [usertrap_res_bare_park]: the residue stays opaque to every CONSUMER,
     and the one party that has to BUILD one -- whoever parks a process that
     has never trapped -- gets a closer instead.  See that file's "THE
     PARK'S CHANNEL THROUGH THE MODULE TYPES". *)
  Include UtResFits.USERTRAP_RES_PARK.
  Parameter wp_forkret :
    forall `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ, !irefslotG Σ, !pavG Σ} `{!ufdG Σ} `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}
      (W : iProp Σ)
      (j : nat) (γs : list gname) (γl γw γft γf γtl : gname)
      (pid : mword 32) (U : ustate) (sts : list fdstate)
      (ks : mword 64) (m : regfile) (av av2 : nat) (eb : bool) (steady : bool),
      wp_forkret_gen_body
        (fun (h : CpuId) (Xc : CurCtx) => usertrap_res_bare (CID := h) (XI := Xc)) W
        j γs γl γw γft γf γtl pid U sts ks m av av2 eb steady.
End FORKRET.
