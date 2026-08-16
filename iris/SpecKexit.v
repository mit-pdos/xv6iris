(* SpecKexit.v -- the public interface of kexit(), stated independently of its
   proof.

     void kexit(int status) {
       struct proc *p = myproc();
       if (p == initproc) panic("init exiting");
       for (int fd = 0; fd < NOFILE; fd++)
         if (p->ofile[fd]) { struct file *f = p->ofile[fd];
                             fileclose(f); p->ofile[fd] = 0; }
       begin_op();  iput(p->cwd);  end_op();  p->cwd = 0;
       acquire(&wait_lock);
       reparent(p);                  // give any children to init
       wakeup(p->parent);            // the parent might be in kwait()
       acquire(&p->lock);
       p->xstate = status;
       p->state  = ZOMBIE;
       release(&wait_lock);
       sched();                      // jump into the scheduler, never to return
       panic("zombie exit");
     }

   @ KernelSyms.kexit = 0x8000201c, 166 bytes / fifty instructions.  The shape,
   read off the image:

     +0x00  a 48-byte frame: ra and s0..s4 saved.  s4 = status, s3 = p,
            s1 = the ofile cursor (&p->ofile[0], bumped by 8), s2 = &p->cwd,
            which is ALSO the cursor's end pointer -- [ofile] runs 208..335
            and [cwd] sits at 336, so the loop's [beq s1,s2] is literally
            "the cursor has walked off the end of the array" ([p_ofile pa
            NOFILE = p_cwd pa], ProcGeom.p_ofile_end).
     +0x12  myproc()                +0x18  a5 = initproc  (auipc/ld)
     +0x28  bne a5,a0 -> +0x3e (the loop's FIRST test); else panic
     +0x38  the loop's back edge: s1 += 8; beq s1,s2 -> +0x4c
     +0x3e  ld a0,0(s1); beqz -> +0x38; fileclose(a0); sd x0,0(s1); -> +0x38
     +0x4c  begin_op / iput(p->cwd) / end_op / p->cwd = 0
     +0x60  acquire(&wait_lock) / reparent(p) / wakeup(p->parent)
     +0x7c  acquire(&p->lock) / p->xstate = s4 / p->state = 5 (ZOMBIE)
     +0x92  release(&wait_lock) / sched() / panic("zombie exit")

   ==== IT DIVERGES, SO THE CONTRACT IS A CONSUMPTION LIST ==============

   Like scheduler()'s, this spec has no continuation: the postcondition of a
   function that never returns is [WP Loop], full stop
   (claude-notes/completed/scheduler.md).  What that makes the precondition
   is a list of everything kexit CONSUMES, and the interesting entries are
   the process's own:

   * [proc_priv] goes in and does not come back.  It is the ONE resource
     kexit exists to retire: every descriptor's [file_ref] goes to
     fileclose, the cwd reference goes to iput, and what is left --
     the scalar cells, the emptied array with the fd units fileclose handed
     back, the user page table and the trapframe page -- is exactly
     [ProcInv.proc_dormant _ ZOMBIE] minus its context cells, which is what
     the park deposits in [p->lock] for kwait()/freeproc to reclaim.  The
     [FDSPARE] allowance travels beside it (FdSlots.v) and is retired the
     same way.

   * [own_ctx] and the hart tag go in and do not come back either, for the
     same reason they come BACK from yield and sleep: the difference between
     a park you return from and a park you do not is entirely in whether the
     resume ever happens, and kexit's does not.  Its saved context is
     nonetheless real memory, and the parked slot owns it -- see
     [SchedCtx.proc_slots_park_gen], which forgets the RECORD and keeps the
     cells.

   * The whole file-system stack rides through because of the three
     instructions [begin_op(); iput(p->cwd); end_op();]: [bio_ctx],
     [log_ctx], the crash seam, the disk fabric and three buffer slots are
     end_op's and iput's premises verbatim.  Nothing about the log survives
     the call sequence -- the reservation is opened and closed inside kexit
     -- so none of it appears in a postcondition that does not exist.

   ==== WHAT ITS CALLER MUST HOLD ======================================

   THE TRAP-CSR COMPLEMENT [trap_csrs_ext eb] / [cpu_claim_ext eb pj], and
   NOT [eb = true ->].  At level 0 with an enabled base the pushing acquire
   hands out the trap CSRs the chain payload demands: kexit's own
   acquire(&wait_lock) produces that pay and the release(&wait_lock) before
   sched() spends the SECOND acquire's, so at [eb = true] kexit is balanced,
   the complement is [emp], and it asks the caller for no [arm_pay] -- the
   sys_pause rule.  With the base DISABLED the acquire mints nothing, and
   the pair has to come from the caller, which is the trap.  That is what
   lets usertrap call kexit(-1) on the paths that have not run intr_on() --
   the whole point of the eb-generic sweep.  Nothing is handed back, because
   kexit does not return.

   [is_lock γw wait_lock_addr ... wait_res] -- kexit is the second consumer
   of the parent table after kwait, and takes it exactly as kwait does.

   The [initproc] cell at any fraction: kexit reads it for the panic test and
   reparent reads it again for the new parent.  It is write-once (userinit is
   the only writer, and is one of the tree's assumed contracts), so a
   fraction is all any reader needs and nothing here has to say who holds the
   rest.  Same premise, same spelling, as SpecReparent.v's.

   NOTE the panic arm is NOT ruled out.  kexit's caller does not have to
   prove [p <> initproc]: [panic] never returns, so the [panic_wp_any]
   convention closes that arm at zero cost (SpecPanic.v), and the honest
   reading of the contract is "exits the calling process, or panics".  The
   same convention closes the [panic("zombie exit")] that follows sched --
   which is the arm a resumed zombie would take, and the reason its saved
   context can be forgotten rather than proved unreachable. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto.
Require Import InstrBytes.
Require Import RegFile.
Require Import SmodeCore.
Require Import KernelText.
Require Import IntrDefs.
Require Import WpLock.
Require Import ProcGeom CpuOwn.
Require Import FdSlots FileInv.
Require Import StackOwn.
Require Import WpMmodeLeafBase.
Require Import ProcDefs.
Require Import ProcInv.
Require Import SchedCtx.
Require Import KallocInv.
Require Import IcacheEscrow IrefSlots InodeRegion.
Require Import SpecFileclose.
Require Import WaitInv.
Require Import WpUart.
Require Import DiskPtsto DiskInv.
Require Import BioInv.
Require Import FsBlocks LogInv.
Require Import FsCrash.
Require Import PanicStub.
Require Import SpecProcinit.   (* [wait_lock_addr] -- procinit is what makes it *)
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import ProcAvail.
Local Open Scope Z_scope.
Import Defs.

(* kexit's own six frame slots, plus the deepest callee below it: fileclose
   (68 -- a descriptor may name an inode file, so its own arm reaches iput);
   iput wants 60, end_op 58, reparent 24, sched 16. *)
Notation K_kexit := (90%nat) (only parsing).
Definition wp_kexit_sconf_body
    `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !fileG Σ, !bioG Σ,
      !diskGhostG Σ, !uartGhostG Σ, !fsLogG Σ, !logG Σ, !fsCrashG Σ, !kallocG Σ,
      !irefslotG Σ, !pavG Σ, !iregG Σ}
    `{GEN : GenId} `{CID : CpuId}
    (γft γf γw : gname)                               (* ftable lock, ftable, wait *)
     (γs : list gname) (j : nat) (γl : gname)
    (γu : uart_names) (γd : disk_names) (γk : gname)  (* disk fabric + lock  *)
    (pd pav pu : mword 64)
    (bn : bio_names)
    (γ : log_names) (γfs : fs_names)
    (cov : gset Z) (logstart : Z) (dev : mword 32)
    (ip : mword 64) (dqi : dfrac)                     (* the initproc cell   *)
    (γkl : gname) (γka : gname * gname)               (* kmem.lock, kalloc   *)
    (γi : gname) (cn : ic_names) (γtl : gname)        (* the inode cache     *)
    (bmapstart inodestart : Z) (nib : nat) (size : Z)
    (dqb dqs : dfrac) (us : gset Z)
    (on : option nat) (fn : fclose_names)
    (m : regfile) (av : nat) (eb : bool) (b : bool) (lks : gset string)
    (pid : mword 32) (V : pprivate) :=
  let pcE : mword 64 := mword_of_int KernelSyms.kexit in
  let pj := proc_addr j in
  (* [fn] is not an extra degree of freedom: it is exactly kexit's own ghosts,
     bundled the way fileclose's environment is indexed.  One equation rather
     than fifteen coherence conjuncts, and it computes away in the proof.  The
     pid fraction is the quarter [ProcInv.proc_priv_pid_ofile] lends. *)
  fn = MkFCloseNames γs j γl γkl γka γu γd γk pd pav pu bn γ γfs
         cov logstart dev pid (DfracOwn (1/4))
         γi cn γtl bmapstart inodestart nib size dqb dqs ->
  (j < NPROC)%nat ->
  γs !! j = Some γl ->
  (K_kexit <= av)%nat ->
  (* the covered range's block-number bounds, and the log's own storage *)
  log_geom_ok cov logstart ->
  (* THE PROCESS HAS A WORKING DIRECTORY.  [begin_op(); iput(p->cwd);] is
     unconditional in xv6 -- there is no null test -- so a caller that
     cannot exhibit one is calling iput on a null pointer.  IT IS NOT A
     PREMISE ANY MORE: [ProcInv.cwd_ref] has no null arm, so
     [proc_priv_cwd_nonzero] projects it straight out of the block this
     contract already takes. *)
  (* THE FRESHNESS PREMISE, AT THE LOWEST RANK kexit (OR ANY CALLEE)
     TOUCHES: "ftable" (1), via the fileclose loop's [SpecFileclose.v]
     premise; "itable" (2, [iput(p->cwd)] directly), "log" (3, [end_op]),
     "wait_lock" (10) and "proc" (11, nested while holding "wait_lock") are
     all higher and follow by [LockRank.locks_below_mono] /
     [locks_below_union_singleton] at each call site. *)
  locks_below lks "log" ->
  sie_cap_gpr m av b pj -∗
  (* entered with no lock held *)
  cpu_own 0 eb pj b lks -∗
  (* THE TRAP-CSR COMPLEMENT, WHERE [eb = true ->] USED TO BE -- the whole
     point of the sweep.  usertrap calls kexit(-1) on paths that have not
     run intr_on(): the first killed(p) check runs before it, and the second
     is reachable from the devintr and vmfault arms.  At [eb = true] both
     conjuncts are [emp] and kexit's own acquire(&wait_lock) mints what the
     interior sleeps need, so no existing caller gains an obligation; at
     [eb = false] the acquire mints nothing and the pair can only have come
     from the TRAP.
     THERE IS NO GIVE-BACK, and that is not an oversight: kexit does not
     return (see the header), so the pair is spent along with everything
     else the dead process was holding.
     See claude-notes/completed/eb-generic-sweep.md. *)
  trap_csrs_ext eb -∗
  cpu_claim_ext eb pj -∗
  kernel_text -∗ pc_is pcE -∗
  (* the proc table, and the scheduler chain the park hands itself to *)
  procs_inv γs -∗
  panic_wp_any -∗
  (* the running-thread bundle -- consumed: this thread parks forever *)
  (* wait_lock, and what it protects *)
  is_lock γw wait_lock_addr "wait_lock"%string wait_res -∗
  (* the open-file table: every non-null descriptor is fileclose'd *)
  is_ftable γft γf -∗
  (* ...and closing one can free a pipe's page, so kexit owns kalloc's side
     too.  The count comes back MOVED -- a descriptor may have held a pipe's
     last end -- which is why the loop carries it existentially. *)
  is_lock γkl (mword_of_int KernelSyms.kmem) "kmem"%string
    (kmem_res γka (mword_of_int (KernelSyms.kmem + 24))) -∗
  kalloc_avail γka on -∗
  (* the file system, for [begin_op(); iput(p->cwd); end_op();] *)
  bio_ctx bn (fs_view γfs γd dev cov) -∗
  log_ctx γ bn γfs cov logstart dev -∗
  fs_crash_seam cov logstart -∗
  gen_cert -∗
  dev_inv γu γd -∗
  disk_geom γd pd pav pu -∗
  is_lock γk d_lock "virtio_disk"%string (disk_res γd pd pav pu) -∗
  bslots bn 3 -∗
  (* THE INODE CACHE, and the two regions iput's truncate arm frees into.
     Both bundles are [SpecFileclose]'s, verbatim: kexit hands them to
     fileclose once per descriptor and then spends them itself on
     [iput(p->cwd)], so stating them twice would be stating them
     differently. *)
  fileclose_ic_env fn -∗
  fileclose_bm fn us -∗
  (* the initproc pointer, at any fraction (write-once; see the header) *)
  (mword_of_int KernelSyms.initproc : mword 64) ↦₈{dqi} ip -∗
  (* the process itself: its private block and its fd-slot allowance *)
  fd_slots FDSPARE -∗
  (* the iref ALLOWANCE.  Only [IREFSPARE], not [1 + IREFSPARE]: the cwd's
     own unit is not the caller's to bring -- it is parked in the itable
     against the reference [p->cwd] holds, and [iput] hands it back at the
     [ld a0,336(s3)].  The two rejoin into the [1 + IREFSPARE] the ZOMBIE
     block parks. *)
  iref_slots IREFSPARE -∗
  proc_priv γf pj pid V -∗
  (* NO continuation: kexit does not return.  See the header. *)
  WP (Loop : expr riscv_lang).

(* ---------------------------------------------------------------------- *)
(* WHAT THE CONSUMPTION LIST IS FOR, checked here.                          *)
(*                                                                          *)
(* The one thing an unproven contract cannot be trusted about is whether it  *)
(* asks for enough.  The load-bearing case is the park: what kexit holds at  *)
(* the [jal sched] -- the DEFICIT block (every descriptor nulled and the cwd *)
(* reference already spent on iput, so there is no [proc_priv] at this V),   *)
(* plus the FDSPARE allowance that travels beside it -- has to               *)
(* BE [SchedCtx.park_pay _ ZOMBIE], or the park cannot be taken and the      *)
(* contract is unprovable for a reason no reader would see.  It is, with no  *)
(* side condition beyond the two facts the loop and the iput establish.      *)
(* (SpecProcinit.proc_ready_lock_res is the same kind of check.)             *)
(* ---------------------------------------------------------------------- *)
Section KexitSeals.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !irefslotG Σ, !pavG Σ, !fileG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Lemma kexit_park_pay (γf : gname) (j : nat) (pid : mword 32) (V : pprivate) :
    pv_ofile V = replicate NOFILE (zero_reg : mword 64) ->
    pv_cwd V = (zero_reg : mword 64) ->
    proc_priv_nocwd γf (proc_addr j) pid V -∗ fd_slots FDSPARE -∗
    iref_slots (1 + IREFSPARE) -∗
    park_pay (proc_addr j) ZOMBIE.
  Proof.
    intros Hof Hcwd. rewrite /park_pay inv_dormant_ZOMBIE.
    iIntros "Hpriv Hsp Hir".
    iApply (proc_priv_to_dormant_zombie γf (proc_addr j) pid V Hof Hcwd
              with "Hpriv Hsp Hir").
  Qed.

End KexitSeals.

Module Type KEXIT.
  Parameter wp_kexit_sconf :
    forall `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !fileG Σ, !bioG Σ,
             !diskGhostG Σ, !uartGhostG Σ, !fsLogG Σ, !logG Σ, !fsCrashG Σ,
             !kallocG Σ, !irefslotG Σ, !pavG Σ, !iregG Σ}
      `{GEN : GenId} `{CID : CpuId}
      (γft γf γw : gname)
      (γs : list gname) (j : nat) (γl : gname)
      (γu : uart_names) (γd : disk_names) (γk : gname)
      (pd pav pu : mword 64)
      (bn : bio_names)
      (γ : log_names) (γfs : fs_names)
      (cov : gset Z) (logstart : Z) (dev : mword 32)
      (ip : mword 64) (dqi : dfrac)
      (γkl : gname) (γka : gname * gname)
      (γi : gname) (cn : ic_names) (γtl : gname)
      (bmapstart inodestart : Z) (nib : nat) (size : Z)
      (dqb dqs : dfrac) (us : gset Z)
      (on : option nat) (fn : fclose_names)
      (m : regfile) (av : nat) (eb : bool) (b : bool) (lks : gset string)
      (pid : mword 32) (V : pprivate),
      wp_kexit_sconf_body γft γf γw γs j γl γu γd γk pd pav pu bn γ γfs
                          cov logstart dev ip dqi γkl γka
                          γi cn γtl bmapstart inodestart nib size dqb dqs us
                          on fn m av eb b lks pid V.
End KEXIT.
