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

   * [own_ctx] and [park_hlf] go in and do not come back either, for the
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

   [eb = true], the parking premise every function that sleeps or parks has
   (SpecSched.v): at level 0 with an enabled base the pushing acquire hands
   out the trap CSRs the chain payload demands.  kexit's own
   acquire(&wait_lock) produces that pay and the release(&wait_lock) before
   sched() spends the SECOND acquire's, so kexit is balanced and asks the
   caller for no [arm_pay] -- the sys_pause rule.

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
Require Import ProcInv.
Require Import SchedCtx.
Require Import KallocInv.
Require Import SpecFileclose.
Require Import WaitInv.
Require Import WpUart.
Require Import DiskPtsto DiskInv.
Require Import BioInv.
Require Import FsBlocks LogInv.
Require Import FsCrash.
Require Import SpecPanic.
Require Import SpecProcinit.   (* [wait_lock_addr] -- procinit is what makes it *)
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Local Open Scope Z_scope.
Import Defs.

(* kexit's own six frame slots, plus the deepest callee below it: fileclose
   (68 -- a descriptor may name an inode file, so its own arm reaches iput);
   iput wants 60, end_op 58, reparent 24, sched 16. *)
Definition K_kexit : nat := 74%nat.

Definition wp_kexit_sconf_body
    `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !fileG Σ, !bioG Σ,
      !diskGhostG Σ, !uartGhostG Σ, !fsLogG Σ, !logG Σ, !fsCrashG Σ, !kallocG Σ}
    `{GEN : GenId} `{CID : CpuId}
    (γft γf γw : gname)                               (* ftable lock, ftable, wait *)
    (Φ : mval -> iProp Σ) (γs : list gname) (j : nat) (γl : gname)
    (γu : uart_names) (γd : disk_names) (γk : gname)  (* disk fabric + lock  *)
    (pd pav pu : mword 64)
    (bn : bio_names)
    (γ : log_names) (γfs : fs_names)
    (cov : gset Z) (logstart : Z) (dev : mword 32)
    (ip : mword 64) (dqi : dfrac)                     (* the initproc cell   *)
    (γkl : gname) (γka : gname * gname)               (* kmem.lock, kalloc   *)
    (on : option nat) (fn : fclose_names)
    (m : regfile) (av : nat) (eb : bool) (C : iProp Σ) (b : bool)
    (pid : mword 32) (V : pprivate) :=
  let pcE : mword 64 := mword_of_int KernelSyms.kexit in
  let pj := proc_addr j in
  (* [fn] is not an extra degree of freedom: it is exactly kexit's own ghosts,
     bundled the way fileclose's environment is indexed.  One equation rather
     than fifteen coherence conjuncts, and it computes away in the proof.  The
     pid fraction is the quarter [ProcInv.proc_priv_pid_ofile] lends. *)
  fn = MkFCloseNames γs j γl γkl γka γu γd γk pd pav pu bn γ γfs
         cov logstart dev pid (DfracOwn (1/4)) ->
  (j < NPROC)%nat ->
  γs !! j = Some γl ->
  (K_kexit <= av)%nat ->
  (* the covered range's block-number bounds, and the log's own storage *)
  log_geom_ok cov logstart ->
  (* the PARKING premise: everything that sleeps or parks needs it *)
  eb = true ->
  sie_cap_gpr m av b pj -∗
  (* entered with no lock held *)
  cpu_own 0 eb pj C b -∗
  kernel_text -∗ pc_is pcE -∗
  (* the proc table, and the scheduler chain the park hands itself to *)
  procs_inv Φ γs -∗
  scheds_inv Φ γs -∗
  panic_wp_any -∗
  (* the running-thread bundle -- consumed: this thread parks forever *)
  running_claim j -∗
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
  (* the initproc pointer, at any fraction (write-once; see the header) *)
  (mword_of_int KernelSyms.initproc : mword 64) ↦₈{dqi} ip -∗
  (* the process itself: its private block and its fd-slot allowance *)
  fd_slots FDSPARE -∗
  proc_priv γf pj pid V -∗
  (* NO continuation: kexit does not return.  See the header. *)
  WP (Loop : expr riscv_lang) {{ Φ }}.

(* ---------------------------------------------------------------------- *)
(* WHAT THE CONSUMPTION LIST IS FOR, checked here.                          *)
(*                                                                          *)
(* The one thing an unproven contract cannot be trusted about is whether it  *)
(* asks for enough.  The load-bearing case is the park: what kexit holds at  *)
(* the [jal sched] -- the private block with every descriptor nulled and the *)
(* cwd dropped, plus the FDSPARE allowance that travels beside it -- has to  *)
(* BE [SchedCtx.park_pay _ ZOMBIE], or the park cannot be taken and the      *)
(* contract is unprovable for a reason no reader would see.  It is, with no  *)
(* side condition beyond the two facts the loop and the iput establish.      *)
(* (SpecProcinit.proc_ready_lock_res is the same kind of check.)             *)
(* ---------------------------------------------------------------------- *)
Section KexitSeals.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !fileG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Lemma kexit_park_pay (γf : gname) (j : nat) (pid : mword 32) (V : pprivate) :
    pv_ofile V = replicate NOFILE (zero_reg : mword 64) ->
    pv_cwd V = (zero_reg : mword 64) ->
    proc_priv γf (proc_addr j) pid V -∗ fd_slots FDSPARE -∗
    park_pay (proc_addr j) ZOMBIE.
  Proof.
    intros Hof Hcwd. rewrite /park_pay inv_dormant_ZOMBIE.
    iIntros "Hpriv Hsp".
    iApply (proc_priv_to_dormant_zombie γf (proc_addr j) pid V Hof Hcwd
              with "Hpriv Hsp").
  Qed.

End KexitSeals.

Module Type KEXIT.
  Parameter wp_kexit_sconf :
    forall `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !fileG Σ, !bioG Σ,
             !diskGhostG Σ, !uartGhostG Σ, !fsLogG Σ, !logG Σ, !fsCrashG Σ, !kallocG Σ}
      `{GEN : GenId} `{CID : CpuId}
      (γft γf γw : gname)
      (Φ : mval -> iProp Σ) (γs : list gname) (j : nat) (γl : gname)
      (γu : uart_names) (γd : disk_names) (γk : gname)
      (pd pav pu : mword 64)
      (bn : bio_names)
      (γ : log_names) (γfs : fs_names)
      (cov : gset Z) (logstart : Z) (dev : mword 32)
      (ip : mword 64) (dqi : dfrac)
      (γkl : gname) (γka : gname * gname)
      (on : option nat) (fn : fclose_names)
      (m : regfile) (av : nat) (eb : bool) (C : iProp Σ) (b : bool)
      (pid : mword 32) (V : pprivate),
      wp_kexit_sconf_body γft γf γw Φ γs j γl γu γd γk pd pav pu bn γ γfs
                          cov logstart dev ip dqi γkl γka on fn
                          m av eb C b pid V.
End KEXIT.
