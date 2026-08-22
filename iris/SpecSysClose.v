(* SpecSysClose.v -- the public interface of sys_close(), stated
   independently of its proof.  Requires only the definitional layer --
   never a whole-function proof file -- so every function proof can be
   checked in parallel.

     uint64 sys_close(void) {
       int fd; struct file *f;
       if (argfd(0, &fd, &f) < 0) return -1;
       myproc()->ofile[fd] = 0;
       fileclose(f);
       return 0;
     }

   @ KernelSyms.sys_close = 0x80004cb2, 24 instructions (see
   CodeSysClose.v for the listing).

   THE POINT OF THIS SPEC.  sys_close is the first proof in which a
   [FileInv.file_ref] LEAVES the process: [proc_priv]'s descriptor [fd] gives
   up the reference it was holding, the descriptor becomes null, and
   fileclose consumes the reference.  Three resources have to line up for
   that, and they are exactly the three ends of the file-table design
   (claude-notes/design/file-table.md):

     - [ProcInv.proc_priv_ofile] borrows descriptor [fd] out of the
       thread-local fd table -- no lock, because the table IS thread-local --
       and takes back a descriptor holding a DIFFERENT value;
     - the reference inside it is what [SpecFileclose] consumes;
     - the [fd_slot] fileclose returns is what re-establishes the EMPTY
       descriptor's own conservation obligation ([ProcInv.ofile_slot]'s left
       disjunct).  Without it the postcondition below would be unprovable --
       which is the whole point of that unit existing.

   The [sd x0,0(a0)] store lands BEFORE the fileclose call, so there is a
   window in which the descriptor is null and the reference is loose in a
   register.  That is not a hole for the same reason sys_dup's window is not
   (design/file-table.md): no other core can reach this process's fd table,
   so the intermediate state never has to be an invariant -- it only has to
   be re-established by the time sys_close returns.

   DETERMINISM.  Which arm runs is a function of the syscall argument and the
   process's own descriptor array, both of which the caller knows, so the
   postcondition says so ([SpecArgfd.arg_fd]) rather than offering an
   unconstrained "closed it, or didn't": a kernel that always returned -1
   would not satisfy this spec. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto.
Require Import InstrBytes.
Require Import RegFile.
Require Import RiscvExtras.
Require Import CalleeSaved KernelText KernelDataInv.
Require Import IntrDefs.
Require Import WpNext.
Require Import LockRank.
Require Import SpecPanic.
Require Import ProcGeom CpuOwn.
Require Import FdSlots FileInv ProcInv.
Require Import SpecArgfd.
Require Import IrefSlots.
Require Import SpecFileclose.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import ProcAvail.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Import Defs.
Local Open Scope Z_scope.


(* sys_close's own frame is 4 slots (addi sp,sp,-32); below it fileclose
   wants 68 -- the descriptor may name an inode file, and that arm reaches
   iput -- argfd 24 and myproc 10. *)
Notation sys_close_stack := (88%nat) (only parsing).
Section SpecSysClose.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fileG Σ, !fdslotG Σ, !irefslotG Σ, !pavG Σ}.
  (* [GenId], for [ProcInv.proc_priv]'s own index: the private block now
     carries [FirstTok.first_tok], whose boot arm names [gen_cert].  The
     definitions below mention the block, so the section has to bind it. *)
  Context `{GEN : GenId}.

  (* sys_close's result, keyed by the returned a0.  In the success case the
     descriptor named by the argument is null and one file reference is
     gone; in the failure case nothing at all has happened. *)
  Definition sys_close_post (γf : gname) (p : mword 64) (pid : mword 32)
      (V : pprivate) (v : mword 64) (r : mword 64) : iProp Σ :=
    (⌜r = (mword_of_int (-1) : mword 64) /\ arg_fd v (pv_ofile V) = None⌝ ∗
       proc_priv γf p pid V
     ∨ ∃ (fd : nat) (fv : mword 64),
         ⌜r = (zero_reg : mword 64) /\ arg_fd v (pv_ofile V) = Some (fd, fv)⌝ ∗
         proc_priv γf p pid (upd_ofile V fd (zero_reg : mword 64)))%I.

End SpecSysClose.

Definition wp_sys_close_sconf_body
    `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
      !irefslotG Σ, !pavG Σ} `{GEN : GenId} `{CID : CpuId}
     (γl γf : gname) (fn : fclose_names) (on : option nat)
    (m : regfile) (av : nat) (n : nat) (eb : bool) (p : mword 64)
    (v : mword 64) (pid : mword 32) (V : pprivate) (b : bool) (lks : gset string) :=
  let pcE : mword 64 := mword_of_int KernelSyms.sys_close in
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5)) in
  (* sys_close reads syscall argument 0, out of the trapframe page
     [proc_priv] carries *)
  pv_tf V !! tf_arg_idx 0 = Some v ->
  (* push_off's transient noff increment stays in int range *)
  (Z.of_nat n + 1 < 2 ^ 31)%Z ->
  (sys_close_stack <= av)%nat ->
  (* sys_close acquires no lock itself; its whole cone is the pure
     PASS-THROUGH to fileclose, whose bound is at "ftable" (1) -- the
     LOWEST rank in the table, and nothing else sys_close touches (argfd,
     myproc) carries any order premise at all. *)
  locks_below lks "log" ->
  (* ---- THE TWO TIES THE PID QUARTER FORCES, and why they are cheap.

     [fileclose]'s FS arm wants a QUARTER of [p->pid] (iput's acquiresleep
     records the holder), and this contract used to take it inside
     [fileclose_fs_env].  That made the premise set UNPAYABLE rather than
     merely large: [ProcInv.proc_priv] owns [p_pid] at ONE HALF and
     [SchedCtx]'s state resource owns the other, so no thread can hold
     [proc_priv] AND a further quarter -- three quarters is more than exists
     outside the lock.  It is the "satisfiable in isolation, refutable at
     the call site" shape durable-notes.md warns about: nothing in the build
     saw it, because the only caller was an [Axiom].

     So the environment below is the NOPID bundle, and the quarter is lent
     out of this function's OWN [proc_priv] for the duration of the
     fileclose call ([ProcInv.proc_priv_pid_ofile] lends it beside the
     descriptor slot, which is exactly what the store to [p->ofile[fd]]
     wants anyway; [SpecFileclose.fileclose_loop_open] is the pairing kexit's
     loop already uses).  The two equations are what identify the lent
     quarter with the one [fn] describes -- [SpecSyscall]'s dispatch
     discharges both, [fcn_pid] by its own [fcn_pid fn = pid] premise and
     [fcn_dq] by [reflexivity]. *)
  fcn_pid fn = pid ->
  fcn_dq fn = DfracOwn (1/4) ->
  sie_cap_gpr KT1 m av b p -∗
  cpu_own n eb p b lks -∗
  (* THE TRAP-CSR COMPLEMENT, THREADED.  [emp] at [eb = true], so no existing
     call site changes; at [eb = false] the real pair, which can only have
     come from the TRAP.  sys_close mints nothing itself -- it holds no lock
     whose acquire would -- so it is a pure PASS-THROUGH to fileclose, whose
     FS arm parks through begin_op / iput / end_op and needs it there.  It
     has to be threaded rather than framed: fileclose's crossing is the
     literal [true], so a hart-indexed resource held across the call could
     not be transported to the arbitrary hart it may return on.  See
     claude-notes/completed/eb-generic-sweep.md. *)
  trap_csrs_ext KT1 eb -∗
  cpu_claim_ext eb p -∗
  kernel_text -∗ kernel_data -∗ pc_is pcE -∗
  is_ftable γl γf -∗
  panic_env -∗
  proc_priv γf p pid V -∗
  (* THE CLOSING ENVIRONMENT.  sys_close closes a descriptor of unknown type,
     so it owns both of fileclose's bundles and hands over whichever the
     type selects ([SpecFileclose.fileclose_env_split]); the other is
     untouched and comes straight back.  This is what a syscall that can
     close ANY [struct file] costs, and there is no honest way to make it
     smaller: closing an inode file writes the disk and sleeps. *)
  (* the unit fileclose borrows to deposit into the slot it frees, in and
     straight back out -- see SpecFileclose's own note. *)
  iref_slot -∗
  fileclose_pipe_env fn on n -∗
  fileclose_fs_env_nopid fn n eb p -∗
  (* THE CROSSING IS THE LITERAL [true], NOT [b].  sys_close calls fileclose,
     whose FD_INODE / FD_DEVICE arm parks, so sys_close can return on another
     hart whatever SIE was doing.  The cost is the CALLER's: it must supply
     its continuation hart-generically (WpNext.wp_next's guard is vacuous at
     [true], so consuming it here is free).  *)
  wp_next true p (fun (CID : CpuId) =>
    ∀ mf : regfile,
      ⌜callee_saved m mf⌝ -∗
      sie_cap_gpr KT1 mf av b p -∗
      cpu_own n eb p b lks -∗
      trap_csrs_ext KT1 eb -∗
      cpu_claim_ext eb p -∗
      pc_is ret_tgt -∗
      sys_close_post γf p pid V v (mf !!! Regidx (mword_of_int 10 : mword 5)) -∗
      (* the whole environment back: the page count may have moved (the
         descriptor may have held a pipe's last end), which is why the pipe
         bundle returns under an existential *)
      (∃ on', fileclose_pipe_env fn on' n) -∗
      fileclose_fs_env_nopid fn n eb p -∗
      iref_slot -∗
      WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

Module Type SYSCLOSE.
  Parameter wp_sys_close_sconf :
    forall `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
             !irefslotG Σ, !pavG Σ} `{GEN : GenId} `{CID : CpuId}
       (γl γf : gname) (fn : fclose_names) (on : option nat)
      (m : regfile) (av : nat) (n : nat) (eb : bool) (p : mword 64)
      (v : mword 64) (pid : mword 32) (V : pprivate) (b : bool) (lks : gset string),
      wp_sys_close_sconf_body γl γf fn on m av n eb p v pid V b lks.
End SYSCLOSE.
