(* SpecSysPipe.v -- the public interface of sys_pipe(), stated independently
   of its proof.  Requires only the definitional layer -- never a
   whole-function proof file -- so every function proof can be checked in
   parallel.

     uint64 sys_pipe(void) {
       uint64 fdarray;                  // user pointer to two ints
       struct file *rf, *wf;
       int fd0, fd1;
       struct proc *p = myproc();
       argaddr(0, &fdarray);
       if (pipealloc(&rf, &wf) < 0) return -1;
       fd0 = -1;
       if ((fd0 = fdalloc(rf)) < 0 || (fd1 = fdalloc(wf)) < 0) {
         if (fd0 >= 0) p->ofile[fd0] = 0;
         fileclose(rf); fileclose(wf); return -1;
       }
       if (copyout(p->pagetable, fdarray,     (char * )&fd0, sizeof(fd0)) < 0 ||
           copyout(p->pagetable, fdarray + 4, (char * )&fd1, sizeof(fd1)) < 0) {
         p->ofile[fd0] = 0; p->ofile[fd1] = 0;
         fileclose(rf); fileclose(wf); return -1;
       }
       return 0;
     }

   @ KernelSyms.sys_pipe = 0x80005338, 71 instructions (offsets 0x00 .. 0xe0;
   see CodeSysPipe.v for the listing).  A 64-byte frame: [fdarray] at
   s0-40, [rf] at s0-48, [wf] at s0-56, and the two [int]s sharing the
   bottom slot -- [fd1] in its LOW word (s0-64), [fd0] in its HIGH word
   (s0-60).

   WHY THIS ONE IS THE INTERESTING SYSCALL.  sys_pipe is the first proof in
   which every layer of the file/proc model is exercised at once and has to
   BALANCE:

     - it CREATES two file references (pipealloc) and INSTALLS them in
       descriptors (fdalloc), where sys_close only destroyed one;
     - it copies kernel data OUT to user memory, so it crosses the
       [proc_pt] altitude ([ProcInv.proc_priv_copy]) and the process's page
       table may GROW under it -- hence the [uptd_ext] descriptor in the
       continuation, exactly as for fetchaddr;
     - and it has FOUR exits over three error tails, each of which has to
       hand back the same resources.

   THE CONSERVATION LAW IS THE SPEC.  Two [fd_slot]s go in -- the
   per-syscall allowance of FdSlots.v, which is what the "+4" in
   [FDSLOTS] is for -- and two come back on EVERY exit.  Tracing them is
   the whole resource argument:

     | exit                  | where the two units end up                  |
     |-----------------------|---------------------------------------------|
     | pipealloc failed      | both returned by pipealloc itself           |
     | fdalloc(rf) failed    | the two fileclose calls return them         |
     | fdalloc(wf) failed    | fdalloc(rf)'s unit pays to re-null ofile    |
     |                       | [fd0]; the two fileclose calls return two   |
     | copyout failed        | the two fdalloc units pay to re-null both   |
     |                       | descriptors; the two fileclose return two   |
     | success               | one per fdalloc, straight through           |

   If any one of those legs leaked, the [+4] allowance would drain and a
   whole-kernel proof could only run sys_pipe finitely often.  That is why
   [SpecFilealloc]'s failure arm and [SpecPipealloc]'s had to start
   returning their units before this spec could be written.

   DETERMINISM, AND ITS LIMIT.  Which descriptors get used is NOT a choice:
   they are the two least free ones, [SpecFdalloc.fd_frees]'s first two
   entries.  Which EXIT is taken, however, genuinely is not a function of
   anything the caller holds -- pipealloc can fail because another core just
   took the last ftable slot or the last page, and copyout can fail on a user
   address this altitude says nothing about -- so the postcondition is an
   honest disjunction there.

   WHAT THIS CONTRACT DOES NOT SAY, and why:

   * NOTHING ABOUT THE USER'S ARRAY.  [SpecCopyout] deliberately does not
     record what the user pages end up holding ([proc_pt] owns them with
     existential contents), so no resource here could carry "fdarray[0] =
     fd0".  Stating it needs a contents-indexed refinement of [proc_pt]; the
     limitation is copyout's, not sys_pipe's.
   * NOTHING ABOUT THE DESCRIPTORS' CONTENTS.  The two [file_ref]s land
     inside [proc_priv], and [ProcInv.ofile_slot] quantifies the [fcontent]
     existentially -- so the post can say descriptor [fd0] names ftable slot
     [k0], but not that [k0]'s type is FD_PIPE and its pipe is the same one
     [fd1] names.  Recovering that needs a PERSISTENT content witness on the
     ftable authority (an [agree] component in [FileInv.fileUR]), which is a
     change to the algebra and to all three of its proved ghost steps.
     Flagged, not built.

   Design: claude-notes/design/pipe.md, claude-notes/design/file-table.md,
   claude-notes/design/proc-struct.md. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExtras.
Require Import InstrBytes.
Require Import RegFile.
Require Import SmodeCore.
Require Import CalleeSaved KernelText KernelDataInv.
Require Import IntrDefs.
Require Import WpNext.
Require Import WpLock.
Require Import ProcGeom CpuOwn.
Require Import KallocInv.
Require Import KvmSpec.
Require Import UserPtTree.
Require Import ProcPtOwn.
Require Import FdSlots FileInv ProcInv.
Require Import SpecFdalloc.
Require Import WpUart.
Require Import DiskPtsto.
Require Import BioInv.
Require Import FsBlocks LogInv.
Require Import FsCrash.
Require Import SpecFileclose.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Import Defs.
Local Open Scope Z_scope.


(* sys_pipe's own frame is 8 slots (c.addi16sp sp,-64).  Below it: copyout
   wants 74, fileclose 68, copyout 50, argaddr 18, fdalloc 14, myproc 10 --
   so pipealloc sets the bound, and what makes pipealloc the deepest is the
   fileclose on its own error path. *)
Definition sys_pipe_stack : nat := 82%nat.

Section SpecSysPipe.
  Context `{!riscvGS Σ, !lockG Σ, !fileG Σ, !fdslotG Σ}.

  (* sys_pipe's result, keyed by the returned a0, over the process state [W]
     the syscall ends with -- i.e. the incoming [V] with copyout's page-table
     growth already folded in (the continuation below does that with
     [upd_upt], so this predicate is purely about the DESCRIPTORS).

     Both arms hand back the two fd units: see the table in the header. *)
  Definition sys_pipe_post (γf : gname) (p : mword 64) (pid : mword 32)
      (W : pprivate) (r : mword 64) : iProp Σ :=
    ((* FAILURE.  Whichever tail ran, the descriptor array is EXACTLY as it
        came in: the two arms that had already installed a descriptor null
        it again, and writing 0 back over a slot that was 0 is the identity
        ([ProcInv.upd_ofile_id], since [fd_frees] only ever names free
        slots). *)
     ⌜r = (mword_of_int (-1) : mword 64)⌝ ∗ proc_priv γf p pid W
     ∨
     (* SUCCESS.  The two least free descriptors now hold the read and the
        write end, in that order. *)
     ∃ (fd0 fd1 : nat) (l : list nat) (k0 k1 : nat),
       ⌜r = (zero_reg : mword 64) /\ fd_frees (pv_ofile W) = fd0 :: fd1 :: l⌝ ∗
       proc_priv γf p pid
         (upd_ofile (upd_ofile W fd0 (fnode k0)) fd1 (fnode k1)))
    ∗ fd_slot ∗ fd_slot.

End SpecSysPipe.

Definition wp_sys_pipe_sconf_body
    `{!riscvGS Σ, !sieG Σ, !lockG Σ, !kallocG Σ, !fdslotG Σ, !fileG Σ,
      !bioG Σ, !diskGhostG Σ, !uartGhostG Σ, !fsLogG Σ, !logG Σ, !fsCrashG Σ} `{GEN : GenId} `{CID : CpuId}
    (γa : gname)  (γfl γf : gname)
    (fn : fclose_names) (on : option nat)
    (m : regfile) (av : nat) (eb : bool) (p : mword 64) (C : iProp Σ)
    (v : mword 64) (pid : mword 32) (V : pprivate) (b : bool) :=
  (* [pipeG] is not a separate binder: [fileG] subsumes it (FileInv.v), and
     naming both would put TWO instance paths to [inG Σ fracR] in scope --
     they print identically and do not unify, so a [pipe_ref] built through
     one does not close a goal stated through the other.  Nothing about pipes
     appears below in any case: the two references sys_pipe creates end up
     inside [proc_priv]'s existentials, as each file's payload. *)
  let pcE : mword 64 := mword_of_int KernelSyms.sys_pipe in
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5)) in
  (* sys_pipe reads syscall argument 0 -- the user address of the two-int
     array -- out of the trapframe page [proc_priv] carries.  Nothing is
     assumed about it: argaddr does not check, and copyout is the check. *)
  pv_tf V !! tf_arg_idx 0 = Some v ->
  (sys_pipe_stack <= av)%nat ->
  sie_cap_gpr m av b p -∗
  (* [n = 0]: copyout's chain reaches vmfault, whose kalloc runs with
     interrupts un-pushed (SpecCopyout.v) -- and sys_pipe holds no lock
     across any of its calls anyway. *)
  cpu_own 0%nat eb p C b -∗
  kernel_text -∗ kernel_data -∗ pc_is pcE -∗
  is_ftable γfl γf -∗
  (* the kmem lock, the sealed page count and panic's contract: pipealloc
     needs the allocator and copyout needs it again for vmfault, and every
     acquire on the way needs [panic_wp] *)
  kalloc_env γa None -∗
  proc_priv γf p pid V -∗
  (* the syscall's own allowance -- two references may be live in locals
     before they reach descriptors.  Both come back. *)
  fd_slot -∗ fd_slot -∗
  (* THE CLOSING ENVIRONMENT.  sys_pipe closes files it took back out of the
     fd table, and [ProcInv.ofile_slot] quantifies their contents -- so, like
     sys_close, it carries both of fileclose's bundles and hands over
     whichever the type selects ([SpecFileclose.fileclose_env_frame]).  That
     it only ever closes pipes is true and unusable: the knowledge of what a
     descriptor names is going to be per-[ofile] ghost state, not something
     recoverable from the file table. *)
  fileclose_pipe_env fn on 0%nat -∗
  fileclose_fs_env fn 0%nat eb p -∗
  wp_next b p (fun (CID : CpuId) =>
    ∀ (mf : regfile) (P' : uptd),
      ⌜callee_saved m mf⌝ -∗
      ⌜uptd_ext (pv_upt V) P'⌝ -∗
      sie_cap_gpr mf av b p -∗
      cpu_own 0%nat eb p C b -∗
      pc_is ret_tgt -∗
      sys_pipe_post γf p pid (upd_upt V P')
        (mf !!! Regidx (mword_of_int 10 : mword 5)) -∗
      (* the environment back; the page count has moved if either close was
         the pipe's last end *)
      (∃ on', fileclose_pipe_env fn on' 0%nat) -∗
      fileclose_fs_env fn 0%nat eb p -∗
      WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

Module Type SYSPIPE.
  Parameter wp_sys_pipe_sconf :
    forall `{!riscvGS Σ, !sieG Σ, !lockG Σ, !kallocG Σ, !fdslotG Σ, !fileG Σ,
             !bioG Σ, !diskGhostG Σ, !uartGhostG Σ, !fsLogG Σ, !logG Σ, !fsCrashG Σ} `{GEN : GenId} `{CID : CpuId}
      (γa : gname) (γfl γf : gname)
      (fn : fclose_names) (on : option nat)
      (m : regfile) (av : nat) (eb : bool) (p : mword 64) (C : iProp Σ)
      (v : mword 64) (pid : mword 32) (V : pprivate) (b : bool),
      wp_sys_pipe_sconf_body γa γfl γf fn on m av eb p C v pid V b.
End SYSPIPE.
