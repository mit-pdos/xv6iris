(* SpecSysFstat.v -- the public interface of sys_fstat(), stated
   independently of its proof.  Requires only the definitional layer and its
   callees' SPECS -- never a whole-function proof file -- so every function
   proof can be checked in parallel.

     uint64 sys_fstat(void) {
       struct file *f;
       uint64 st;
       argaddr(1, &st);
       if (argfd(0, 0, &f) < 0) return -1;
       return filestat(f, st);
     }

   @ KernelSyms.sys_fstat, 58 bytes / 21 instructions (CodeSysFstat.v has the
   listing).  A 32-byte frame; [st] is frame slot 4 ([s0-32]) and [f] is
   frame slot 3 ([s0-24]); ra and s0 are slots 1 and 2.

     +0x00  1101        c.addi     sp,sp,-32
     +0x02  ec06/e822   c.sdsp     ra,24(sp) / s0,16(sp)
     +0x06  1000        c.addi4spn s0,sp,32        s0 := the entry sp
     +0x08  fe040593    addi       a1,s0,-32       &st
     +0x0c  4505        c.li       a0,1
     +0x0e  b17fd0ef    jal        ra,argaddr
     +0x12  fe840613    addi       a2,s0,-24       &f
     +0x16  4581        c.li       a1,0            pfd = NULL
     +0x18  4501        c.li       a0,0
     +0x1a  cf5ff0ef    jal        ra,argfd
     +0x1e  87aa        c.mv       a5,a0
     +0x20  557d        c.li       a0,-1           the error return, hoisted
     +0x22  0007c863    blt        a5,x0,+16       -> the epilogue
     +0x26  fe043583    ld         a1,-32(s0)      st
     +0x2a  fe843503    ld         a0,-24(s0)      f
     +0x2e  bfaff0ef    jal        ra,filestat
     +0x32  60e2/6442/6105/8082    the epilogue

   THREE THINGS WORTH KNOWING ABOUT THE SHAPE.

   * THE ERROR RETURN IS HOISTED.  [c.li a0,-1] runs BEFORE the branch, so
     both arms reach the epilogue with the answer already in a0 and there is
     no [c.mv] on the join.  The epilogue is therefore one lemma over the
     value the arm left in a0, not two copies -- the same move ProofSysClose
     makes with a5.

   * [pfd] IS NULL.  sys_fstat wants the [struct file *] and not the
     descriptor index, so it passes 0 for argfd's [int *pfd].  That is
     exactly the case [SpecArgfd.ofd_out] exists for: a null out-parameter
     carries no resource and its store does not happen, so this caller owes
     argfd nothing for it ([ofd_out_null]).  [pf] is a real stack address and
     its non-nullity comes from the frame's own geometry
     ([StackOwn.stack_own_sp_nonzero]), not from an assumption.

   * ARGADDR RUNS BEFORE ARGFD, and its result is never checked.  A bad
     user address is filestat's (i.e. copyout's) problem, not this
     function's -- copyout's contract is total in the destination.

   ==== THE DESCRIPTOR ENVIRONMENT, AND WHY IT IS A WAND ==================

   THE ONE REAL DESIGN QUESTION IN THIS FILE.  [SpecFilestat.filestat_env fn
   Cf] is INDEXED BY THE FILE'S CONTENT: on the inode arm it names the itable
   slot ([fc_ip Cf = ientry (fsn_ik fn)]), that slot's escrow and sleeplock,
   and a SHARE of that inode's reference.  A syscall cannot own it up front,
   because it does not know -- and cannot know -- which file the descriptor
   names: [ProcInv.ofile_slot] quantifies the slot [k], the fraction [q] AND
   the content [Cf] existentially, and nothing the caller holds pins them.
   Taking [Cf] as a contract parameter does not help: after the borrow the
   proof learns some [Cf'] and has no way to identify it with the parameter
   ([FileInv.file_ref_agree] would do it, but only for a caller that already
   holds a second fraction of the SAME slot's reference, which no caller
   does).

   So what the contract takes is an OPENER: a wand that turns the reference
   the descriptor actually held into the environment for THAT file, and takes
   the environment back afterwards.  Three things recommend this shape:

   * it is honest -- it is a real [iProp], not a pure premise nobody can
     discharge, and it says precisely what is owed;
   * it is the shape the file-table design already predicts.  The per-slot
     pieces are inside the reference: [FileInvDefs.inode_pay] carries
     [inode_shr_held_gen (fc_ip Cf) (q * Q) g], which IS the share ilock
     wants, and it names [k], [dev] and [inum].  The rest of the environment
     (the escrow family, the sleeplock family, the inode region, the block
     cache and the disk fabric) is content-INDEPENDENT, exactly as
     [SpecFileclose.fileclose_fs_env] is.  Building this wand is therefore
     the "carve at entry, gather at exit" bracket SpecFileread.v's header
     defers to B3, packaged so that it is written ONCE rather than in each
     of the three syscalls;
   * it is the precedent this tree already set one level up:
     [SpecSyscall.v]'s [syscall_env] is one abstract parameter for the same
     reason -- spelling the union out at the wrong altitude buys nothing.

   THE FRACTION MAY MOVE ([q'] is existential): a carve leaves the parent
   reference smaller, and filestat takes its reference at an ARBITRARY
   fraction, so nothing downstream cares.  The close puts the original [q]
   back.  The opener is a [==∗] because a carve out of a cinv-parked
   reference is a ghost step.

   ==== WHAT THE POSTCONDITION SAYS ======================================

   [sys_fstat_post] is PURE, and keyed by [SpecArgfd.arg_fd] so that a
   caller learns which arm ran from data it already has: either the
   descriptor was bad and the answer is -1, or filestat ran and the answer is
   [filestat_ret] (0 or -1).  Note the two are not disjoint on the VALUE --
   a good descriptor whose copyout faults also answers -1 -- which is why
   the disjunction is indexed by [arg_fd] and not by [r].

   The process block comes back at an EXTENDED page table, filestat's
   [uptd_ext]; on the failure arm nothing ran and [P'] is [pv_upt V] itself
   ([ProcPtOwn.uptd_ext_refl]).  The descriptor array is UNCHANGED: sys_fstat
   only borrows the reference and puts it straight back. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list functions bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import auth gmap frac.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap ghost_map.
From iris.program_logic Require Import language weakestpre lifting.
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
Require Import SpecPanic.
Require Import FdSlots.
Require Import ProcGeom.
Require Export SwtchCtx.
Require Import CpuOwn.
Require Import SchedCtx.
Require Import SleepLock.
Require Import WpUart.
Require Import DiskPtsto DiskInv.
Require Import BioInv.
Require Import FsBlocks LogInv.
Require Import DinodeEnc.
Require Import InodeInv.
Require Import InodeRegion.
Require Import IrefSlots.
Require Import IcacheInv.
Require Import IcacheEscrow.
Require Import KallocInv.
Require Import UserPtTree.
Require Import KvmSpec.
Require Import ProcPtOwn.
Require Import ProcInv.
Require Import FileInvDefs.
Require Import SpecArgfd.
Require Import SpecArgaddr.
Require Import SpecFilestat.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Import Defs.

Local Open Scope Z_scope.

(* sys_fstat's own frame is 4 slots ([c.addi sp,sp,-32]); below it filestat
   wants [filestat_stack] = 60, which dominates argfd's 24 and argaddr's 18.
   Written as an expression so that a change to filestat's budget cannot
   silently leave this one behind. *)
Definition sys_fstat_stack : nat := (4 + filestat_stack)%nat.

(* WHAT SYS_FSTAT RETURNS, as a function of what the caller already knows.
   The disjunction is indexed by [arg_fd], not by [r]: filestat's own -1
   (copyout faulted) is not distinguishable from argfd's by the value. *)
Definition sys_fstat_ret (V : pprivate) (v : mword 64) (r : mword 64) : Prop :=
  (r = (mword_of_int (-1) : mword 64) /\ arg_fd v (pv_ofile V) = None)
  \/ (exists (fd : nat) (fv : mword 64),
        arg_fd v (pv_ofile V) = Some (fd, fv) /\ filestat_ret r).

Section SpecSysFstat.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !fileG Σ, !kallocG Σ,
            !bioG Σ, !diskGhostG Σ, !uartGhostG Σ, !fsLogG Σ, !logG Σ,
            !icacheG Σ, !irefslotG Σ, !iregG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  (* THE DESCRIPTOR ENVIRONMENT (see the header).  Given the reference the
     descriptor turned out to hold, produce filestat's environment for THAT
     file; take it back at the end and restore the reference at its original
     fraction.

     A caller that knows the descriptor names a pipe (or anything else
     without an inode) can build this for free -- [filestat_env] is [emp]
     there -- which is what [fstat_fdenv_nofs] below says. *)
  Definition fstat_fdenv (γf : gname) : iProp Σ :=
    (∀ (k : nat) (q : Qp) (Cf : fcontent),
       ⌜(k < NFILE)%nat⌝ -∗
       file_ref γf k q Cf ==∗
       ∃ (fn : fstat_names) (q' : Qp),
         filestat_env fn Cf ∗ file_ref γf k q' Cf ∗
         (file_ref γf k q' Cf -∗ filestat_env_out fn Cf ==∗
            file_ref γf k q Cf))%I.

  (* The trivial instance, and the check that the definition is not
     accidentally unsatisfiable: for a descriptor whose file carries no
     inode the environment is [emp] on both sides, so the opener is the
     identity.  (It is stated over ALL contents under the hypothesis, so a
     caller that has ruled the inode arm out -- pipealloc's files, a pipe
     descriptor -- owes nothing at all.) *)
  Lemma fstat_fdenv_nofs (γf : gname) (fn0 : fstat_names) :
    (forall Cf : fcontent, ~ fstat_has_inode Cf) -> ⊢ fstat_fdenv γf.
  Proof.
    intro Hno. rewrite /fstat_fdenv.
    iIntros (k q Cf) "_ Href". iModIntro. iExists fn0, q.
    iSplitR; [by iApply filestat_env_none|].
    iFrame "Href". iIntros "Href Hout". by iFrame "Href".
  Qed.

End SpecSysFstat.

Definition wp_sys_fstat_sconf_body
    `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !fileG Σ, !kallocG Σ,
      !bioG Σ, !diskGhostG Σ, !uartGhostG Σ, !fsLogG Σ, !logG Σ,
      !icacheG Σ, !irefslotG Σ, !iregG Σ}
    `{GEN : GenId} `{CID : CpuId}

    (γa : gname) (γf : gname)                    (* kalloc, the file table  *)
    (γs : list gname) (j : nat) (γlp : gname)    (* the running process     *)
    (pidv : mword 32) (V : pprivate)
    (v : mword 64)                               (* syscall argument 0      *)
    (m : regfile) (av : nat) (eb : bool) (C : iProp Σ) (b : bool) :=
  let pcE : mword 64 := mword_of_int KernelSyms.sys_fstat in
  let pj := proc_addr j in
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5)) in
  (sys_fstat_stack <= av)%nat ->
  (j < NPROC)%nat ->
  γs !! j = Some γlp ->
  length γs = NPROC ->
  (* the two syscall arguments, out of the trapframe page [proc_priv]
     carries.  Argument 1 (the stat buffer) is fetched but never inspected
     here -- it goes straight to copyout, whose contract is total in the
     destination -- so only argument 0's word has to be named. *)
  pv_tf V !! tf_arg_idx 0 = Some v ->
  (exists v1 : mword 64, pv_tf V !! tf_arg_idx 1 = Some v1) ->
  (* PARKING PREMISE (hart-generic scheduler protocol): filestat's ilock
     sleeps, so this syscall parks. *)
  eb = true ->
  sie_cap_gpr m av b pj -∗
  (* a syscall runs at push_off level 0 *)
  cpu_own 0%nat eb pj C b -∗
  kernel_text -∗ kernel_data -∗ pc_is pcE -∗
  (* filestat itself never panics; ilock and iunlock do, and this is theirs *)
  panic_wp_any -∗
  proc_priv γf pj pidv V -∗
  kalloc_env γa None -∗
  procs_inv γs -∗
  (* ...and the environment for whatever file the descriptor names *)
  fstat_fdenv γf -∗
  (* THE CROSSING IS THE LITERAL [true]: filestat parks, and a park moves the
     hart with interrupts off, so the crossing has nothing to do with SIE
     (SpecFilestat.v's note, and SpecSyscall.v's pinned index above). *)
  wp_next true pj (fun (CID : CpuId) =>
    ∀ (mf : regfile) (r : mword 64) (P' : uptd),
      ⌜callee_saved m mf⌝ -∗
      ⌜uptd_ext (pv_upt V) P'⌝ -∗
      ⌜sys_fstat_ret V v r⌝ -∗
      ⌜mf !!! Regidx (mword_of_int 10 : mword 5) = r⌝ -∗
      sie_cap_gpr mf av b pj -∗
      cpu_own 0%nat eb pj C b -∗
      pc_is ret_tgt -∗
      proc_priv γf pj pidv (upd_upt V P') -∗
      kalloc_env γa None -∗
      WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

Module Type SYSFSTAT.
  Parameter wp_sys_fstat_sconf :
    forall `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !fileG Σ, !kallocG Σ,
             !bioG Σ, !diskGhostG Σ, !uartGhostG Σ, !fsLogG Σ, !logG Σ,
             !icacheG Σ, !irefslotG Σ, !iregG Σ}
      `{GEN : GenId} `{CID : CpuId}

      (γa : gname) (γf : gname)
      (γs : list gname) (j : nat) (γlp : gname)
      (pidv : mword 32) (V : pprivate)
      (v : mword 64)
      (m : regfile) (av : nat) (eb : bool) (C : iProp Σ) (b : bool),
      wp_sys_fstat_sconf_body γa γf γs j γlp pidv V v m av eb C b.
End SYSFSTAT.
