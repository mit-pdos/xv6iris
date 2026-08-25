(* SpecSysFork.v -- the public interface of sys_fork(), stated independently
   of its proof.

     uint64 sys_fork(void) { return kfork(); }

   @ KernelSyms.sys_fork = 0x80002910, nine instructions:

     +0x00  1141        c.addi     sp,sp,-16     16-byte frame
     +0x02  e406        c.sdsp     ra,8(sp)
     +0x04  e022        c.sdsp     s0,0(sp)
     +0x06  0800        c.addi4spn s0,sp,16
     +0x08  b5eff0ef    jal        ra,kfork      a0 := kfork()
     +0x0c  60a2        c.ldsp     ra,8(sp)
     +0x0e  6402        c.ldsp     s0,0(sp)
     +0x10  0141        c.addi     sp,sp,16
     +0x12  8082        c.ret

   THE POINT OF THIS SPEC is that it is a THIN one, and that it is now
   POSSIBLE to state.  sys_fork is a pure forwarder -- gcc emits no cast at
   all, so [a0] comes back from kfork and leaves untouched -- so everything
   interesting is in [SpecKfork], and this contract's only job is to prove
   that a syscall-altitude caller can actually PAY what kfork asks.  That
   was not true until [ProcInv.cwd_ref] became real: kfork used to carry
   five icache premises (an [IcacheInv.inode_ref] on the entry [p->cwd]
   names, an [IrefSlots.iref_slot], and the slot / device / inum that went
   with them) which NO CALLER COULD DISCHARGE, and this file could not have
   been written.  The parent's reference now comes out of its own
   [proc_priv] and the iref unit out of allocproc's block, so what is left
   is only what a caller genuinely holds.

   WHAT IS LEFT, and none of it is kfork-specific: the interrupt/nesting
   bundle ([sie_cap_gpr], [cpu_own]), the caller's own private block
   ([proc_priv], handed back verbatim -- kfork only READS the parent), the
   allocator at [kalloc_env _ None], and four persistent handles: the
   process table, the nextpid and wait_lock spinlocks, the ftable and the
   itable.  The last two travel with the FS fabric ([γfs], [cov],
   [logstart], [nib]) because [IcacheEscrow.is_itable2]'s resource does;
   kfork does no I/O and touches no log, and inherits them only because its
   [idup] call takes the itable lock.  A syscall dispatcher that already
   holds the fs fabric -- which every FS syscall does -- pays nothing extra.

   THE RETURN VALUE is kfork's, unchanged: [-1] on either failure arm, or
   the child's pid sign-extended exactly as [c.lw]/[c.mv a0,s1] left it.
   The disjunction is restated here rather than projected out of
   [kfork_post], because the caller of a syscall wrapper should not have to
   know that predicate's shape.

   THE STACK BUDGET is cumulative and this frame is 2 slots:
   [K_kfork + 2 <= av].  [K_sys_fork] names the total. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto.
Require Import FirstTok.  (* [first_done] -- the child's token's source *)
Require Import InstrBytes.
Require Import RegFile.
Require Import RiscvExtras.
Require Import CalleeSaved KernelText.
Require Import IntrDefs.
Require Import WpNext.
Require Import WpLock.
Require Import CpuOwn.
Require Import FdSlots FileInv.
Require Import ProcInv.
Require Import SchedCtx.
Require Import FsBlocks.
Require Import InodeRegion.
Require Import IrefSlots.
Require Import IcacheInv.
Require Import IcacheEscrow.
Require Import SpecProcinit.
Require Import WaitInv.
Require Import KvmSpec.
Require Import SpecAllocpid.
Require Import SpecKfork.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import ProcAvail.
Require Import SyscParkEnv ParkCap.   (* [park_world] / [park_token] *)
Require Import Xv6Cameras.  (* [logG]: [ireg_inv]'s own instance argument *)
Import Defs.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Require Import TsoCtx.
Local Open Scope Z_scope.

(* kfork's budget plus this function's own two slots. *)
Notation K_sys_fork := ((K_kfork + 2)%nat) (only parsing).
Definition wp_sys_fork_sconf_body
    `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fileG Σ, !fdslotG Σ,
      !irefslotG Σ, !pavG Σ} `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}
    (γa γp γw γl γf γil γic : gname) (γs : list gname)
    (cn : ic_names) (γfs : fs_names) (cov : gset Z) (logstart : Z)
    (inodestart : Z) (nib : nat)
    (m : regfile) (lvl av : nat) (eb : bool) (p : mword 64)
    (b : bool) (pid : mword 32) (V : pprivate) (lks : gset string) :=
  let pcE : mword 64 := mword_of_int KernelSyms.sys_fork in
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5)) in
  (K_sys_fork <= av)%nat ->
  (* propagates to kfork's own nesting bound *)
  (Z.of_nat lvl + 2 < 2 ^ 31)%Z ->
  (* straight through to kfork, whose cone floors at wait_lock (8) *)
  locks_below lks "wait_lock" ->
  sie_cap_gpr KT1 m av b p -∗
  cpu_own lvl eb p b lks -∗
  kernel_text -∗ pc_is pcE -∗
  procs_inv γs -∗
  is_lock γp alp_pid_lock "nextpid"%string nextpid_res -∗
  is_lock γw wait_lock_addr "wait_lock"%string wait_res -∗
  is_ftable γl γf -∗
  is_itable2 γil cn γfs γic cov logstart nib icfg_dev -∗
  itable_inv -∗
  (* the inode region, and it travels with the fs fabric for the SAME reason
     the itable does -- kfork's [np->cwd = idup(p->cwd)], whose [ref++] is a
     ledger move since increment IVe (iclaim-ledger.md §3.19).  Persistent,
     and every FS syscall's dispatch already holds it (a projection of the
     [fs_ready] its bundle carries), so a dispatcher pays nothing
     extra.  sys_fork does no I/O and touches no log. *)
  ireg_inv γic γfs inodestart nib -∗
  kalloc_env γa None -∗
  (* the proc table's sealed regime, threaded to kfork's allocproc
     ([ProcAvail.v]); persistent, so it costs nothing to carry *)
  procs_avail None -∗
  (* THE WORLD THE CHILD'S PARK NEEDS ([SyscParkEnv.park_world]): the
     device complement, console, wire invariant, trampoline claim and an
     [initproc] share, all persistent, read out of the parent's
     [syscall_env] and handed straight down to kfork. *)
  park_world γs -∗
  park_token γs -∗
  (* THE STEADY ARM OF [FirstTok.first_tok], and the ONE thing fork cannot
     take out of the parent's block: the parent's token may be the EXCLUSIVE
     boot arm, and the child needs a token of its own.  [first_done] is
     persistent, so a copy is free -- and it is what
     [FirstTok.first_tok_of_done] mints the child's token from, at the
     [sd a0,336(s4)] that closes the child's construction window. *)
  first_done -∗
  proc_priv γf p pid V -∗
  wp_next b p (fun (CID : CpuId) =>
    ∀ mf : regfile,
      ⌜ callee_saved m mf ⌝ -∗
      sie_cap_gpr KT1 mf av b p -∗
      cpu_own lvl eb p b lks -∗
      pc_is ret_tgt -∗
      (* the caller's block comes back verbatim: kfork only reads it *)
      proc_priv γf p pid V -∗
      kalloc_env γa None -∗
      (* ... and the return value is kfork's own, unchanged *)
      ⌜ mf !!! Regidx (mword_of_int 10 : mword 5) = (mword_of_int (-1) : mword 64)
        \/ (exists pidv : mword 32,
              mf !!! Regidx (mword_of_int 10 : mword 5)
              = (sign_extend' 64 pidv : mword 64)) ⌝ -∗
      WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

Module Type SYSFORK.
  Parameter wp_sys_fork_sconf :
    forall `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fileG Σ, !fdslotG Σ,
             !irefslotG Σ, !pavG Σ} `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}
      (γa γp γw γl γf γil γic : gname) (γs : list gname)
      (cn : ic_names) (γfs : fs_names) (cov : gset Z) (logstart : Z)
      (inodestart : Z) (nib : nat)
      (m : regfile) (lvl av : nat) (eb : bool) (p : mword 64)
      (b : bool) (pid : mword 32) (V : pprivate) (lks : gset string),
      wp_sys_fork_sconf_body γa γp γw γl γf γil γic γs cn γfs cov logstart
                             inodestart nib m lvl av eb p b pid V lks.
End SYSFORK.
