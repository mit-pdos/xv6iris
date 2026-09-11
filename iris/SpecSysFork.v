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
   allocator at [kalloc_env _ None], four persistent handles (the process
   table, the nextpid and wait_lock spinlocks, the ftable and the itable),
   and ONE LINEAR RESOURCE: the child's user-execution slot, which is
   kfork's own premise passed straight through.  The forking process
   deposited it at the ecall and the trap route carried it here
   ([SpecUsertrap.ut_fork_in] / [SpecSyscall.sysc_fork_in]), so sys_fork
   mints nothing.  The last two travel with the FS fabric ([fsc_fs], [fsc_cov],
   [fsc_logst], [nib]) because [IcacheEscrow.is_itable2]'s resource does;
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
Require Import ProcGeom.  (* [PIDMAX] -- kernel/param.h *)
Require Import SchedCtx.
Require Import InodeRegion.
Require Import IrefSlots.
Require Import IcacheInv.
Require Import IcacheEscrow.
Require Import SpecProcinit.
Require Import WaitInv.
Require Import KvmSpec.
Require Import PidLock.
Require Import SpecKfork.
Require Import UexecSlot.  (* [uvis_of] -- the child's key *)
Require Import UexecRet.   (* [uslot] -- the deposit sys_fork forwards *)
Require Import KforkChild. (* [kfork_child] -- the record it is stated at *)
Require Import ChildTok.   (* [child_tok] / [my_pay] -- fork's two pieces *)
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import ProcAvail.
Require Import SyscParkEnv ParkCap.   (* [park_world] / [park_token] *)
Require Import Xv6Cameras.  (* [logG]: [ireg_inv]'s own instance argument *)
Import Defs.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Require Import FsCfg.   (* [fscfg]: the fs configuration is AMBIENT *)
Local Open Scope Z_scope.
Require Import TsoCtx.

(* kfork's budget plus this function's own two slots. *)
Notation K_sys_fork := ((K_kfork + 2)%nat) (only parsing).
Definition wp_sys_fork_sconf_body
    `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fileG Σ, !fdslotG Σ,
      !irefslotG Σ, !pavG Σ, !wchG Σ} `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}
    (γp γw γl γf : gname) (γs : list gname)
    (m : regfile) (lvl av : nat) (eb : bool) (p : mword 64)
    (b : bool) (pid : mword 32) (U : ustate) (sts : list fdstate)
    (* the caller's children set, forwarded to kfork with its row -- see
       [SpecKfork.kfork_post].  sys_fork never reads it either. *)
    (csP : gset gname)
    (* the child's exit payload, forwarded to kfork -- see
       [SpecKfork.kfork_post].  sys_fork never reads it. *)
    (Q : Z -> iProp Σ)
    (lks : gset string) :=
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
  is_lock γp alp_pid_lock "nextpid"%string nextpid_res_at -∗
  is_lock γw wait_lock_addr "wait_lock"%string (wait_res_at) -∗
  is_ftable γl γf -∗
  is_itable2 fsc_itlock fsc_ic fsc_fs fsc_ireg fsc_cov fsc_logst icfg_nib icfg_dev -∗
  itable_inv -∗
  (* the inode region, and it travels with the fs fabric for the SAME reason
     the itable does -- kfork's [np->cwd = idup(p->cwd)], whose [ref++] is a
     ledger move since increment IVe (iclaim-ledger.md §3.19).  Persistent,
     and every FS syscall's dispatch already holds it (a projection of the
     [fs_ready] its bundle carries), so a dispatcher pays nothing
     extra.  sys_fork does no I/O and touches no log. *)
  ireg_inv fsc_ireg fsc_fs icfg_ist icfg_nib -∗
  (* THE ALLOCATOR AT ITS PAIR, not behind [kalloc_env]'s existential (rank
     1d).  kfork NAMES the free-list count/seal pair ([KvmSpec.kalloc_env_at],
     because allocproc must speak about the count), and the pair is
     [FsCfg.fscfg]'s [fsc_kpages] now rather than a threaded gname -- so a
     row that hid it behind an [∃ γk] could no longer be handed on.  Every
     caller has it: it is spelled out inside [FsReady.fs_ready]
     ([fs_ready_kmem]), which is exactly why the field is there. *)
  kalloc_env_at fsc_kalloc fsc_kpages None -∗
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
  (* THE CHILD'S CONTINUATION, straight through to kfork.  fork's DEPOSIT:
     the process handed the kernel the WP its child will run when it made
     the ecall, and the trap route ([SpecUsertrap.ut_fork_in],
     [SpecSyscall.sysc_fork_in]) carries it here.  ONE slot, at the record
     [SpecKfork] states from the parent -- so sys_fork neither mints nor
     re-keys, it forwards. *)
  (* THE CHILD'S GENERATION IS ∀-BOUND: allocproc mints a fresh one inside
     the kfork this call makes, so no caller can name it, and a newly
     created process has no children ([UexecRet.uexec_fork_child_F]).
     ...AND THE SLOT MAY READ THE CHILD'S OWN PAYLOAD ([ChildTok.my_pay]
     of the [Q] this call is at): kfork hands it over out of the split it
     makes, and a verified child needs it to prove its own exit. *)
  (* ...AND SO IS ITS PID, on exactly the generation's terms: <allocpid>
     chooses it inside this call, so the CALLER cannot name it either.  IT
     IS THE PID THE POST RETURNS: kfork parks the child at the number
     [kfork_post]'s success arm hands back as [pidv], so a parent holding
     [ChildTok.child_tok γ pidv Q] knows the pid its child's key is at --
     [ChildTok.gen_pid] reads it off the token -- and a verified parent can
     therefore say what its child's getpid(2) will answer. *)
  (∀ (g' : gname) (pidc : mword 32),
     my_pay g' Q -∗ uslot (uvis_of (kfork_child U) sts g' ∅ pidc)) -∗
  proc_priv γf p pid U -∗
  (* THE PARENT'S DESCRIPTOR STATES.  fork's whole effect on descriptors is
     that the CHILD gets these -- [SpecKfork]'s copy loop retypes the child's
     ghost at exactly this list, one slot per [filedup] -- so the caller has
     to name them, and gets them back untouched. *)
  fd_frags (pv_fdg (us_V U)) sts -∗
  (* ...AND THE CALLER'S CHILDREN ROW, on the same channel: kfork moves it
     under the <wait_lock> it takes to write [np->parent], and the moved
     row comes back below. *)
  ch_frag (pv_chg (us_V U)) p csP -∗
  wp_next b p (fun (CID : CpuId) =>
    ∀ mf : regfile,
      ⌜ callee_saved m mf ⌝ -∗
      sie_cap_gpr KT1 mf av b p -∗
      cpu_own lvl eb p b lks -∗
      pc_is ret_tgt -∗
      (* the caller's block comes back verbatim: kfork only reads it *)
      proc_priv γf p pid U -∗
      fd_frags (pv_fdg (us_V U)) sts -∗
      kalloc_env_at fsc_kalloc fsc_kpages None -∗
      (* ... and the return value is kfork's own, unchanged -- including the
         pid's interval, which is what the dispatcher relays into its own
         fork row and the trap loop reads as [r <> 0] *)
      (* ...AND, ON THE PID ARM, THE CHILD TOKEN: the parent's quarter of
         the child's generation at the payload this call chose, straight
         out of [SpecKfork.kfork_post].  An iProp disjunction and no
         longer a pure one, because the pid arm now carries a RESOURCE --
         which is the whole of what fork gives its parent. *)
      (* ...AND THE CALLER'S CHILDREN ROW, MOVED on the pid arm: kfork put
         the child's generation in the caller's set under <wait_lock>, so
         what comes back is the reading the resume key is built at. *)
      ( (⌜ mf !!! Regidx (mword_of_int 10 : mword 5) = (mword_of_int (-1) : mword 64) ⌝ ∗
         ch_frag (pv_chg (us_V U)) p csP)
        ∨ (∃ (pidv : mword 32) (γ : gname),
              ⌜ mf !!! Regidx (mword_of_int 10 : mword 5)
                = (sign_extend' 64 pidv : mword 64) ⌝ ∗
              ⌜ (1 <= bv_unsigned pidv <= PIDMAX)%Z ⌝ ∗
              child_tok γ pidv Q ∗
              ch_frag (pv_chg (us_V U)) p (csP ∪ {[γ]})) ) -∗
      WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

Require Import UserFd.   (* [ufdG] -- the class a minted user slot needs *)
Module Type SYSFORK.
  Parameter wp_sys_fork_sconf :
    forall `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fileG Σ, !fdslotG Σ,
             !irefslotG Σ, !pavG Σ, !wchG Σ} `{!ufdG Σ}
      `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}
      (γp γw γl γf : gname) (γs : list gname)
      (m : regfile) (lvl av : nat) (eb : bool) (p : mword 64)
      (b : bool) (pid : mword 32) (U : ustate) (sts : list fdstate)
      (csP : gset gname)
      (Q : Z -> iProp Σ)
      (lks : gset string),
      wp_sys_fork_sconf_body γp γw γl γf γs
 m lvl av eb p b pid U sts csP Q lks.
End SYSFORK.
