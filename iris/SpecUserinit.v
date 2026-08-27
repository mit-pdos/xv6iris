(* SpecUserinit.v -- the public interface of userinit() (kernel/proc.c).
   PROVEN: [ProofUserinit.v] discharges it, [LinkUserinit.v] links it.

     void userinit(void) {
       struct proc *p = allocproc();
       initproc = p;
       p->cwd = namei("/");
       p->state = RUNNABLE;
       release(&p->lock);
     }

   (THIS KERNEL'S userinit, read off [CodeUserinit.v]: twenty-two
   instructions, three calls and two stores.  Upstream's uvmfirst /
   trapframe / safestrcpy lines are not in this image and the decode is what
   says so.)

   ---- THIS FILE USED TO BE AN ASSUMED CONTRACT.  IT IS NOT ANY MORE. ----

   The axiom that stood here assumed userinit's WHOLE BODY, on the grounds
   that namei "drags in the whole file-system cone".  It does not:
   [namei("/")] is a path of one separator, so [skipelem] returns 0 on its
   first call, the walk's body never runs, and the only callee reached is
   [iget(ROOTDEV, ROOTINO)].  What is assumed now is exactly that one call,
   at the premises the boot client can produce
   ([SpecNameiRootBoot.NAMEI_ROOT_BOOT], whose header is the inventory) --
   four persistent inode-cache rows short of a contract the tree already
   proves.  Everything else about userinit is a theorem.

   ---- WHAT IT TAKES ------------------------------------------------------

   THE COUNTED PROC REGIME is the headline.  userinit does NOT test
   allocproc's result -- it stores through the returned pointer at +0x24 --
   so the proof has to REFUTE allocproc's empty-table arm, and
   [ProcAvail.procs_avail (Some (S k))] is the only thing that can
   (claude-notes/kernel-defects.md, "UNREACHABLE, BY THE CALLER'S
   POSITION").  It is threaded exactly as [kalloc_env] is and comes back one
   slot lighter.  The page budget is the same story for allocproc's two
   freeproc failure tails: [K_allocproc < nb] refutes both.

   THE [nextpid] LOCK is allocproc's own premise, and main builds it out of
   procinit's [lk_fresh] and the .data cell (durable-notes.md, "A WRITABLE
   GLOBAL INSIDE THE LOADED IMAGE...").

   THE ONE [iref_slot] namei's [iget] spends is NOT a premise: allocproc
   hands back [iref_slots (1 + IREFSPARE)] and the [1] is exactly it.  In
   kfork that unit pays for [idup]; here it pays for the root's [iget], and
   in both cases it is the working directory's.

   ---- WHAT COMES BACK ----------------------------------------------------

   NOTHING ABOUT THE FIRST PROCESS CROSSES BACK OUT: main does not use
   [initproc], and the process userinit made is reached by the scheduler
   through [procs_inv], which is persistent and rides in unchanged.  The
   RUNNABLE park swallows the private block, the fd allowance and the saved
   context; the [initproc] cell comes back at an unspecified value and
   PERSISTENT (userinit's store is the last write it ever gets), and the
   two counted regimes come back one unit down.

   THE PAGE COUNT COMES BACK EXISTENTIALLY ([nc <= K_allocproc]) rather than
   at a fixed subtraction: allocproc's own post reports what it spent, and
   inventing a round number here would be [claude-notes/durable-notes.md]'s
   "a numeral that silently encodes another constant's value".

   THE FTABLE'S GNAME DOES NOT APPEAR.  allocproc's post mentions it (in
   [ProcInv.proc_priv_nocwd]) and so does [FORKRET_PARK], but the block
   userinit hands over has every descriptor null, so nothing about the open
   file table is observable in this contract; the proof instantiates both
   callees at one arbitrary name. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import excl.
From iris.base_logic.lib Require Import ghost_var gen_heap invariants.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto.
Require Import RegFile InstrBytes.
Require Import RiscvExtras.
Require Import CalleeSaved KernelText KernelDataInv.
Require Import IntrDefs.
Require Import WireInv.   (* [wire_inv] *)
Require Import UsertrapRes.   (* [devintr_caps_any] -- the park's device complement *)
Require Import WaitInv.       (* [wait_res] *)
Require Import SpecProcinit.  (* [wait_lock_addr] *)
Require Import FileInv.       (* [is_ftable] *)
Require Import ConsoleInv.    (* [console_ready] *)
Require Import KptExecMap.   (* [kmap_at tramp_vpn tramp_ppn KP_rx] *)
Require Import WpNext.
Require Import WpLock.
Require Import CpuOwn.
Require Import LockRank.
(* the classes the binder list generalizes over -- [fileG] (which carries
   the cache's [icfg] and [icacheG] as superclass fields) and the two device
   ghosts [panic_env] needs.  A bare [Require Import SpecPanic] does not put
   them in scope and backtick generalization then invents fresh binders. *)
Require Import FileInvDefs.
Require Import SpecPanic.
Require Import FdSlots.
Require Import SchedCtx.
Require Import KvmSpec.
Require Import ProcAvail.
Require Import SpecAllocpid.
(* the two callee contracts whose budgets this one is the sum of.  Neither
   pulls the file-system cone: [SpecNameiRootBoot] is a leaf by design (its
   header says why) and [SpecAllocproc] is the proc/kalloc layer. *)
Require Import SpecAllocproc.
Require Import SpecNameiRootBoot.
(* the four inode-cache rows namei's corner takes, spelled at the ambient
   configuration (fs-cfg-boot.md stage (e)).  [Require Import] is not
   transitive, so naming them here needs their own files even though
   [SpecNameiRootBoot] already states them. *)
Require Import IcacheInv IcacheEscrow InodeRegion InodeInv.
Require Import FsCfg.
(* THE BOOT TOKEN'S TWO PAYLOAD BUNDLES (fs-cfg-boot.md stage (f)).  Named
   here rather than spelled out: [FirstTok] is where they are DEFINED, main
   assembles both at +0x9e, and this contract is the courier that carries
   them past allocproc to the park.  [FirstTok] sits below every process
   file (it imports only the fs and kalloc layers), so the import is a leaf
   and not a cone. *)
Require Import FirstTok.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Require Import TsoCtx.
Local Open Scope Z_scope.


(* userinit's own frame is 32 bytes (4 slots); its deepest callee is [namei]
   at its root corner (74), over allocproc's 48 and release's 10.  Written
   as the sum rather than as 78 (durable-notes.md, "A STACK-BUDGET PREMISE
   IS ARITHMETIC"). *)
Notation K_userinit := ((4 + K_namei_root_boot)%nat) (only parsing).

Definition wp_userinit_sconf_body
    `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fileG Σ, !fdslotG Σ, !irefslotG Σ, !pavG Σ}
    `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}
    (γp : gname) (γs : list gname)
    (* THE PARK'S NAMES: the open-file table's two gnames, the wait lock's,
       the ticks lock's, and the disk geometry's three words.  userinit
       reads none of them; they index the six persistent rows below, which
       the first process's trap-loop environment is assembled from at the
       park (SpecForkretParkPaid.v, UsertrapRes.park_env). *)
    (γft γf γw γtl : gname) (pd pav pu : mword 64)
    (m : regfile) (K : nat) (eb : bool) (pj : mword 64)
    (on : option nat) (np : nat) (v0 : mword 64)
    (b : bool) (lks : gset string) :=
  let pcE : mword 64 := mword_of_int KernelSyms.userinit in
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5)) in
  (K_userinit <= K)%nat ->
  (* allocproc's four pages, at its own STRICT convention *)
  (exists nb, on = Some nb /\ (K_allocproc < nb)%nat) ->
  (* allocproc's own [acquire] is on "proc" (9); the only lock taken while
     it is held is namei's "itable" (14), which follows by
     [LockRank.locks_below_mono]. *)
  (* THE TWO CONFIG TIES, forwarded to namei's root corner.  They are
     [FsCfgBoot.fs_boot_supply]'s first two ties, which main holds because
     the boot-era fupd minted the configuration; at [icfg_nib = 0] the
     [inode_held] namei returns could not exist.  They sit ABOVE
     [locks_below] so that main's call can keep discharging that one as a
     side goal. *)
  icfg_dev = ROOTDEV ->
  (0 < icfg_nib)%nat ->
  locks_below lks "proc" ->
  sie_cap_gpr KT1 m K b pj -∗
  cpu_own 0%nat eb pj b lks -∗
  kernel_text -∗ kernel_data -∗ pc_is pcE -∗
  (* iget's "iget: no inodes" arm is live code *)
  panic_env -∗
  (* ---- THE FOUR INODE-CACHE ROWS ----
     userinit's [namei("/")] is the tree's earliest inode-cache client, and
     these four are its whole demand ([SpecNameiRootBoot]'s header is the
     inventory).  Stated at [fileG]'s own configuration fields, so this
     signature grows four PERSISTENT rows and no gname binders; main builds
     them at exactly these names with [IcacheBoot.icache_boot_at] at
     main+0x92 (fs-cfg-boot.md stage (e)). *)
  is_itable2 fsc_itlock fsc_ic fsc_fs fsc_ireg fsc_cov fsc_logst
             icfg_nib icfg_dev -∗
  itable_inv -∗
  ic_escrows fsc_ic fsc_fs fsc_ireg fsc_cov fsc_logst -∗
  ireg_inv fsc_ireg fsc_fs icfg_ist icfg_nib -∗
  (* ---- THE BOOT TOKEN'S DEPOSIT (fs-cfg-boot.md (f-2)) ----
     userinit is the COURIER, not a consumer: it reads none of these three
     and spends none of them.  They are here because the ONE place the boot
     token can be staged is the park userinit performs on the first process
     -- forkret runs on that park's saved context, and its [if (first)] arm
     is the token's only consumer.  main holds all three at +0x9e
     ([ProofMain.mn_grp_fs]) and cannot stage them itself: main never parks
     anything.

     THE CELL IS PINNED, not existential, and that is the whole point: it
     is `static int first = 1`, one of the image's two writable initialized
     .data words, carved at [BootShared.v]'s boot data run and threaded
     pinned through the boot chain.  A holder of [∃ w, first_addr ↦₄ w]
     could not tell which arm of forkret's branch it is in.

     STAGED, NOT YET PASSED.  Until D1 lands ([SpecForkretPark]'s package
     grows a [FirstTok.first_tok] row -- the humans' seam), the proof holds
     these to the [forkret_park] call site and drops them there; the loud
     comment at that site is the handoff.  See [ProofUserinit]. ---- *)
  first_addr ↦₄ (mword_of_int 1 : mword 32) -∗
  first_boot_persist -∗
  first_fsinit -∗
  (* the proc array's lock invariant: allocproc scans it, and release gives
     back the slot userinit found.  Persistent, so threading it is free. *)
  procs_inv γs -∗
  is_lock γp alp_pid_lock "nextpid"%string (λ ξ : CtxId, nextpid_res (XI := ξ)) -∗
  (* ---- THE SIX PARK ROWS (claude-notes/projects/forkret-park.md §3 E3).
     All persistent, none read here: they are what the first process's
     trap loop needs of the kernel BEYOND the file system (which forkret's
     boot arm establishes later and hands to the park's closer).  The
     device complement is stated at the ambient uart / disk / disk-lock
     names, which is what [fclose_ties] pins the record to. ---- *)
  devintr_caps_any fsc_uart fsc_disk fsc_dlock γtl γs pd pav pu -∗
  is_lock γw wait_lock_addr "wait_lock"%string <{ wait_res }> -∗
  is_ftable γft γf -∗
  ConsoleInv.console_ready -∗
  wire_inv -∗
  kmap_at tramp_vpn tramp_ppn KP_rx -∗
  (* ---- the two counted regimes ----
     AT THE AMBIENT [fsc_kalloc], not at a threaded [γa], and that is what
     makes the deposit possible.  The token's allocator row is
     [KvmSpec.kalloc_env_at fsc_kalloc fsc_kpages None] ([FirstTok]'s note says why the
     BUNDLE and not the pair), and userinit mints it by sealing THIS
     regime once allocproc's last counted draw is done.  A [γa] the caller
     chose could never be shown equal to [fsc_kalloc], so the seal's result
     could not be the token's row.  main already applies this contract at
     [fsc_kalloc] -- [ProofMain] builds the bundle out of [kinit]'s own
     post at exactly that name -- so nothing upstream loses generality. *)
  kalloc_env_at fsc_kalloc fsc_kpages on -∗
  procs_avail (Some (S np)) -∗
  (* the one global cell userinit writes *)
  (mword_of_int KernelSyms.initproc : mword 64) ↦₈ v0 -∗
  wp_next b pj (fun (CID : CpuId) =>
    ∀ mf : regfile,
      sie_cap_gpr KT1 mf K b pj -∗
      pc_is ret_tgt -∗
      ⌜ callee_saved m mf
        /\ mf !!! Regidx (mword_of_int 1 : mword 5)
           = (m !!! Regidx (mword_of_int 1 : mword 5) : mword 64) ⌝ -∗
      cpu_own 0%nat eb pj b lks -∗
      (* SEALED, not counted, and irreversibly so: the token userinit
         deposits carries [kalloc_env_at fsc_kalloc fsc_kpages None], and
         [KallocInv.kalloc_avail_seal] is a one-shot.  main discards this
         row anyway -- the boot chain has no further kalloc client on this
         hart -- so the strengthening from "counted" to "sealed" costs its
         one caller nothing. *)
      kalloc_env_at fsc_kalloc fsc_kpages None -∗
      (* SEALED TOO, and for the same reason and at the same instant.  The
         slot ledger leaves the COUNTED regime at userinit's park, because
         that is where the last boot-era allocation has happened and where
         the first process's trap-loop environment is assembled:
         [ProofSyscall.syscall_env]'s [sysc_proc_env] wants
         [procs_avail None], and [ProcAvail.procs_avail_seal] is one-way.
         main discards this row -- nothing in the boot chain allocates a
         proc after userinit -- so the change costs its one caller nothing,
         exactly as the [kalloc_env_at] strengthening one line up does. *)
      procs_avail None -∗
      (* PERSISTED, not handed back exclusive.  Nothing writes this cell
         after userinit's one store, and every later reader
         ([SpecKexit.v], [SpecReparent.v], [SpecSyscall.v]) already takes it
         at an arbitrary [dfrac] -- so discarding here costs no caller
         anything and makes every later copy free.  That is what lets a
         fresh process's trap-loop residue carry its own share:
         [UsertrapRes.ut_own_nopt] wants [initproc ↦₈{un_dqi N} (un_ip N)],
         and [un_dqi] is the record builder's choice
         ([iris/ForkretParkClose.v], [claude-notes/projects/forkret-park.md]). *)
      (∃ v : mword 64, (mword_of_int KernelSyms.initproc : mword 64) ↦₈□ v) -∗
      WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

Module Type USERINIT.
  Parameter wp_userinit_sconf :
    forall `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fileG Σ, !fdslotG Σ, !irefslotG Σ, !pavG Σ}
      `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}
      (γp : gname) (γs : list gname)
      (γft γf γw γtl : gname) (pd pav pu : mword 64)
      (m : regfile) (K : nat) (eb : bool) (pj : mword 64)
      (on : option nat) (np : nat) (v0 : mword 64)
      (b : bool) (lks : gset string),
      wp_userinit_sconf_body γp γs γft γf γw γtl pd pav pu m K eb pj on np v0 b lks.
End USERINIT.
