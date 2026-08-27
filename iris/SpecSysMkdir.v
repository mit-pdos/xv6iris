(* SpecSysMkdir.v -- the public interface of sys_mkdir(), stated
   independently of its proof.  Requires only the definitional layer --
   never a whole-function proof file -- so every function proof can be
   checked in parallel.

     uint64 sys_mkdir(void) {
       char path[MAXPATH];
       struct inode *ip;

       begin_op();
       if (argstr(0, path, MAXPATH) < 0 || (ip = create(path, T_DIR, 0, 0)) == 0) {
         end_op();
         return -1;
       }
       iunlockput(ip);
       end_op();
       return 0;
     }

   @ KernelSyms.sys_mkdir, 72 bytes / 26 instructions (CodeSysMkdir.v).
   An EIGHTEEN-slot frame: ra@136 (slot 1), s0@128 (slot 2, the frame
   pointer) and the low SIXTEEN slots -- slot 18 down to slot 3 -- being the
   [char path[128]] local.  [addi aN,s0,-144] is that buffer's address, and
   it is also the pushed sp.  **No callee-saved register beyond ra/s0 is
   touched at all**: [ip] never leaves a0 (create returns it there and
   iunlockput's argument is already in place), so there is no [s1] to save,
   and the epilogue is three instructions.

   ==== WHAT THIS CONTRACT IS ABOUT =====================================

   sys_mkdir is the FIRST of the two syscall-level consumers of the sealed
   [SpecCreate.wp_create_sconf] (sys_mknod is the other, and is this file's
   twin).  It contributes nothing of its own: it opens a log transaction,
   fetches one string, hands it to create with [ty := T_DIR] and
   [major = minor = 0], and drops the LOCKED inode create hands back.  So
   the whole contract is create's own, with the process block and the two
   ledgers threaded around it and everything inode-shaped consumed inside.

   THE C SHORT-CIRCUIT COMPILES TO ONE SHARED FAILURE ARM.  Both
   disjuncts -- the [bltz] at +0x1a on argstr's return and the [c.beqz] at
   +0x2c on create's -- branch to the SAME block at +0x40 (end_op, [a0 =
   -1], jump to the epilogue), with no intermediate rejoin and no register
   to restore.  There are therefore exactly TWO arms, not the four
   sys_chdir has.

   ==== THE LOG LEDGER, AND THE FLOOR IT RESTS ON =======================

   begin_op mints [LogInv.log_op g MAXOPBLOCKS] = ten units, create takes
   the whole reservation in SET form ([LogInv.log_opS], because its own
   distinct-block set is at most six against a counted sum far past ten --
   SpecCreate.v's header), and end_op retires whatever is left.  So nothing
   log-shaped crosses this interface.

   What does NOT close on its own is the [iunlockput(ip)] at +0x2e, which
   runs BEFORE end_op and wants [SpecIput.iput_units] = three in hand.
   Nothing between create's return and that call mints a unit, so the call
   is payable only out of create's own residue -- and create's post offers
   a CEILING ([u' <= u]) that says nothing about it.  The clause that makes
   this function provable is the [ok = true] floor
   [(iput_units <= u')%nat], added to [SpecCreate]'s post for exactly these
   two callers.  It is guarded on [ok] and the guard is forced (create's
   [fail:] tail cannot pay it -- see SpecCreate.v's header); [ok = true] is
   precisely when this function runs its [iunlockput], so the guard costs
   nothing here.  On the mkdir arm the floor is ATTAINED, with zero slack
   ([CreateBudget.cr_budget_mkdir]'s [u6 = 3]).

   ==== THE REFERENCE LEDGER ============================================

   create is entered with [iref_slots ns] for [create_slots <= ns] and, on
   success, keeps exactly ONE out -- the reference to the inode it returns
   -- which its post now states as the equation [S ns' = ns].
   [iunlockput(ip)] spends that reference and hands the slot back, so the
   success arm ends at [ns' + 1 = ns]; the failure arms never made a
   reference and create's post gives [ns' = ns] outright; and the argstr
   arm never reached create.  All three therefore end at [ns], which is
   what this contract says.

   IT USED TO SAY THE INTERVAL [ns - create_slots <= ns2 <= ns], on the
   grounds that create's own figure was an interval and this was the
   tightest thing statable.  That was true of the STATEMENT and not of the
   function: all nine of create's continuation sites already computed the
   exact figure and then weakened it.  Saying it outright is what lets a
   caller re-establish [create_slots <= ns] and go round again, and what
   lets [SpecSyscall]'s dispatch hand [iref_slots IREFSPARE] back
   unchanged -- which it must, because [UsertrapRes.ut_own] carries the
   allowance at that literal.

   NO COLOUR-LEDGER RESOURCE APPEARS HERE (design/fs-icache.md 20.18
   ruling 1).  Every directory record this syscall writes is written
   INSIDE create, whose contract owns that accounting.

   ==== WHAT ITS CALLER MUST HOLD ======================================

   Strictly more than sys_chdir's, and all of it is create's rather than
   this function's: the printk credential pair ([printk_env] and the pure
   [printk_gen_contract]) that ialloc's out-of-inodes arm needs, all FOUR
   superblock cells rather than two ([sb_ninodes] and [sb_size] beside
   [sb_inodestart] and [sb_bmapstart]), and mkfs's inode geometry
   ([1 < ninodes <= 16 * nib < 2^31] plus the [ushort] tie
   [16 * nib <= 2^16] create's [lw a2,4(s3)] consumes).

   [eb = true] is create's premise, inherited verbatim.  The
   [trap_csrs_ext] / [cpu_claim_ext] complement is threaded anyway,
   uniformly with begin_op / iunlockput / end_op, and is [emp] there --
   create itself does not take the pair, so the walk drops it and re-mints
   per callee (ProofNamex's device).

   THE CROSSING IS THE LITERAL [true]: this function sleeps in all four of
   its callees, so it may return on a hart other than the one it was called
   on.

   DETERMINISM: none is claimed, and none is available.  Which of the two
   arms runs is a function of the FILE SYSTEM and of the user string, and
   no caller of this contract knows either.  The postcondition is therefore
   the honest disjunction on the returned a0. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list functions bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import auth gmap frac.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap ghost_map.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto.
Require Import InstrBytes.
Require Import RegFile.
Require Import RiscvExtras.
Require Import CalleeSaved KernelText KernelDataInv.
Require Import IntrDefs.
Require Import WpNext.
Require Import WpLock.
Require Import FdSlots.
Require Import ProcGeom.
Require Export SwtchCtx.
Require Import CpuOwn.
Require Import SchedCtx.
Require Import WpUart.
Require Import DiskPtsto DiskInv.
Require Import BioInv.
Require Import FsBlocks LogInv.
Require Import FsCrash.
Require Import BitmapInv.
Require Import InodeInv.
Require Import InodeRegion.
Require Import IrefSlots.
Require Import IcacheRef.
Require Import IcacheInv.
Require Import IcacheEscrow.
Require Import KvmSpec.
Require Import FileInvDefs.
Require Import UserPtTree.
Require Import ProcPtOwn.
Require Import ProcInv.
Require Import SpecPrintk.      (* [printk_env], [printk_gen_contract] *)
Require Import SpecDirlink.     (* [ic_sleeplocks], [ireg_blocks_ok] *)
Require Import SpecCreate.      (* [create_slots], [create_units], [K_create] *)
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import ProcAvail.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Require Import FsCfg.   (* [fscfg]: the fs configuration is AMBIENT *)
Import Defs.

Local Open Scope Z_scope.

(* sys_mkdir's own frame is 144 bytes -- EIGHTEEN slots ([c.addi16sp sp,-144]
   at +0x00), of which sixteen are the [path] buffer.  Its deepest callee is
   create (114); iunlockput wants 64, argstr 60, end_op 58, begin_op 26. *)
Notation K_sys_mkdir := (142%nat) (only parsing).
Section SpecSysMkdir.
  Context `{!riscvGS Σ, FSC : fscfg}.

  (* sys_mkdir's result: 0, or -1.  Nothing else reaches the caller -- the
     inode create returned was iunlockput inside, and [proc_priv] comes back
     at the SAME record (only the page table may have grown, which is
     argstr's report and is relayed separately). *)
  Definition sys_mkdir_ret (r : mword 64) : Prop :=
    r = (zero_reg : mword 64) \/ r = (mword_of_int (-1) : mword 64).

End SpecSysMkdir.

Definition wp_sys_mkdir_sconf_body
    `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
      !irefslotG Σ, !pavG Σ} `{GEN : GenId} `{CID : CpuId}

    (γf : gname) (γa : gname) (γpr : gname)             (* ftable, kalloc, printk *)
    (gs : list gname) (j : nat) (gl : gname)            (* the running process *)
    (gu : uart_names) (gd : disk_names) (gk : gname)    (* disk fabric + lock  *)
    (pd pav pu : mword 64)
    (bn : bio_names)
    (g : log_names)
    (gtl : gname)                       (* the itable's lock   *)
    (bmapstart inodestart : Z) (nib : nat)
    (ninodes : Z) (size : Z) (dev : mword 32)
    (ns : nat)                                          (* the iref ledger     *)
    (dqb dqs dqbs dqn : dfrac)
    (v : mword 64)                                      (* syscall argument 0  *)
    (pid : mword 32) (V : pprivate)
    (m : regfile) (K : nat) (eb : bool)
    (b : bool) (lks : gset string) :=
  let pcE : mword 64 := mword_of_int KernelSyms.sys_mkdir in
  let pj := proc_addr j in
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5)) in
  (K_sys_mkdir <= K)%nat ->
  (* ---- the icache's ambient ties, threaded verbatim to create ---- *)
  dev = icfg_dev ->
  nib = icfg_nib ->
  g = icfg_log ->
  inodestart = icfg_ist ->
  dev = ROOTDEV ->
  (0 < nib)%nat ->
  (* ---- the block-layer geometry, threaded verbatim to create / iunlockput ---- *)
  log_geom_ok fsc_cov fsc_logst ->
  0 < size <= BPB ->
  0 <= bmapstart ->
  bmapstart ∈ fsc_cov ->
  ~ (bmapstart ∈ log_region_set fsc_logst) ->
  0 <= inodestart ->
  cov_below fsc_cov size ->
  bitmap_geom_ok fsc_cov fsc_logst bmapstart size ->
  ireg_blocks_ok inodestart nib fsc_cov fsc_logst ->
  (* ---- ialloc's three geometry premises, and mkfs's [ushort] tie ---- *)
  1 < ninodes ->
  ninodes <= 16 * Z.of_nat nib ->
  ninodes < 2 ^ 31 ->
  16 * Z.of_nat nib <= 2 ^ 16 ->
  (* ---- ialloc's no-inodes arm calls printk, not panic ---- *)
  printk_gen_contract (kt := KT1) γpr gu gd ->
  (* ---- the reference allowance create's walk needs ---- *)
  (create_slots <= ns)%nat ->
  (j < NPROC)%nat ->
  gs !! j = Some gl ->
  (* create's own premise, inherited: the body runs with the base enabled *)
  eb = true ->
  (* argstr reads syscall argument 0 out of the trapframe page [proc_priv]
     carries *)
  pv_tf V !! tf_arg_idx 0 = Some v ->
  sie_cap_gpr KT1 m K b pj -∗
  (* ENTERED WITH NO LOCK HELD, exactly as sys_chdir: the depth is pinned at
     ZERO, so [CpuOwn.cpu_own_zero_empty] DERIVES [lks = ∅] and every order
     goal the four callees raise is [locks_below ∅ _]. *)
  cpu_own 0 eb pj b lks -∗
  (* THE TRAP-CSR COMPLEMENT, THREADED.  [emp] at [eb = true] -- which this
     contract's own premise forces -- so no caller gains an obligation. *)
  trap_csrs_ext KT1 eb -∗
  cpu_claim_ext eb pj -∗
  kernel_text -∗ kernel_data -∗ pc_is pcE -∗
  (* ---- the two persistent credentials ialloc's printk arm needs ---- *)
  printk_env γpr gu gd -∗
  (* ---- the block layer ---- *)
  bio_ctx bn (fs_view fsc_fs gd dev fsc_cov) -∗
  log_ctx g bn fsc_fs fsc_cov fsc_logst dev -∗
  fs_crash_seam fsc_cov fsc_logst -∗
  gen_cert -∗
  dev_inv gu gd -∗
  disk_geom gd pd pav pu -∗
  is_lock gk d_lock "virtio_disk"%string (disk_res gd pd pav pu) -∗
  bslots 3 -∗
  (* ---- the inode cache, and the region ialloc claims out of ---- *)
  is_itable2 gtl fsc_ic fsc_fs fsc_ireg fsc_cov fsc_logst nib dev -∗
  itable_inv -∗
  ic_escrows fsc_ic fsc_fs fsc_ireg fsc_cov fsc_logst -∗
  ic_sleeplocks fsc_ic -∗
  ireg_inv fsc_ireg fsc_fs inodestart nib -∗
  (* ...AND THE SEALED REGIME (iclaim-ledger.md §3.2, RULING B).  Persistent,
     borrowed and never spent; it rides the SAME channel [ireg_inv] does,
     down to [SpecCreate] -> [SpecIalloc] -> [InodeRegion.ireg_claim_au],
     the one mover that mints a [c] column.  Its producer is the boot
     chain's ([IcacheRef.ity_shoot] on fsinit's returned [ireg_boot]), which
     terminates at the EXISTING [LinkForkretNF.wp_forkret_nf_ax] IOU -- no
     new axiom, and a premise pulls nothing into [Print Assumptions]. *)
  ireg_open -∗
  (* ---- the FOUR superblock cells (create reads all of them) ---- *)
  sb_ninodes ↦₄{dqn} (mword_of_int ninodes : mword 32) -∗
  sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
  sb_size ↦₄{dqbs} (mword_of_int size : mword 32) -∗
  sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
  bitmap_inv fsc_fs bmapstart fsc_cov fsc_logst size -∗
  (* argstr's page-table side, and create's (iget's ipool arm allocates) *)
  kalloc_env γa None -∗
  (* the running-thread bundle *)
  procs_inv gs -∗
  (* ---- the process, whole, and the reference allowance ---- *)
  iref_slots ns -∗
  proc_priv γf pj pid V -∗
  (* THE CROSSING IS THE LITERAL [true], NOT [b]: sys_mkdir sleeps (begin_op,
     argstr's fault path, create and end_op all park), so it can return on
     another hart whatever SIE was doing. *)
  wp_next true pj (fun (CID : CpuId) =>
  ∀ (mf : regfile) (ns' : nat) (P' : uptd),
      ⌜callee_saved m mf⌝ -∗
      (* the page table may have GROWN: argstr's fetchstr faults user pages
         in.  [uptd_ext] is argstr's own report, relayed. *)
      ⌜uptd_ext (pv_upt V) P'⌝ -∗
      sie_cap_gpr KT1 mf K b pj -∗
      cpu_own 0 eb pj b lks -∗
      trap_csrs_ext KT1 eb -∗
      cpu_claim_ext eb pj -∗
      pc_is ret_tgt -∗
      bslots 3 -∗
      sb_ninodes ↦₄{dqn} (mword_of_int ninodes : mword 32) -∗
      sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
      sb_size ↦₄{dqbs} (mword_of_int size : mword 32) -∗
      sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
      (* NO ORDERING on the free pool: create both ALLOCATES (balloc under
         dirlink) and FREES (itrunc under its fail arm's iunlockput of a
         link-count-zero inode), and the two do not cancel. *)
      (* the allowance, spend-at-most: see the header's reference ledger *)
      (* THE LEDGER CLOSES, EXACTLY.  This used to be create's interval
         passed through; create states its figure exactly now (every failure
         arm returns the ledger whole, every success arm keeps ONE out), and
         this function's [iunlockput] is what hands that one back -- so all
         three arms end where they started.  A client can therefore
         re-establish its own [create_slots <= ns] and call again, which the
         interval could not support (FsSyscalls.v's note (S3)). *)
      ⌜ns' = ns⌝ -∗
      iref_slots ns' -∗
      proc_priv γf pj pid (upd_upt V P') -∗
      ⌜sys_mkdir_ret (mf !!! Regidx (mword_of_int 10 : mword 5))⌝ -∗
      WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

Module Type SYSMKDIR.
  Parameter wp_sys_mkdir_sconf :
    forall `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ, !irefslotG Σ, !pavG Σ} `{GEN : GenId} `{CID : CpuId}
      (γf : gname) (γa : gname) (γpr : gname)
      (gs : list gname) (j : nat) (gl : gname)
      (gu : uart_names) (gd : disk_names) (gk : gname)
      (pd pav pu : mword 64)
      (bn : bio_names)
      (g : log_names)
      (gtl : gname)
      (bmapstart inodestart : Z) (nib : nat)
      (ninodes : Z) (size : Z) (dev : mword 32)
      (ns : nat)
      (dqb dqs dqbs dqn : dfrac)
      (v : mword 64)
      (pid : mword 32) (V : pprivate)
      (m : regfile) (K : nat) (eb : bool)
      (b : bool) (lks : gset string),
      wp_sys_mkdir_sconf_body γf γa γpr gs j gl gu gd gk pd pav pu bn g
                              gtl bmapstart inodestart nib
                              ninodes size dev ns dqb dqs dqbs dqn v
                              pid V m K eb b lks.
End SYSMKDIR.
