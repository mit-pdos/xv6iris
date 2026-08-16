(* SpecSysMknod.v -- the public interface of sys_mknod(), stated
   independently of its proof.  Requires only the definitional layer --
   never a whole-function proof file -- so every function proof can be
   checked in parallel.

     uint64 sys_mknod(void) {
       struct inode *ip;
       char path[MAXPATH];
       int major, minor;

       begin_op();
       argint(1, &major);
       argint(2, &minor);
       if ((argstr(0, path, MAXPATH)) < 0 ||
           (ip = create(path, T_DEVICE, major, minor)) == 0) {
         end_op();
         return -1;
       }
       iunlockput(ip);
       end_op();
       return 0;
     }

   @ KernelSyms.sys_mknod, 96 bytes / 32 instructions (CodeSysMknod.v).
   A TWENTY-slot frame: ra@152 (slot 1), s0@144 (slot 2, the frame
   pointer), the [char path[128]] local in slots 18 down to 3
   ([addi aN,s0,-144]), **the two [int] locals sharing slot 19** -- [minor]
   in its low word at [s0-152], [major] in its high word at [s0-148] --
   and slot 20 unused padding.  As in sys_mkdir, [ip] never leaves a0, so
   no callee-saved register beyond ra and s0 is ever touched.

   ==== WHAT THIS CONTRACT IS ABOUT =====================================

   sys_mknod is sys_mkdir's twin: the second syscall-level consumer of the
   sealed [SpecCreate.wp_create_sconf], differing only in what it puts in
   create's argument registers.  It opens a log transaction, fetches two
   [int]s and one string, hands them to create with [ty := T_DEVICE], and
   drops the LOCKED inode create hands back.  Everything the header of
   SpecSysMkdir.v says about the ledgers, the shared failure arm and the
   dropped complement holds here verbatim; only the three points below are
   its own.

   TWO C LOCALS IN ONE FRAME SLOT, AND A HALFWORD READ OUT OF AN [int].
   argint writes a 4-byte cell; the [lh a3,-152(s0)] / [lh a2,-148(s0)] at
   +0x32 / +0x36 then read the LOW HALFWORD of each, because create's
   [short major, short minor] parameters are narrower than the [int]
   locals.  So the walk splits slot 19 into two words
   ([InstrBytes.word_pointsto_split4]) and each word into two halfwords,
   and rejoins on the way to the epilogue.  Nothing about it reaches this
   contract: the values are consumed inside create and the inode is
   dropped, so neither [major] nor [minor] appears below.  What the caller
   must supply is only that trapframe words [tf_arg_idx 1] and
   [tf_arg_idx 2] exist -- argraw's premise, spelled through [pv_tf V].

   BOTH argint RETURN VALUES ARE IGNORED by the C, and [SpecArgint]'s post
   claims nothing about a0, so there is nothing to discard and no arm to
   refute: an out-of-range index would have panicked inside argraw, which
   is why the index premises are [i < NARG] here rather than a branch.

   ==== THE LEDGERS, AND WHAT THEY REST ON ==============================

   Identical to sys_mkdir's, and for identical reasons.  begin_op mints ten
   units, create takes the whole reservation in SET form, end_op retires
   the rest; the [iunlockput(ip)] at +0x46 runs BEFORE end_op and is
   payable only out of create's residue, which is what the [ok = true]
   floor [(iput_units <= u')%nat] in create's post exists for.  This arm is
   the NON-directory one, so it closes with slack
   ([CreateBudget.cr_budget_file]) where sys_mkdir's closes exactly; the
   clause is the same clause.

   The reference ledger is likewise sys_mkdir's: create keeps one slot out
   on success ([ok = true -> S ns' <= ns]) and the [iunlockput] hands it
   back, so [ns - create_slots <= ns2 <= ns] covers both arms.

   ==== WHAT ITS CALLER MUST HOLD ======================================

   create's premise set, unchanged: the printk credential pair ialloc's
   out-of-inodes arm needs, all FOUR superblock cells, and mkfs's inode
   geometry including the [ushort] tie [16 * nib <= 2^16].  [eb = true] is
   create's premise inherited verbatim; the [trap_csrs_ext] /
   [cpu_claim_ext] complement is threaded but is [emp] there.

   THE CROSSING IS THE LITERAL [true]: this function sleeps in begin_op,
   argstr's fault path, create and end_op, so it may return on a hart other
   than the one it was called on.  (The two argint calls do NOT park --
   their own crossing is at [b] -- but the function's is the join of all
   five.)

   DETERMINISM: none is claimed, and none is available.  The postcondition
   is the honest disjunction on the returned a0. *)
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
Require Import PanicStub.
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
Require Import KallocInv.
Require Import KvmSpec.
Require Import FileInvDefs.
Require Import UserPtTree.
Require Import ProcPtOwn.
Require Import ProcInv.
Require Import SpecPrintk.      (* [printk_env], [printk_gen_contract] *)
Require Import SpecIput.        (* [iput_units] *)
Require Import SpecDirlink.     (* [ic_sleeplocks], [ireg_blocks_ok] *)
Require Import SpecNamex.       (* [ROOTDEV] *)
Require Import SpecCreate.      (* [create_slots], [create_units], [T_DEVICE] *)
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import ProcAvail.
Import Defs.

Local Open Scope Z_scope.

(* sys_mknod's own frame is 160 bytes -- TWENTY slots ([c.addi16sp sp,-160]
   at +0x00), of which sixteen are the [path] buffer and one holds the two
   [int] locals.  Its deepest callee is create (114); iunlockput wants 64,
   argstr 60, end_op 58, begin_op 26, argint 18. *)
Notation K_sys_mknod := (144%nat) (only parsing).
Section SpecSysMknod.
  Context `{!riscvGS Σ}.

  (* sys_mknod's result: 0, or -1.  Nothing else reaches the caller -- the
     inode create returned was iunlockput inside, and [proc_priv] comes back
     at the SAME record but for argstr's page-table growth, which is relayed
     separately. *)
  Definition sys_mknod_ret (r : mword 64) : Prop :=
    r = (zero_reg : mword 64) \/ r = (mword_of_int (-1) : mword 64).

End SpecSysMknod.

Definition wp_sys_mknod_sconf_body
    `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !fileG Σ, !kallocG Σ,
      !bioG Σ, !diskGhostG Σ, !uartGhostG Σ, !fsLogG Σ, !logG Σ, !fsCrashG Σ,
      !irefslotG Σ, !pavG Σ, !iregG Σ}
    `{GEN : GenId} `{CID : CpuId}

    (γf : gname) (γa : gname) (γpr : gname)             (* ftable, kalloc, printk *)
    (gs : list gname) (j : nat) (gl : gname)            (* the running process *)
    (gu : uart_names) (gd : disk_names) (gk : gname)    (* disk fabric + lock  *)
    (pd pav pu : mword 64)
    (bn : bio_names)
    (g : log_names) (gfs : fs_names) (gi : gname)
    (cn : ic_names) (gtl : gname)                       (* the icache + itable *)
    (cov : gset Z) (logstart bmapstart inodestart : Z) (nib : nat)
    (ninodes : Z) (size : Z) (dev : mword 32)
    (used : gset Z)
    (ns : nat)                                          (* the iref ledger     *)
    (dqb dqs dqbs dqn : dfrac)
    (v0 v1 v2 : mword 64)                    (* syscall arguments 0 / 1 / 2 *)
    (pid : mword 32) (V : pprivate)
    (m : regfile) (K : nat) (eb : bool)
    (b : bool) (lks : gset string) :=
  let pcE : mword 64 := mword_of_int KernelSyms.sys_mknod in
  let pj := proc_addr j in
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5)) in
  (K_sys_mknod <= K)%nat ->
  (* ---- the icache's ambient ties, threaded verbatim to create ---- *)
  dev = icfg_dev ->
  nib = icfg_nib ->
  g = icfg_log ->
  inodestart = icfg_ist ->
  dev = ROOTDEV ->
  (0 < nib)%nat ->
  (* ---- the block-layer geometry, threaded verbatim to create / iunlockput ---- *)
  log_geom_ok cov logstart ->
  0 < size <= BPB ->
  0 <= bmapstart ->
  bmapstart ∈ cov ->
  ~ (bmapstart ∈ log_region_set logstart) ->
  0 <= inodestart ->
  cov_below cov size ->
  bitmap_geom_ok cov logstart bmapstart size ->
  ireg_blocks_ok inodestart nib cov logstart ->
  (* ---- ialloc's three geometry premises, and mkfs's [ushort] tie ---- *)
  1 < ninodes ->
  ninodes <= 16 * Z.of_nat nib ->
  ninodes < 2 ^ 31 ->
  16 * Z.of_nat nib <= 2 ^ 16 ->
  (* ---- ialloc's no-inodes arm calls printk, not panic ---- *)
  printk_gen_contract γpr gu gd ->
  (* ---- the reference allowance create's walk needs ---- *)
  (create_slots <= ns)%nat ->
  (j < NPROC)%nat ->
  gs !! j = Some gl ->
  (* create's own premise, inherited: the body runs with the base enabled *)
  eb = true ->
  (* THE THREE SYSCALL ARGUMENTS, read out of the trapframe page
     [proc_priv] carries: argstr takes 0, and the two argints take 1 and 2.
     The VALUES do not reach the postcondition -- [major] and [minor] are
     consumed inside create and the inode is dropped -- so all the caller
     owes is that the words exist. *)
  pv_tf V !! tf_arg_idx 0 = Some v0 ->
  pv_tf V !! tf_arg_idx 1 = Some v1 ->
  pv_tf V !! tf_arg_idx 2 = Some v2 ->
  sie_cap_gpr m K b pj -∗
  (* ENTERED WITH NO LOCK HELD: the depth is pinned at ZERO, so
     [CpuOwn.cpu_own_zero_empty] DERIVES [lks = ∅] and every order goal the
     five callees raise is [locks_below ∅ _]. *)
  cpu_own 0 eb pj b lks -∗
  (* THE TRAP-CSR COMPLEMENT, THREADED.  [emp] at [eb = true] -- which this
     contract's own premise forces -- so no caller gains an obligation. *)
  trap_csrs_ext eb -∗
  cpu_claim_ext eb pj -∗
  kernel_text -∗ kernel_data -∗ pc_is pcE -∗
  panic_wp_any -∗
  (* ---- the two persistent credentials ialloc's printk arm needs ---- *)
  printk_env γpr gu gd -∗
  (* ---- the block layer ---- *)
  bio_ctx bn (fs_view gfs gd dev cov) -∗
  log_ctx g bn gfs cov logstart dev -∗
  fs_crash_seam cov logstart -∗
  gen_cert -∗
  dev_inv gu gd -∗
  disk_geom gd pd pav pu -∗
  is_lock gk d_lock "virtio_disk"%string (disk_res gd pd pav pu) -∗
  bslots bn 3 -∗
  (* ---- the inode cache, and the region ialloc claims out of ---- *)
  is_itable2 gtl cn gfs gi cov logstart nib dev -∗
  itable_inv -∗
  ic_escrows cn gfs gi cov logstart -∗
  ic_sleeplocks cn -∗
  ireg_inv gi gfs inodestart nib -∗
  (* ---- the FOUR superblock cells (create reads all of them) ---- *)
  sb_ninodes ↦₄{dqn} (mword_of_int ninodes : mword 32) -∗
  sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
  sb_size ↦₄{dqbs} (mword_of_int size : mword 32) -∗
  sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
  bitmap_res gfs bmapstart cov logstart size used -∗
  (* argstr's page-table side, and create's (iget's ipool arm allocates) *)
  kalloc_env γa None -∗
  (* the running-thread bundle *)
  procs_inv gs -∗
  (* ---- the process, whole, and the reference allowance ---- *)
  iref_slots ns -∗
  proc_priv γf pj pid V -∗
  (* THE CROSSING IS THE LITERAL [true], NOT [b]: sys_mknod sleeps (begin_op,
     argstr's fault path, create and end_op all park), so it can return on
     another hart whatever SIE was doing. *)
  wp_next true pj (fun (CID : CpuId) =>
  ∀ (mf : regfile) (used' : gset Z) (ns' : nat) (P' : uptd),
      ⌜callee_saved m mf⌝ -∗
      (* the page table may have GROWN: argstr's fetchstr faults user pages
         in.  [uptd_ext] is argstr's own report, relayed. *)
      ⌜uptd_ext (pv_upt V) P'⌝ -∗
      sie_cap_gpr mf K b pj -∗
      cpu_own 0 eb pj b lks -∗
      trap_csrs_ext eb -∗
      cpu_claim_ext eb pj -∗
      pc_is ret_tgt -∗
      bslots bn 3 -∗
      sb_ninodes ↦₄{dqn} (mword_of_int ninodes : mword 32) -∗
      sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
      sb_size ↦₄{dqbs} (mword_of_int size : mword 32) -∗
      sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
      (* NO ORDERING on the free pool: create both ALLOCATES and FREES. *)
      bitmap_res gfs bmapstart cov logstart size used' -∗
      (* the allowance, spend-at-most: see the header's reference ledger *)
      ⌜((ns - create_slots)%nat <= ns')%nat /\ (ns' <= ns)%nat⌝ -∗
      iref_slots ns' -∗
      proc_priv γf pj pid (upd_upt V P') -∗
      ⌜sys_mknod_ret (mf !!! Regidx (mword_of_int 10 : mword 5))⌝ -∗
      WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

Module Type SYSMKNOD.
  Parameter wp_sys_mknod_sconf :
    forall `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !fileG Σ, !kallocG Σ,
             !bioG Σ, !diskGhostG Σ, !uartGhostG Σ, !fsLogG Σ, !logG Σ,
             !fsCrashG Σ, !irefslotG Σ, !pavG Σ, !iregG Σ}
      `{GEN : GenId} `{CID : CpuId}
      (γf : gname) (γa : gname) (γpr : gname)
      (gs : list gname) (j : nat) (gl : gname)
      (gu : uart_names) (gd : disk_names) (gk : gname)
      (pd pav pu : mword 64)
      (bn : bio_names)
      (g : log_names) (gfs : fs_names) (gi : gname)
      (cn : ic_names) (gtl : gname)
      (cov : gset Z) (logstart bmapstart inodestart : Z) (nib : nat)
      (ninodes : Z) (size : Z) (dev : mword 32)
      (used : gset Z)
      (ns : nat)
      (dqb dqs dqbs dqn : dfrac)
      (v0 v1 v2 : mword 64)
      (pid : mword 32) (V : pprivate)
      (m : regfile) (K : nat) (eb : bool)
      (b : bool) (lks : gset string),
      wp_sys_mknod_sconf_body γf γa γpr gs j gl gu gd gk pd pav pu bn g gfs gi
                              cn gtl cov logstart bmapstart inodestart nib
                              ninodes size dev used ns dqb dqs dqbs dqn
                              v0 v1 v2 pid V m K eb b lks.
End SYSMKNOD.
