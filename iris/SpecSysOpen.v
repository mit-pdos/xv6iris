(* SpecSysOpen.v -- the public interface of sys_open(), stated independently
   of its proof.  Requires only the definitional layer -- never a whole-
   function proof file -- so every function proof can be checked in parallel.

     uint64 sys_open(void) {
       char path[MAXPATH];
       int fd, omode;
       struct file *f;
       struct inode *ip;
       int n;

       argint(1, &omode);
       if ((n = argstr(0, path, MAXPATH)) < 0) return -1;

       begin_op();

       if (omode & O_CREATE) {
         ip = create(path, T_FILE, 0, 0);
         if (ip == 0) { end_op(); return -1; }
       } else {
         if ((ip = namei(path)) == 0) { end_op(); return -1; }
         ilock(ip);
         if (ip->type == T_DIR && omode != O_RDONLY) {
           iunlockput(ip); end_op(); return -1;
         }
       }

       if (ip->type == T_DEVICE && (ip->major < 0 || ip->major >= NDEV)) {
         iunlockput(ip); end_op(); return -1;
       }

       if ((f = filealloc()) == 0 || (fd = fdalloc(f)) < 0) {
         if (f) fileclose(f);
         iunlockput(ip); end_op(); return -1;
       }

       if (ip->type == T_DEVICE) { f->type = FD_DEVICE; f->major = ip->major; }
       else                      { f->type = FD_INODE;  f->off = 0; }
       f->ip = ip;
       f->readable = !(omode & O_WRONLY);
       f->writable = (omode & O_WRONLY) || (omode & O_RDWR);

       if ((omode & O_TRUNC) && ip->type == T_FILE) itrunc(ip);

       iunlock(ip);
       end_op();
       return fd;
     }

   @ KernelSyms.sys_open, 342 bytes (CodeSysOpen.v).  A TWENTY-FOUR slot
   frame ([addi sp,sp,-192] at +0x00, [addi s0,sp,192] at +0x06), carved --
   numbering slots from the top, [pa_stk sp0 n] = sp0 - 8n:

     slot  1  (s0-8)    ra
     slot  2  (s0-16)   s0, the frame pointer (= the ENTRY sp)
     slot  3  (s0-24)   s1 = ip  -- saved LATE, at +0x28
     slot  4  (s0-32)   s2 = f   -- saved LATER, at +0x5e
     slot  5  (s0-40)   s3 = fd  -- saved LATER STILL, at +0x68
     slot  6  (s0-48)   dead
     slots 7..22        [char path[MAXPATH]] -- [addi a1,s0,-176]
     slot 23            [int omode] in its UPPER word, [s0-180]
     slot 24            dead (the frame's bottom)

   THE THREE REGISTER SAVES ARE SHRINK-WRAPPED, AND THAT MAKES THE FRAME
   CARVE ARM-DEPENDENT -- unlike sys_chdir's and sys_link's, where one
   [*_frame_join] serves every exit.  The prologue pushes only ra and s0;
   [c.sdsp s1,168] is at +0x28, AFTER the [argstr < 0] branch, [sd s2,160]
   at +0x5e after the T_DEVICE test, [sd s3,152] at +0x68 after filealloc
   succeeded.  The epilogue at +0xca restores only ra/s0, and every arm
   reloads exactly the subset it saved (+0xd8/+0x10a/+0x116 reload s1;
   +0x12e reloads s1+s2; +0x126 reloads s3 then falls into +0x12e; the
   success tail +0xc4 reloads all three).  ARM 0 never owns slot 5 at all.
   Nothing about [path] reaches this contract: it is carved out of
   [stack_own] with [StackBytes.slotsn_bytes_own].

   ==== WHAT THIS CONTRACT IS ABOUT =====================================

   sys_open is the tree's FIRST WRITER of [f->ip] and [f->off], and the only
   syscall that PUBLISHES a file payload out of an inode reference.  Two
   facts about that, because they are what the walk is:

   * THE [+1] INODE REFERENCE NEVER LEAVES.  create / namei hand back a
     reference, and instead of an [iput] the walk PARKS it in [f->ip] with
     [FileInvDefs.inode_pay_alloc]: the shed reference, the generation it
     names and that generation's [ity_shot] become the FD_INODE payload at
     fraction one.  That is the same ledger sentence as sys_chdir's
     [p->cwd], one descriptor further along -- which is why the success arm
     ends one iref unit short and the allowance below is spend-at-most
     rather than conserved.
   * THE WRITABLE-FD-IS-NOT-A-DIRECTORY WITNESS IS THE THEOREM OF THIS
     WALK.  [inode_pay_alloc] demands [wr = true -> ty <> T_DIR], and both
     arms discharge it FROM THE CODE: the O_CREATE arm passes T_FILE (and
     create's ok arm reports [di_type dn ∈ {T_FILE, T_DEVICE}]), while the
     else arm's test at +0xf6 forces [omode = O_RDONLY = 0] on any T_DIR
     inode, whence [f->writable = (omode & 1) || (omode & 3) = 0].  This is
     where filewrite's [DirView.dir_ok] obligation -- five frames up -- is
     actually paid.

   THE [major] BOUNDS CHECK IS ONE UNSIGNED TEST, NOT TWO.  The C is
   [ip->major < 0 || ip->major >= NDEV]; gcc emitted [lhu] + [bltu 9 <u a4].
   A negative [short] zero-extends to [>= 0x8000 > 9], so the single
   unsigned compare decides both disjuncts and the walk has ONE branch to
   price, not a short-circuit pair.

   ==== THE REFERENCE LEDGER, AND WHY IT IS THREE ======================

   [create_slots] -- three, create's own -- goes in, and at most three come
   out spent.  The O_CREATE arm IS create, so its allowance is create's
   verbatim; the else arm's namei takes two and hands one back, and the
   third pays for the reference that ends up in [f->ip].  Every failure arm
   releases what it made ([iunlockput(ip)]), and the success arm keeps
   exactly one -- parked, as above.

   ==== THE LOG LEDGER CLOSES AT THREE, AND THE FLOOR IS THE WALK =======

   begin_op mints [LogInv.log_op g MAXOPBLOCKS] = ten units and end_op
   retires whatever is left, so nothing log-shaped crosses this interface.
   The whole ledger (machine-checked in [SysOpenBudget.v]) turns on what the
   two entry arms leave AT THE JOIN: the else arm leaves nine, and the
   O_CREATE arm can offer only [SpecCreate]'s [ok = true] FLOOR, which is
   [iput_units] = three -- exactly what each of ARMs D/E/F spends on its
   [iunlockput].  Without S6-mkdir's floor the create arm reaches the join
   with a bare [u' <= u] whose corner is zero: the floor is not a
   convenience for this walk, it is the walk ([so_create_nofloor_busts]).
   The COUNTED namei contract busts it at [L = 3] and leaves one where the
   join needs three ([so_counted_namei_busts]), so the SET form is forced
   here for sys_chdir's reason at a longer tail.

   The O_TRUNC tail is payable out of create's three with no credit, because
   [it_entry false u = S (S u)]: freeing a file's blocks costs two, every
   [bfree] hitting the one bitmap block and the tail flush the one inode
   block ([so_trunc_closes]).  sys_open could not supply a credit in any
   case -- create's post reports [Sb ⊆ Sb'] and never a membership.

   ==== THE FILE-TABLE LEDGER: ONE UNIT IN, ONE UNIT OUT ===============

   One [fd_slot] is the syscall's allowance.  filealloc CONSUMES it (the new
   reference has to live somewhere); fdalloc hands one back when it installs
   the descriptor (the descriptor's own unit); filealloc's failure arm hands
   it straight back, and ARM F-FAIL's [fileclose] hands it back after
   fdalloc refused.  So every one of the eight arms returns exactly one.

   ARM F-FAIL's extra [fileclose(f)] IS FREE, and that is
   [SpecFileclose.fileclose_env_none]'s doing: the file it closes is still
   FD_NONE ([SpecFilealloc]'s post pins the type), and fileclose's
   environment at FD_NONE is [emp].  pipealloc's reason, reused -- which is
   why no [fclose_names] and no closing environment appear below.

   ==== WHAT ITS CALLER MUST HOLD ======================================

   [eb = true] is create's and namei's premise, inherited verbatim.  The
   [trap_csrs_ext] / [cpu_claim_ext] complement is threaded anyway, and is
   [emp] there.

   THE CROSSING IS THE LITERAL [true]: this function sleeps in create, in
   namei, in ilock, in itrunc, in begin_op and in end_op, so it may return
   on a hart other than the one it was called on.

   THE BITMAP IS AN INVARIANT ([BitmapInv.bitmap_inv], inside [fs_ready]):
   create's dirlink can ALLOCATE and both the failure arms' iunlockputs and
   the O_TRUNC tail can FREE, and the contract says nothing about either.

   DETERMINISM: none is claimed and none is available.  Which of the eight
   arms runs is a function of the FILE SYSTEM, of the user's path and of
   [omode], and no caller of this contract knows any of that.  The
   postcondition is the honest disjunction on the returned a0. *)
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
Require Import FileInv.               (* [is_ftable], [fnode] *)
Require Import UserPtTree.
Require Import ProcPtOwn.
Require Import ProcInv.
Require Import SpecPrintk.      (* [printk_env], [printk_gen_contract] *)
Require Import SpecDirlink.     (* [ic_sleeplocks], [ireg_blocks_ok] *)
Require Import SpecFdalloc.     (* [fd_frees] *)
Require Import SpecCreate.      (* [create_slots] *)
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import ProcAvail.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Require Import FsCfg.   (* [fscfg]: the fs configuration is AMBIENT *)
Import Defs.

Local Open Scope Z_scope.

(* sys_open's own frame is 192 bytes -- TWENTY-FOUR slots ([addi sp,sp,-192]
   at +0x00) -- over its deepest callee, create (114).  Every other callee
   fits under that: namei 106, fileclose [8 + K_iput] = 68, iunlockput 64,
   argstr 60, end_op 58, itrunc 50, ilock 44, begin_op 26, iunlock 26,
   argint 18, filealloc 14, fdalloc 14. *)
Notation K_sys_open := (148%nat) (only parsing).
(* THE REFERENCE ALLOWANCE.  create's own, and for create's own reason; see
   the header's reference ledger. *)
Definition sys_open_slots : nat := create_slots.

Section SpecSysOpen.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fileG Σ, !fdslotG Σ, !irefslotG Σ}.
  (* [GenId], for [ProcInv.proc_priv]'s own index: the private block now
     carries [FirstTok.first_tok], whose boot arm names [gen_cert].  The
     definitions below mention the block, so the section has to bind it. *)
  Context `{GEN : GenId}.

  (* sys_open's result, keyed by the returned a0, over the process state [W]
     the syscall ends with -- i.e. the incoming [V] with argstr's page-table
     growth already folded in (the continuation below does that with
     [upd_upt], so this predicate is purely about the DESCRIPTORS).

     Both arms hand the fd unit back: see the header's file-table ledger. *)
  Definition sys_open_post (γf : gname) (p : mword 64) (pid : mword 32)
      (W : pprivate) (r : mword 64) : iProp Σ :=
    ((* FAILURE, on any of the seven arms.  The descriptor array is EXACTLY
        as it came in: no arm that installed a descriptor can fail after
        doing so -- fdalloc is the last thing that can refuse. *)
     ⌜r = (mword_of_int (-1) : mword 64)⌝ ∗ proc_priv γf p pid W
     ∨
     (* SUCCESS.  The LEAST free descriptor now names the new file, and the
        returned a0 is that descriptor.  Which file slot it is is
        existential: the file table is not the caller's to name. *)
     ∃ (fd : nat) (l : list nat) (k : nat),
       ⌜r = (mword_of_int (Z.of_nat fd) : mword 64) /\
        fd_frees (pv_ofile W) = fd :: l⌝ ∗
       proc_priv γf p pid (upd_ofile W fd (fnode k)))
    ∗ fd_slot.

End SpecSysOpen.

Definition wp_sys_open_sconf_body
    `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
      !irefslotG Σ, !pavG Σ} `{GEN : GenId} `{CID : CpuId}

    (γfl γf : gname) (γa : gname) (γpr : gname)   (* ftable lock + ghost, kalloc, printk *)
    (gs : list gname) (j : nat) (gl : gname)            (* the running process *)
    (gu : uart_names) (gd : disk_names) (gk : gname)    (* disk fabric + lock  *)
    (pd pav pu : mword 64)
    (bn : bio_names)
    (g : log_names) (gfs : fs_names) (gi : gname)
    (gtl : gname)                       (* the itable's lock   *)
    (cov : gset Z) (logstart bmapstart inodestart : Z) (nib : nat)
    (ninodes : Z) (size : Z) (dev : mword 32)
    (ns : nat)                                          (* the iref ledger     *)
    (dqb dqs dqbs dqn : dfrac)
    (v vom : mword 64)                       (* syscall arguments 0 and 1   *)
    (pid : mword 32) (V : pprivate)
    (m : regfile) (K : nat) (eb : bool)
    (b : bool) (lks : gset string) :=
  let pcE : mword 64 := mword_of_int KernelSyms.sys_open in
  let pj := proc_addr j in
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5)) in
  (K_sys_open <= K)%nat ->
  (* ---- the icache's ambient ties, threaded verbatim to create / namei ---- *)
  dev = icfg_dev ->
  nib = icfg_nib ->
  g = icfg_log ->
  inodestart = icfg_ist ->
  dev = ROOTDEV ->
  (0 < nib)%nat ->
  (* ---- the block-layer geometry, threaded to create / itrunc / iunlockput ---- *)
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
  printk_gen_contract (kt := KT1) γpr gu gd ->
  (* ---- the reference allowance: create's own ---- *)
  (sys_open_slots <= ns)%nat ->
  (j < NPROC)%nat ->
  gs !! j = Some gl ->
  (* create's and namei's own premise, inherited: the body runs with the
     base enabled *)
  eb = true ->
  (* argstr reads syscall argument 0 (the path) and argint argument 1
     (omode) out of the trapframe page [proc_priv] carries.  Nothing is
     assumed about either: argstr checks the string and the walk reads
     [omode] as a plain int. *)
  pv_tf V !! tf_arg_idx 0 = Some v ->
  pv_tf V !! tf_arg_idx 1 = Some vom ->
  sie_cap_gpr KT1 m K b pj -∗
  (* ENTERED WITH NO LOCK HELD, exactly as sys_mkdir: the depth is pinned at
     ZERO, so [CpuOwn.cpu_own_zero_empty] DERIVES [lks = ∅] and every order
     goal the twelve callees raise is [locks_below ∅ _] -- including
     filealloc's and fileclose's "ftable", which is rank 1. *)
  cpu_own 0 eb pj b lks -∗
  (* THE TRAP-CSR COMPLEMENT, THREADED.  [emp] at [eb = true] -- which this
     contract's own premise forces -- so no caller gains an obligation. *)
  trap_csrs_ext KT1 eb -∗
  cpu_claim_ext eb pj -∗
  kernel_text -∗ kernel_data -∗ pc_is pcE -∗
  (* ---- the two persistent credentials ialloc's printk arm needs ---- *)
  printk_env γpr gu gd -∗
  (* ---- the open-file table: filealloc, fdalloc and fileclose ---- *)
  is_ftable γfl γf -∗
  (* ---- the block layer ---- *)
  bio_ctx bn (fs_view gfs gd dev cov) -∗
  log_ctx g bn gfs cov logstart dev -∗
  fs_crash_seam cov logstart -∗
  gen_cert -∗
  dev_inv gu gd -∗
  disk_geom gd pd pav pu -∗
  is_lock gk d_lock "virtio_disk"%string (disk_res gd pd pav pu) -∗
  bslots 3 -∗
  (* ---- the inode cache, and the region ialloc / itrunc claim out of ---- *)
  is_itable2 gtl fsc_ic gfs gi cov logstart nib dev -∗
  itable_inv -∗
  ic_escrows fsc_ic gfs gi cov logstart -∗
  ic_sleeplocks fsc_ic -∗
  ireg_inv gi gfs inodestart nib -∗
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
  bitmap_inv gfs bmapstart cov logstart size -∗
  (* argstr's page-table side, and create's / namei's (iget's ipool arm
     allocates) *)
  kalloc_env γa None -∗
  (* the running-thread bundle *)
  procs_inv gs -∗
  (* ---- the process, whole, and the two allowances ---- *)
  iref_slots ns -∗
  fd_slot -∗
  proc_priv γf pj pid V -∗
  (* THE CROSSING IS THE LITERAL [true], NOT [b]: sys_open sleeps in create,
     in namei, in ilock, in itrunc and in the two op brackets, so it can
     return on another hart whatever SIE was doing.  Vacuous at [true], so
     consuming it costs the caller nothing. *)
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
      (* NO ORDERING on the free pool: create ALLOCATES (balloc under
         dirlink) and both the failure arms and the O_TRUNC tail FREE. *)
      (* THE WHOLE ALLOWANCE, BACK.  The success arm parks a reference in
         [f->ip] and it is NOT spent for good: an untyped table entry's
         payload is itself one unit ([FileInvDefs.file_core_none]), and
         publishing the file releases it in exchange -- the entry holds one
         unit's worth either way, as [iref_frac] when free and as the
         inode reference when open.  Every failure arm iputs instead.  An
         exact ledger is what makes sys_open wireable into the dispatch,
         which lends [IREFSPARE] and must get [IREFSPARE] back. *)
      ⌜ns' = ns⌝ -∗
      iref_slots ns' -∗
      (* the descriptor table, the fd unit and the return value *)
      sys_open_post γf pj pid (upd_upt V P')
        (mf !!! Regidx (mword_of_int 10 : mword 5)) -∗
      WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

Module Type SYSOPEN.
  Parameter wp_sys_open_sconf :
    forall `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ, !irefslotG Σ, !pavG Σ} `{GEN : GenId} `{CID : CpuId}
      (γfl γf : gname) (γa : gname) (γpr : gname)
      (gs : list gname) (j : nat) (gl : gname)
      (gu : uart_names) (gd : disk_names) (gk : gname)
      (pd pav pu : mword 64)
      (bn : bio_names)
      (g : log_names) (gfs : fs_names) (gi : gname)
      (gtl : gname)
      (cov : gset Z) (logstart bmapstart inodestart : Z) (nib : nat)
      (ninodes : Z) (size : Z) (dev : mword 32)
      (ns : nat)
      (dqb dqs dqbs dqn : dfrac)
      (v vom : mword 64)
      (pid : mword 32) (V : pprivate)
      (m : regfile) (K : nat) (eb : bool)
      (b : bool) (lks : gset string),
      wp_sys_open_sconf_body γfl γf γa γpr gs j gl gu gd gk pd pav pu bn g gfs
                             gi gtl cov logstart bmapstart inodestart nib
                             ninodes size dev ns dqb dqs dqbs dqn v vom
                             pid V m K eb b lks.
End SYSOPEN.
