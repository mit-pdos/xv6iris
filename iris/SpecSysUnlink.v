(* SpecSysUnlink.v -- the public interface of sys_unlink(), stated
   independently of its proof.  Requires only the definitional layer --
   never a whole-function proof file -- so every function proof can be
   checked in parallel.

     uint64 sys_unlink(void) {
       struct inode *ip, *dp;
       struct dirent de;
       char name[DIRSIZ], path[MAXPATH];
       uint off;

       if (argstr(0, path, MAXPATH) < 0) return -1;

       begin_op();
       if ((dp = nameiparent(path, name)) == 0) { end_op(); return -1; }

       ilock(dp);

       // Cannot unlink "." or "..".
       if (namecmp(name, ".") == 0 || namecmp(name, "..") == 0)
         goto bad;

       if ((ip = dirlookup(dp, name, &off)) == 0)
         goto bad;
       ilock(ip);

       if (ip->nlink < 1) panic("unlink: nlink < 1");
       if (ip->type == T_DIR && !isdirempty(ip)) {
         iunlockput(ip);
         goto bad;
       }

       memset(&de, 0, sizeof(de));
       if (writei(dp, 0, (uint64)&de, off, sizeof(de)) != sizeof(de))
         panic("unlink: writei");
       if (ip->type == T_DIR) { dp->nlink--; iupdate(dp); }
       iunlockput(dp);

       ip->nlink--;
       iupdate(ip);
       iunlockput(ip);

       end_op();
       return 0;

      bad:
       iunlockput(dp);
       end_op();
       return -1;
     }

   @ KernelSyms.sys_unlink, 384 bytes / 129 instructions (CodeSysUnlink.v),
   the LARGEST function in sysfile.c and the last one proven.  A THIRTY slot
   frame ([c.addi16sp sp,-240] at +0x00, [c.addi4spn s0,sp,240] at +0x06),
   carved -- numbering slots from the top, [pa_stk sp0 n] = sp0 - 8n:

     slot  1  (s0-8)    ra
     slot  2  (s0-16)   s0, the frame pointer (= the ENTRY sp)
     slot  3  (s0-24)   s1 = dp  -- saved LATE, at +0x1a
     slot  4  (s0-32)   s2 = ip  -- saved LATER, at +0x5c
     slot  5  (s0-40)   s3       -- saved LATER STILL, at +0x72
     slots 6..7         dead
     slots 7..8         [struct dirent de] -- writei's, [addi s3,s0,-64]
     slots 9..10        [char name[DIRSIZ]] -- [addi a1,s0,-80]
     slots 11..26       [char path[MAXPATH]] -- [addi a1,s0,-208]
     slot 27            [uint off] in its UPPER word, [s0-212]
     slots 28..29       [struct dirent de] -- isdirempty's, [addi a2,s0,-232]
     slot 30            dead (the frame's bottom)

   THE TWO [de] BUFFERS ARE DIFFERENT SLOTS, and that is not an accident of
   the carve: gcc INLINED isdirempty (see below), and the two [de]s have
   disjoint live ranges, so it gave each its own storage.

   [s3] is DUAL-USE -- isdirempty's loop counter [off] at +0x104..+0x128,
   then the address [&de] at +0x8a -- which is why it is saved before
   [ilock(ip)] and reloaded on every arm at or below the isdirempty test.

   THE THREE REGISTER SAVES ARE SHRINK-WRAPPED, SO THE FRAME CARVE IS
   ARM-DEPENDENT (sys_open's shape, not sys_link's): the prologue pushes
   only ra and s0; [c.sdsp s1,216] is at +0x1a, AFTER the [argstr < 0]
   branch, [c.sdsp s2,208] at +0x5c after BOTH namecmp guards, and
   [c.sdsp s3,200] at +0x72 after dirlookup succeeded.  Each exit restores
   exactly the subset its own path saved: ARM A (+0x170) restores nothing,
   ARM B (+0xe8) restores s1, the [bad:] tail (+0x166) restores s1, ARM D
   (+0x158) restores s2 then falls into [bad:], ARM E (+0x17a) restores s2
   and s3 then falls into [bad:], and the success tail (+0xda) restores all
   three.  Nothing about the two buffers reaches this contract: they are
   carved out of [stack_own] with [StackBytes.slotsn_bytes_own].

   ==== isdirempty HAS NO SYMBOL ========================================

   [grep -i isdirempty kernel-rocq/*.v] is EMPTY and [KernelSyms.v] names
   only [sys_unlink]: gcc folded the whole helper into
   sys_unlink+0x0f8..+0x12c.  So there is no [CodeIsdirempty.v], no
   contract, no coverage row and there never will be -- the loop is a BLOCK
   LEMMA inside [ProofSysUnlink], and its invariant is a fact about that
   block.  Two consequences reach this interface:

   * THE LOOP SPENDS NO LOG BUDGET WHATEVER.  Its body is [readi], whose
     contract takes no [log_op], no [log_ctx] and no [γ : log_names] at all
     ([SpecReadi.v]'s "READI MODIFIES NOTHING" banner), so however many
     records the directory has, no arm's figure depends on its size.  That
     is what makes the whole ledger parameter-free in the directory.
   * ITS SHORT-READ ARM IS A PANIC.  [readi] is EXACT, so
     [!= sizeof(de)] is reachable only where 16 does not divide the
     directory's size; the arm needs no multiple-of-16 invariant, it is
     discharged against [SpecPanic] and never returns.

   ==== WHAT THIS CONTRACT IS ABOUT =====================================

   sys_unlink is the kernel's ONLY record-DELETING path, and the walk is
   where the fragment campaign's delete half is finally spent.  Three facts,
   because they are what the walk is:

   * THE ZEROING COLLAPSES A TICKET.  [memset(&de,0,16)] then
     [writei(dp,0,&de,off,16)] at +0x8a..+0xa4 is the exact inverse of
     dirlink's append: [DirLinks.dir_links_unlink] fires CALLER-SIDE on the
     record [dirlookup] found and RELEASES one [InodeRegion.ilink ip],
     which the [ip->nlink--; iupdate(ip)] at +0xbe..+0xca then CONSUMES
     through [SpecIupdate.wp_iupdate_unlink].  Nothing colour-shaped crosses
     this interface in either direction.
   * ITS HOME-LIVE PREMISE COMES FROM THE PAYLOAD, NOT FROM A GUARD.
     [dir_links_unlink] wants [di_nlink dp <> 0] of the HOME, and unlike
     create and namex sys_unlink has no [nlink == 0] re-check to walk.  What
     supplies it is [DirView.dir_orphan_clean] (fs-fragments-campaign.md,
     PASS 2): an ORPHANED directory's live records are exactly "." and "..",
     the two [namecmp] guards at +0x44 / +0x58 say the matched record is
     neither, and [dirlookup]'s found arm says the record is live -- so the
     home cannot be orphaned.  The clause is a property of THIS binary and
     of no earlier one: it was refuted by sys_link's unguarded [dirlink]
     until f60ff58 gave sys_link create's orphan re-check.
   * THE T_DIR ARM's [dp->nlink--] SPENDS THE CHILD's ".." TICKET.  The only
     [ilink dp] in the system lives inside [ip]'s own [dir_links], at the
     index of [ip]'s "..", and [DirView.dir_dots_ix] +
     [FsLookup.fdir_dots_index] + [DirLinks.dir_links_dotdot_out] are what
     name it.  That clause is guarded on [T_DIR] AND [di_nlink ip <> 0], and
     the liveness is the kernel's own [if (ip->nlink < 1) panic] at +0x7c --
     walked before the zeroing, like the two namecmp refusals.  In exchange
     the clause HANDS BACK [2 <= dir_nrec (di_size ip)], so the isdirempty
     loop never has to establish a record count.

   ==== THE REFERENCE LEDGER CLOSES AT TWO ON EVERY ARM =================

   [iref_slots 2] goes in and comes back out unchanged.  TWO, not sys_link's
   three, and the difference is structural: sys_link runs its SECOND resolve
   with [ip] already held, while sys_unlink's ONE resolve runs holding
   nothing.  The peak is therefore [max(the walker's own two, dp + ip)] = 2.

   * nameiparent takes two units and hands ONE back on success (the second
     pays for [dp]);
   * [dirlookup]'s found arm produces [ip] out of the remaining unit and its
     not-found arm returns that unit unspent;
   * every arm releases what it made -- [iunlockput(dp)] at [bad:],
     [iunlockput(ip)] then [iunlockput(dp)] on the isdirempty refusal, both
     on the success arm -- and the argstr arm makes no reference at all.

   ==== THE LOG LEDGER IS THE SET FORM, AND THE ZEROING PAYS FOR THE TAIL =

   begin_op mints [LogInv.log_op g MAXOPBLOCKS] = ten units and end_op
   retires whatever is left, so nothing log-shaped crosses this interface.
   The whole ledger is machine-checked in [SysUnlinkBudget.v]; three facts
   about it, because they decide the contract's premises:

   * ONE WALK, AND IT RUNS FIRST.  Nothing is held while [nameiparent] runs,
     so the ledger below it is parameterised by ONE reported boolean and
     enters at nine or ten -- never sys_link's seven.  The COUNTED walker is
     hopeless here for sys_chdir's reason: [(L+1) * iput_units] demands
     twelve of the ten at a three-component path.
   * THE ZEROING PAYS FOR THE WHOLE TAIL.  [SpecWritei.wi16_post]'s
     MEMBERSHIP TRIO at [tot = 16] puts [IBLOCK dp] in the op's set, so both
     the T_DIR [iupdate(dp)] and the [iunlockput(dp)] behind it run
     CREDITED.  Only [ip]'s own flush is uncredited, and it has to be:
     [dirlookup] and the isdirempty loop are pure reads, so nothing logs
     [IBLOCK ip] before it.  Relaying [wi16_spend] ALONE busts the worst
     corner by one -- [SysUnlinkBudget.su_ok_busts_without_the_membership_trio].
   * NO CORRELATION CLAUSE IS NEEDED.  [su_ok_uncorrelated] closes the T_DIR
     arm at [crb = false] together with [w1 = true] -- the nine-unit,
     uncredited-bitmap corner [SysLinkBudget.sl_corr] exists to exclude --
     and [su_ok_corner_is_exact] says it lands there at EXACTLY
     [iput_units].

   ==== WHAT ITS CALLER MUST HOLD ======================================

   [eb = true] is nameiparent's premise, inherited verbatim.  The
   [trap_csrs_ext] / [cpu_claim_ext] complement is threaded anyway,
   uniformly with begin_op / ilock / writei / iupdate / iunlockput / end_op,
   and is [emp] there.

   THE CROSSING IS THE LITERAL [true]: this function parks in every one of
   its ten distinct callees, so it may return on a hart other than the one
   it was called on.

   THE BITMAP IS NOT MONOTONE, in either direction: the zeroing [writei] can
   ALLOCATE (its contract cannot refute an allocating write even though the
   record it overwrites is inside the directory's existing size) and every
   [iunlockput] can FREE (itrunc, under a link-count-zero inode -- which is
   exactly what a successful unlink of the last link produces); the bitmap
   is an invariant, so the contract says nothing about it.

   DETERMINISM: none is claimed, and none is available.  Which of the six
   arms runs is a function of the FILE SYSTEM and of the user's path, and no
   caller of this contract knows any of that.  The postcondition is the
   honest disjunction on the returned a0. *)
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
Require Import SpecPrintk.
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
Require Import SpecDirlink.    (* [ic_sleeplocks], [ireg_blocks_ok] *)
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import ProcAvail.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Require Import TsoCtx.
Import Defs.

Local Open Scope Z_scope.

(* sys_unlink's own frame is 240 bytes -- THIRTY slots ([c.addi16sp sp,-240]
   at +0x00) -- over its deepest callee, nameiparent (104).  Every other
   callee fits under that: dirlookup 90, readi 78, writei 78, iunlockput 64,
   argstr 60, end_op 58, ilock 44, iupdate 44, begin_op 26, namecmp 4,
   memset 2. *)
Notation K_sys_unlink := (144%nat) (only parsing).
(* THE REFERENCE ALLOWANCE.  Two, and TWO is what the single resolve buys:
   see the header's reference ledger, and [SysUnlinkBudget]'s section 6. *)
Definition sys_unlink_slots : nat := 2%nat.

(* sys_unlink's result, as the honest disjunction on a0.  Unlike sys_link
   there is no shared [c.mv a0,a5]: each arm writes its own literal with a
   [c.li] -- 0 at +0xd8 on the success arm, -1 at +0xe6 (ARM B), +0x164
   ([bad:]) and +0x170 (ARM A). *)
Definition sys_unlink_ret (r : mword 64) : Prop :=
  r = (mword_of_int (-1) : mword 64) \/ r = (zero_reg : mword 64).

Definition wp_sys_unlink_sconf_body
    `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
      !irefslotG Σ, !pavG Σ} `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}

    (γf : gname) (γa : gname) (γpr : gname)      (* ftable, kalloc, printk   *)
    (gs : list gname) (j : nat) (gl : gname)     (* the running process      *)
    (gu : uart_names) (gd : disk_names) (gk : gname)   (* disk fabric + lock *)
    (pd pav pu : mword 64)
    (bn : bio_names)
    (g : log_names) (gfs : fs_names) (gi : gname)
    (cn : ic_names) (gtl : gname)                      (* the icache + itable *)
    (cov : gset Z) (logstart bmapstart inodestart : Z) (nib : nat)
    (size : Z) (dev : mword 32)
    (dqb dqs dqbs : dfrac)
    (v0 : mword 64)                           (* syscall argument 0         *)
    (pid : mword 32) (V : pprivate)
    (m : regfile) (K : nat) (eb : bool)
    (b : bool) (lks : gset string) :=
  let pcE : mword 64 := mword_of_int KernelSyms.sys_unlink in
  let pj := proc_addr j in
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5)) in
  (K_sys_unlink <= K)%nat ->
  (* ---- the icache's ambient ties, threaded verbatim to the walk ---- *)
  dev = icfg_dev ->
  nib = icfg_nib ->
  (* the region's two ambient ties (fs-log.md G.25).  Threaded to
     nameiparent, and ALSO consumed HERE: both [wp_iupdate_unlink] calls
     discharge their receipt premise through a disjunct that names them. *)
  g = icfg_log ->
  inodestart = icfg_ist ->
  dev = ROOTDEV ->
  (0 < nib)%nat ->
  (* ---- the block-layer geometry ---- *)
  log_geom_ok cov logstart ->
  0 < size <= BPB ->
  0 <= bmapstart ->
  bmapstart ∈ cov ->
  ~ (bmapstart ∈ log_region_set logstart) ->
  0 <= inodestart ->
  cov_below cov size ->
  bitmap_geom_ok cov logstart bmapstart size ->
  ireg_blocks_ok inodestart nib cov logstart ->
  (* mkfs's [ushort] geometry: the zeroed record's [de.inum] is a halfword
     and [dirlookup]'s answer is read back against the region's inum range,
     so the two have to agree on the width.  create's and sys_link's premise
     verbatim. *)
  16 * Z.of_nat nib <= 2 ^ 16 ->
  (* ---- balloc's out-of-blocks arm (under the zeroing writei) calls
     printk, not panic ---- *)
  printk_gen_contract (kt := KT1) γpr gu gd ->
  (j < NPROC)%nat ->
  gs !! j = Some gl ->
  (* nameiparent's own premise, inherited: the walker runs with the base
     enabled *)
  eb = true ->
  (* the single [argstr] call reads syscall argument 0 out of the trapframe
     page [proc_priv] carries.  Nothing is assumed about it: argstr checks
     the string itself. *)
  pv_tf V !! tf_arg_idx 0 = Some v0 ->
  sie_cap_gpr KT1 m K b pj -∗
  (* ENTERED WITH NO LOCK HELD, and that is why there is no [locks_below]
     premise here: the depth is pinned at ZERO, so [CpuOwn.cpu_own_zero_empty]
     DERIVES [lks = ∅] and every order goal the ten callees raise is
     [locks_below ∅ _]. *)
  cpu_own 0 eb pj b lks -∗
  (* THE TRAP-CSR COMPLEMENT, THREADED.  [emp] at [eb = true] -- which this
     contract's own premise forces -- so no caller gains an obligation. *)
  trap_csrs_ext KT1 eb -∗
  cpu_claim_ext eb pj -∗
  kernel_text -∗ kernel_data -∗ pc_is pcE -∗
  printk_env γpr gu gd -∗
  (* ---- the block layer ---- *)
  bio_ctx bn (fs_view gfs gd dev cov) -∗
  log_ctx g bn gfs cov logstart dev -∗
  fs_crash_seam cov logstart -∗
  gen_cert -∗
  dev_inv gu gd -∗
  disk_geom gd pd pav pu -∗
  is_lock gk d_lock "virtio_disk"%string (disk_res gd pd pav pu) -∗
  bslots 3 -∗
  (* ---- the inode cache, and the region the two flushes write ---- *)
  is_itable2 gtl cn gfs gi cov logstart nib dev -∗
  itable_inv -∗
  ic_escrows cn gfs gi cov logstart -∗
  ic_sleeplocks cn -∗
  ireg_inv gi gfs inodestart nib -∗
  (* ...AND THE SEALED REGIME (iclaim-ledger.md §3.2, RULING B; §6′ RULING G).
     Persistent, borrowed and never spent; it rides the SAME channel
     [ireg_inv] does.  It is here because this contract reaches iput, whose
     free path FREEZES the inode, and §2.3's boot-shelter clause makes a
     freezer exhibit the regime it freezes under.  A runtime caller hands
     [SpecIput] the LEFT arm of its borrowed disjunction and discards what
     comes back; only ireclaim, which freezes before the seal is fired,
     lends [ireg_boot] instead. *)
  ireg_open -∗
  (* ---- the three superblock cells the zeroing's writei / bmap / balloc
     and the walk's own iunlockputs read ---- *)
  sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
  sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
  sb_size ↦₄{dqbs} (mword_of_int size : mword 32) -∗
  bitmap_inv gfs bmapstart cov logstart size -∗
  (* argstr's page-table side, and the walk's (iget's ipool arm allocates) *)
  kalloc_env γa None -∗
  (* the running-thread bundle *)
  procs_inv gs -∗
  (* ---- the process, and the reference allowance the walk needs ---- *)
  iref_slots sys_unlink_slots -∗
  proc_priv γf pj pid V -∗
  (* THE CROSSING IS THE LITERAL [true], NOT [b]: sys_unlink parks in every
     one of its ten distinct callees, so it can return on another hart
     whatever SIE was doing.
     Vacuous at [true], so consuming it costs the caller nothing. *)
  wp_next true pj (fun (CID : CpuId) =>
  ∀ (mf : regfile) (P' : uptd),
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
      sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
      sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
      sb_size ↦₄{dqbs} (mword_of_int size : mword 32) -∗
      (* NO ORDERING on the free pool: the zeroing's writei can ALLOCATE and
         every iunlockput can FREE (itrunc).  See the header. *)
      (* the allowance, whole: see the header's reference ledger *)
      iref_slots sys_unlink_slots -∗
      (* the process block, at the same everything but the page table *)
      proc_priv γf pj pid (upd_upt V P') -∗
      ⌜sys_unlink_ret (mf !!! Regidx (mword_of_int 10 : mword 5))⌝ -∗
      WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

Module Type SYSUNLINK.
  Parameter wp_sys_unlink_sconf :
    forall `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ, !irefslotG Σ, !pavG Σ} `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}
      (γf : gname) (γa : gname) (γpr : gname)
      (gs : list gname) (j : nat) (gl : gname)
      (gu : uart_names) (gd : disk_names) (gk : gname)
      (pd pav pu : mword 64)
      (bn : bio_names)
      (g : log_names) (gfs : fs_names) (gi : gname)
      (cn : ic_names) (gtl : gname)
      (cov : gset Z) (logstart bmapstart inodestart : Z) (nib : nat)
      (size : Z) (dev : mword 32)
      (dqb dqs dqbs : dfrac)
      (v0 : mword 64)
      (pid : mword 32) (V : pprivate)
      (m : regfile) (K : nat) (eb : bool)
      (b : bool) (lks : gset string),
      wp_sys_unlink_sconf_body γf γa γpr gs j gl gu gd gk pd pav pu bn g gfs
                               gi cn gtl cov logstart bmapstart inodestart
                               nib size dev dqb dqs dqbs v0 pid V
                               m K eb b lks.
End SYSUNLINK.
