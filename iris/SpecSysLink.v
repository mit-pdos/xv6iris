(* SpecSysLink.v -- the public interface of sys_link(), stated
   independently of its proof.  Requires only the definitional layer --
   never a whole-function proof file -- so every function proof can be
   checked in parallel.

     uint64 sys_link(void) {
       char name[DIRSIZ], new[MAXPATH], old[MAXPATH];
       struct inode *dp, *ip;

       if (argstr(0, old, MAXPATH) < 0 || argstr(1, new, MAXPATH) < 0)
         return -1;

       begin_op();
       if ((ip = namei(old)) == 0) { end_op(); return -1; }

       ilock(ip);
       if (ip->type == T_DIR) { iunlockput(ip); end_op(); return -1; }
       if (ip->nlink >= NLINK_MAX) { iunlockput(ip); end_op(); return -1; }

       ip->nlink++;
       iupdate(ip);
       iunlock(ip);

       if ((dp = nameiparent(new, name)) == 0) goto bad;
       ilock(dp);
       // dp may have been unlinked while we resolved it
       if (dp->nlink == 0) { iunlockput(dp); goto bad; }
       if (dp->dev != ip->dev || dirlink(dp, name, ip->inum) < 0) {
         iunlockput(dp); goto bad;
       }
       iunlockput(dp);
       iput(ip);
       end_op();
       return 0;

      bad:
       ilock(ip);
       ip->nlink--;
       iupdate(ip);
       iunlockput(ip);
       end_op();
       return -1;
     }

   @ KernelSyms.sys_link, 292 bytes / 101 instructions (CodeSysLink.v).
   A THIRTY-EIGHT slot frame ([c.addi16sp sp,-304] at +0x00), carved:

     slot  1  (sp+296)  ra
     slot  2  (sp+288)  s0, the frame pointer (= the ENTRY sp)
     slot  3  (sp+280)  s1 = ip     -- saved LATE, at +0x30
     slot  4  (sp+272)  s2 = dp     -- saved LATER STILL, at +0x5c
     slots 5..6         [char name[DIRSIZ]] -- [addi a1,s0,-48]
     slots 7..22        [char new[MAXPATH]] -- [addi a1,s0,-176]
     slots 23..38       [char old[MAXPATH]] -- [addi a1,s0,-304]

   THE TWO REGISTER SAVES ARE SHRINK-WRAPPED.  [c.sdsp s1] runs only after
   BOTH argstr calls succeed and [c.sdsp s2] only after the type and
   NLINK_MAX guards pass, and each exit restores exactly what its own path
   saved -- so the two argstr-failure arms neither save nor restore either
   register, which is sound because neither is written on those paths.
   Nothing about the three buffers reaches this contract: they are carved
   out of [stack_own] with [StackBytes.slotsn_bytes_own].

   ==== WHAT THIS CONTRACT IS ABOUT =====================================

   sys_link is the first SYSCALL-level consumer of the CREDITED iupdate
   pair ([SpecIupdate.wp_iupdate_link] / [wp_iupdate_unlink]) and of the
   kernel's NLINK_MAX guard arm, so its walk is where the whole link-ledger
   contract layer is exercised end to end.  Two facts about that, because
   they are what the walk is:

   * THE LEDGER FRAGMENT IS MINTED AND SETTLED INSIDE THIS FUNCTION.  The
     [ip->nlink++; iupdate(ip)] at +0x5e..+0x66 mints one
     [InodeRegion.ilink] against the count that pays for it; on the success
     path the [dirlink] at +0x9c lets the caller DEPOSIT it into the
     parent's [DirLinks.dir_links] ([dir_links_dirlink], caller-side --
     design/fs-icache.md 20.18 ruling 1 keeps every ledger resource OUT of
     [SpecDirlink]); on every route to [bad:] the [ip->nlink--; iupdate(ip)]
     at +0xfa..+0x106 CONSUMES it back.  Nothing colour-shaped crosses this
     interface in either direction.
   * THE ORPHAN GUARD IS WHAT MAKES THE DEPOSIT LEGAL.  The [lh a5,74(s2)]
     / [c.beqz] at +0x84..+0x88 -- create's re-check, given to sys_link at
     f60ff58 -- refuses to [dirlink] into a parent a concurrent rmdir has
     orphaned, which would strand the [ilink] above in a directory whose
     [itrunc] discards records without dropping counts.  Its arm is ARM E2,
     a plain [iunlockput(dp); goto bad;], so nothing about it reaches this
     contract except that the [-1] disjunct now has one more way to happen.
   * THE NLINK_MAX GUARD IS WHAT MAKES THE MINT LEGAL.  [wp_iupdate_link]'s premise
     [di_nlink dn0 <> mword_of_int 32767] is exactly the [beq a4,a5] at
     +0x58 falling through; the [lui a4,0x8 / addi a4,a4,-1] pair at
     +0x54/+0x56 is 32767,
     and the test is [==] rather than [>=] because [nlink] is a signed
     short and NLINK_MAX is SHRT_MAX.  The SIGNED/UNSIGNED gap the twelfth
     stop recorded is closed by [InodeRegion]'s (L4) range clause, which is
     where the increment premise is discharged.

   ==== THE REFERENCE LEDGER CLOSES AT THREE ON EVERY ARM ===============

   [iref_slots 3] goes in and comes back out unchanged, and three -- one
   more than sys_chdir's two -- is forced by the SECOND resolve: when
   nameiparent runs, [ip] is already held.

   * namei takes two units and hands ONE back on success (the second pays
     for the reference it returns), so the walk's peak is [ip] plus the
     walker's own two;
   * nameiparent does the same for [dp];
   * every arm releases what it made -- [iunlockput(ip)] on the type and
     NLINK_MAX arms and at [bad:], [iunlockput(dp)] + [iput(ip)] on the
     success arm -- and the two argstr arms make no reference at all.

   ==== THE LOG LEDGER IS THE SET FORM, AND IT HAS TO BE ================

   begin_op mints [LogInv.log_op g MAXOPBLOCKS] = ten units and end_op
   retires whatever is left, so nothing log-shaped crosses this interface.
   sys_link runs TWO unbounded-depth walks inside one transaction, so the
   COUNTED namei/nameiparent contracts are hopeless here for sys_chdir's
   reason squared: [(L + 1) * iput_units] demands twelve of the ten at a
   three-component path, twice over.  The SET form prices each walk at
   [SpecNamex.walk_need L <= 4] and spends at most one.

   Note that the two [argstr] calls run BEFORE [begin_op] -- unlike
   sys_chdir, where the string fetch is inside the transaction -- so the
   two argstr-failure arms carry no log resource at all.

   ==== WHAT ITS CALLER MUST HOLD ======================================

   [eb = true] is namei's premise, inherited verbatim.  The
   [trap_csrs_ext] / [cpu_claim_ext] complement is threaded anyway,
   uniformly with begin_op / iupdate / iput / iunlockput / end_op, and is
   [emp] there.

   THE CROSSING IS THE LITERAL [true]: this function sleeps in every one of
   its eleven distinct callees, so it may return on a hart other than the
   one it was called on.

   THE BITMAP IS NOT MONOTONE, in either direction: [dirlink]'s writei can
   ALLOCATE (balloc, growing the directory) and the two walks' iunlockputs
   can FREE (itrunc), so -- unlike sys_chdir -- no [used' ⊆ used] is
   claimed.  create's contract is unordered for the same pair of reasons.

   DETERMINISM: none is claimed, and none is available.  Which of the
   eight arms runs is a function of the FILE SYSTEM and of the user's two
   strings, and no caller of this contract knows any of that.  The
   postcondition is the honest disjunction on the returned a0. *)
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
Require Import SpecIput.       (* [iput_units] *)
Require Import SpecDirlink.    (* [ic_sleeplocks], [ireg_blocks_ok] *)
Require Import SpecNamex.      (* [walk_need], [ROOTDEV] *)
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import ProcAvail.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Import Defs.

Local Open Scope Z_scope.

(* sys_link's own frame is 304 bytes -- THIRTY-EIGHT slots
   ([c.addi16sp sp,-304] at +0x00).  Its deepest callee is namei (106);
   nameiparent wants 104, dirlink 100, iunlockput 64, argstr 60, iput 60,
   end_op 58, ilock 44, iupdate 44, begin_op 26, iunlock 26. *)
Notation K_sys_link := (154%nat) (only parsing).
(* THE REFERENCE ALLOWANCE.  Three, and the third one is nameiparent's:
   see the header's reference ledger. *)
Definition sys_link_slots : nat := 3%nat.

(* sys_link's result, as the honest disjunction on a0.  BOTH values come
   out of the same [c.mv a0,a5] at +0x11a, whose a5 each arm set to its own
   literal: 0 at +0xb4 on the success arm, -1 at every failure. *)
Definition sys_link_ret (r : mword 64) : Prop :=
  r = (mword_of_int (-1) : mword 64) \/ r = (zero_reg : mword 64).

Definition wp_sys_link_sconf_body
    `{!riscvGS Σ, !xv6G Σ, !fdslotG Σ, !fileG Σ,
      !irefslotG Σ, !pavG Σ} `{GEN : GenId} `{CID : CpuId}

    (γf : gname) (γa : gname) (γpr : gname)      (* ftable, kalloc, printk   *)
    (gs : list gname) (j : nat) (gl : gname)     (* the running process      *)
    (gu : uart_names) (gd : disk_names) (gk : gname)   (* disk fabric + lock *)
    (pd pav pu : mword 64)
    (bn : bio_names)
    (g : log_names) (gfs : fs_names) (gi : gname)
    (cn : ic_names) (gtl : gname)                      (* the icache + itable *)
    (cov : gset Z) (logstart bmapstart inodestart : Z) (nib : nat)
    (size : Z) (dev : mword 32)
    (used : gset Z)
    (dqb dqs dqbs : dfrac)
    (v0 v1 : mword 64)                        (* syscall arguments 0 and 1  *)
    (pid : mword 32) (V : pprivate)
    (m : regfile) (K : nat) (eb : bool)
    (b : bool) (lks : gset string) :=
  let pcE : mword 64 := mword_of_int KernelSyms.sys_link in
  let pj := proc_addr j in
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5)) in
  (K_sys_link <= K)%nat ->
  (* ---- the icache's ambient ties, threaded verbatim to the two walks ---- *)
  dev = icfg_dev ->
  nib = icfg_nib ->
  (* the region's two ambient ties (fs-log.md G.25).  Threaded to namei and
     nameiparent, and ALSO consumed HERE: the [bad:] arm discharges
     [wp_iupdate_unlink]'s receipt premise through its LEFT disjunct, which
     is exactly this pair. *)
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
  (* mkfs's [ushort] geometry, create's premise verbatim and for the same
     reason: it is what makes the [lw a2,4(s1)] at +0x96 -- which SIGN
     extends the 32-bit [ip->inum] cell -- agree with [SpecDirlink]'s
     ZERO-extended halfword argument. *)
  16 * Z.of_nat nib <= 2 ^ 16 ->
  (* ---- dirlink's out-of-blocks arm calls printk, not panic ---- *)
  printk_gen_contract (kt := KT1) γpr gu gd ->
  (j < NPROC)%nat ->
  gs !! j = Some gl ->
  (* namei's own premise, inherited: the walker runs with the base enabled *)
  eb = true ->
  (* the two argstr calls read syscall arguments 0 and 1 out of the
     trapframe page [proc_priv] carries *)
  pv_tf V !! tf_arg_idx 0 = Some v0 ->
  pv_tf V !! tf_arg_idx 1 = Some v1 ->
  sie_cap_gpr KT1 m K b pj -∗
  (* ENTERED WITH NO LOCK HELD, and that is why there is no [locks_below]
     premise here: the depth is pinned at ZERO, so [CpuOwn.cpu_own_zero_empty]
     DERIVES [lks = ∅] and every order goal the eleven callees raise is
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
  bslots bn 3 -∗
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
  (* ---- the three superblock cells dirlink's writei / bmap / balloc read ---- *)
  sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
  sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
  sb_size ↦₄{dqbs} (mword_of_int size : mword 32) -∗
  bitmap_res gfs bmapstart cov logstart size used -∗
  (* argstr's page-table side, and the two walks' (iget's ipool arm allocates) *)
  kalloc_env γa None -∗
  (* the running-thread bundle *)
  procs_inv gs -∗
  (* ---- the process, and the reference allowance the two walks need ---- *)
  iref_slots sys_link_slots -∗
  proc_priv γf pj pid V -∗
  (* THE CROSSING IS THE LITERAL [true], NOT [b]: sys_link parks in every
     one of its eleven distinct callees, so it can return on another hart
     whatever SIE was doing.
     Vacuous at [true], so consuming it costs the caller nothing. *)
  wp_next true pj (fun (CID : CpuId) =>
  ∀ (mf : regfile) (used' : gset Z) (P' : uptd),
      ⌜callee_saved m mf⌝ -∗
      (* the page table may have GROWN: the two fetchstrs fault user pages
         in.  [uptd_ext] is argstr's own report, composed across the pair by
         [ProcPtOwn.uptd_ext_trans]. *)
      ⌜uptd_ext (pv_upt V) P'⌝ -∗
      sie_cap_gpr KT1 mf K b pj -∗
      cpu_own 0 eb pj b lks -∗
      trap_csrs_ext KT1 eb -∗
      cpu_claim_ext eb pj -∗
      pc_is ret_tgt -∗
      bslots bn 3 -∗
      sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
      sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
      sb_size ↦₄{dqbs} (mword_of_int size : mword 32) -∗
      (* NO ORDERING on the free pool: dirlink both ALLOCATES (balloc, under
         its writei) and the two walks FREE (itrunc, under an iunlockput of
         a link-count-zero inode).  See the header. *)
      bitmap_res gfs bmapstart cov logstart size used' -∗
      (* the allowance, whole: see the header's reference ledger *)
      iref_slots sys_link_slots -∗
      (* the process block, at the same everything but the page table *)
      proc_priv γf pj pid (upd_upt V P') -∗
      ⌜sys_link_ret (mf !!! Regidx (mword_of_int 10 : mword 5))⌝ -∗
      WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

Module Type SYSLINK.
  Parameter wp_sys_link_sconf :
    forall `{!riscvGS Σ, !xv6G Σ, !fdslotG Σ, !fileG Σ, !irefslotG Σ, !pavG Σ} `{GEN : GenId} `{CID : CpuId}
      (γf : gname) (γa : gname) (γpr : gname)
      (gs : list gname) (j : nat) (gl : gname)
      (gu : uart_names) (gd : disk_names) (gk : gname)
      (pd pav pu : mword 64)
      (bn : bio_names)
      (g : log_names) (gfs : fs_names) (gi : gname)
      (cn : ic_names) (gtl : gname)
      (cov : gset Z) (logstart bmapstart inodestart : Z) (nib : nat)
      (size : Z) (dev : mword 32)
      (used : gset Z)
      (dqb dqs dqbs : dfrac)
      (v0 v1 : mword 64)
      (pid : mword 32) (V : pprivate)
      (m : regfile) (K : nat) (eb : bool)
      (b : bool) (lks : gset string),
      wp_sys_link_sconf_body γf γa γpr gs j gl gu gd gk pd pav pu bn g gfs gi
                             cn gtl cov logstart bmapstart inodestart nib
                             size dev used dqb dqs dqbs v0 v1 pid V
                             m K eb b lks.
End SYSLINK.
