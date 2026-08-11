(* SpecDirlink.v -- the public interface of dirlink.

     int
     dirlink(struct inode *dp, char *name, uint inum)
     {
       int off;
       struct dirent de;
       struct inode *ip;

       if((ip = dirlookup(dp, name, 0)) != 0){
         iput(ip);
         return -1;
       }
       for(off = 0; off < dp->size; off += sizeof(de)){
         if(readi(dp, 0, (uint64)&de, off, sizeof(de)) != sizeof(de))
           panic("dirlink read");
         if(de.inum == 0)
           break;
       }
       strncpy(de.name, name, DIRSIZ);
       de.inum = inum;
       if(writei(dp, 0, (uint64)&de, off, sizeof(de)) != sizeof(de))
         return -1;
       return 0;
     }

   170 bytes.  Geometry VERIFIED off CodeDirlink.v: [addi sp,sp,-80] /
   [addi s0,sp,80], so [&de = s0-80] ([addi s4,s0,-80] at +0x2a, and the
   [lhu a5,-80(s0)] free test at +0x42, the [sh s6,-80(s0)] inum store at
   +0x7c, the [addi a2,s0,-80] writei source at +0x84) and
   [&de.name = s0-78] ([addi a0,s0,-78] at +0x74, strncpy's destination);
   [li a2,14] at +0x70 is DIRSIZ; the callee at +0x78 is **strncpy**
   (0x80000dd6), not safestrcpy.  THREE registers are saved LAZILY (s1 at
   +0x1c, s3/s4 at +0x24/+0x26) and the two early exits skip their
   restores.

   The return value is computed BRANCHLESSLY at +0x90..+0x96:
   [addi a0,a0,-16; sltu a0,zero,a0; subw a0,zero,a0], i.e.
   [a0 = -(writei(...) != 16)].

   ---- WHY THE CONTRACT IS THE UNION OF THREE ---------------------------

   dirlink is the campaign's widest precondition: it calls dirlookup (hence
   readi, namecmp and iget), iput on the found arm, and readi/strncpy/writei
   on the other.  So it threads dirlookup's bundle, writei's log +
   inode-region + bitmap bundle, and iput's itrunc geometry, all at once.
   It runs INSIDE A TRANSACTION (writei's bmap can allocate).

   TWO PREMISES ARE QUANTIFIED OVER RECORDS RATHER THAN NAMED, because the
   record dirlookup stops at is not known until it stops:

   - [DirView.dir_inums_ok] -- iget's argument bound (see SpecDirlookup.v).
     Since fs-icache.md §15(a) a caller gets it out of the icache: it is
     the conjunct [DirView.dir_ok icfg_nib dn data] riding in
     [IcacheEscrow.ic_loaded];
   - [ireg_blocks_ok] -- iput's [IBLOCK inum inodestart] membership facts,
     stated for EVERY inum the region covers rather than for the one child.
     That is strictly the better shape: it is a fact about the superblock
     layout, provable once, instead of a fact about a directory's contents.

   ---- THE GRANULARITY PREMISE IS GONE (fs-icache.md §15(b)) -----------

   [16 | di_size dn] used to be a premise here too, refuting
   panic("dirlink read") at +0x60 (the [bne a0,s3] at +0x3e).  It is not a
   system invariant -- dirlink's OWN short-write arm is what breaks it (see
   the APPEND arm below: on [tot < 16] the new size is [16*k0 + tot]) -- so
   the short-readi turn is now a LIVE panic arm, discharged with
   [SpecPanic.panic_wp_any], and no caller owes granularity.  A dirlink on a
   directory a previous short write corrupted therefore PANICS rather than
   returning; that is what the C does, and it is the honest post-state.

   ---- THE ARMS ---------------------------------------------------------

   FOUND (the name is already there): a0 = -1, the directory's data, block
   map and metadata are UNCHANGED, the child reference dirlookup minted has
   been spent by iput ([used' <= used], iput's spend-at-most budget), and
   the ledger unit comes back.

   APPEND: [dir_first data nrec s = None], and writei ran at
   [off = 16 * dir_slot data nrec] -- the first FREE record, or [nrec]
   itself when every record is live, which is where the scan's own [s1]
   lands.  writei's OWN -1 arm is DEAD here ([off <= size] because the slot
   is at most [nrec], and [size + 16 <= MAXFILE*BSIZE] is a premise), so the
   only failure left is a SHORT WRITE (bmap out of blocks), which is what
   [a0 = -1 /\ tot < 16] reports.  On [tot = 16] the window holds
   [dirent_bytes (de_of_name inum s)] -- strncpy NUL-pads, so the stored
   record IS [DirentEnc.de_of_name] -- and the size is raised by writei's
   own [wi_dinode].

   ---- THE RANGE CLAUSE IS EXACT (fs-icache.md §15.1(i), retrofitted) ----

   writei's postcondition concedes a DISTURBED REGION of up to BSIZE
   unspecified bytes above the written window, because a user copy that
   faults part-way is committed without advancing [tot].  dirlink writes
   from a KERNEL buffer ([user = false]), where either_copyin cannot fail
   at all, and SpecWritei now says so: [user = false -> dist = 0].  So the
   clause below is TWO-way, not three-way, and the third arm -- the SHORT
   write, [tot < 16] -- differs from the old file in exactly the [tot]
   bytes it wrote and NOWHERE ELSE.

   That is what a writer needs to re-park [DirView.dir_ok] over a
   middle-slot link: under the old clause the write could have clobbered
   up to 64 FOLLOWING records with arbitrary bytes and dir-wf was
   underivable (§15.1(i)).  [DirView.dir_ok_dirlink] is the derivation the
   tightened clause unlocks; create (fs-sysfile S5) is its first caller.

   ---- THE LINKED INUM'S RANGE PREMISE ---------------------------------

   [bv_unsigned inum < 16 * nib] on the mword-16 argument is NOT used by
   dirlink's own proof -- the [sh] stores sixteen bits whatever they are.
   It is here for the WRITER: [dir_ok] over the new directory needs every
   live record's inum inside the inode region, and the record dirlink just
   stored carries [inum].  (On a one-byte short write the stored halfword
   is [inum mod 256], which the premise still bounds -- the free slot's
   old high byte is zero.  See [dir_ok_dirlink].)  Stating it now keeps
   S5 from having to reopen this contract.  It is free for every caller:
   create's inum comes from ialloc, whose payout carries exactly this
   bound.

   NOTE ON THE NAME.  [s] is DEFINED as [bname 14 fn], the canonical view of
   the caller's own buffer, so the design's two extra caller obligations
   ("length s <= 14", "nonul s") are NOT premises: they are
   [DirentEnc.bname_length_le] and [DirentEnc.cut_nul_nonul], free.  What
   makes the stored record exactly [de_of_name inum s] is that strncpy's
   post ([SpecStrncpy.snc_post]) forces [bview 14 h = name_pad (bname 14 fn)]
   on both of its arms -- [DirView.snc_bview] is that step.

   THE BUDGET.  writei's [wi_cost off 16] is SEVEN whenever [16 | off]: the
   sixteen bytes never straddle a block, because 1024 = 64*16.  iput wants
   three.  So one constant, [dirlink_units = 7], covers both arms, and the
   postcondition is spend-at-most.                                        *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list functions bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import auth gmap frac.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap ghost_map.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvModelBytes.
Require Import RiscvLang RiscvPtsto.
Require Import InstrBytes.
Require Import RegFile.
Require Import SmodeCore.
Require Import CalleeSaved KernelText.
Require Import IntrDefs.
Require Import WpNext.
Require Import WpLock.
Require Import SpecPanic.
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
Require Import KernelDataInv.
Require Import SpecPrintkGen.
Require Import DinodeEnc.
Require Import DirentEnc.
Require Import DirView.
Require Import InodeInv.
Require Import InodeLock.
Require Import InodeRegion.
Require Import IrefSlots.
Require Import IcacheRef.
Require Import IcacheInv.
Require Import IcacheEscrow.
Require Import SleepLock.
Require Import KallocInv.
Require Import UserPtTree.
Require Import KvmSpec.
Require Import ProcPtOwn.
Require Import FileInv ProcInv.
Require Import SpecWritei.
Require Import SpecDirlookup.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Import Defs.

Local Open Scope Z_scope.

(* dirlink's own frame is 80 bytes (10 slots); its deepest callees are
   dirlookup (82) and writei (70). *)
Definition K_dirlink : nat := 92%nat.

(* writei's [wi_cost off 16] at a 16-aligned [off] (= 7), which dominates
   iput's 3. *)
Definition dirlink_units : nat := 7%nat.

(* iput's two block-membership premises, for EVERY inum the inode region
   covers rather than for the one child dirlookup happens to return.  See
   the header.

   HOISTED to [InodeInv.v] (fs-namei N5) once ialloc and ireclaim became
   its third and fourth consumers -- a Spec file must not require another
   function's Spec, and InodeInv is the lowest file that sees both
   [IBLOCK] and [log_region_set].  This transparent alias keeps every
   existing spelling ([ireg_blocks_ok ...] unqualified, and
   [SpecDirlink.ireg_blocks_ok ...] qualified) working unchanged; new
   contracts should name [InodeInv.ireg_blocks_ok] directly. *)
Definition ireg_blocks_ok (inodestart : Z) (nib : nat)
    (cov : gset Z) (logstart : Z) : Prop :=
  InodeInv.ireg_blocks_ok inodestart nib cov logstart.

Section DirlinkSpec.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !fileG Σ, !kallocG Σ,
            !bioG Σ, !diskGhostG Σ, !uartGhostG Σ, !fsLogG Σ, !logG Σ,
            ICFG : icfg, !icacheG Σ, !irefslotG Σ, !iregG Σ}.

  (* Every entry's inode sleeplock, in the shape [IcacheBoot.icache_alloc]
     hands it out.  iput names ONE slot's lock; dirlink cannot know which
     entry dirlookup's iget will return, so -- exactly as iget takes
     [ic_escrows] rather than [ic_escrow] -- it takes the family.
     Persistent, so it costs a caller nothing. *)
  Definition ic_sleeplocks (cn : ic_names) : iProp Σ :=
    ([∗ list] kk ∈ seq 0 NINODE,
       ∃ γil γisl : gname,
         is_sleeplock γil γisl (i_lock (ientry kk)) "inode"%string
                      (ic_tok cn kk))%I.

  Global Instance ic_sleeplocks_persistent cn : Persistent (ic_sleeplocks cn).
  Proof. apply _. Qed.
End DirlinkSpec.

Definition wp_dirlink_sconf_body
    `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !fileG Σ, !kallocG Σ,
      !bioG Σ, !diskGhostG Σ, !uartGhostG Σ, !fsLogG Σ, !logG Σ,
      ICFG : icfg, !icacheG Σ, !irefslotG Σ, !iregG Σ}
    `{GEN : GenId} `{CID : CpuId}

    (γs : list gname) (j : nat) (γl : gname)          (* the running process *)
    (γu : uart_names) (γd : disk_names) (γk : gname)  (* disk fabric + lock  *)
    (pd pav pu : mword 64)
    (bn : bio_names)
    (γ : log_names) (γfs : fs_names) (γi : gname)
    (cn : ic_names) (gtl : gname)                     (* the icache + itable *)
    (γa : gname) (γf : gname) (γpr : gname)
    (cov : gset Z) (logstart : Z) (inodestart : Z) (nib : nat)
    (bmapstart : Z) (size : Z) (dev : mword 32)
    (used : gset Z)
    (ip : mword 64) (dinum : mword 32)                (* the DIRECTORY       *)
    (bm : blkmap) (data : nat -> list (bv 8))
    (dn dn0 : dinode)
    (fn : nat -> bv 8)                                (* the caller's name   *)
    (inum : mword 16)                                 (* the LINKED inum     *)
    (ncount : nat)
    (pidv : mword 32) (dq dqd dqn dqs dqb dqbs dqf : dfrac)
    (m : regfile) (K : nat) (eb : bool) (C : iProp Σ)
    (b : bool) :=
  let pcE : mword 64 := mword_of_int KernelSyms.dirlink in
  let pj := proc_addr j in
  let nb := m !!! Regidx (mword_of_int 11 : mword 5) in
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5)) in
  let nrec := dir_nrec (bv_unsigned (di_size dn)) in
  let s := bname 14 fn in
  let k0 := dir_slot data nrec in
  (K_dirlink <= K)%nat ->
  (* ---- dirlookup's premises (NO granularity -- see the header) ---- *)
  di_type dn = T_DIR ->
  bm_covers bm (bv_unsigned (di_size dn)) ->
  bv_unsigned (di_size dn) <= Z.of_nat MAXFILE * Z.of_nat BSIZE ->
  dir_inums_ok data nrec nib ->
  (* THE APPEND FITS.  This is what kills writei's own -1 arm: the write is
     at [16*k0 <= size] and ends at [16*k0 + 16 <= size + 16]. *)
  bv_unsigned (di_size dn) + 16 <= Z.of_nat MAXFILE * Z.of_nat BSIZE ->
  (* ---- writei's premises ---- *)
  log_geom_ok cov logstart ->
  blkmap_wf cov logstart bm ->
  blk_holes_zero bm data ->
  di_addrs dn = bm_cells bm ->
  bv_unsigned (di_size dn) < 2 ^ 31 ->
  0 <= inodestart ->
  IBLOCK dinum inodestart ∈ cov ->
  ~ (IBLOCK dinum inodestart ∈ log_region_set logstart) ->
  bv_unsigned dinum < 16 * Z.of_nat nib ->
  (* ---- THE LINKED CHILD'S OWN RANGE (unused here, owed to the writer) ----
     the premise above is the DIRECTORY's inum; this one is the inum being
     linked, and it is what lets a caller re-park [DirView.dir_ok] over the
     record dirlink stores.  See the header. *)
  bv_unsigned inum < 16 * Z.of_nat nib ->
  bitmap_geom_ok cov logstart bmapstart size ->
  printk_gen_contract γpr γu γd ->
  (* ---- iput's premises (itrunc's geometry) ---- *)
  0 < size <= BPB ->
  0 <= bmapstart ->
  bmapstart ∈ cov ->
  ~ (bmapstart ∈ log_region_set logstart) ->
  cov_below cov size ->
  ireg_blocks_ok inodestart nib cov logstart ->
  (* ENOUGH BUDGET for either arm -- see the header *)
  (dirlink_units <= ncount)%nat ->
  (j < NPROC)%nat ->
  γs !! j = Some γl ->
  (* a0 = dp *)
  m !!! Regidx (mword_of_int 10 : mword 5) = ip ->
  (* a2 = inum, as a ZERO-extended halfword: the [sh s6,-80(s0)] at +0x7c
     stores exactly the low sixteen bits, and every caller's inum is a real
     inode number. *)
  m !!! Regidx (mword_of_int 12 : mword 5)
    = (zero_extend' 64 (inum : mword 16) : mword 64) ->
  (* PARKING PREMISE *)
  eb = true ->
  sie_cap_gpr m K b pj -∗
  cpu_own 0 eb pj C b -∗
  kernel_text -∗ pc_is pcE -∗
  panic_wp_any -∗
  kernel_data -∗
  printk_env γpr γu γd -∗
  bio_ctx bn (fs_view γfs γd dev cov) -∗
  log_ctx γ bn γfs cov logstart dev -∗
  kalloc_env γa None -∗
  (* ---- THE LOCKED DIRECTORY ---- *)
  i_dev ip ↦₄{dqd} dev -∗
  i_inum ip ↦₄{dqf} dinum -∗
  inode_meta ip dn -∗
  inode_map γfs ip bm -∗
  inode_blocks γfs bm data -∗
  (* ---- THE CALLER'S 14-BYTE NAME BUFFER (namecmp's f, strncpy's src) ---- *)
  ([∗ list] i ∈ seq 0 14, pa_add nb i ↦ₘ{dqn} fn i) -∗
  (* ---- the superblock cells and the bitmap ---- *)
  sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
  sb_size ↦₄{dqbs} (mword_of_int size : mword 32) -∗
  sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
  bitmap_res γfs bmapstart cov logstart size used -∗
  (* ---- the inode region and the directory's own (stale) record ---- *)
  ireg_inv γi γfs inodestart nib -∗
  dinode_at γi dinum dn0 -∗
  (* ---- the caller's own pid cell ---- *)
  p_pid pj ↦₄{dq} pidv -∗
  (* ---- the running-thread bundle and the disk fabric ---- *)
  procs_inv γs -∗
  dev_inv γu γd -∗
  disk_geom γd pd pav pu -∗
  is_lock γk d_lock "virtio_disk"%string (disk_res γd pd pav pu) -∗
  bslots bn 3 -∗
  (* ---- THE ICACHE ---- *)
  is_itable2 gtl cn γfs γi cov logstart nib dev -∗
  itable_inv -∗
  ic_escrows cn γfs γi cov logstart -∗
  ic_sleeplocks cn -∗
  iref_slot -∗
  (* ---- THIS OPERATION'S RESERVATION ---- *)
  log_op γ ncount -∗
  wp_next b pj (fun (CID : CpuId) =>
  ∀ (mf : regfile) (found : bool)
    (bm' : blkmap) (data' : nat -> list (bv 8)) (dn' dn0' : dinode)
    (n' : nat) (used' : gset Z)
    (tot : nat),
      ⌜callee_saved m mf⌝ -∗
      sie_cap_gpr mf K b pj -∗
      cpu_own 0 eb pj C b -∗
      pc_is ret_tgt -∗
      (* ---- everything comes back, at the possibly-updated indices ---- *)
      i_dev ip ↦₄{dqd} dev -∗
      i_inum ip ↦₄{dqf} dinum -∗
      inode_meta ip dn' -∗
      inode_map γfs ip bm' -∗
      inode_blocks γfs bm' data' -∗
      ([∗ list] i ∈ seq 0 14, pa_add nb i ↦ₘ{dqn} fn i) -∗
      sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
      sb_size ↦₄{dqbs} (mword_of_int size : mword 32) -∗
      sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
      bitmap_res γfs bmapstart cov logstart size used' -∗
      dinode_at γi dinum dn0' -∗
      p_pid pj ↦₄{dq} pidv -∗
      bslots bn 3 -∗
      (* NET ZERO on the ledger: dirlookup's iget spends one and iput
         returns one on the found arm; nothing is spent on the other. *)
      iref_slot -∗
      (* at most [dirlink_units] gone, and none gained *)
      ⌜((ncount - dirlink_units)%nat <= n')%nat /\ (n' <= ncount)%nat⌝ -∗
      log_op γ n' -∗
      (* ---- THE TWO ARMS ---- *)
      ⌜if found
        then (* the name was already there: iput spent the child *)
          dir_first data nrec s <> None
          /\ mf !!! Regidx (mword_of_int 10 : mword 5)
             = (mword_of_int (-1) : mword 64)
          /\ bm' = bm /\ data' = data /\ dn' = dn /\ dn0' = dn0
          /\ used' ⊆ used
          /\ tot = 0%nat
        else (* the append, through writei at [16*k0] *)
          dir_first data nrec s = None
          /\ used ⊆ used'
          /\ blkmap_wf cov logstart bm'
          /\ blk_holes_zero bm' data'
          /\ di_addrs dn' = bm_cells bm'
          /\ bv_unsigned (di_size dn') < 2 ^ 31
          /\ bm_covers bm' (bv_unsigned (di_size dn'))
          /\ dn' = wi_dinode dn bm' (16 * k0)%nat tot
          /\ dn0' = dn'
          /\ (tot <= 16)%nat
          (* THE RANGE CLAUSE: the record's bytes in the window and NOTHING
             ELSE.  writei's disturbed region is empty on the kernel arm --
             see the header, and fs-icache.md §15.1(i). *)
          /\ (forall x : nat,
                file_byte data' x
                = if decide ((16 * k0 <= x)%nat /\ (x < 16 * k0 + tot)%nat)
                  then dirent_bytes (de_of_name inum s) !!! (x - 16 * k0)%nat
                  else file_byte data x)
          (* the branchless return: 0 exactly when all sixteen went in *)
          /\ ((mf !!! Regidx (mword_of_int 10 : mword 5)
                 = (mword_of_int 0 : mword 64) /\ tot = 16%nat)
              \/ (mf !!! Regidx (mword_of_int 10 : mword 5)
                    = (mword_of_int (-1) : mword 64) /\ (tot < 16)%nat))⌝ -∗
      WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

Module Type DIRLINK.
  Parameter wp_dirlink_sconf :
    forall `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !fileG Σ, !kallocG Σ,
             !bioG Σ, !diskGhostG Σ, !uartGhostG Σ, !fsLogG Σ, !logG Σ,
             ICFG : icfg, !icacheG Σ, !irefslotG Σ, !iregG Σ}
      `{GEN : GenId} `{CID : CpuId}
      (γs : list gname) (j : nat) (γl : gname)
      (γu : uart_names) (γd : disk_names) (γk : gname)
      (pd pav pu : mword 64)
      (bn : bio_names)
      (γ : log_names) (γfs : fs_names) (γi : gname)
      (cn : ic_names) (gtl : gname)
      (γa : gname) (γf : gname) (γpr : gname)
      (cov : gset Z) (logstart : Z) (inodestart : Z) (nib : nat)
      (bmapstart : Z) (size : Z) (dev : mword 32)
      (used : gset Z)
      (ip : mword 64) (dinum : mword 32)
      (bm : blkmap) (data : nat -> list (bv 8))
      (dn dn0 : dinode)
      (fn : nat -> bv 8)
      (inum : mword 16)
      (ncount : nat)
      (pidv : mword 32) (dq dqd dqn dqs dqb dqbs dqf : dfrac)
      (m : regfile) (K : nat) (eb : bool) (C : iProp Σ)
      (b : bool),
      wp_dirlink_sconf_body γs j γl γu γd γk pd pav pu bn γ γfs γi cn gtl
                            γa γf γpr cov logstart inodestart nib bmapstart
                            size dev used ip dinum bm data dn dn0 fn inum
                            ncount pidv dq dqd dqn dqs dqb dqbs dqf
                            m K eb C b.
End DIRLINK.
