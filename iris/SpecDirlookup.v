(* SpecDirlookup.v -- the public interface of dirlookup.

     struct inode*
     dirlookup(struct inode *dp, char *name, uint *poff)
     {
       uint off, inum;
       struct dirent de;

       if(dp->type != T_DIR)
         panic("dirlookup not DIR");

       for(off = 0; off < dp->size; off += sizeof(de)){
         if(readi(dp, 0, (uint64)&de, off, sizeof(de)) != sizeof(de))
           panic("dirlookup read");
         if(de.inum == 0)
           continue;
         if(namecmp(name, de.name) == 0){
           if(poff)  *poff = off;
           inum = de.inum;
           return iget(dp->dev, inum);
         }
       }
       return 0;
     }

   172 bytes.  Geometry VERIFIED off CodeDirlookup.v, not off fs.c:
   [addi sp,sp,-96] / [addi s0,sp,96], so [&de = s0-96] ([addi s4,s0,-96] at
   +0x2a) and [&de.name = s0-94] ([addi s6,s0,-94] at +0x30); the record
   stride 16 is [li s3,16] at +0x2e, which feeds readi's [n] AND the
   [addiw s1,s1,16] at +0x52; the free test is the ZERO-EXTENDING
   [lhu a5,-96(s0)] at +0x6e, so it is the halfword and not a byte; the
   size is RE-READ every iteration ([lw a5,76(s2)] at +0x54) and compared
   [bgeu s1,a5]; and the iget arguments are [lw a0,0(s2)] (dp->dev,
   SIGN-extended) and [lhu a1,-96(s0)] (the inum, ZERO-extended).

   ---- WHAT IT SPEAKS IN ------------------------------------------------

   [DirView.v]'s record view over [InodeInv.file_byte data]: [dir_inum],
   [dir_name], [dir_live], [dir_match] and the first-match search
   [dir_first].  [nrec] is [dir_nrec (di_size dn)] = size/16, the number of
   WHOLE records; when the size is NOT a multiple of 16 the loop takes one
   turn past [nrec] and dies in panic("dirlookup read") -- see below.

   ---- THE THREE PREMISES A CALLER MUST BRING ---------------------------

   (1) [di_type dn = T_DIR].  Refutes panic("dirlookup not DIR") at +0x1c;
       namex tests exactly this before calling.

   (2) readi's own threading: [bm_covers], the MAXFILE*BSIZE size bound,
       [log_geom_ok] / [blkmap_wf].  Note that readi's JOINT NUMERIC
       premise is NOT a caller premise here: [off + 16 <= size <=
       MAXFILE*BSIZE] discharges it at every call.

   (3) [DirView.dir_inums_ok] -- EVERY LIVE RECORD'S INUM IS INSIDE THE
       INODE REGION.  iget's one argument premise is [bv_unsigned inum <
       16 * nib], and dirlookup's inum comes off the DISK, so nothing in
       the proof can establish it: it is a well-formedness fact about the
       directory's contents and it must be a premise.  It is quantified
       over the records because the matching record is not known until the
       loop stops.

       WHERE A CALLER GETS IT (fs-icache.md §15(a)): it is now a SYSTEM
       INVARIANT, the conjunct [DirView.dir_ok icfg_nib dn data] riding in
       [IcacheEscrow.ic_loaded] and in [ipool_shape]'s allocated arm, so
       namex destructs it out of ilock's postcondition at a directory it
       could not have named in advance -- [DirView.dir_ok_dir] is the one
       step, and it wants [nib = icfg_nib].

   ---- THE GRANULARITY PREMISE IS GONE (fs-icache.md §15(b)) -----------

   [16 | di_size dn] USED to be premise (2), and under it every loop readi
   had [off + 16 <= size], [rd_clamp] was 16, and panic("dirlookup read")
   at +0x46 was dead.  It is NOT an invariant: THIS kernel's balloc returns
   0 when the disk is full (stock xv6 panics -- see SpecBalloc.v's header),
   so dirlink's third arm really does append a PREFIX of a 16-byte record
   and leaves [size = 16*nrec + tot] permanently non-granular.  The next
   scan of such a directory takes ONE extra turn of the loop, at
   [i = nrec] with [16*nrec < size], whose readi returns [tot < 16] and
   whose [bne a0,s3] at +0x6a is TAKEN -- into panic("dirlookup read").
   That arm is now LIVE and discharged against [SpecPanic].  No
   postcondition arm is added: panic never returns, so the found/notfound
   arms carry an implicit "...and every readi in the scan returned 16",
   which is what the old premise gave and what the panic arm gives without
   it.  A caller -- namex included -- needs no granularity fact at all.

   ---- THE TWO ARMS ----------------------------------------------------

   FOUND:  [dir_first data nrec s = Some k]; a0 is iget's entry pointer and
   the caller gets iget's [inode_ref] at the 32-bit widening of that
   record's inum; [*poff = 16k] on the non-null arm.

   NOT FOUND: [dir_first data nrec s = None]; a0 = 0; the [iref_slot] the
   caller brought for iget comes BACK (iget is only reached on the found
   arm), and [*poff] is untouched.

   The directory bundle -- [i_dev], [inode_meta], [inode_map],
   [inode_blocks] -- comes back LITERALLY unchanged on both arms: readi
   modifies nothing and iget touches only icache state.

   dirlookup SLEEPS (readi does), so it threads the full running-process
   bundle and takes the parking premise.  It enters and returns at noff 0. *)
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
Require Import KernelDataInv.
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
Require Import DinodeEnc.
Require Import DirentEnc.
Require Import DirView.
Require Import InodeInv.
Require Import InodeRegion.
Require Import IrefSlots.
Require Import IcacheRef.
Require Import IcacheInv.
Require Import IcacheEscrow.
Require Import KallocInv.
Require Import KvmSpec.
Require Import FileInvDefs.
Require Import IcacheRef.
Require Import IrefSlots.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import ProcAvail.
Import Defs.

Local Open Scope Z_scope.

(* dirlookup's own frame is 96 bytes (12 slots); its deepest callee is
   readi at 78 (namecmp wants 4, iget 16).

   78, and readi's dominant chain is now bmap's (not copyout's): printk's
   real stack need (48, printk_stack) dominates bmap (64), which dominates
   readi (78, SpecReadi.v's header has the arithmetic) -- so this one is
   12 + 78 = 90. *)
Notation K_dirlookup := (100%nat) (only parsing).
(* T_DIR, read off the [li a5,1] at +0x1a that [lh a4,68(a0)] is compared
   against. *)
Definition T_DIR : mword 16 := mword_of_int 1.

(* [dir_inums_ok] -- the premise iget's argument bound forces on the CALLER
   (see the header) -- used to be defined here.  fs-icache.md §15(a) made it
   a conjunct of the icache's escrow payloads, which are defined far below
   any spec file, so it now lives in [DirView.v] and this file re-exports it
   by importing DirView.  The premise below is unchanged. *)

Definition wp_dirlookup_sconf_body
    `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !fileG Σ, !kallocG Σ,
      !bioG Σ, !diskGhostG Σ, !uartGhostG Σ, !fsLogG Σ, !logG Σ,
      ICFG : icfg, !icacheG Σ, !irefslotG Σ, !pavG Σ, !iregG Σ}
    `{GEN : GenId} `{CID : CpuId}

    (γs : list gname) (j : nat) (γl : gname)          (* the running process *)
    (γu : uart_names) (γd : disk_names) (γk : gname)  (* disk fabric + lock  *)
    (pd pav pu : mword 64)
    (bn : bio_names)
    (γfs : fs_names) (γi : gname)
    (cn : ic_names) (gtl : gname)                     (* the icache + itable *)
    (γa : gname) (γf : gname)                         (* kalloc, file table  *)
    (cov : gset Z) (logstart : Z) (nib : nat) (dev : mword 32)
    (ip : mword 64)
    (bm : blkmap) (data : nat -> list (bv 8))
    (dn : dinode)
    (fn : nat -> bv 8)                                (* the caller's name   *)
    (hasp : bool) (pofv : mword 32)                   (* poff, two-armed     *)
    (pidv : mword 32) (dq dqd dqn : dfrac)
    (m : regfile) (K : nat) (eb : bool)
    (b : bool) (lks : gset string) :=
  let pcE : mword 64 := mword_of_int KernelSyms.dirlookup in
  let pj := proc_addr j in
  let nb := m !!! Regidx (mword_of_int 11 : mword 5) in
  let pf := m !!! Regidx (mword_of_int 12 : mword 5) in
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5)) in
  let nrec := dir_nrec (bv_unsigned (di_size dn)) in
  let s := bname 14 fn in
  (K_dirlookup <= K)%nat ->
  (* (1) the panic at +0x1c is refuted.  NOTE that panic("dirlookup read")
     at +0x46 is NOT refuted -- it is a live arm, see the header. *)
  di_type dn = T_DIR ->
  (* (2) readi's own threading, verbatim *)
  log_geom_ok cov logstart ->
  blkmap_wf cov logstart bm ->
  bm_covers bm (bv_unsigned (di_size dn)) ->
  bv_unsigned (di_size dn) <= Z.of_nat MAXFILE * Z.of_nat BSIZE ->
  (* (3) iget's argument bound, over the records -- see the header *)
  dir_inums_ok data nrec nib ->
  (j < NPROC)%nat ->
  γs !! j = Some γl ->
  (* a0 = dp *)
  m !!! Regidx (mword_of_int 10 : mword 5) = ip ->
  (* a2 = poff, reflected into a ghost boolean the way readi's [user] is *)
  eq_vec (m !!! Regidx (mword_of_int 12 : mword 5)) zero_reg = negb hasp ->
  (* PARKING PREMISE -- readi sleeps *)
  eb = true ->
  (* the order premise, at the LOWEST rank this cone touches; every
     higher one follows by [locks_below_mono]. *)
  locks_below lks "bcache" ->
  sie_cap_gpr m K b pj -∗
  cpu_own 0 eb pj b lks -∗
  kernel_text -∗ kernel_data -∗ pc_is pcE -∗
  (* THE SHORT READ arm calls [panic("dirlookup read")], and panic is an
     ordinary call: the literal comes out of [kernel_data] above and the
     console credentials printk needs out of [panic_env].  Both persistent,
     and every caller of dirlookup already holds them. *)
  panic_env -∗
  bio_ctx bn (fs_view γfs γd dev cov) -∗
  kalloc_env γa None -∗
  (* ---- THE LOCKED DIRECTORY, readi's bundle verbatim ---- *)
  i_dev ip ↦₄{dqd} dev -∗
  inode_meta ip dn -∗
  inode_map γfs ip bm -∗
  inode_blocks γfs bm data -∗
  (* ---- THE CALLER'S 14-BYTE NAME BUFFER (namecmp's [f]) ---- *)
  ([∗ list] i ∈ seq 0 14, pa_add nb i ↦ₘ{dqn} fn i) -∗
  (* ---- poff: a 4-byte cell, or nothing ---- *)
  (if hasp then pf ↦₄ pofv else emp) -∗
  (* ---- the caller's own pid cell (bread's acquiresleep records it) ---- *)
  p_pid pj ↦₄{dq} pidv -∗
  (* ---- the running-thread bundle and the disk fabric ---- *)
  procs_inv γs -∗
  dev_inv γu γd -∗
  disk_geom γd pd pav pu -∗
  is_lock γk d_lock "virtio_disk"%string (disk_res γd pd pav pu) -∗
  bslot bn -∗
  (* ---- THE ICACHE, exactly as iget takes it ---- *)
  is_itable2 gtl cn γfs γi cov logstart nib dev -∗
  itable_inv -∗
  ic_escrows cn γfs γi cov logstart -∗
  (* ONE ledger unit for the iget on the found arm; RETURNED on the other *)
  iref_slot -∗
  (* THE CROSSING IS THE LITERAL [true], NOT [b].  This function can SLEEP
     (through namex / dirlookup, down to ilock and sleep), so a park moves
     the hart with interrupts off and the crossing has nothing to do with
     SIE.  Spelled [b] the two coincide at the only instance the [eb = true]
     premise admits, which is why this went unnoticed. *)
  wp_next true pj (fun (CID : CpuId) =>
  ∀ (mf : regfile) (found : bool) (k : nat) (kslot : nat) (q : Qp),
      ⌜callee_saved m mf⌝ -∗
      sie_cap_gpr mf K b pj -∗
      cpu_own 0 eb pj b lks -∗
      pc_is ret_tgt -∗
      (* THE DIRECTORY COMES BACK UNTOUCHED *)
      i_dev ip ↦₄{dqd} dev -∗
      inode_meta ip dn -∗
      inode_map γfs ip bm -∗
      inode_blocks γfs bm data -∗
      ([∗ list] i ∈ seq 0 14, pa_add nb i ↦ₘ{dqn} fn i) -∗
      p_pid pj ↦₄{dq} pidv -∗
      bslot bn -∗
      (* THE TWO ARMS *)
      (if found
       then ⌜dir_first data nrec s = Some k
             /\ (kslot < NINODE)%nat
             /\ mf !!! Regidx (mword_of_int 10 : mword 5) = ientry kslot⌝ ∗
            inode_ref kslot q dev
              (zero_extend' 32 (dir_inum data k : mword 16) : mword 32) ∗
            (if hasp
             then pf ↦₄ (mword_of_int (Z.of_nat (16 * k)) : mword 32)
             else emp)
       else ⌜dir_first data nrec s = None
             /\ mf !!! Regidx (mword_of_int 10 : mword 5)
                = (mword_of_int 0 : mword 64)⌝ ∗
            iref_slot ∗
            (if hasp then pf ↦₄ pofv else emp)) -∗
      WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

Module Type DIRLOOKUP.
  Parameter wp_dirlookup_sconf :
    forall `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !fileG Σ, !kallocG Σ,
             !bioG Σ, !diskGhostG Σ, !uartGhostG Σ, !fsLogG Σ, !logG Σ,
             ICFG : icfg, !icacheG Σ, !irefslotG Σ, !pavG Σ, !iregG Σ}
      `{GEN : GenId} `{CID : CpuId}
      (γs : list gname) (j : nat) (γl : gname)
      (γu : uart_names) (γd : disk_names) (γk : gname)
      (pd pav pu : mword 64)
      (bn : bio_names)
      (γfs : fs_names) (γi : gname)
      (cn : ic_names) (gtl : gname)
      (γa : gname) (γf : gname)
      (cov : gset Z) (logstart : Z) (nib : nat) (dev : mword 32)
      (ip : mword 64)
      (bm : blkmap) (data : nat -> list (bv 8))
      (dn : dinode)
      (fn : nat -> bv 8)
      (hasp : bool) (pofv : mword 32)
      (pidv : mword 32) (dq dqd dqn : dfrac)
      (m : regfile) (K : nat) (eb : bool)
      (b : bool) (lks : gset string),
      wp_dirlookup_sconf_body γs j γl γu γd γk pd pav pu bn γfs γi cn gtl
                              γa γf cov logstart nib dev ip bm data dn
                              fn hasp pofv pidv dq dqd dqn m K eb b lks.
End DIRLOOKUP.
