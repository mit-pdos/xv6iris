(* SpecReadi.v -- the public interface of readi, stated independently of its
   proof.  Requires only the definitional layer -- never a whole-function
   proof file -- so every function proof can be checked in parallel.

     int readi(struct inode *ip, int user_dst, uint64 dst, uint off, uint n)
     {
       uint tot, m;  struct buf *bp;

       if(off > ip->size || off + n < off)   return 0;
       if(off + n > ip->size)                n = ip->size - off;

       for(tot = 0; tot < n; tot += m, off += m, dst += m){
         uint addr = bmap(ip, off/BSIZE);
         if(addr == 0) break;
         bp = bread(ip->dev, addr);
         m = min(n - tot, BSIZE - off%BSIZE);
         if(either_copyout(user_dst, dst, bp->data + (off % BSIZE), m) == -1) {
           brelse(bp);  tot = -1;  break;
         }
         brelse(bp);
       }
       return tot;
     }

   242 bytes, 97 instructions -- writei's structural twin, and simpler in
   every way that matters:

   ==== READI MODIFIES NOTHING =========================================

   No [log_write], no [iupdate], no [inode_meta] update, no log resources at
   all: [inode_map], [inode_blocks] and [inode_meta] come back at the SAME
   [bm], [data] and [dn].  There is therefore no [log_op] budget, no
   [log_ctx], no [γ : log_names], and no disturbed region -- writei's
   three-way range clause (kernel defect D1's fix) has no analogue here,
   because the failure path releases a buffer it never touched.

   ==== ...WHICH IS WHY IT NEEDS bm_covers ==============================

   readi calls bmap, and bmap ALLOCATES when the slot is zero -- which calls
   log_write.  But fileread does not wrap readi in a transaction, so an
   allocating read would hit panic("log_write outside of trans").  It never
   happens because every block below a file's size is allocated, and
   [InodeInv.bm_covers] is that statement; under it every one of readi's
   bmap calls satisfies [SpecBmap.BMAP_NOALLOC]'s single extra premise
   ([InodeInv.bm_covers_off] does the /BSIZE and returns both the index
   bound and the nonzero fact).  Design:
   claude-notes/design/fs-inode.md, "readi, and why it forced a no-alloc
   bmap".

   [bm_covers] is not restated in the postcondition: [bm] and [dn] come back
   LITERALLY unchanged, so the caller's own premise still holds of them.

   ==== THE FILE'S SIZE BOUNDS THE BLOCK INDEX =========================

   readi has NO MAXFILE*BSIZE check of its own -- it clamps [n] to the file's
   end instead and trusts the size.  So the file-system invariant
   [ip->size <= MAXFILE*BSIZE] is a genuine PREMISE here: without it a file
   claiming a larger size would drive bmap past MAXFILE and into its
   panic("bmap: out of range").  It also subsumes the size's 2^31 bound.

   ==== WHAT COMES BACK, AND WHERE ======================================

   The bytes DELIVERED are the file's bytes.  Stated on the flat byte view
   [InodeInv.file_byte] -- readi's postcondition is writei's range clause
   run in the other direction, over the same [inode_blocks] -- and, because
   the destination's untouched tail is equally nameable, with NO existential
   at all: after reading [tot] bytes the destination holds

     rd_delivered data dst_olds off tot
       = fun i => if i < tot then file_byte data (off + i) else dst_olds i

   which is exact on both ends.  (writei needed an existential [wrote]
   because its SOURCE was user memory; readi's source is the file, which the
   caller's own [inode_blocks] names.)

   That clause lives inside the [if user], because the destination is a
   pointer into ONE OF TWO ADDRESS SPACES and which one is a run-time
   argument -- exactly what [either_copyout]'s ghost [user] flag is for
   (claude-notes/completed/either-copy.md names readi/writei as the reason
   it is a ghost boolean).  readi THREADS the flag: [proc_priv] is required
   only on the user arm, and on that arm nothing is said about the bytes the
   process will read back.

   ==== THE RETURN VALUE IS EXACT =======================================

   Two arms, not three.  Under [bm_covers] the "bmap returned 0" break is
   DEAD, so the only way to stop early is [either_copyout] faulting -- which
   returns 0 unconditionally on the kernel arm.  Hence:

   - a0 = -1 and [user = true] -- the copy out faulted part-way;
   - a0 = tot and [tot = rd_clamp (di_size dn) off n] -- the whole clamped
     count was read.

   The up-front bounds failure ([off > ip->size]) is NOT a third arm: it
   returns 0, and [rd_clamp] is 0 there, so it IS the second arm with
   [tot = 0].  Collapsing them is what makes the contract exact rather than
   merely bounded -- a caller learns that a returning readi read everything
   there was to read.

   COVERAGE NOTE: the joint numeric premise [off + n < 2^31] (writei's, and
   for the same reason -- it is what makes the [c.addw] at +0x022
   non-wrapping) makes xv6's own [off + n < off] overflow test dead by
   premise rather than proving what the code does when it fires.

   readi SLEEPS (bmap, bread, brelse, and copyout on the user arm), so it
   threads the full running-process bundle.  It enters and returns at
   noff 0. *)
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
Require Import DinodeEnc.
Require Import InodeInv.
Require Import KallocInv.
Require Import UserPtTree.
Require Import KvmSpec.
Require Import ProcPtOwn.
Require Import ProcInv.
Require Import FileInvDefs.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Import Defs.

Local Open Scope Z_scope.

(* readi's own frame is 112 bytes (14 slots).  Its deepest callee is now
   either_copyout at 58; bmap wants 56, bread 40, brelse 26.

   58, NOT 56, and it is the far end of a chain that starts in copyout: [psz]
   has to outlive walkaddr / vmfault / memmove there, so gcc parked it in s11,
   copyout's frame grew to 14 slots and its budget went 50 -> 52
   (SpecCopyout.v), which pushed either_copyout 56 -> 58 (6 + 52), which
   pushes this one 70 -> 72.  Note bmap is UNAFFECTED and still 56 -- it does
   not reach copyout -- so the two are no longer equal and "both 56" is no
   longer the right way to remember this number. *)
Definition K_readi : nat := 72%nat.

(* ===================================================================== *)
(*  THE TWO PURE FUNCTIONS THE CONTRACT SPEAKS IN                        *)
(* ===================================================================== *)

(* [n], clamped to the file's end.  Zero when [off] is already past the end,
   which is exactly what the pre-frame exit returns. *)
Definition rd_clamp (szw : bv 32) (off n : nat) : nat :=
  if decide (Z.to_nat (bv_unsigned szw) < off + n)%nat
  then (Z.to_nat (bv_unsigned szw) - off)%nat
  else n.

(* the destination after [tot] bytes have been read: the file's bytes below
   [tot], the caller's own bytes at and above it. *)
Definition rd_delivered (data : nat -> list (bv 8)) (dst_olds : nat -> bv 8)
    (off tot i : nat) : bv 8 :=
  if decide (i < tot)%nat
  then file_byte data (off + i)%nat
  else dst_olds i.

Definition wp_readi_sconf_body
    `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !irefslotG Σ, !fileG Σ, !kallocG Σ,
      !bioG Σ, !diskGhostG Σ, !uartGhostG Σ, !fsLogG Σ, !logG Σ}
    `{GEN : GenId} `{CID : CpuId}
    
    (γs : list gname) (j : nat) (γl : gname)          (* the running process *)
    (γu : uart_names) (γd : disk_names) (γk : gname)  (* disk fabric + lock  *)
    (pd pav pu : mword 64)
    (bn : bio_names)
    (γfs : fs_names)
    (γa : gname) (γf : gname)                         (* kalloc, file table  *)
    (cov : gset Z) (logstart : Z) (dev : mword 32)
    (ip : mword 64)
    (bm : blkmap) (data : nat -> list (bv 8))
    (dn : dinode)
    (user : bool) (off n : nat) (dst_olds : nat -> bv 8)
    (V : pprivate)
    (pidv : mword 32) (dq dqd : dfrac)
    (m : regfile) (K : nat) (eb : bool) (C : iProp Σ)
    (b : bool) :=
  let pcE : mword 64 := mword_of_int KernelSyms.readi in
  let pj := proc_addr j in
  let dst := m !!! Regidx (mword_of_int 12 : mword 5) in
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5)) in
  (K_readi <= K)%nat ->
  (* the covered range's block-number bounds, and the log's own storage *)
  log_geom_ok cov logstart ->
  blkmap_wf cov logstart bm ->
  (* EVERY BLOCK BELOW THE SIZE IS ALLOCATED -- what makes every interior
     bmap call a BMAP_NOALLOC one, and hence what keeps readi out of the
     log entirely.  See the header. *)
  bm_covers bm (bv_unsigned (di_size dn)) ->
  (* the file-system invariant readi trusts instead of checking: a size past
     MAXFILE*BSIZE would drive bmap into its out-of-range panic.  It also
     subsumes [bv_unsigned (di_size dn) < 2^31], which is what makes the
     [c.lw a5,76(a0)] at +0x000 read the size exactly. *)
  bv_unsigned (di_size dn) <= Z.of_nat MAXFILE * Z.of_nat BSIZE ->
  (* THE JOINT NUMERIC PREMISE, writei's verbatim: [off] and [n] are uints
     whose SUM stays in int range -- not two separate bounds, which would
     let the [c.addw a4,a3] at +0x022 wrap.  See the header's coverage
     note. *)
  (Z.of_nat off + Z.of_nat n < 2 ^ 31) ->
  (j < NPROC)%nat ->
  γs !! j = Some γl ->
  (* a0 = ip *)
  m !!! Regidx (mword_of_int 10 : mword 5) = ip ->
  (* a1 = user_dst, reflected into the ghost boolean the way
     either_copyout's own contract spells it *)
  eq_vec (m !!! Regidx (mword_of_int 11 : mword 5)) zero_reg = negb user ->
  (* a3 = off, a4 = n -- the RV64 ABI's sign-extended uints, which for
     these ranges are the literals *)
  m !!! Regidx (mword_of_int 13 : mword 5) = (mword_of_int (Z.of_nat off) : mword 64) ->
  m !!! Regidx (mword_of_int 14 : mword 5) = (mword_of_int (Z.of_nat n) : mword 64) ->
  sie_cap_gpr m K b pj -∗
  cpu_own 0 eb pj C b -∗
  (* THE TRAP-CSR COMPLEMENT, NOT THE BARE PAIR.  readi never acquires
     anything itself -- its interior sleepers (bmap's bread, its own
     bread, brelse, either_copyout's copyout) all supply and consume the
     pair internally -- so this is a PURE PASS-THROUGH: at [eb = true] it
     is [emp] and no existing caller gains an obligation; at [eb = false]
     the caller holds it because the trap handed it over, and readi
     threads it to bmap and bread unchanged and takes it back from each in
     turn.  See claude-notes/projects/eb-generic-sweep.md. *)
  trap_csrs_ext eb -∗
  cpu_claim_ext eb pj -∗
  kernel_text -∗ pc_is pcE -∗
  panic_wp_any -∗
  bio_ctx bn (fs_view γfs γd dev cov) -∗
  (* either_copyout's user arm reaches copyout, which reaches vmfault/kalloc *)
  kalloc_env γa None -∗
  (* ip->dev: read, never written -- a FRACTION *)
  i_dev ip ↦₄{dqd} dev -∗
  (* ip->size, read once at +0x000 and never written.  The whole metadata
     bundle rather than the one cell, because that is what a caller holding
     a locked inode has; it comes back untouched. *)
  inode_meta ip dn -∗
  (* THE FILE'S BLOCK MAP AND ITS DATA BLOCKS, both returned UNCHANGED *)
  inode_map γfs ip bm -∗
  inode_blocks γfs bm data -∗
  (* THE DESTINATION, AND THE PID CELL THAT RIDES WITH IT.  On the user arm a
     virtual address into the running process's own space; on the kernel arm
     the caller's own [n]-byte buffer, whose current contents are [dst_olds].

     THE PID FRACTION IS THE KERNEL ARM'S, AND ONLY THE KERNEL ARM'S.  bread's
     acquiresleep records the caller's pid, so readi needs a share of
     [p->pid] either way -- but on the USER arm it borrows that share out of
     [proc_priv] itself ([ProcInv.proc_priv_pid]) rather than asking for it.
     It has to: that accessor is a BORROW, it consumes the block and returns a
     wand, so no caller can hold [proc_priv] and the fraction at the same
     time.  The cell is fully accounted for -- [ProcInv.proc_priv_core] holds
     one half and [SchedCtx.proc_pub] the other, behind [p->lock] -- so there
     is no third fragment anywhere for a caller to reach.  A caller therefore
     supplies ONE OR THE OTHER and never both.

     (An earlier version of this contract asked for both at once, with a
     comment claiming [proc_priv_pid] supplied the quarter alongside the
     block.  It does not, and the user arm was uncallable; fileread, its
     first caller, is what found it.  [SpecWritei.v] still has the same
     shape -- see claude-notes/design/file-table.md.) *)
  (if user
   then proc_priv_core pj pidv V
   else ([∗ list] i ∈ seq 0 n, pa_add dst i ↦ₘ dst_olds i) ∗
        p_pid pj ↦₄{dq} pidv) -∗
  (* the running-thread bundle *)
  procs_inv γs -∗
  (* the disk fabric *)
  dev_inv γu γd -∗
  disk_geom γd pd pav pu -∗
  is_lock γk d_lock "virtio_disk"%string (disk_res γd pd pav pu) -∗
  (* ONE slot unit.  bmap-with-no-allocation wants one and hands it back
     before readi's own bread takes it; brelse returns that one too. *)
  bslot bn -∗
  (* THE CROSSING IS THE LITERAL [true], NOT [b].  This function can SLEEP
     (its bread / ilock / bwrite does), and a park moves the hart with
     interrupts off, so the crossing has nothing to do with SIE -- the
     porting guide's "a PARKING function's [wp_next] index is [true]
     UNCONDITIONALLY".  Spelled [b] the two coincide at the only instance
     the [eb = true] premise admits, which is why this went unnoticed; once
     [eb = false] is reachable the [b] form would promise the caller it
     comes back on the hart it called from, which a park makes false. *)
  wp_next true pj (fun (CID : CpuId) =>
  ∀ (mf : regfile) (tot : nat) (P' : uptd),
      ⌜callee_saved m mf⌝ -∗
      ⌜uptd_ext (pv_upt V) P'⌝ -∗
      (* never more than the clamped count *)
      ⌜(tot <= rd_clamp (di_size dn) off n)%nat⌝ -∗
      (* THE TWO ARMS.  The "bmap returned 0" break is dead under
         [bm_covers], and either_copyout answers 0 unconditionally on the
         kernel arm, so a short read is possible ONLY on the user arm and
         the second arm is an EQUALITY.  See the header. *)
      ⌜(mf !!! Regidx (mword_of_int 10 : mword 5) = (mword_of_int (-1) : mword 64)
        /\ user = true)
       \/ (mf !!! Regidx (mword_of_int 10 : mword 5)
             = (mword_of_int (Z.of_nat tot) : mword 64)
           /\ tot = rd_clamp (di_size dn) off n)⌝ -∗
      sie_cap_gpr mf K b pj -∗
      cpu_own 0 eb pj C b -∗
      trap_csrs_ext eb -∗
      cpu_claim_ext eb pj -∗
      pc_is ret_tgt -∗
      i_dev ip ↦₄{dqd} dev -∗
      inode_meta ip dn -∗
      inode_map γfs ip bm -∗
      inode_blocks γfs bm data -∗
      (* THE BYTES DELIVERED ARE THE FILE'S BYTES.  Exact on both ends: the
         untouched tail still holds what the caller put there.  The pid
         fraction goes back the way it came -- with the kernel arm's buffer,
         or inside the user arm's block. *)
      (if user
       then proc_priv_core pj pidv (upd_upt V P')
       else ([∗ list] i ∈ seq 0 n,
              pa_add dst i ↦ₘ rd_delivered data dst_olds off tot i) ∗
            p_pid pj ↦₄{dq} pidv) -∗
      bslot bn -∗
      WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

Module Type READI.
  Parameter wp_readi_sconf :
    forall `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !irefslotG Σ, !fileG Σ, !kallocG Σ,
             !bioG Σ, !diskGhostG Σ, !uartGhostG Σ, !fsLogG Σ, !logG Σ}
      `{GEN : GenId} `{CID : CpuId}
      
      (γs : list gname) (j : nat) (γl : gname)
      (γu : uart_names) (γd : disk_names) (γk : gname)
      (pd pav pu : mword 64)
      (bn : bio_names)
      (γfs : fs_names)
      (γa : gname) (γf : gname)
      (cov : gset Z) (logstart : Z) (dev : mword 32)
      (ip : mword 64)
      (bm : blkmap) (data : nat -> list (bv 8))
      (dn : dinode)
      (user : bool) (off n : nat) (dst_olds : nat -> bv 8)
      (V : pprivate)
      (pidv : mword 32) (dq dqd : dfrac)
      (m : regfile) (K : nat) (eb : bool) (C : iProp Σ)
      (b : bool),
      wp_readi_sconf_body γs j γl γu γd γk pd pav pu bn γfs γa γf
                          cov logstart dev ip bm data dn
                          user off n dst_olds V
                          pidv dq dqd m K eb C b.
End READI.
