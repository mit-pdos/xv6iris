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

   ==== off AND n ARE FULL 32-BIT uints =================================

   Both are C [uint]s, so both range over [0, 2^32) -- and the RV64 ABI
   hands a 32-bit argument over SIGN-EXTENDED, [uint] included, so a value
   at or above 2^31 arrives in a3/a4 as a NEGATIVE 64-bit word.  That is
   what the two register premises spell:

     m a3 = sign_extend' 64 (mword_of_int (Z.of_nat off) : mword 32)

   Below 2^31 that IS the plain literal ([rd_arg32_small]), so a caller who
   had the old premise still reads the same one rewrite later.

   THE POSTCONDITION DOES NOT MOVE WITH THE WIDENING.  [rd_clamp] is already
   0 at [off > size], and a 32-bit [off] at or above 2^31 is past the end of
   every file (the size is bounded by MAXFILE*BSIZE), so the arm the
   widening opens is the arm that was already there -- the pre-frame exit,
   returning 0.  What the widening costs is one reading of the [bltu a5,a3]
   at +0x002: a sign-extended-negative a3 is ABOVE the size as an unsigned
   64-bit word, which is what makes that 64-bit compare decide the 32-bit
   unsigned one the C is written in.

   COVERAGE NOTE: the joint numeric premise [off + n < 2^32] is the sum in
   the MATHEMATICAL integers, and it is what makes the [c.addw a4,a3] at
   +0x022 non-wrapping.  It is the one thing this contract asks beyond
   32-bittedness, and it is what leaves xv6's own [off + n < off] overflow
   test dead by premise rather than proving what the code does when it
   fires.

   IT IS GUARDED BY THE SIZE TEST -- [off <= ip->size -> off + n < 2^32] --
   and the guard is not a convenience, it is what the instruction order
   already says: +0x022 is BEHIND the [bltu a5,a3] at +0x002, so the add is
   reached only for an [off] inside the file, where a size at most
   MAXFILE*BSIZE makes the bound free.  Ungard it and the contract excludes
   exactly the offsets the size test rejects, which is the case kexec's
   phdr read hands over -- [elf.phoff] is four untrusted bytes, [n] is 56,
   and nothing in exec bounds the sum.  The guard opens only [off > size],
   where [rd_clamp] is already 0, so THE POSTCONDITION DOES NOT MOVE; the
   case that would move it (a small [off] with [n] near 2^32, sum wrapping
   while [rd_clamp] is nonzero) sits under the guard and still owes the
   bound.

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
Require Import PrintintArith.
Require Import InstrBytes.
Require Import RegFile.
Require Import RiscvExtras.
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
Require Import InodeInv.
Require Import UserPtTree.
Require Import KvmSpec.
Require Import ProcPtOwn.
Require Import ProcInv.
Require Import FileInvDefs.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import ProcAvail.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Require Import TsoCtx.
Import Defs.

Local Open Scope Z_scope.

(* readi's own frame is 112 bytes (14 slots).  Its deepest callee is now
   bmap at 64 (itself dominated by balloc's out-of-blocks printk, 58, which
   is itself dominated by printk's own real stack need, printk_stack = 48);
   either_copyout wants 58, bread 40, brelse 26.

   64, NOT 56: bmap's own budget grew 56 -> 64 when SpecPrintk.v's general
   contract stopped undercounting printk's frame (38 -> 48), which pushed
   balloc's out-of-blocks arm 50 -> 58, which pushed bmap 56 -> 64 (6 + 58).
   either_copyout's 58 (SpecCopyout.v's own, unrelated, [psz]-in-s11 chain)
   does NOT reach printk, so it is unaffected and is no longer the max. *)
Notation K_readi := (88%nat) (only parsing).
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

(* ===================================================================== *)
(*  THE ABI's 32-BIT ARGUMENT, FOR A CALLER WHOSE ARGUMENT IS SMALL      *)
(* ===================================================================== *)

(* [off] and [n] arrive sign-extended (see the header).  Below 2^31 that is
   the plain 64-bit literal, which is the form every caller with a bounded
   argument -- dirlookup's [16*i], fileread's [f->off] -- already has. *)
Lemma rd_arg32_small (x : nat) : (Z.of_nat x < 2 ^ 31)%Z ->
  (mword_of_int (Z.of_nat x) : mword 64)
  = sign_extend' 64 (mword_of_int (Z.of_nat x) : mword 32).
Proof.
  intro Hx. symmetry. apply PrintintArith.sext32_64_small.
  split; [apply Nat2Z.is_nonneg | exact Hx].
Qed.

(* THE BUFFER CARRIES ITS OWN TIER [ktb] -- the kernel arm's destination is
   a FRAME local for one caller (dirlookup's [de]) and a KT0 page for the
   next (kexec's segment).  Same shape as SpecMemmove.v's note. *)
Definition wp_readi_sconf_body
    `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !irefslotG Σ, !pavG Σ, !fileG Σ} `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}
    
    (ktb : ktier) `{!KtierLe ktb KT1} (γs : list gname) (j : nat) (γl : gname)          (* the running process *)
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
    (m : regfile) (K : nat) (eb : bool)
    (b : bool) (lks : gset string) :=
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
  (* [off] is a uint, full stop -- a caller reading one out of an untrusted
     struct can pay this and nothing narrower. *)
  (Z.of_nat off < 2 ^ 32) ->
  (* THE JOINT NUMERIC PREMISE, GUARDED BY THE SIZE TEST.  The sum must not
     wrap 32 bits, because that is what makes the [c.addw a4,a3] at +0x022
     denote [off + n] rather than its wrap -- and it is what keeps the C's
     own [off + n < off] overflow test dead.  But +0x022 sits AFTER the
     [bltu a5,a3] at +0x002, so it is reached only when [off] is inside the
     file, and that is exactly what this premise may assume.
       Stated UNGUARDED it excludes precisely the wrapping offsets the size
     test already rejects -- which is what kexec's phdr read hands over
     ([elf.phoff] is four untrusted bytes and [n] is 56), and no loop in
     exec can bound them.  Guarded, a caller discharges it from
     [off <= size <= MAXFILE*BSIZE] by [lia], with no case analysis at the
     call site and no bound on the untrusted field at all.
       THE GUARD DOES NOT MOVE THE POSTCONDITION, and the direction matters:
     it opens only [off > size], where [rd_clamp] is already 0 and the
     pre-frame exit returns 0.  The case that WOULD move it -- a small [off]
     with an [n] near 2^32, where the sum wraps while [rd_clamp] is not 0 --
     has [off <= size], so the guard still demands the bound there. *)
  (Z.of_nat off <= bv_unsigned (di_size dn) ->
   Z.of_nat off + Z.of_nat n < 2 ^ 32) ->
  (j < NPROC)%nat ->
  γs !! j = Some γl ->
  (* a0 = ip *)
  m !!! Regidx (mword_of_int 10 : mword 5) = ip ->
  (* a1 = user_dst, reflected into the ghost boolean the way
     either_copyout's own contract spells it *)
  eq_vec (m !!! Regidx (mword_of_int 11 : mword 5)) zero_reg = negb user ->
  (* a3 = off, a4 = n -- the RV64 ABI's sign-extended uints, at the FULL
     32-bit range, so at or above 2^31 these words are negative.  Below
     2^31 they are the plain literals ([rd_arg32_small]). *)
  m !!! Regidx (mword_of_int 13 : mword 5)
    = sign_extend' 64 (mword_of_int (Z.of_nat off) : mword 32) ->
  m !!! Regidx (mword_of_int 14 : mword 5)
    = sign_extend' 64 (mword_of_int (Z.of_nat n) : mword 32) ->
  (* readi's cone: its own bread and brelse both directly acquire "bcache"
     (rank 4, LockRank.v); bmap (BMAP_NOALLOC) and either_copyout expose no
     locks_below premise of their own, so "bcache" is the lowest -- and
     only -- bound this contract states. *)
  locks_below lks "bcache" ->
  sie_cap_gpr KT1 m K b pj -∗
  cpu_own 0 eb pj b lks -∗
  (* THE TRAP-CSR COMPLEMENT, NOT THE BARE PAIR.  readi never acquires
     anything itself -- its interior sleepers (bmap's bread, its own
     bread, brelse, either_copyout's copyout) all supply and consume the
     pair internally -- so this is a PURE PASS-THROUGH: at [eb = true] it
     is [emp] and no existing caller gains an obligation; at [eb = false]
     the caller holds it because the trap handed it over, and readi
     threads it to bmap and bread unchanged and takes it back from each in
     turn.  See claude-notes/completed/eb-generic-sweep.md. *)
  trap_csrs_ext KT1 eb -∗
  cpu_claim_ext eb pj -∗
  kernel_text -∗ kernel_data -∗ pc_is pcE -∗
  panic_env -∗
  bio_ctx bn (fs_view γfs γd dev cov) -∗
  (* THE BYTE VIEW'S ROW (durable-disk 1c-flip step 3).  readi is the one
     whole-block reader in the tree that holds NO log/region/bitmap
     invariant -- by design, it takes no [log_ctx] -- so the row it needs
     to turn "the buffer holds [bsl]" into "[bsl] is what my byte run says"
     comes in as its own premise.  Persistent, and every caller has one
     ([InodeRegion.ireg_inv_bytes]). *)
  fs_bytes_any γfs -∗
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
   else ([∗ list] i ∈ seq 0 n, pa_add dst i ↦ₘ[ktb] dst_olds i) ∗
        proc_priv_bare pj pidv V) -∗
  (* the running-thread bundle *)
  procs_inv γs -∗
  (* the disk fabric *)
  dev_inv γu γd -∗
  disk_geom γd pd pav pu -∗
  is_lock γk d_lock "virtio_disk"%string (disk_res γd pd pav pu) -∗
  (* ONE slot unit.  bmap-with-no-allocation wants one and hands it back
     before readi's own bread takes it; brelse returns that one too. *)
  bslot -∗
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
      sie_cap_gpr KT1 mf K b pj -∗
      cpu_own 0 eb pj b lks -∗
      trap_csrs_ext KT1 eb -∗
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
              pa_add dst i ↦ₘ[ktb] rd_delivered data dst_olds off tot i) ∗
            proc_priv_bare pj pidv V) -∗
      bslot -∗
      WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

Module Type READI.
  Parameter wp_readi_sconf :
    forall `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !irefslotG Σ, !pavG Σ, !fileG Σ} `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}
      
      (ktb : ktier) `{!KtierLe ktb KT1} (γs : list gname) (j : nat) (γl : gname)
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
      (m : regfile) (K : nat) (eb : bool)
      (b : bool) (lks : gset string),
      wp_readi_sconf_body ktb γs j γl γu γd γk pd pav pu bn γfs γa γf
                          cov logstart dev ip bm data dn
                          user off n dst_olds V
                          pidv dq dqd m K eb b lks.
End READI.
