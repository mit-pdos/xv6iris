(* SpecWritei.v -- the public interface of writei, stated independently of
   its proof.  Requires only the definitional layer -- never a whole-function
   proof file -- so every function proof can be checked in parallel.

     int writei(struct inode *ip, int user_src, uint64 src, uint off, uint n)
     {
       uint tot, m;  struct buf *bp;

       if(off > ip->size || off + n < off)     return -1;
       if(off + n > MAXFILE*BSIZE)             return -1;

       for(tot = 0; tot < n; tot += m, off += m, src += m){
         uint addr = bmap(ip, off/BSIZE);
         if(addr == 0) break;
         bp = bread(ip->dev, addr);
         m = min(n - tot, BSIZE - off%BSIZE);
         if(either_copyin(bp->data + (off % BSIZE), user_src, src, m) == -1) {
           brelse(bp);  break;
         }
         log_write(bp);
         brelse(bp);
       }

       if(off > ip->size) ip->size = off;
       iupdate(ip);
       return tot;
     }

   256 bytes, 98 instructions -- the largest function of the inode layer, and
   structurally the hardest: a loop with two breaks, three early exits, and
   five conditionally-saved registers.  Design:
   claude-notes/design/fs-inode.md, "writei -- the loop, and what a PARTIAL
   write may claim".

   ==== THE POSTCONDITION IS A FLAT BYTE-RANGE CLAIM ====================

   [inode_blocks γfs bm data] is indexed by file BLOCK; writei is about a
   byte RANGE that straddles blocks.  Stating the effect per block would
   force every caller to redo the straddle arithmetic, so the view is
   defined once ([file_byte] below) and the whole effect is ONE clause:

     forall k, file_byte data' k = if off <= k < off + tot
                                   then <the byte written at k>
                                   else file_byte data k

   -- which covers a full write, a short write and a zero write uniformly.

   ==== ...PLUS A BOUNDED DISTURBED REGION ==============================

   The clause above is NOT the whole truth, and the reason is the fix to
   kernel defect D1 (claude-notes/kernel-defects.md).  When either_copyin
   fails part-way it has already copied a PREFIX of the chunk into the
   buffer, and writei now does

       log_write(bp);  brelse(bp);  break;

   -- i.e. it COMMITS the partial chunk rather than stranding it in the
   buffer cache.  That is the consistent thing to do (the alternative is a
   block whose contents depend on cache state), but it means the file
   genuinely changes OUTSIDE [off, off+tot): the return value [tot] is not
   advanced over the failed chunk, while the chunk's bytes are logged.

   So the postcondition admits a DISTURBED REGION immediately after the
   written range: [dist] bytes at [off+tot], with [dist <= BSIZE] because
   one chunk never crosses a block boundary, holding unspecified bytes
   [dstb].  Everything at or beyond [off+tot+dist] is unchanged, and
   [dist = 0] whenever no copy failed -- which a caller reads off
   [tot = n].  Both the bound and the [tot = n] tie are what make the
   clause usable: without them "the rest of the file is untouched" would be
   unavailable at every offset.

   WHAT THE "BYTE WRITTEN" IS, AND WHY IT IS AN EXISTENTIAL.  On the KERNEL
   arm the source bytes are the caller's own and the clause pins them.  On
   the USER arm they are copied out of user memory, about which the kernel
   may assume NOTHING -- [SpecCopyin]/[SpecEitherCopyin] hand the
   destination back as [exists dst_new] for exactly that reason -- so there
   is no nameable "source byte at k - off" at all.  The honest shape is
   therefore an existentially quantified [wrote : nat -> bv 8] plus a tie
   that fires only on the kernel arm.  A contract that named the source
   bytes unconditionally would be UNPROVABLE.

   HOLES READ AS ZEROS ([InodeInv.blk_holes_zero]).  [inode_blocks] leaves
   [data i] unconstrained at an UNALLOCATED index [i], and bmap deposits a
   freshly allocated block into the bundle at [replicate BSIZE 0] -- so
   without a normalisation of the unallocated indices the clause above is
   false the moment writei extends the file.  [blk_holes_zero] is that
   normalisation, threaded in and back out; it is also the xv6 file semantics
   (a hole reads as zeros).  It lives next to [inode_blocks] in InodeInv.v,
   as does the flat view [file_byte] the clause above is stated on.

   ==== COVERAGE IS PRESERVED ===========================================

   [InodeInv.bm_covers bm sz] -- every file block whose first byte is below
   [sz] is allocated -- is what keeps readi out of the log entirely
   (SpecReadi.v's header).  writei EXTENDS the file, so a caller that writes
   and then reads could never re-establish it unless writei promised it: the
   predicate is therefore a PREMISE at the old size and a POSTCONDITION at
   the new one.

   It is provable rather than merely desirable because writei allocates every
   block it writes -- through bmap, BEFORE [tot] is advanced over the chunk --
   and installs [size' = max(size, off + tot)].  So a block below the new size
   is either below the OLD size (the premise, carried across each bmap call by
   [InodeInv.bm_covers_keep], whose hypothesis is exactly the "never
   un-allocates" clause SpecBmap already carries) or was allocated by the loop
   itself, which is the loop invariant [bm_covers bmI (off + tot)].  Neither
   break arm needs a special case: both stop [tot] early, and the DISTURBED
   REGION below lies at or above [off + tot], hence at or above the new size,
   where coverage claims nothing.

   ==== A SHORT WRITE IS A NORMAL RETURN ================================

   The two breaks -- bmap returning 0 (out of blocks) and either_copyin
   returning -1 (bad user pointer) -- leave [tot < n] and RETURN [tot].
   Only the three up-front checks return -1.  A contract promising
   [tot = n] would be unprovable and one treating a short write as failure
   would be useless to filewrite, which loops on exactly this.

   The -1 arm additionally reports WHY (off past the end, or the range past
   MAXFILE*BSIZE), so a caller that has checked those knows it will not be
   taken.  The overflow test at +0x02e is DEAD BY THE JOINT NUMERIC PREMISE
   [off + n < 2^31] below -- NOT by two separate bounds on [off] and [n],
   which would let the [addw] at +0x022 wrap.  See that premise's comment,
   including the coverage note it carries.

   ==== SIZE AND FLUSH ==================================================

   [ip->size] is raised to the ADVANCED [off] when the write went past the
   old end, and [iupdate] then runs UNCONDITIONALLY on every returning path
   -- including [n = 0].  So writei needs everything iupdate needs
   ([i_inum], [inode_meta], the [sb + 24] field, the inode block's own
   [fsblock]) on top of everything bmap needs.

   [di_addrs dn'] is set to [bm_cells bm']: [inode_meta] owns only the five
   scalar cells, so that field is a phantom index that may be
   re-instantiated freely, and choosing the FINAL map is what lets a caller
   call iupdate again (design doc, decision record).

   ==== THE GHOST user FLAG IS THREADED, NOT SPECIALISED =================

   [either_copyin] carries [user] as a ghost boolean with [proc_priv]
   required only on the user arm and the tighter length bound on the kernel
   arm; claude-notes/completed/either-copy.md says readi/writei are exactly
   why.  writei threads it: the precondition and the postcondition are
   [if user then ... else ...], and the descriptor comes back EXTENDED (the
   copy may fault pages in) on the user arm.

   ==== THE BUDGET IS SPEND-AT-MOST, WITH AN ITERATION BOUND =============

   Per iteration: bmap at most 5, plus writei's own log_write 1 = 6; plus
   iupdate's 1 at the end.  The iteration count is bounded by the number of
   blocks the range straddles ([wi_blocks]), because every iteration but the
   last fills its block to the boundary.  So the premise is the lower bound
   [wi_cost off n <= ncount] and the postcondition is spend-at-most -- writei
   BRANCHES, and [log_op] has no mover outside the log spinlock, so a path
   that skips a spend cannot burn the surplus (SpecBmap.v's header).

   NOTE ON TIGHTNESS: 6 per block is bmap's worst case (two ballocs plus its
   own log_write), not the amortised cost -- the indirect block is allocated
   at most once in a file's life.  Tightening it needs an arm-aware bmap
   budget, not a change here.

   writei SLEEPS (bmap, bread, brelse, iupdate), so it threads the full
   running-process bundle.  It enters and returns at noff 0. *)
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
Require Import BcacheInv BioInv.
Require Import FsBlocks LogInv.
Require Import FsCrash.
Require Import BlockWords.
Require Import DinodeEnc.
Require Import InodeInv.
Require Import KallocInv.
Require Import UserPtTree.
Require Import KvmSpec.
Require Import ProcPtOwn.
Require Import FileInv ProcInv.
Require Import SpecIupdate.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Import Defs.

Local Open Scope Z_scope.

(* writei's own frame is 112 bytes (14 slots).  Its deepest callees are bmap
   and either_copyin, both 56; iupdate wants 44, bread 40, brelse 26,
   log_write 18. *)
Definition K_writei : nat := 70%nat.

(* [file_byte], [file_byte_block] and [blk_holes_zero] live in InodeInv.v,
   next to [inode_blocks] whose flat view they are.  They were parked here
   while editing InodeInv.v was too expensive; both are shared with readi. *)

(* ===================================================================== *)
(*  THE ITERATION BOUND AND THE BUDGET                                    *)
(* ===================================================================== *)

(* the number of blocks the byte range [off, off+n) can touch.  Every
   iteration but the last fills its block to the boundary, so this bounds
   the loop count. *)
Definition wi_blocks (off n : nat) : nat :=
  ((off `mod` BSIZE + n + BSIZE - 1) `div` BSIZE)%nat.

(* six units per iteration (bmap 5 + log_write 1), plus iupdate's one *)
Definition wi_cost (off n : nat) : nat := (6 * wi_blocks off n + 1)%nat.

(* the on-disk inode writei flushes: the caller's metadata with the size
   raised to the advanced offset when the write went past the old end, and
   the addrs field re-instantiated at the FINAL map (the phantom index -- see
   the header and the design doc's decision record). *)
Definition wi_dinode (dn : dinode) (bm' : blkmap) (off tot : nat) : dinode :=
  MkDinode (di_type dn) (di_major dn) (di_minor dn) (di_nlink dn)
    (if decide (bv_unsigned (di_size dn) < Z.of_nat (off + tot))
     then (mword_of_int (Z.of_nat (off + tot)) : mword 32)
     else di_size dn)
    (bm_cells bm').

Definition wp_writei_sconf_body
    `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !fileG Σ, !kallocG Σ,
      !bioG Σ, !diskGhostG Σ, !uartGhostG Σ, !fsLogG Σ, !logG Σ}
    `{GEN : GenId} `{CID : CpuId}
    (Φ : mval -> iProp Σ)
    (γs : list gname) (j : nat) (γl : gname)          (* the running process *)
    (γu : uart_names) (γd : disk_names) (γk : gname)  (* disk fabric + lock  *)
    (pd pav pu : mword 64)
    (bn : bio_names)
    (γ : log_names) (γfs : fs_names)
    (γa : gname) (γf : gname)                         (* kalloc, file table  *)
    (cov : gset Z) (logstart : Z) (inodestart : Z) (dev : mword 32)
    (ip : mword 64) (inum : mword 32)
    (bm : blkmap) (data : nat -> list (bv 8))
    (dn : dinode) (ds : list dinode)
    (user : bool) (off n : nat) (src_bytes : nat -> bv 8)
    (V : pprivate) (ncount : nat)
    (pidv : mword 32) (dq dqd dqn dqs : dfrac)
    (m : regfile) (K : nat) (eb : bool) (C : iProp Σ)
    (b : bool) :=
  let pcE : mword 64 := mword_of_int KernelSyms.writei in
  let pj := proc_addr j in
  let src := m !!! Regidx (mword_of_int 12 : mword 5) in
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5)) in
  (K_writei <= K)%nat ->
  (* ENOUGH BUDGET for the worst case: six units per straddled block, plus
     iupdate's one.  See the header. *)
  (wi_cost off n <= ncount)%nat ->
  (* the covered range's block-number bounds, and the log's own storage *)
  log_geom_ok cov logstart ->
  (* the inode's own block, exactly as iupdate takes it *)
  0 <= inodestart ->
  IBLOCK inum inodestart ∈ cov ->
  ~ (IBLOCK inum inodestart ∈ log_region_set logstart) ->
  diblk_wf ds ->
  di_addrs dn = bm_cells bm ->
  (* the file's block map, and the normalisation of its holes *)
  blkmap_wf cov logstart bm ->
  blk_holes_zero bm data ->
  (* EVERY BLOCK BELOW THE FILE'S SIZE IS ALLOCATED.  Threaded in and back
     out at the NEW size -- see the header. *)
  bm_covers bm (bv_unsigned (di_size dn)) ->
  (* THE JOINT NUMERIC PREMISE.  [off] and [n] are uints whose SUM stays in
     int range -- not two separate bounds.  It is what makes the
     [addw a5,a3,a4] at +0x022 non-wrapping, and hence what makes the
     [bltu a5,a3] overflow test at +0x02e DEAD.  Two separate 2^31 bounds
     do NOT suffice: their sum can reach 2^32, the 32-bit add wraps, the
     sign-extended result is huge, and the MAXFILE*BSIZE compare at +0x02a
     is then taken -- a live arm whose proof would need a wrapping-[addw]
     reading that this tree does not have.

     Every caller can discharge it: filewrite's [off] is bounded by the
     file size (<= MAXFILE*BSIZE = 274432) and its [n] is chunked, and the
     in-kernel callers (dirlink, the create path) pass small constants.

     COVERAGE NOTE: this means xv6's own [off + n < off] overflow check is
     not exercised by the proof -- the premise makes that arm dead rather
     than proving what the code does when it fires. *)
  (Z.of_nat off + Z.of_nat n < 2 ^ 31) ->
  bv_unsigned (di_size dn) < 2 ^ 31 ->
  (j < NPROC)%nat ->
  γs !! j = Some γl ->
  (* a0 = ip *)
  m !!! Regidx (mword_of_int 10 : mword 5) = ip ->
  (* a1 = user_src, reflected into the ghost boolean the way
     either_copyin's own contract spells it *)
  eq_vec (m !!! Regidx (mword_of_int 11 : mword 5)) zero_reg = negb user ->
  (* a3 = off, a4 = n -- the RV64 ABI's sign-extended uints, which for
     these ranges are the literals *)
  m !!! Regidx (mword_of_int 13 : mword 5) = (mword_of_int (Z.of_nat off) : mword 64) ->
  m !!! Regidx (mword_of_int 14 : mword 5) = (mword_of_int (Z.of_nat n) : mword 64) ->
  (* PARKING PREMISE (hart-generic scheduler protocol) -- everything below
     sleeps.  See SpecSched.v / SpecSleep.v. *)
  eb = true ->
  sie_cap_gpr m K b pj -∗
  cpu_own 0 eb pj C b -∗
  kernel_text -∗ pc_is pcE -∗
  panic_wp_any -∗
  bio_ctx bn (fs_view γfs γd dev cov) -∗
  log_ctx γ bn γfs cov logstart dev -∗
  (* either_copyin's user arm reaches copyin, which reaches vmfault/kalloc *)
  kalloc_env γa None -∗
  (* ip->dev and ip->inum: read, never written -- FRACTIONS *)
  i_dev ip ↦₄{dqd} dev -∗
  i_inum ip ↦₄{dqn} inum -∗
  (* the five metadata cells (ip->size is read AND written), the thirteen
     addrs cells and the indirect block, and the file's data blocks *)
  inode_meta ip dn -∗
  inode_map γfs ip bm -∗
  inode_blocks γfs bm data -∗
  (* sb.inodestart, read once inside iupdate *)
  sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
  (* THE INODE BLOCK, as sixteen pure dinodes *)
  fsblock γfs (IBLOCK inum inodestart) (diblk_bytes ds) -∗
  (* THE SOURCE.  On the user arm a virtual address into the running
     process's own space; on the kernel arm the caller's own byte buffer,
     returned unchanged. *)
  (if user
   then proc_priv γf pj pidv V
   else [∗ list] i ∈ seq 0 n, pa_add src i ↦ₘ src_bytes i) -∗
  (* the caller's own pid cell (acquiresleep records it).  On the user arm
     this is [proc_priv]'s own quarter (ProcInv.proc_priv_pid). *)
  p_pid pj ↦₄{dq} pidv -∗
  (* the running-thread bundle *)
  procs_inv Φ γs -∗
  scheds_inv Φ γs -∗
  own_ctx (p_context pj) -∗
  park_hlf j true -∗
  (* the disk fabric *)
  dev_inv γu γd -∗
  disk_geom γd pd pav pu -∗
  is_lock γk d_lock "virtio_disk"%string (disk_res γd pd pav pu) -∗
  (* THREE slot units -- bmap's peak; writei's own bread holds one across
     either_copyin and log_write, and log_write wants one of its own *)
  bslots bn 3 -∗
  (* THE RESERVATION, spend-at-most *)
  log_op γ ncount -∗
  wp_next b pj (fun (CID : CpuId) =>
  ∀ (mf : regfile) (tot : nat) (bm' : blkmap) (data' : nat -> list (bv 8))
    (dn' : dinode) (ds' : list dinode) (n' : nat)
    (wrote : nat -> bv 8) (dist : nat) (dstb : nat -> bv 8) (P' : uptd),
      ⌜callee_saved m mf⌝ -∗
      ⌜blkmap_wf cov logstart bm'⌝ -∗
      ⌜blk_holes_zero bm' data'⌝ -∗
      ⌜diblk_wf ds'⌝ -∗
      ⌜di_addrs dn' = bm_cells bm'⌝ -∗
      ⌜bv_unsigned (di_size dn') < 2 ^ 31⌝ -∗
      (* COVERAGE IS PRESERVED, AT THE NEW SIZE.  See the header. *)
      ⌜bm_covers bm' (bv_unsigned (di_size dn'))⌝ -∗
      (* THE DISTURBED REGION: at most one block, immediately after the
         written range, and EMPTY unless a copy failed part-way.  See the
         header. *)
      ⌜(dist <= BSIZE)%nat⌝ -∗
      ⌜(tot = n)%nat -> dist = 0%nat⌝ -∗
      (* THE RANGE CLAUSE -- the whole effect of the write, in one line *)
      ⌜forall k : nat,
         file_byte data' k
         = if decide ((off <= k)%nat /\ (k < off + tot)%nat)
           then wrote (k - off)%nat
           else if decide ((off + tot <= k)%nat /\ (k < off + tot + dist)%nat)
                then dstb (k - (off + tot))%nat
                else file_byte data k⌝ -∗
      (* ...and, on the KERNEL arm only, what those bytes were *)
      ⌜user = false -> forall i : nat, (i < tot)%nat -> wrote i = src_bytes i⌝ -∗
      (* THE TWO ARMS, on the returned a0.  A SHORT WRITE IS THE SECOND
         ARM, not the first: only the up-front checks answer -1. *)
      ⌜(mf !!! Regidx (mword_of_int 10 : mword 5) = (mword_of_int (-1) : mword 64)
        /\ (bv_unsigned (di_size dn) < Z.of_nat off
            \/ (MAXFILE * BSIZE < off + n)%nat)
        /\ tot = 0%nat /\ dist = 0%nat
        /\ bm' = bm /\ data' = data /\ dn' = dn /\ ds' = ds
        /\ n' = ncount)
       \/ (mf !!! Regidx (mword_of_int 10 : mword 5)
             = (mword_of_int (Z.of_nat tot) : mword 64)
           /\ (tot <= n)%nat
           /\ dn' = wi_dinode dn bm' off tot
           /\ ds' = <[islot inum := dn']> ds)⌝ -∗
      (* at most [wi_cost off n] units gone, and none gained *)
      ⌜((ncount - wi_cost off n)%nat <= n')%nat /\ (n' <= ncount)%nat⌝ -∗
      ⌜uptd_ext (pv_upt V) P'⌝ -∗
      sie_cap_gpr mf K b pj -∗
      cpu_own 0 eb pj C b -∗
      pc_is ret_tgt -∗
      own_ctx (p_context pj) -∗
      park_hlf j true -∗
      p_pid pj ↦₄{dq} pidv -∗
      i_dev ip ↦₄{dqd} dev -∗
      i_inum ip ↦₄{dqn} inum -∗
      inode_meta ip dn' -∗
      inode_map γfs ip bm' -∗
      inode_blocks γfs bm' data' -∗
      sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
      fsblock γfs (IBLOCK inum inodestart) (diblk_bytes ds') -∗
      (if user
       then proc_priv γf pj pidv (upd_upt V P')
       else [∗ list] i ∈ seq 0 n, pa_add src i ↦ₘ src_bytes i) -∗
      bslots bn 3 -∗
      log_op γ n' -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
  WP (Loop : expr riscv_lang) {{ Φ }}.

Module Type WRITEI.
  Parameter wp_writei_sconf :
    forall `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !fileG Σ, !kallocG Σ,
             !bioG Σ, !diskGhostG Σ, !uartGhostG Σ, !fsLogG Σ, !logG Σ}
      `{GEN : GenId} `{CID : CpuId}
      (Φ : mval -> iProp Σ)
      (γs : list gname) (j : nat) (γl : gname)
      (γu : uart_names) (γd : disk_names) (γk : gname)
      (pd pav pu : mword 64)
      (bn : bio_names)
      (γ : log_names) (γfs : fs_names)
      (γa : gname) (γf : gname)
      (cov : gset Z) (logstart : Z) (inodestart : Z) (dev : mword 32)
      (ip : mword 64) (inum : mword 32)
      (bm : blkmap) (data : nat -> list (bv 8))
      (dn : dinode) (ds : list dinode)
      (user : bool) (off n : nat) (src_bytes : nat -> bv 8)
      (V : pprivate) (ncount : nat)
      (pidv : mword 32) (dq dqd dqn dqs : dfrac)
      (m : regfile) (K : nat) (eb : bool) (C : iProp Σ)
      (b : bool),
      wp_writei_sconf_body Φ γs j γl γu γd γk pd pav pu bn γ γfs γa γf
                           cov logstart inodestart dev ip inum bm data dn ds
                           user off n src_bytes V ncount
                           pidv dq dqd dqn dqs m K eb C b.
End WRITEI.
