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

   ...AND THE REGION IS EMPTY ON THE KERNEL ARM (fs-icache.md §15.1(i)).
   The partially-copied chunk exists only because [either_copyin] can FAIL
   part-way, and it can only fail on the USER arm: [SpecEitherCopyin]'s
   post is [r = 0 \/ r = -1] when [user], but a bare [r = 0] when not --
   the kernel path is a [memmove] with no fault to take.  So the -1 break
   is DEAD for [user = false] and the third clause

     user = false -> dist = 0

   is provable rather than merely plausible.  It is what lets dirlink's
   middle-slot write claim EXACTNESS above the record (the up-to-64
   following records the three-way clause otherwise concedes), and hence
   what lets a writer re-park [DirView.dir_ok] after a dirlink -- create's
   obligation in the fs-sysfile campaign.  Stated as its own clause rather
   than by case-splitting the range clause: consumers on the user arm are
   untouched, and a kernel-arm consumer rewrites [dist] to 0 and reads the
   two-way clause off the same line.

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

   ==== ...AND THE TWO CONJUNCTS A RE-PARKER NEEDS ======================

   [IcacheEscrow.ic_loaded] carries [InodeLock.inode_ok cov logstart dn' bm'
   data'], whose SEVEN conjuncts a caller that re-parks the inode after the
   write has to rebuild.  Five of them are the clauses above (blkmap_wf,
   bm_covers, di_addrs, [di_type] -- which [wi_dinode] keeps definitionally
   -- and blk_holes_zero).  The remaining two are the SIZE CAP
   [di_size dn' <= MAXFILE*BSIZE] (the [< 2^31] clause above is weaker) and
   [InodeInv.inode_sized data'].  fileread re-parks the IDENTICAL record and
   so never needed them; dirlink forwards rather than re-parks; filewrite is
   the first caller to re-park a CHANGED payload, which is why they appear
   only now.

   BOTH ARE STATED AS PRESERVATIONS, not as facts, and they have to be.
   Neither is provable outright:

   - the size cap, because [wi_dinode] installs [max(di_size dn, off+tot)]
     and the guard at +0x2a bounds only [off+n]; nothing in writei's
     premises bounds the caller's OWN [di_size dn] below MAXFILE*BSIZE (the
     premise is [< 2^31]), and on the -1 arm [dn' = dn] outright;
   - [inode_sized], because writei touches only the blocks its range
     straddles.  Every other index keeps [data i], whose length no resource
     in the cone constrains ([FsBlocks.fs_chalf] is a bare ghost_map half --
     InodeInv.v 503-506), and again on the -1 arm [data' = data].

   So both would have to be PREMISES, at which point they would ripple into
   SpecDirlink and every caller below it.  Stating the implication instead
   costs a re-parking caller nothing -- it holds both antecedents already,
   out of the very [inode_ok] it is going to rebuild -- and costs a caller
   that does not re-park (dirlink) exactly nothing at all: no premise moves,
   and the two clauses are dropped at its boundary.

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
   ([i_inum], [inode_meta], the [sb + 24] field, and -- since C2 -- the
   inode REGION's [ireg_inv] plus this inum's own [dinode_at] fragment
   instead of the block's [fs_chalf] half) on top of everything bmap needs.

   THE REGION'S RECORD IS NOT [dn].  [dn0] is what the region currently
   holds for this inum, which is STALE by construction (that is what the
   flush is for), and the postcondition names the record the call leaves
   there: [dn'] on the writing arm, [dn0] untouched on the -1 arm, which
   returns before iupdate is reached.  That existential replaces the old
   [ds'] one exactly.

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

   The iteration count is bounded by the number of blocks the range
   straddles ([wi_blocks]), because every iteration but the last fills its
   block to the boundary.  So the premise is the lower bound
   [wi_cost_bmonly off n <= ncount] and the postcondition is spend-at-most
   -- writei BRANCHES, and [log_op] has no mover outside the log spinlock,
   so a path that skips a spend cannot burn the surplus (SpecBmap.v's
   header).

   THE COST IS TWO PER BLOCK, NOT SIX, AND THAT IS WHAT MAKES filewrite
   PROVABLE.  The naive per-iteration sum -- bmap's worst case 5 plus
   writei's own log_write -- gives [wi_cost], and [wi_cost 1023 FW_MAX = 25]
   against a MAXOPBLOCKS of 10: filewrite's own four-block chunk would be
   unpayable and the KERNEL would be at fault rather than the proof.  It is
   not: the 6 double-counts, because within ONE transaction the same block
   is logged once however many times it is written.  Under link 2's
   set-form bmap contract the honest figure is [wi_cost_bmonly = 2B + 2],
   which at B = 4 is EXACTLY 10.  See [WriteiBudget] sections 9-10 and
   fs-icache.md section 18.

   WHICH ABSORPTIONS ARE MODELLED, and which are merely true.  Two: the
   bitmap block (there is exactly one per file system, so every balloc of a
   transaction logs the SAME block and only the first pays --
   [WriteiBudget.one_bitmap_block]), and a freshly allocated data block
   (balloc's [bzero] already logged it, so writei's own [log_write] of it is
   free).  A third -- the indirect block, across ITERATIONS -- is true and
   deliberately NOT modelled: it would buy the three slots between 10 and
   [WriteiBudget.wi_cost_tight = 7], and the machinery is proven and parked
   in [WriteiBudget]'s [LogAmort] section for the day a kernel change needs
   them.  Today's accounting fits with ZERO slack
   ([WriteiBudget.wi_cost_bmonly_no_slack]).

   ==== ...AND THE CONTRACT COMES IN TWO FORMS ==========================

   [wp_writei_sconf] is the COUNTED form above.  [wp_writei_gen] below is
   the SET form of fs-icache.md section 18 clause 1: it takes
   [LogInv.log_opS γ ncount Sb] and returns [log_opS γ n' Sb'] with
   [Sb ⊆ Sb'], so a caller running writei inside a transaction it also uses
   for other calls can thread ONE set.  The counted form is DERIVED from it
   -- [log_op] IS [∃ Sb, log_opS] -- at whatever set the existential was
   hiding, exactly wp_bmap_sconf's pattern, so no existing caller moves.

   writei TAKES NO CREDIT PARAMETER, unlike bmap and log_write.  It does not
   need one: its loop invariant carries the unpaid bitmap block as one unit
   of held-back POTENTIAL ([WriteiBudget.bm_pot]) rather than as a case
   split, and [WriteiBudget.wi_inv_enter] establishes the invariant at ANY
   entry set.  A caller that has already logged the bitmap simply gets a
   call that spends one less than its budget allowed.

   NO CEILING ON [Sb' ∖ Sb] IS OFFERED.  Section 18 clause 1 asks for one
   and bmap supplies it, but S3l's finding is that no obligation anywhere
   consumes a ceiling -- callers only ever claim MEMBERSHIPS -- and here it
   would have to name every data block the loop touched, i.e. a set-valued
   function of the loop-carried [blkmap].  That is exactly the shape S3l
   recommended against letting the decorative clause force.  Budget
   soundness is carried by the counter alone: [log_spend_step] already
   refuses to grow [Sb] without spending a unit.

   ==== ====================================================================

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
Require Import RiscvExtras.
Require Import CalleeSaved KernelText.
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
Require Import DinodeEnc.
Require Import InodeInv.
Require Import InodeRegion.
Require Import BitmapInv.
Require Import SpecBmap.
Require Import KernelDataInv.
Require Import SpecPrintk.
Require Import UserPtTree.
Require Import KvmSpec.
Require Import ProcPtOwn.
Require Import ProcInv.
Require Import FileInvDefs.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import ProcAvail.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Import Defs.

Local Open Scope Z_scope.

(* writei's own frame is 112 bytes (14 slots).  Its deepest callee is now
   bmap at 64 (itself dominated by balloc's out-of-blocks printk, 58, which
   is itself dominated by printk's own real stack need, printk_stack = 48;
   see SpecReadi.v's header); either_copyin wants 56 (unaffected -- it does
   not reach printk), iupdate 44, bread 40, brelse 26, log_write 18. *)
Notation K_writei := (88%nat) (only parsing).
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

(* six units per iteration (bmap 5 + log_write 1), plus iupdate's one.
   THE LOOSE BOUND, kept because [WriteiBudget]'s sections 1-9 are stated
   against it: it is what the budget ruling had to REPLACE, since
   [wi_cost 1023 FW_MAX = 25] busts MAXOPBLOCKS. *)
Definition wi_cost (off n : nat) : nat := (6 * wi_blocks off n + 1)%nat.

(* THE REAL COST, under the one-credit set-form bmap contract of
   fs-icache.md section 18 (link 2).  TWO units per straddled block -- the
   block's own [log_write], plus the one indirect write that did not absorb
   -- plus one for the bitmap block (paid at most once in the whole call,
   whichever iteration first allocates) and one for the trailing iupdate.

     wi_cost_bmonly 1023 FW_MAX = 10 = MAXOPBLOCKS, EXACTLY.

   [WriteiBudget] section 9 is the derivation, section 10 is this number as
   a loop invariant, and [WriteiBudget.wi_cost_bmonly_fits] /
   [wi_cost_bmonly_value] / [wi_cost_bmonly_no_slack] are the arithmetic.
   It lives HERE rather than in [WriteiBudget] only because of the import
   direction: [WriteiBudget] requires this file.

   NON-MONOTONICITY, AND WHY EVERY CONSUMER IS RE-CHECKED.  This is NOT
   uniformly below [wi_cost] -- [wi_cost_bmonly 0 0 = 2] against
   [wi_cost 0 0 = 1], because the bitmap unit is held back even on the
   empty range, while the loose bound charged only iupdate's.  So swapping
   it in can make a caller's premise HARDER, and the empty-range arm of
   every call site is audited explicitly rather than assumed to follow.
   ([WriteiBudget.wi_cost_tight_incomparable] records the same trap for the
   two-credit cost.) *)
Definition wi_cost_bmonly (off n : nat) : nat := (2 * wi_blocks off n + 2)%nat.

(* ===================================================================== *)
(*  THE SIXTEEN-BYTE SEAM -- the credit-aware spend for a single-block    *)
(*  write (GR-3 stage-3 ruling, projects/fs-sysfile.md §GR-3).            *)
(*                                                                        *)
(*  dirlink's only writei shape is a 16-aligned sixteen-byte window       *)
(*  (1024 = 64 * 16, so a record never straddles), and create's ledger    *)
(*  needs that call priced at its ABSORPTIONS, not at the coarse bound:   *)
(*  the bitmap-only amortization provably cannot close cr_budget_mkdir    *)
(*  (CreateBudget.wi16_bmonly_amort_insufficient).  The figure below is   *)
(*  bmap's arm-wise cost, plus writei's own log_write of the target       *)
(*  block -- free when balloc just bzero'ed it ([al]) or when the caller  *)
(*  had already logged it ([crd]) -- plus the trailing iupdate ([cru]).   *)
(*                                                                        *)
(*    [crb] : bmapstart ∈ Sb            (SpecBmap's [cr], verbatim)       *)
(*    [crd] : the target block ∈ Sb                                       *)
(*    [cru] : IBLOCK inum inodestart ∈ Sb                                 *)
(*    [al]  : bmap allocated ([bmap_alloced bm bm' fbn] -- DERIVED, both  *)
(*            maps are already post variables, so no new existential)     *)
(*    [ind] : the window is on the indirect path ([bmap_ind fbn])         *)
Definition wi16_spend (crb crd cru al ind : bool) : nat :=
  (bmap_cost crb al ind + (if (al || crd)%bool then 0 else 1)
   + (if cru then 0 else 1))%nat.

(* THE COARSE ALLOWANCE DOMINATES THE CREDIT-AWARE FIGURE at every value
   of the five booleans -- [wi_cost_bmonly off 16] is four whenever the
   window sits in one block, and four is exactly the worst corner here (an
   allocating indirect window at an unpaid bitmap block, whose own
   [log_write] then absorbs).  So a caller that relays the coarse bound is
   not being LOOSE about the maximum; what it loses is the per-call
   VARIATION, which is the whole of what create's interior links need. *)
Lemma wi16_spend_le4 (crb crd cru al ind : bool) :
  (wi16_spend crb crd cru al ind <= 4)%nat.
Proof. destruct crb, crd, cru, al, ind; vm_compute; lia. Qed.

(* ...and what must be IN HAND on entry.  Credits do NOT lower this:
   log_write's contract takes [log_opS (S u)] on BOTH arms (a unit in hand
   even to absorb) and so does iupdate's.  bmap's own requirement is
   [SpecBmap.bmap_need]. *)
Definition wi16_need (crb ind : bool) : nat := (bmap_need crb ind + 2)%nat.

Lemma wi16_need_value_dir : wi16_need false false = 4%nat.
Proof. reflexivity. Qed.

(* For comparison with the LANDED loose bound: whenever the sixteen bytes
   sit inside one block, [wi_blocks off 16 = 1] and [wi_cost_bmonly off 16
   = 4] -- the same number [wi16_need false false] gives.  THE NEED WAS
   NEVER THE PROBLEM; the SPEND bound is. *)
Lemma wi16_need_matches_landed (off : nat) :
  wi_blocks off 16 = 1%nat ->
  wi16_need false false = wi_cost_bmonly off 16.
Proof.
  intros H. unfold wi16_need, bmap_need, wi_cost_bmonly.
  rewrite H. reflexivity.
Qed.

(* the disk block the single-block window lands on, as [log_write] names
   it in the ledger ([uint bno] -- SpecLogWrite's union element, verbatim,
   so the membership clause below is literal). *)
Definition wi_tgt_blk (bm : blkmap) (off : nat) : Z :=
  uint (blkmap_get bm (off `div` BSIZE)%nat : mword 32).

(* THE EXPOSED CLAUSE, as one named Prop so the contract grows by exactly
   one pure wand.  Guarded by the SUCCESS arm ([0 < tot] -- on the
   early-exit arm nothing is logged and the memberships are false) and by
   the single-block shape ([wi_blocks off n = 1] -- the multi-block loop
   invariant is deliberately NOT strengthened; the LogAmort third
   amortization stays parked and the coarse [wi_cost_bmonly] clause above
   stays).  The membership half is what lets a caller derive the NEXT
   call's credit booleans: [Sb ⊆ Sb'] alone provably cannot
   (projects/fs-sysfile.md §GR-3, derivation 2). *)
Definition wi16_post (bmapstart : Z) (inum : mword 32) (inodestart : Z)
    (ncount n' off n tot : nat) (bm bm' : blkmap) (Sb Sb' : gset Z) : Prop :=
  (0 < tot)%nat -> wi_blocks off n = 1%nat ->
  let fbn := (off `div` BSIZE)%nat in
  let al := bmap_alloced bm bm' fbn in
  let ind := bmap_ind fbn in
  let crb := bool_decide (bmapstart ∈ Sb) in
  let crd := bool_decide (wi_tgt_blk bm' off ∈ Sb) in
  let cru := bool_decide (IBLOCK inum inodestart ∈ Sb) in
  ((ncount - wi16_spend crb crd cru al ind)%nat <= n')%nat
  /\ wi_tgt_blk bm' off ∈ Sb'
  /\ IBLOCK inum inodestart ∈ Sb'
  /\ (al = true -> bmapstart ∈ Sb').

(* ...AND THE SPEND HALF AGAIN, WITHOUT THE [0 < tot] GUARD.  The same
   expression bounds the spend at EVERY [tot], because each way out of the
   loop leaves the ledger at a SUB-figure of it:

     - the up-front [-1] return spends nothing at all ([n' = ncount]);
     - the bmap-out-of-blocks break never reached writei's own
       [log_write], so the data-block term is UNSPENT (and on that arm
       [bmap_alloced] can only be the INDIRECT allocation, which
       [bmap_cost] already prices);
     - the part-way [either_copyin] break runs [log_write(bp)] BEFORE it
       leaves (fs.c's "might have partially updated the block"), which is
       exactly what the data-block term pays for.

   Only the MEMBERSHIP trio of [wi16_post] genuinely needs [0 < tot]:
   nothing enters [Sb'] on the -1 route, so no membership is available
   there at all.  A caller that must price a FAILING single-block write --
   create's [fail:] entries, through dirlink's append -- has no other
   source for the credit-aware figure: the coarse [wi_cost_bmonly] clause
   is four, and the interior mkdir entries reach their dirlink with six in
   hand against an [iput_units] of three.  Neither [tot] nor [Sb'] appears
   below, which is what makes this clause the SAME fact on every arm. *)
Definition wi16_spend_any (bmapstart : Z) (inum : mword 32) (inodestart : Z)
    (ncount n' off n : nat) (bm bm' : blkmap) (Sb : gset Z) : Prop :=
  wi_blocks off n = 1%nat ->
  let fbn := (off `div` BSIZE)%nat in
  let al := bmap_alloced bm bm' fbn in
  let ind := bmap_ind fbn in
  let crb := bool_decide (bmapstart ∈ Sb) in
  let crd := bool_decide (wi_tgt_blk bm' off ∈ Sb) in
  let cru := bool_decide (IBLOCK inum inodestart ∈ Sb) in
  ((ncount - wi16_spend crb crd cru al ind)%nat <= n')%nat.

(* CHUNK ATOMICITY AT THE SINGLE-BLOCK CORNER.  A write whose whole range
   sits in one block is copied by ONE iteration ([m = min (n - tot,
   BSIZE - off mod BSIZE)] is the whole of [n]), so the loop either
   completes it or leaves [tot] at the zero it started from: every break
   arm exits WITHOUT advancing [tot], the part-way copy included (its
   bytes become the postcondition's disturbed region [dist], not part of
   [tot]).  Nothing else in this contract pins a granularity -- the arms
   below bound [tot] by [tot <= n] and by the returned [a0], and a caller
   that needs "16 or nothing" (dirlink's fixed-width dirent) cannot get it
   from either. *)
Definition wi16_atomic (off n tot : nat) : Prop :=
  wi_blocks off n = 1%nat -> tot = 0%nat \/ tot = n.

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

(* THE BUFFER CARRIES ITS OWN TIER [ktb] -- the kernel arm's destination is
   a FRAME local for one caller (dirlookup's [de]) and a KT0 page for the
   next (kexec's segment).  Same shape as SpecMemmove.v's note. *)
Definition wp_writei_sconf_body
    `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !irefslotG Σ, !pavG Σ, !fileG Σ, ICFG : icfg} `{GEN : GenId} `{CID : CpuId}
    
    (ktb : ktier) `{!KtierLe ktb KT1} (γs : list gname) (j : nat) (γl : gname)          (* the running process *)
    (γu : uart_names) (γd : disk_names) (γk : gname)  (* disk fabric + lock  *)
    (pd pav pu : mword 64)
    (bn : bio_names)
    (γ : log_names) (γfs : fs_names) (γi : gname)
    (γa : gname) (γf : gname)                         (* kalloc, file table  *)
    (cov : gset Z) (logstart : Z) (inodestart : Z) (nib : nat)
    (bmapstart : Z) (size : Z) (dev : mword 32)
    (γpr : gname)
    (ip : mword 64) (inum : mword 32)
    (bm : blkmap) (data : nat -> list (bv 8))
    (dn dn0 : dinode)
    (user : bool) (off n : nat) (src_bytes : nat -> bv 8)
    (V : pprivate) (ncount : nat)
    (pidv : mword 32) (dq dqd dqn dqs dqb dqbs : dfrac)
    (m : regfile) (K : nat) (eb : bool)
    (b : bool) (lks : gset string) :=
  let pcE : mword 64 := mword_of_int KernelSyms.writei in
  let pj := proc_addr j in
  let src := m !!! Regidx (mword_of_int 12 : mword 5) in
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5)) in
  (K_writei <= K)%nat ->
  (* ENOUGH BUDGET for the worst case: TWO units per straddled block, plus
     one for the bitmap block and one for iupdate.  See the header. *)
  (wi_cost_bmonly off n <= ncount)%nat ->
  (* the covered range's block-number bounds, and the log's own storage *)
  log_geom_ok cov logstart ->
  (* the inode's own block, exactly as iupdate takes it *)
  0 <= inodestart ->
  IBLOCK inum inodestart ∈ cov ->
  ~ (IBLOCK inum inodestart ∈ log_region_set logstart) ->
  (* the inum is one the inode REGION covers -- iupdate's premise, which
     replaced the block-half premise and its [diblk_wf ds] (design §11.3) *)
  bv_unsigned inum < 16 * Z.of_nat nib ->
  di_addrs dn = bm_cells bm ->
  (* THE INODE IS ALLOCATED (fs-icache §16.4).  iupdate's flush keeps this
     inum's fragment OUT of the region invariant, which the region's arm
     only permits for a nonzero type -- a type-0 flush is iput's free path
     and absorbs the fragment instead.  Every caller has it: a locked
     inode's [InodeLock.inode_ok] carries it, and dirlink's own
     [di_type dn = T_DIR] is stronger. *)
  bv_unsigned (di_type dn) <> 0 ->
  (* TYPE STABILITY (fs-icache.md §19.6 Part 1, fs-sysfile S5d).  The
     record writei flushes keeps [dn]'s type ([wi_dinode] moves size and
     addrs only), and [InodeRegion.ireg_write_au] now forbids a flush that
     RETYPES the region's record -- so what writei owes is that the stale
     [dn0] and the in-memory [dn] already agree on the type.  Every caller
     has it for free: it holds the two as the SAME record, out of
     [IcacheEscrow.ic_loaded]'s single [dinode_at] (filewrite passes
     [dnl dnl]).  Same premise, same reason, as SpecIupdate.v's. *)
  di_type_stable dn dn0 ->
  (* NLINK STABILITY (fs-icache.md §20.6, fs-sysfile S5f): the link
     ledger's twin of the premise above, travelling for the same reason --
     the record the REGION holds at the iupdate below is the stale [dn0].
     [InodeRegion.di_nlink_stable_refl] discharges it at any caller that
     holds the two as ONE record with a nonzero type. *)
  di_nlink_stable dn dn0 ->
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
  (* the bitmap's geometry, forwarded through bmap to balloc *)
  bitmap_geom_ok cov logstart bmapstart size ->
  (* balloc's out-of-blocks arm calls the GENERAL printk path; carried as a
     hypothesis, never a functor.  See SpecBalloc.v's header. *)
  printk_gen_contract (kt := KT1) γpr γu γd ->
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
  (* NO eb-GATED RESTRICTION HERE.  An earlier round of the sweep had to
     add [eb = false -> bm_covers bm (off + n)] -- "an interrupts-off
     caller must already own the whole range" -- because writei's loop
     allocates through [SpecBmap.wp_bmap_gen_body], which in turn needed
     balloc's CREDITED contract, and that one was still pinned at
     [eb = true].  Both have since been generalized, so the allocating
     path is reachable at either index and the restriction is gone.  See
     claude-notes/completed/eb-generic-sweep.md ("Round 13"). *)
  (* writei's loop reaches bread/log_write/brelse, whose bound is at "log"
     (3); nothing writei's cone touches ranks lower.  One premise covers the
     whole cone (mirrors SpecBfree.v's). *)
  locks_below lks "log" ->
  sie_cap_gpr KT1 m K b pj -∗
  cpu_own 0 eb pj b lks -∗
  (* THE TRAP-CSR COMPLEMENT, NOT THE BARE PAIR.  writei holds no lock of
     its own -- every push_off/pop_off pair that can mint or spend an
     [arm_pay 0 eb _] lives inside bmap/bread/iupdate (and, through them,
     acquiresleep / virtio_disk_rw), so writei is a PURE PASS-THROUGH: it
     neither mints nor spends this complement itself, only threads it down
     to each bmap/bread/iupdate call and takes it back from their
     continuations.  At [eb = true] the complement is [emp], so no existing
     caller gains an obligation; at [eb = false] it is the honest pair, held
     by the caller because the TRAP handed it over.  See
     claude-notes/completed/sched-hart-generic.md and
     claude-notes/completed/eb-generic-sweep.md. *)
  trap_csrs_ext KT1 eb -∗
  cpu_claim_ext eb pj -∗
  kernel_text -∗ pc_is pcE -∗
  (* the two PERSISTENT printk credentials, forwarded through bmap to balloc *)
  kernel_data -∗
  printk_env γpr γu γd -∗
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
  (* sb.size and sb.bmapstart, and THE BITMAP: bmap's interior balloc needs
     all three, and writei calls bmap once per straddled block *)
  sb_size ↦₄{dqbs} (mword_of_int size : mword 32) -∗
  sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
  bitmap_inv γfs bmapstart cov logstart size -∗
  (* THE INODE REGION, and this inum's (stale) on-disk record: iupdate's
     resources, threaded through (design §11.3/§12) *)
  ireg_inv γi γfs inodestart nib -∗
  dinode_at γi inum dn0 -∗
  (* THE SOURCE, AND THE PID CELL THAT RIDES WITH IT.  On the user arm a
     virtual address into the running process's own space; on the kernel arm
     the caller's own byte buffer, returned unchanged.

     THE PID FRACTION IS THE KERNEL ARM'S, AND ONLY THE KERNEL ARM'S.
     bread's acquiresleep records the caller's pid, so writei needs a share
     of [p->pid] either way -- but on the USER arm it borrows that share out
     of [proc_priv] itself ([ProcInv.proc_priv_pid]) rather than asking for
     it.  It has to: that accessor is a BORROW, it consumes the block and
     returns a wand, so no caller can hold [proc_priv] and the fraction at
     the same time.  The cell is fully accounted for --
     [ProcInv.proc_priv_core] holds one half and [SchedCtx.proc_pub] the
     other, behind [p->lock] -- so there is no third fragment anywhere for a
     caller to reach.  A caller therefore supplies ONE OR THE OTHER and
     never both.

     (This contract asked for both at once until S3p, with a comment
     claiming [proc_priv_pid] supplied the quarter alongside the block.  It
     does not, and the user arm was UNCALLABLE; filewrite, its first
     user-arm caller, is what forced the repair.  [SpecReadi.v]:244-267 is
     the same fix, made one stage earlier by fileread.) *)
  (if user
   then proc_priv_core pj pidv V
   else ([∗ list] i ∈ seq 0 n, pa_add src i ↦ₘ[ktb] src_bytes i) ∗
        proc_priv_bare pj pidv V) -∗
  (* the running-thread bundle *)
  procs_inv γs -∗
  (* the disk fabric *)
  dev_inv γu γd -∗
  disk_geom γd pd pav pu -∗
  is_lock γk d_lock "virtio_disk"%string (disk_res γd pd pav pu) -∗
  (* THREE slot units -- bmap's peak; writei's own bread holds one across
     either_copyin and log_write, and log_write wants one of its own *)
  bslots 3 -∗
  (* THE RESERVATION, spend-at-most *)
  log_op γ ncount -∗
  (* THE CROSSING IS THE LITERAL [true], NOT [b].  This function can SLEEP,
     and a park moves the hart with interrupts off, so the crossing has
     nothing to do with SIE.  Spelled [b] the two coincide at the only
     instance the [eb = true] premise admits, which is why this went
     unnoticed; once [eb = false] is reachable the [b] form would promise
     the caller it comes back on the hart it called from. *)
  wp_next true pj (fun (CID : CpuId) =>
  ∀ (mf : regfile) (tot : nat) (bm' : blkmap) (data' : nat -> list (bv 8))
    (dn' dn0' : dinode) (n' : nat)
    (wrote : nat -> bv 8) (dist : nat) (dstb : nat -> bv 8) (P' : uptd),
      ⌜callee_saved m mf⌝ -∗
      (* THE ALLOCATOR NEVER UN-MARKS: [used] only grows, across every bmap
         the loop performs. *)
      ⌜blkmap_wf cov logstart bm'⌝ -∗
      ⌜blk_holes_zero bm' data'⌝ -∗
      ⌜di_addrs dn' = bm_cells bm'⌝ -∗
      ⌜bv_unsigned (di_size dn') < 2 ^ 31⌝ -∗
      (* COVERAGE IS PRESERVED, AT THE NEW SIZE.  See the header. *)
      ⌜bm_covers bm' (bv_unsigned (di_size dn'))⌝ -∗
      (* THE LAST TWO [InodeLock.inode_ok] CONJUNCTS, AS PRESERVATIONS.
         See the header's "...AND THE TWO CONJUNCTS A RE-PARKER NEEDS". *)
      ⌜bv_unsigned (di_size dn) <= Z.of_nat MAXFILE * Z.of_nat BSIZE ->
       bv_unsigned (di_size dn') <= Z.of_nat MAXFILE * Z.of_nat BSIZE⌝ -∗
      ⌜inode_sized data -> inode_sized data'⌝ -∗
      (* THE DISTURBED REGION: at most one block, immediately after the
         written range, and EMPTY unless a copy failed part-way.  See the
         header. *)
      ⌜(dist <= BSIZE)%nat⌝ -∗
      ⌜(tot = n)%nat -> dist = 0%nat⌝ -∗
      (* ...and EMPTY OUTRIGHT on the KERNEL arm: either_copyin cannot fail
         there, so the committed partial chunk never exists.  §15.1(i). *)
      ⌜user = false -> dist = 0%nat⌝ -∗
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
        /\ bm' = bm /\ data' = data /\ dn' = dn /\ dn0' = dn0
        /\ n' = ncount)
       \/ (mf !!! Regidx (mword_of_int 10 : mword 5)
             = (mword_of_int (Z.of_nat tot) : mword 64)
           /\ (tot <= n)%nat
           /\ dn' = wi_dinode dn bm' off tot
           /\ dn0' = dn')⌝ -∗
      (* at most [wi_cost_bmonly off n] units gone, and none gained *)
      ⌜((ncount - wi_cost_bmonly off n)%nat <= n')%nat /\ (n' <= ncount)%nat⌝ -∗
      ⌜uptd_ext (pv_upt V) P'⌝ -∗
      sie_cap_gpr KT1 mf K b pj -∗
      cpu_own 0 eb pj b lks -∗
      trap_csrs_ext KT1 eb -∗
      cpu_claim_ext eb pj -∗
      pc_is ret_tgt -∗
      i_dev ip ↦₄{dqd} dev -∗
      i_inum ip ↦₄{dqn} inum -∗
      inode_meta ip dn' -∗
      inode_map γfs ip bm' -∗
      inode_blocks γfs bm' data' -∗
      sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
      sb_size ↦₄{dqbs} (mword_of_int size : mword 32) -∗
      sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
      dinode_at γi inum dn0' -∗
      (* the source goes back the way it came -- with the kernel arm's
         buffer, or inside the user arm's block *)
      (if user
       then proc_priv_core pj pidv (upd_upt V P')
       else ([∗ list] i ∈ seq 0 n, pa_add src i ↦ₘ[ktb] src_bytes i) ∗
            proc_priv_bare pj pidv V) -∗
      bslots 3 -∗
      log_op γ n' -∗
      WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

(* ===================================================================== *)
(*  THE SET-FORM CONTRACT (fs-icache.md section 18 clause 1)              *)
(*  Everything except the ledger is VERBATIM [wp_writei_sconf_body]:      *)
(*  same premises, same resources, same twelve postcondition clauses.     *)
(*  Only [log_op] becomes [log_opS], and [Sb ⊆ Sb'] is added.             *)
(*  [wp_writei_sconf] is this contract with the set forgotten, derived    *)
(*  at the [log_op] existential's own witness -- so no caller moves.      *)
(* ===================================================================== *)
(* THE BUFFER CARRIES ITS OWN TIER [ktb] -- the kernel arm's destination is
   a FRAME local for one caller (dirlookup's [de]) and a KT0 page for the
   next (kexec's segment).  Same shape as SpecMemmove.v's note. *)
Definition wp_writei_gen_body
    `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !irefslotG Σ, !pavG Σ, !fileG Σ, ICFG : icfg} `{GEN : GenId} `{CID : CpuId}
    
    (ktb : ktier) `{!KtierLe ktb KT1} (γs : list gname) (j : nat) (γl : gname)          (* the running process *)
    (γu : uart_names) (γd : disk_names) (γk : gname)  (* disk fabric + lock  *)
    (pd pav pu : mword 64)
    (bn : bio_names)
    (γ : log_names) (γfs : fs_names) (γi : gname)
    (γa : gname) (γf : gname)                         (* kalloc, file table  *)
    (cov : gset Z) (logstart : Z) (inodestart : Z) (nib : nat)
    (bmapstart : Z) (size : Z) (dev : mword 32)
    (γpr : gname)
    (ip : mword 64) (inum : mword 32)
    (bm : blkmap) (data : nat -> list (bv 8))
    (dn dn0 : dinode)
    (user : bool) (off n : nat) (src_bytes : nat -> bv 8)
    (V : pprivate) (ncount : nat) (Sb : gset Z)
    (pidv : mword 32) (dq dqd dqn dqs dqb dqbs : dfrac)
    (m : regfile) (K : nat) (eb : bool)
    (b : bool) (lks : gset string) :=
  let pcE : mword 64 := mword_of_int KernelSyms.writei in
  let pj := proc_addr j in
  let src := m !!! Regidx (mword_of_int 12 : mword 5) in
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5)) in
  (K_writei <= K)%nat ->
  (* ENOUGH BUDGET for the worst case: TWO units per straddled block, plus
     one for the bitmap block and one for iupdate.  See the header. *)
  (wi_cost_bmonly off n <= ncount)%nat ->
  (* the covered range's block-number bounds, and the log's own storage *)
  log_geom_ok cov logstart ->
  (* the inode's own block, exactly as iupdate takes it *)
  0 <= inodestart ->
  IBLOCK inum inodestart ∈ cov ->
  ~ (IBLOCK inum inodestart ∈ log_region_set logstart) ->
  (* the inum is one the inode REGION covers -- iupdate's premise, which
     replaced the block-half premise and its [diblk_wf ds] (design §11.3) *)
  bv_unsigned inum < 16 * Z.of_nat nib ->
  di_addrs dn = bm_cells bm ->
  (* THE INODE IS ALLOCATED (fs-icache §16.4).  iupdate's flush keeps this
     inum's fragment OUT of the region invariant, which the region's arm
     only permits for a nonzero type -- a type-0 flush is iput's free path
     and absorbs the fragment instead.  Every caller has it: a locked
     inode's [InodeLock.inode_ok] carries it, and dirlink's own
     [di_type dn = T_DIR] is stronger. *)
  bv_unsigned (di_type dn) <> 0 ->
  (* TYPE STABILITY (fs-icache.md §19.6 Part 1, fs-sysfile S5d).  The
     record writei flushes keeps [dn]'s type ([wi_dinode] moves size and
     addrs only), and [InodeRegion.ireg_write_au] now forbids a flush that
     RETYPES the region's record -- so what writei owes is that the stale
     [dn0] and the in-memory [dn] already agree on the type.  Every caller
     has it for free: it holds the two as the SAME record, out of
     [IcacheEscrow.ic_loaded]'s single [dinode_at] (filewrite passes
     [dnl dnl]).  Same premise, same reason, as SpecIupdate.v's. *)
  di_type_stable dn dn0 ->
  (* NLINK STABILITY (fs-icache.md §20.6, fs-sysfile S5f): the link
     ledger's twin of the premise above, travelling for the same reason --
     the record the REGION holds at the iupdate below is the stale [dn0].
     [InodeRegion.di_nlink_stable_refl] discharges it at any caller that
     holds the two as ONE record with a nonzero type. *)
  di_nlink_stable dn dn0 ->
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
  (* the bitmap's geometry, forwarded through bmap to balloc *)
  bitmap_geom_ok cov logstart bmapstart size ->
  (* balloc's out-of-blocks arm calls the GENERAL printk path; carried as a
     hypothesis, never a functor.  See SpecBalloc.v's header. *)
  printk_gen_contract (kt := KT1) γpr γu γd ->
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
  (* NO eb-GATED RESTRICTION HERE -- see [wp_writei_sconf_body] above. *)
  (* writei's loop reaches bread/log_write/brelse, whose bound is at "log"
     (3); nothing writei's cone touches ranks lower.  One premise covers the
     whole cone (mirrors SpecBfree.v's). *)
  locks_below lks "log" ->
  sie_cap_gpr KT1 m K b pj -∗
  cpu_own 0 eb pj b lks -∗
  (* THE TRAP-CSR COMPLEMENT, NOT THE BARE PAIR.  Same pure-pass-through
     shape as [wp_writei_sconf_body] above -- required so that
     [wp_writei_sconf] (which must reach [eb = false]) can continue to be
     DERIVED from this SET-FORM core: writei's own loop must present the
     bitmap-block credit to bmap across several iterations, which only the
     SET form ([bmap]'s [cr]/[Sb]) can express, so the derivation has to
     reach through here at whatever [eb] the counted caller was given.  See
     claude-notes/completed/eb-generic-sweep.md. *)
  trap_csrs_ext KT1 eb -∗
  cpu_claim_ext eb pj -∗
  kernel_text -∗ pc_is pcE -∗
  (* the two PERSISTENT printk credentials, forwarded through bmap to balloc *)
  kernel_data -∗
  printk_env γpr γu γd -∗
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
  (* sb.size and sb.bmapstart, and THE BITMAP: bmap's interior balloc needs
     all three, and writei calls bmap once per straddled block *)
  sb_size ↦₄{dqbs} (mword_of_int size : mword 32) -∗
  sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
  bitmap_inv γfs bmapstart cov logstart size -∗
  (* THE INODE REGION, and this inum's (stale) on-disk record: iupdate's
     resources, threaded through (design §11.3/§12) *)
  ireg_inv γi γfs inodestart nib -∗
  dinode_at γi inum dn0 -∗
  (* THE SOURCE, AND THE PID CELL THAT RIDES WITH IT.  On the user arm a
     virtual address into the running process's own space; on the kernel arm
     the caller's own byte buffer, returned unchanged.

     THE PID FRACTION IS THE KERNEL ARM'S, AND ONLY THE KERNEL ARM'S.
     bread's acquiresleep records the caller's pid, so writei needs a share
     of [p->pid] either way -- but on the USER arm it borrows that share out
     of [proc_priv] itself ([ProcInv.proc_priv_pid]) rather than asking for
     it.  It has to: that accessor is a BORROW, it consumes the block and
     returns a wand, so no caller can hold [proc_priv] and the fraction at
     the same time.  The cell is fully accounted for --
     [ProcInv.proc_priv_core] holds one half and [SchedCtx.proc_pub] the
     other, behind [p->lock] -- so there is no third fragment anywhere for a
     caller to reach.  A caller therefore supplies ONE OR THE OTHER and
     never both.

     (This contract asked for both at once until S3p, with a comment
     claiming [proc_priv_pid] supplied the quarter alongside the block.  It
     does not, and the user arm was UNCALLABLE; filewrite, its first
     user-arm caller, is what forced the repair.  [SpecReadi.v]:244-267 is
     the same fix, made one stage earlier by fileread.) *)
  (if user
   then proc_priv_core pj pidv V
   else ([∗ list] i ∈ seq 0 n, pa_add src i ↦ₘ[ktb] src_bytes i) ∗
        proc_priv_bare pj pidv V) -∗
  (* the running-thread bundle *)
  procs_inv γs -∗
  (* the disk fabric *)
  dev_inv γu γd -∗
  disk_geom γd pd pav pu -∗
  is_lock γk d_lock "virtio_disk"%string (disk_res γd pd pav pu) -∗
  (* THREE slot units -- bmap's peak; writei's own bread holds one across
     either_copyin and log_write, and log_write wants one of its own *)
  bslots 3 -∗
  (* THE RESERVATION, spend-at-most *)
  (* THE RESERVATION, SET FORM: the op's logged set rides beside the
     counter.  No credit parameter -- see the header. *)
  log_opS γ ncount Sb -∗
  (* THE CROSSING IS THE LITERAL [true], NOT [b] -- writei's bread/bmap/
     iupdate park, and the counted form above already says [true]. *)
  wp_next true pj (fun (CID : CpuId) =>
  ∀ (mf : regfile) (tot : nat) (bm' : blkmap) (data' : nat -> list (bv 8))
    (dn' dn0' : dinode) (n' : nat)
    (wrote : nat -> bv 8) (dist : nat) (dstb : nat -> bv 8) (P' : uptd)
    (Sb' : gset Z),
      ⌜callee_saved m mf⌝ -∗
      (* THE ALLOCATOR NEVER UN-MARKS: [used] only grows, across every bmap
         the loop performs. *)
      ⌜blkmap_wf cov logstart bm'⌝ -∗
      ⌜blk_holes_zero bm' data'⌝ -∗
      ⌜di_addrs dn' = bm_cells bm'⌝ -∗
      ⌜bv_unsigned (di_size dn') < 2 ^ 31⌝ -∗
      (* COVERAGE IS PRESERVED, AT THE NEW SIZE.  See the header. *)
      ⌜bm_covers bm' (bv_unsigned (di_size dn'))⌝ -∗
      (* THE LAST TWO [InodeLock.inode_ok] CONJUNCTS, AS PRESERVATIONS.
         See the header's "...AND THE TWO CONJUNCTS A RE-PARKER NEEDS". *)
      ⌜bv_unsigned (di_size dn) <= Z.of_nat MAXFILE * Z.of_nat BSIZE ->
       bv_unsigned (di_size dn') <= Z.of_nat MAXFILE * Z.of_nat BSIZE⌝ -∗
      ⌜inode_sized data -> inode_sized data'⌝ -∗
      (* THE DISTURBED REGION: at most one block, immediately after the
         written range, and EMPTY unless a copy failed part-way.  See the
         header. *)
      ⌜(dist <= BSIZE)%nat⌝ -∗
      ⌜(tot = n)%nat -> dist = 0%nat⌝ -∗
      (* ...and EMPTY OUTRIGHT on the KERNEL arm: either_copyin cannot fail
         there, so the committed partial chunk never exists.  §15.1(i). *)
      ⌜user = false -> dist = 0%nat⌝ -∗
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
        /\ bm' = bm /\ data' = data /\ dn' = dn /\ dn0' = dn0
        /\ n' = ncount)
       \/ (mf !!! Regidx (mword_of_int 10 : mword 5)
             = (mword_of_int (Z.of_nat tot) : mword 64)
           /\ (tot <= n)%nat
           /\ dn' = wi_dinode dn bm' off tot
           /\ dn0' = dn')⌝ -∗
      (* at most [wi_cost_bmonly off n] units gone, and none gained *)
      ⌜((ncount - wi_cost_bmonly off n)%nat <= n')%nat /\ (n' <= ncount)%nat⌝ -∗
      (* THE SET ONLY GROWS.  No ceiling -- see the header. *)
      ⌜Sb ⊆ Sb'⌝ -∗
      (* ...and on a single-block success, the spend is the credit-aware
         [wi16_spend] and the three logged blocks are IN the returned set.
         ADDITIVE -- see [wi16_post]'s header. *)
      ⌜wi16_post bmapstart inum inodestart ncount n' off n tot bm bm' Sb Sb'⌝ -∗
      (* ...the SAME spend bound with no success guard on it, and the
         chunk-granularity fact that goes with it.  ADDITIVE -- see
         [wi16_spend_any] / [wi16_atomic]. *)
      ⌜wi16_spend_any bmapstart inum inodestart ncount n' off n bm bm' Sb⌝ -∗
      ⌜wi16_atomic off n tot⌝ -∗
      ⌜uptd_ext (pv_upt V) P'⌝ -∗
      sie_cap_gpr KT1 mf K b pj -∗
      cpu_own 0 eb pj b lks -∗
      trap_csrs_ext KT1 eb -∗
      cpu_claim_ext eb pj -∗
      pc_is ret_tgt -∗
      i_dev ip ↦₄{dqd} dev -∗
      i_inum ip ↦₄{dqn} inum -∗
      inode_meta ip dn' -∗
      inode_map γfs ip bm' -∗
      inode_blocks γfs bm' data' -∗
      sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
      sb_size ↦₄{dqbs} (mword_of_int size : mword 32) -∗
      sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
      dinode_at γi inum dn0' -∗
      (* the source goes back the way it came -- with the kernel arm's
         buffer, or inside the user arm's block *)
      (if user
       then proc_priv_core pj pidv (upd_upt V P')
       else ([∗ list] i ∈ seq 0 n, pa_add src i ↦ₘ[ktb] src_bytes i) ∗
            proc_priv_bare pj pidv V) -∗
      bslots 3 -∗
      log_opS γ n' Sb' -∗
      WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

Module Type WRITEI.
  Parameter wp_writei_sconf :
    forall `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !irefslotG Σ, !pavG Σ, !fileG Σ, ICFG : icfg} `{GEN : GenId} `{CID : CpuId}

      (ktb : ktier) `{!KtierLe ktb KT1} (γs : list gname) (j : nat) (γl : gname)
      (γu : uart_names) (γd : disk_names) (γk : gname)
      (pd pav pu : mword 64)
      (bn : bio_names)
      (γ : log_names) (γfs : fs_names) (γi : gname)
      (γa : gname) (γf : gname)
      (cov : gset Z) (logstart : Z) (inodestart : Z) (nib : nat)
      (bmapstart : Z) (size : Z) (dev : mword 32)
      (γpr : gname)
      (ip : mword 64) (inum : mword 32)
      (bm : blkmap) (data : nat -> list (bv 8))
      (dn dn0 : dinode)
      (user : bool) (off n : nat) (src_bytes : nat -> bv 8)
      (V : pprivate) (ncount : nat)
      (pidv : mword 32) (dq dqd dqn dqs dqb dqbs : dfrac)
      (m : regfile) (K : nat) (eb : bool)
      (b : bool) (lks : gset string),
      wp_writei_sconf_body ktb γs j γl γu γd γk pd pav pu bn γ γfs γi γa γf
                           cov logstart inodestart nib bmapstart size dev γpr
                           ip inum bm data dn dn0
                           user off n src_bytes V ncount
                           pidv dq dqd dqn dqs dqb dqbs m K eb b lks.

  (* the SET-FORM contract; [wp_writei_sconf] above is its instance with the
     set forgotten, kept as its own parameter so that every existing caller
     is unchanged (wp_bmap_gen / wp_balloc_gen's pattern) *)
  Parameter wp_writei_gen :
    forall `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !irefslotG Σ, !pavG Σ, !fileG Σ, ICFG : icfg} `{GEN : GenId} `{CID : CpuId}

      (ktb : ktier) `{!KtierLe ktb KT1} (γs : list gname) (j : nat) (γl : gname)
      (γu : uart_names) (γd : disk_names) (γk : gname)
      (pd pav pu : mword 64)
      (bn : bio_names)
      (γ : log_names) (γfs : fs_names) (γi : gname)
      (γa : gname) (γf : gname)
      (cov : gset Z) (logstart : Z) (inodestart : Z) (nib : nat)
      (bmapstart : Z) (size : Z) (dev : mword 32)
      (γpr : gname)
      (ip : mword 64) (inum : mword 32)
      (bm : blkmap) (data : nat -> list (bv 8))
      (dn dn0 : dinode)
      (user : bool) (off n : nat) (src_bytes : nat -> bv 8)
      (V : pprivate) (ncount : nat) (Sb : gset Z)
      (pidv : mword 32) (dq dqd dqn dqs dqb dqbs : dfrac)
      (m : regfile) (K : nat) (eb : bool)
      (b : bool) (lks : gset string),
      wp_writei_gen_body ktb γs j γl γu γd γk pd pav pu bn γ γfs γi γa γf
                         cov logstart inodestart nib bmapstart size dev γpr
                         ip inum bm data dn dn0
                         user off n src_bytes V ncount Sb
                         pidv dq dqd dqn dqs dqb dqbs m K eb b lks.
End WRITEI.
