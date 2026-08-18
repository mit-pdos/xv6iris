(* SpecBmap.v -- the public interface of bmap, stated independently of its
   proof.  Requires only the definitional layer -- never a whole-function
   proof file -- so every function proof can be checked in parallel.

     static uint bmap(struct inode *ip, uint bn) {
       uint addr, *a;
       struct buf *bp;
       if(bn < NDIRECT){
         if((addr = ip->addrs[bn]) == 0){
           addr = balloc(ip->dev);
           if(addr == 0) return 0;
           ip->addrs[bn] = addr;
         }
         return addr;
       }
       bn -= NDIRECT;
       if(bn < NINDIRECT){
         if((addr = ip->addrs[NDIRECT]) == 0){
           addr = balloc(ip->dev);
           if(addr == 0) return 0;
           ip->addrs[NDIRECT] = addr;
         }
         bp = bread(ip->dev, addr);
         a = (uint * ) bp->data;
         if((addr = a[bn]) == 0){
           addr = balloc(ip->dev);
           if(addr){ a[bn] = addr; log_write(bp); }
         }
         brelse(bp);
         return addr;
       }
       panic("bmap: out of range");
     }

   THE CONTRACT (claude-notes/design/fs-inode.md, "bmap's contract").
   One existential map bm' and the returned block, in two arms:

   - a0 = 0 -- allocation failed, and [blkmap_get bm' bn = 0].  Note that
     bm' is NOT claimed equal to bm: the indirect-path failure can already
     have allocated and installed the INDIRECT block before failing on the
     data block, so "the map is unchanged" would simply be false there.
     What both arms do promise is that bm' agrees with bm at every file
     index except possibly bn.
   - a0 = r <> 0 -- [blkmap_get bm' bn = r].

   Both arms return [inode_map γfs ip bm'] and [blkmap_wf cov logstart bm'].
   The fresh data block is DEPOSITED, not returned: bmap takes the
   caller's [inode_blocks] bundle and gives it back with the freshly
   allocated block in it, so nothing here is asymmetric between the two
   arms (design doc, "Why the fresh block is deposited, not returned").
   The bundles are ALSO what carry the per-block exclusive [blk_own]
   tokens, and those are the only thing that can re-establish
   [blkmap_wf]'s injectivity when balloc's block is installed --
   [fsblock] is a half element, so two at one key are consistent.

   THE BUDGET IS SPEND-AT-MOST, not spend-exactly: [log_op γ n] in with
   (5 <= n), and [log_op γ n'] out with (n - 5 <= n' <= n).  bmap cannot
   promise to have spent five, because it has no way to BURN a surplus --
   [log_op] moves only through the ledger authority inside log.lock, which
   bmap never takes -- and on the direct-hit path it does no balloc and no
   log_write at all.  See the clause itself for why the premise is a lower
   bound on the caller's counter rather than a (5 + u) shape.

   THE PANIC ARM IS DEAD.  bmap's [panic("bmap: out of range")] at +0xb2
   is reached only when bn - NDIRECT >= NINDIRECT, which the premise
   (bn < MAXFILE) rules out -- the same way both of log_write's panics are
   dead.  The panic credentials are still threaded, because the interior
   acquire's own holding-check arm wants a panic contract regardless.

   THE s4 QUIRK.  gcc saves s4 only on the paths that reach bread
   ([c.sdsp s4,0(sp)] at +0x058 / +0x060 / +0x0b2) and restores it once at
   +0x088; the direct path jumps straight to the shared epilogue at +0x08a
   and never touches it.  So [callee_saved] is established per-arm rather
   than once at the epilogue -- the join at +0x08a is reached with s4
   either restored or never written.  That is a fact about bmap's PROOF;
   the contract below just says [callee_saved m mf].

   THE BITMAP RIDES THROUGH, because balloc's does.  bmap takes the two
   superblock cells and [BitmapInv.bitmap_res] and hands them back; the
   returned bitmap is at an EXISTENTIAL [used'] with [used ⊆ used'],
   because bmap may allocate twice (the indirect block and the data block)
   and a caller has no use for the exact set -- only for the fact that the
   allocator never un-marks a block.  Who owns the bitmap between calls is
   deliberately still open (claude-notes/design/fs-bitmap.md, "Who owns
   bitmap_res between calls"); it is passed in and returned updated, as
   [inode_map] is.

   [BMAP_NOALLOC] below is UNCHANGED by this: with all three allocation
   sites dead there is no balloc, hence no bitmap and no superblock cell.

   bmap SLEEPS (bread, and balloc), so it threads the full running-process
   bundle exactly as SpecBread.v does.  It enters and returns at noff 0. *)
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
Require Import InodeInv.
Require Import BitmapInv.
Require Import KernelDataInv.
Require Import SpecPrintk.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import ProcAvail.
Import Defs.

Local Open Scope Z_scope.

(* bmap's own frame is 48 bytes (6 slots) -- [c.addi16sp sp,-48] at +0x00
   (s4 rides in the same frame, at slot 0, on the indirect paths).  Its
   deepest callee is balloc (58, itself dominated by printk's out-of-blocks
   path); bread wants 40 and log_write 18. *)
Notation K_bmap := (74%nat) (only parsing).
(* ===================================================================== *)
(*  THE ARMS, AS THE CALLER READS THEM OFF THE BLOCK MAP                  *)
(*  (fs-icache.md section 18: "bmap: ONE credit (the bitmap), arm-wise    *)
(*  exact")                                                               *)
(* ===================================================================== *)

(* [wp_bmap_gen] below is the SET-FORM contract: it takes [LogInv.log_opS]
   rather than [log_op], so the caller can see WHICH blocks this call put
   into the transaction's logged set and absorb its own later writes of
   them.  The counted [wp_bmap_sconf] above is this contract with the set
   forgotten -- [log_op] IS [∃ Sb, log_opS], so the counted seal runs the
   credited proof at whatever set that existential was hiding, claiming no
   credit ([cr := false]).  [BMAP_NOALLOC] never had a budget at all and is
   untouched.

   THE ONE CREDIT IS THE BITMAP BLOCK.  There is exactly one
   ([WriteiBudget.one_bitmap_block]), so every balloc of a transaction
   log_writes the same block and only the first pays.  [cr] is the caller's
   claim that it has already paid for it, and the premise
   [cr = true -> bmapstart ∈ Sb] is what makes the claim honest.

   THE COST IS ARM-WISE, and the arm is a FUNCTION of the block map going
   in and coming out -- which is what makes it usable: a caller must be
   able to COMPUTE what a call cost it, and [bm']/[bm] are exactly what it
   already learns from the rest of the postcondition.  A per-call constant
   is not an option: charging the maximum on the direct-hit arm busts
   MAXOPBLOCKS for a four-block chunk of writei (the arm that allocates
   nothing must cost nothing), which is [WriteiBudget]'s whole section 9.

   THE SECOND CREDIT -- the indirect block, across ITERATIONS of a caller's
   loop -- is deliberately NOT taken.  [WriteiBudget.wi_cost_bmonly] is the
   accounting that follows (2B+2 = exactly 10 at B = 4, zero slack) and
   [wi_cost_tight] (B+3 = 7) is what the second credit would buy; the
   machinery for it is proven and parked in [WriteiBudget]. *)

(* the file index is on the indirect path *)
Definition bmap_ind (fbn : nat) : bool := bool_decide (NDIRECT <= fbn)%nat.

(* bmap allocated the INDIRECT block on this call *)
Definition bmap_ai (bm bm' : blkmap) : bool :=
  bool_decide (bv_unsigned (bm_ind bm) = 0 /\ bv_unsigned (bm_ind bm') <> 0).

(* bmap allocated the DATA block for [fbn] on this call *)
Definition bmap_ad (bm bm' : blkmap) (fbn : nat) : bool :=
  bool_decide (bv_unsigned (blkmap_get bm fbn) = 0
               /\ bv_unsigned (blkmap_get bm' fbn) <> 0).

(* ...either of them: the arm on which the bitmap block was log_written *)
Definition bmap_alloced (bm bm' : blkmap) (fbn : nat) : bool :=
  (bmap_ai bm bm' || bmap_ad bm bm' fbn)%bool.

(* WHAT AN ARM COSTS THE LEDGER.  Nothing at all when nothing was
   allocated.  Otherwise one unit for the bitmap block (two when the
   caller had not already paid for it), plus, on the indirect path, ONE
   more: either bmap's own [log_write] of the indirect block at +0xb0
   (when the indirect block was already there), or balloc's [bzero] of the
   indirect block it just allocated -- and never both, because in the
   second case the [log_write] absorbs against the [bzero], same call,
   same block.  That coincidence is why one number covers both. *)
Definition bmap_cost (cr al ind : bool) : nat :=
  (if al then (if cr then 1 else 2) + (if ind then 1 else 0) else 0)%nat.

(* ...and what must be IN HAND on entry.  balloc wants two units even when
   it absorbs (log_write's own "a unit in hand" survives the absorbing
   arm), and the indirect path can run balloc twice with a log_write after
   it, so the deepest requirement is balloc's two on top of what the
   indirect allocation itself already spent. *)
Definition bmap_need (cr ind : bool) : nat :=
  (if ind then (if cr then 3 else 4) else 2)%nat.

Lemma bmap_cost_le3 (cr al ind : bool) : (bmap_cost cr al ind <= 3)%nat.
Proof. destruct cr, al, ind; vm_compute; lia. Qed.

Lemma bmap_need_le4 (cr ind : bool) : (bmap_need cr ind <= 4)%nat.
Proof. destruct cr, ind; vm_compute; lia. Qed.

(* balloc's own two units are wanted on every allocating arm *)
Lemma bmap_need_ge2 (cr ind : bool) : (2 <= bmap_need cr ind)%nat.
Proof. destruct cr, ind; vm_compute; lia. Qed.

Lemma bmap_ind_lt (fbn : nat) : (fbn < NDIRECT)%nat -> bmap_ind fbn = false.
Proof. intros H. apply bool_decide_eq_false_2. lia. Qed.

Lemma bmap_ind_ge (fbn : nat) : (NDIRECT <= fbn)%nat -> bmap_ind fbn = true.
Proof. intros H. apply bool_decide_eq_true_2. exact H. Qed.

(* the two shapes the interior proof discharges the arm booleans with *)
Lemma bmap_alloced_none (bm bm' : blkmap) (fbn : nat) :
  bm_ind bm' = bm_ind bm ->
  blkmap_get bm' fbn = blkmap_get bm fbn ->
  bmap_alloced bm bm' fbn = false.
Proof.
  intros Hi Hd. unfold bmap_alloced, bmap_ai, bmap_ad. rewrite Hi Hd.
  case_bool_decide as H1; [exfalso; destruct H1 as [Ha Hb]; exact (Hb Ha)|].
  case_bool_decide as H2; [exfalso; destruct H2 as [Ha Hb]; exact (Hb Ha)|].
  reflexivity.
Qed.

Lemma bmap_ad_none (bm bm' : blkmap) (fbn : nat) :
  blkmap_get bm' fbn = blkmap_get bm fbn -> bmap_ad bm bm' fbn = false.
Proof.
  intros Hd. unfold bmap_ad. rewrite Hd.
  apply bool_decide_eq_false_2. intros [H1 H2]. exact (H2 H1).
Qed.

Lemma bmap_ad_true (bm bm' : blkmap) (fbn : nat) :
  bv_unsigned (blkmap_get bm fbn) = 0 ->
  bv_unsigned (blkmap_get bm' fbn) <> 0 ->
  bmap_ad bm bm' fbn = true.
Proof. intros H1 H2. apply bool_decide_eq_true_2. exact (conj H1 H2). Qed.

Lemma bmap_alloced_of_ad (bm bm' : blkmap) (fbn : nat) :
  bmap_ad bm bm' fbn = true -> bmap_alloced bm bm' fbn = true.
Proof. intros H. unfold bmap_alloced. rewrite H. apply orb_true_r. Qed.

Lemma bmap_alloced_of_ai (bm bm' : blkmap) (fbn : nat) :
  bmap_ai bm bm' = true -> bmap_alloced bm bm' fbn = true.
Proof. intros H. unfold bmap_alloced. rewrite H. reflexivity. Qed.

Lemma bmap_ai_true (bm bm' : blkmap) :
  bv_unsigned (bm_ind bm) = 0 ->
  bv_unsigned (bm_ind bm') <> 0 ->
  bmap_ai bm bm' = true.
Proof. intros H1 H2. apply bool_decide_eq_true_2. exact (conj H1 H2). Qed.

Definition wp_bmap_sconf_body
    `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !irefslotG Σ, !pavG Σ, !bioG Σ, !diskGhostG Σ,
      !uartGhostG Σ, !fsLogG Σ, !logG Σ}
    `{GEN : GenId} `{CID : CpuId}
    
    (γs : list gname) (j : nat) (γl : gname)          (* the running process *)
    (γu : uart_names) (γd : disk_names) (γk : gname)  (* disk fabric + lock  *)
    (pd pav pu : mword 64)
    (bn : bio_names)
    (γ : log_names) (γfs : fs_names)
    (cov : gset Z) (logstart : Z) (bmapstart : Z) (size : Z) (dev : mword 32)
    (used : gset Z) (γpr : gname)
    (ip : mword 64) (bm : blkmap) (data : nat -> list (bv 8)) (fbn : nat)
    (n : nat)
    (pidv : mword 32) (dq dqd dqb dqs : dfrac)
    (m : regfile) (K : nat) (eb : bool)
    (b : bool) (lks : gset string) :=
  let pcE : mword 64 := mword_of_int KernelSyms.bmap in
  let pj := proc_addr j in
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5)) in
  (* the uint bn argument, as the 32-bit word the ABI passes *)
  let bnw : mword 32 := mword_of_int (Z.of_nat fbn) in
  (K_bmap <= K)%nat ->
  (* enough budget for the worst case: balloc(indirect) 2 + balloc(data) 2
     + bmap's own log_write 1 *)
  (5 <= n)%nat ->
  (* the covered range's block-number bounds (bread's 2^31 arithmetic
     premise, and 0 is never a client block) and the fact that the log's
     own storage is covered *)
  log_geom_ok cov logstart ->
  (* the bitmap's geometry, forwarded verbatim to balloc *)
  bitmap_geom_ok cov logstart bmapstart size ->
  (* balloc's out-of-blocks arm calls the GENERAL printk path; its contract
     rides as a hypothesis, never a functor, so that neither balloc nor bmap
     inherits LinkPrintk's Axiom.  See SpecBalloc.v's header. *)
  printk_gen_contract (kt := KT1) γpr γu γd ->
  (* KILLS THE PANIC ARM *)
  (fbn < MAXFILE)%nat ->
  blkmap_wf cov logstart bm ->
  (j < NPROC)%nat ->
  γs !! j = Some γl ->
  (* a0 = ip; a1 = bn, sign-extended as the RV64 ABI passes a uint *)
  m !!! Regidx (mword_of_int 10 : mword 5) = ip ->
  m !!! Regidx (mword_of_int 11 : mword 5) = sign_extend' 64 bnw ->
  (* bmap ALLOCATES here, so its cone reaches balloc -> log_write ("log", 3);
     the bread/brelse floor ("bcache", 4) follows by [locks_below_mono]. *)
  locks_below lks "log" ->
  sie_cap_gpr KT1 m K b pj -∗
  cpu_own 0 eb pj b lks -∗
  (* THE TRAP-CSR COMPLEMENT, NOT THE BARE PAIR.  bmap holds no lock of its
     own -- every push_off/pop_off pair that can mint or spend an
     [arm_pay 0 eb _] lives inside bread/balloc (and, through them,
     acquiresleep / virtio_disk_rw), so bmap is a PURE PASS-THROUGH: it
     neither mints nor spends this complement itself, only threads it down
     to each bread/balloc call and takes it back from their continuations.
     At [eb = true] the complement is [emp], so no existing caller gains an
     obligation; at [eb = false] it is the honest pair, held by the caller
     because the TRAP handed it over.  See
     claude-notes/completed/sched-hart-generic.md and
     claude-notes/completed/eb-generic-sweep.md. *)
  trap_csrs_ext KT1 eb -∗
  cpu_claim_ext eb pj -∗
  kernel_text -∗ pc_is pcE -∗
  (* the two PERSISTENT printk credentials, forwarded to balloc *)
  kernel_data -∗
  printk_env γpr γu γd -∗
  panic_env -∗
  bio_ctx bn (fs_view γfs γd dev cov) -∗
  log_ctx γ bn γfs cov logstart dev -∗
  (* ip->dev, read (never written) on all four balloc/bread call paths --
     a FRACTION, so the caller keeps its own copy *)
  i_dev ip ↦₄{dqd} dev -∗
  (* THE BLOCK MAP, and THE FILE'S DATA BLOCKS.  Both, because balloc hands
     the freshly allocated DATA block's [fsblock] half (and its exclusive
     [blk_own] token) to bmap and there is nowhere else to put them: the
     design doc's "the fresh half is deposited into the bundle" is exactly
     this, and a bmap that returned only [inode_map] would strand the block
     it just allocated.  The tokens inside the two bundles are also what
     re-establish [blkmap_wf]'s injectivity at an insertion
     ([InodeInv.inode_fresh]). *)
  inode_map γfs ip bm -∗
  inode_blocks γfs bm data -∗
  (* the caller's own pid cell (bread's acquiresleep records it) *)
  p_pid pj ↦₄{dq} pidv -∗
  (* the two superblock fields and the bitmap, all three for balloc's sake *)
  sb_size ↦₄{dqs} (mword_of_int size : mword 32) -∗
  sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
  bitmap_res γfs bmapstart cov logstart size used -∗
  (* the running-thread bundle *)
  procs_inv γs -∗
  (* the disk fabric *)
  dev_inv γu γd -∗
  disk_geom γd pd pav pu -∗
  is_lock γk d_lock "virtio_disk"%string (disk_res γd pd pav pu) -∗
  (* THREE slot units: bmap's own bread of the indirect block holds one
     across the interior balloc (which needs two of its own) and across
     log_write; brelse hands it back at the end. *)
  bslots bn 3 -∗
  (* THE RESERVATION, as a SPEND-AT-MOST clause.  bmap costs at most five
     units -- two per balloc x 2, plus its own log_write -- but it cannot
     hand back a surplus: [log_op] moves only through [LogInv.log_spend_step]
     against the ledger authority inside log.lock, and bmap never takes that
     lock.  So the direct-hit path returns the reservation untouched and the
     failure paths return whatever balloc refunded.  Stating a lower bound
     [n - 5 <= n'] rather than an exact [n - 5] is what makes that sound;
     the upper bound [n' <= n] is free and stops the contract from being
     satisfiable by a bmap that MINTS budget.  The premise is a lower bound
     on the caller's own counter rather than a [5 + u] shape, so a writei
     loop can present its counter directly and re-present what comes back. *)
  log_op γ n -∗
  (* THE CROSSING IS THE LITERAL [true], NOT [b].  This function can SLEEP
     (its bread / ilock / bwrite does), and a park moves the hart with
     interrupts off, so the crossing has nothing to do with SIE -- the
     porting guide's "a PARKING function's [wp_next] index is [true]
     UNCONDITIONALLY".  Spelled [b] the two coincide at the only instance
     the [eb = true] premise admits, which is why this went unnoticed; once
     [eb = false] is reachable the [b] form would promise the caller it
     comes back on the hart it called from, which a park makes false. *)
  wp_next true pj (fun (CID : CpuId) =>
  ∀ (mf : regfile) (bm' : blkmap) (n' : nat) (data' : nat -> list (bv 8))
    (used' : gset Z),
      ⌜callee_saved m mf⌝ -∗
      (* THE ALLOCATOR NEVER UN-MARKS: [used] only grows.  The exact set is
         existential because bmap may allocate twice. *)
      ⌜used ⊆ used'⌝ -∗
      ⌜blkmap_wf cov logstart bm'⌝ -∗
      (* bm' agrees with bm at every file index except possibly bn *)
      ⌜forall i : nat, (i < MAXFILE)%nat -> i <> fbn ->
         blkmap_get bm' i = blkmap_get bm i⌝ -∗
      (* ...and bmap NEVER UN-ALLOCATES: an index that already named a
         block still names the same one.  Together with the zero side
         condition on the deposit below this is what lets a caller carry
         "the blocks I did not write are the blocks that were there" across
         the call -- writei is the first consumer that needs it, and
         without it the contract permits a bmap that drops a mapping. *)
      ⌜forall i : nat, (i < MAXFILE)%nat -> bv_unsigned (blkmap_get bm i) <> 0 ->
         blkmap_get bm' i = blkmap_get bm i⌝ -∗
      (* the two arms, on the returned a0 *)
      ⌜(mf !!! Regidx (mword_of_int 10 : mword 5) = (mword_of_int 0 : mword 64)
        /\ bv_unsigned (blkmap_get bm' fbn) = 0)
       \/ (mf !!! Regidx (mword_of_int 10 : mword 5)
             = sign_extend' 64 (blkmap_get bm' fbn : mword 32)
           /\ bv_unsigned (blkmap_get bm' fbn) <> 0)⌝ -∗
      sie_cap_gpr KT1 mf K b pj -∗
      cpu_own 0 eb pj b lks -∗
      trap_csrs_ext KT1 eb -∗
      cpu_claim_ext eb pj -∗
      pc_is ret_tgt -∗
      p_pid pj ↦₄{dq} pidv -∗
      sb_size ↦₄{dqs} (mword_of_int size : mword 32) -∗
      sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
      bitmap_res γfs bmapstart cov logstart size used' -∗
      i_dev ip ↦₄{dqd} dev -∗
      inode_map γfs ip bm' -∗
      (* THE DEPOSIT.  [data'] is [data] except that a freshly allocated
         data block for [fbn] arrives all-zero.  A caller reads WHETHER an
         allocation happened off the MAP (the arm disjunction above and
         [blkmap_get bm' fbn]), never off [data'] -- which is why one
         disjunction, and not a case split coupled to the arms, is the
         right shape here; [InodeInv.inode_blocks_insert] and
         [inode_blocks_frame] are the two lemmas that produce the two
         disjuncts.

         THE ZERO SIDE CONDITION ON THE SECOND DISJUNCT is what makes this
         clause usable by writei.  Without it the contract permits a bmap
         that OVERWRITES an already-allocated block with zeroes, and then no
         caller can carry "the bytes outside the range I wrote are the bytes
         that were there before" across the call -- which is writei's whole
         postcondition.  It costs nothing: the deposit branch of bmap's proof
         runs exactly where [inode_blocks_insert]'s own
         [bv_unsigned (blkmap_get bm fbn) = 0] premise is already discharged. *)
      ⌜data' = data
       \/ (bv_unsigned (blkmap_get bm fbn) = 0
           /\ data' = <[fbn := replicate BSIZE (bv_0 8)]> data)⌝ -∗
      inode_blocks γfs bm' data' -∗
      bslots bn 3 -∗
      (* at most five units gone, and none gained *)
      ⌜((n - 5)%nat <= n')%nat /\ (n' <= n)%nat⌝ -∗
      log_op γ n' -∗
      WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

(* ===================================================================== *)
(*  THE CREDITED / SET-FORM CONTRACT                                      *)
(*  Everything above the budget clause is verbatim [wp_bmap_sconf_body];  *)
(*  only the ledger changes shape.  [wp_bmap_sconf] is derived from this  *)
(*  at [cr := false] with the set forgotten, so no existing caller moves. *)
(* ===================================================================== *)
Definition wp_bmap_gen_body
    `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !irefslotG Σ, !pavG Σ, !bioG Σ, !diskGhostG Σ,
      !uartGhostG Σ, !fsLogG Σ, !logG Σ}
    `{GEN : GenId} `{CID : CpuId}

    (γs : list gname) (j : nat) (γl : gname)          (* the running process *)
    (γu : uart_names) (γd : disk_names) (γk : gname)  (* disk fabric + lock  *)
    (pd pav pu : mword 64)
    (bn : bio_names)
    (γ : log_names) (γfs : fs_names)
    (cov : gset Z) (logstart : Z) (bmapstart : Z) (size : Z) (dev : mword 32)
    (used : gset Z) (γpr : gname)
    (ip : mword 64) (bm : blkmap) (data : nat -> list (bv 8)) (fbn : nat)
    (n : nat) (cr : bool) (Sb : gset Z)
    (pidv : mword 32) (dq dqd dqb dqs : dfrac)
    (m : regfile) (K : nat) (eb : bool)
    (b : bool) (lks : gset string) :=
  let pcE : mword 64 := mword_of_int KernelSyms.bmap in
  let pj := proc_addr j in
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5)) in
  let bnw : mword 32 := mword_of_int (Z.of_nat fbn) in
  (K_bmap <= K)%nat ->
  (* THE RESERVATION: enough for the deepest arm this index can take *)
  (bmap_need cr (bmap_ind fbn) <= n)%nat ->
  log_geom_ok cov logstart ->
  bitmap_geom_ok cov logstart bmapstart size ->
  printk_gen_contract (kt := KT1) γpr γu γd ->
  (* THE CREDIT'S PREMISE: claiming the bitmap block is already paid for
     means claiming this op has already logged it.  There is only one. *)
  (cr = true -> bmapstart ∈ Sb) ->
  (* NO eb-GATED RESTRICTION HERE.  An earlier round of the sweep had to
     add [eb = false -> the slot is already filled], because proving the
     credited ledger through an ACTUAL allocation needs balloc's CREDITED
     contract -- the fresh data block's address enters [Sb'] only through
     ITS success arm -- and [wp_balloc_gen_body] was still pinned at
     [eb = true].  It no longer is: it was generalized in the same round
     as this one, so the allocating arm is reachable at either index and
     the restriction is gone.  See
     claude-notes/completed/eb-generic-sweep.md ("Round 13"). *)
  (fbn < MAXFILE)%nat ->
  blkmap_wf cov logstart bm ->
  (j < NPROC)%nat ->
  γs !! j = Some γl ->
  m !!! Regidx (mword_of_int 10 : mword 5) = ip ->
  m !!! Regidx (mword_of_int 11 : mword 5) = sign_extend' 64 bnw ->
  (* bmap ALLOCATES here, so its cone reaches balloc -> log_write ("log", 3);
     the bread/brelse floor ("bcache", 4) follows by [locks_below_mono]. *)
  locks_below lks "log" ->
  sie_cap_gpr KT1 m K b pj -∗
  cpu_own 0 eb pj b lks -∗
  (* THE TRAP-CSR COMPLEMENT.  Same pure-pass-through shape as
     [wp_bmap_sconf_body] above -- required so that a LOOPING caller (e.g.
     writei, which must present the bitmap-block credit across several
     bmap calls within its own loop and therefore cannot go through the
     counted/sconf form, which has no [cr]/[Sb] at all) can reach this
     contract at [eb = false] too.  See
     claude-notes/completed/eb-generic-sweep.md. *)
  trap_csrs_ext KT1 eb -∗
  cpu_claim_ext eb pj -∗
  kernel_text -∗ pc_is pcE -∗
  kernel_data -∗
  printk_env γpr γu γd -∗
  panic_env -∗
  bio_ctx bn (fs_view γfs γd dev cov) -∗
  log_ctx γ bn γfs cov logstart dev -∗
  i_dev ip ↦₄{dqd} dev -∗
  inode_map γfs ip bm -∗
  inode_blocks γfs bm data -∗
  p_pid pj ↦₄{dq} pidv -∗
  sb_size ↦₄{dqs} (mword_of_int size : mword 32) -∗
  sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
  bitmap_res γfs bmapstart cov logstart size used -∗
  procs_inv γs -∗
  dev_inv γu γd -∗
  disk_geom γd pd pav pu -∗
  is_lock γk d_lock "virtio_disk"%string (disk_res γd pd pav pu) -∗
  bslots bn 3 -∗
  log_opS γ n Sb -∗
  (* THE CROSSING IS THE LITERAL [true], NOT [b] -- bmap's bread/balloc
     park. *)
  wp_next true pj (fun (CID : CpuId) =>
  ∀ (mf : regfile) (bm' : blkmap) (n' : nat) (data' : nat -> list (bv 8))
    (used' : gset Z) (Sb' : gset Z),
      ⌜callee_saved m mf⌝ -∗
      ⌜used ⊆ used'⌝ -∗
      ⌜blkmap_wf cov logstart bm'⌝ -∗
      ⌜forall i : nat, (i < MAXFILE)%nat -> i <> fbn ->
         blkmap_get bm' i = blkmap_get bm i⌝ -∗
      ⌜forall i : nat, (i < MAXFILE)%nat -> bv_unsigned (blkmap_get bm i) <> 0 ->
         blkmap_get bm' i = blkmap_get bm i⌝ -∗
      ⌜(mf !!! Regidx (mword_of_int 10 : mword 5) = (mword_of_int 0 : mword 64)
        /\ bv_unsigned (blkmap_get bm' fbn) = 0)
       \/ (mf !!! Regidx (mword_of_int 10 : mword 5)
             = sign_extend' 64 (blkmap_get bm' fbn : mword 32)
           /\ bv_unsigned (blkmap_get bm' fbn) <> 0)⌝ -∗
      sie_cap_gpr KT1 mf K b pj -∗
      cpu_own 0 eb pj b lks -∗
      trap_csrs_ext KT1 eb -∗
      cpu_claim_ext eb pj -∗
      pc_is ret_tgt -∗
      p_pid pj ↦₄{dq} pidv -∗
      sb_size ↦₄{dqs} (mword_of_int size : mword 32) -∗
      sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
      bitmap_res γfs bmapstart cov logstart size used' -∗
      i_dev ip ↦₄{dqd} dev -∗
      inode_map γfs ip bm' -∗
      ⌜data' = data
       \/ (bv_unsigned (blkmap_get bm fbn) = 0
           /\ data' = <[fbn := replicate BSIZE (bv_0 8)]> data)⌝ -∗
      inode_blocks γfs bm' data' -∗
      bslots bn 3 -∗
      (* THE LEDGER, ARM-WISE.  Four clauses, and a caller needs all four:
         the cost (what it may charge itself), the two set bounds (what it
         may still absorb, and what it must own up to when IT has a caller),
         and the two memberships that are the absorption itself. *)
      ⌜(* (a) the spend, arm-wise exact -- as an upper bound, because bmap
              cannot BURN a surplus it did not spend *)
        (n <= n' + bmap_cost cr (bmap_alloced bm bm' fbn) (bmap_ind fbn))%nat
        /\ (n' <= n)%nat
        (* (b) the set only grows... *)
        /\ Sb ⊆ Sb'
        (* ...and grows by AT MOST the three blocks bmap can log: the one
              bitmap block, the file's indirect block, and the data block
              for this index *)
        /\ Sb' ⊆ Sb ∪ {[bmapstart]} ∪ {[bv_unsigned (bm_ind bm')]}
                    ∪ {[bv_unsigned (blkmap_get bm' fbn)]}
        (* (c) any allocation at all logged THE BITMAP BLOCK, so the next
              call may present [cr := true] *)
        /\ (bmap_alloced bm bm' fbn = true -> bmapstart ∈ Sb')
        (* (d) ...and a freshly allocated DATA block was log_written by
              balloc's own bzero, which is what lets the caller absorb its
              own [log_write] of the very same block *)
        /\ (bmap_ad bm bm' fbn = true ->
              bv_unsigned (blkmap_get bm' fbn) ∈ Sb')
        (* (e) THE DIRECT PATH DOES NOT TOUCH THE INDIRECT SLOT.  Honest
              frame fact both direct arms hold literally (the allocating
              one builds its map at [bm_ind bm]; the other returns [bm]),
              and the clause that makes [wi16_spend]'s single [al] boolean
              derivable at the caller: with it, [bmap_ind fbn = false]
              gives [bmap_ai = false], so [bmap_alloced = bmap_ad] and
              clause (d) pays the caller's own log_write of the target.
              Without it, "allocated an INDIRECT block for a DIRECT index"
              is physically impossible but not contract-refutable (GR-3
              stage-3 W2 stop report, projects/fs-sysfile.md). *)
        /\ (bmap_ind fbn = false -> bm_ind bm' = bm_ind bm)⌝ -∗
      log_opS γ n' Sb' -∗
      WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

Module Type BMAP.
  Parameter wp_bmap_sconf :
    forall `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !irefslotG Σ, !pavG Σ, !bioG Σ, !diskGhostG Σ,
             !uartGhostG Σ, !fsLogG Σ, !logG Σ}
      `{GEN : GenId} `{CID : CpuId}
      
      (γs : list gname) (j : nat) (γl : gname)
      (γu : uart_names) (γd : disk_names) (γk : gname)
      (pd pav pu : mword 64)
      (bn : bio_names)
      (γ : log_names) (γfs : fs_names)
      (cov : gset Z) (logstart : Z) (bmapstart : Z) (size : Z) (dev : mword 32)
      (used : gset Z) (γpr : gname)
      (ip : mword 64) (bm : blkmap) (data : nat -> list (bv 8)) (fbn : nat)
      (n : nat)
      (pidv : mword 32) (dq dqd dqb dqs : dfrac)
      (m : regfile) (K : nat) (eb : bool)
      (b : bool) (lks : gset string),
      wp_bmap_sconf_body γs j γl γu γd γk pd pav pu bn γ γfs
                         cov logstart bmapstart size dev used γpr ip bm data fbn n
                         pidv dq dqd dqb dqs m K eb b lks.

  (* the SET-FORM contract; [wp_bmap_sconf] above is its instance at
     [cr := false] with the set forgotten, kept as its own parameter so
     that every existing caller is unchanged (wp_balloc_gen's pattern) *)
  Parameter wp_bmap_gen :
    forall `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !irefslotG Σ, !pavG Σ, !bioG Σ, !diskGhostG Σ,
             !uartGhostG Σ, !fsLogG Σ, !logG Σ}
      `{GEN : GenId} `{CID : CpuId}

      (γs : list gname) (j : nat) (γl : gname)
      (γu : uart_names) (γd : disk_names) (γk : gname)
      (pd pav pu : mword 64)
      (bn : bio_names)
      (γ : log_names) (γfs : fs_names)
      (cov : gset Z) (logstart : Z) (bmapstart : Z) (size : Z) (dev : mword 32)
      (used : gset Z) (γpr : gname)
      (ip : mword 64) (bm : blkmap) (data : nat -> list (bv 8)) (fbn : nat)
      (n : nat) (cr : bool) (Sb : gset Z)
      (pidv : mword 32) (dq dqd dqb dqs : dfrac)
      (m : regfile) (K : nat) (eb : bool)
      (b : bool) (lks : gset string),
      wp_bmap_gen_body γs j γl γu γd γk pd pav pu bn γ γfs
                       cov logstart bmapstart size dev used γpr ip bm data fbn
                       n cr Sb
                       pidv dq dqd dqb dqs m K eb b lks.
End BMAP.

(* ===================================================================== *)
(*  bmap FOR A CALLER THAT CANNOT ALLOCATE                                *)
(* ===================================================================== *)

(* readi calls bmap, and bmap allocates when the slot is zero -- which calls
   log_write.  But fileread does NOT wrap readi in a transaction, so an
   allocating read would hit panic("log_write outside of trans").  It never
   happens because every block below a file's size is allocated
   ([InodeInv.bm_covers] is that statement), and under the single premise

       bv_unsigned (blkmap_get bm fbn) <> 0

   ALL THREE of bmap's allocation sites are dead:

   - the direct slot test at +0x26 and the indirect ENTRY test at +0x80 are
     decided by the premise itself;
   - the indirect-BLOCK test at +0x4c is decided by the premise TOO, and
     that is why this contract needs no second hypothesis about bm_ind:
     [blkmap_wf]'s "no indirect block => no entries" conjunct read backwards
     ([InodeInv.blkmap_wf_ind_nz]) turns "the entry at an indirect index is
     nonzero" into "the indirect block exists".

   So the contract drops EVERYTHING the allocation arms needed:

   - no [log_op] and no budget premise -- bmap performs no [log_write], so
     there is no reservation to spend and none to hand back;
   - no [log_ctx], and hence no [γ : log_names] at all;
   - [bslot bn] rather than [bslots bn 3].  The three were bread's one held
     across balloc's two; with balloc dead only bread's own unit remains,
     and brelse returns it.

   ...and the postcondition is correspondingly exact rather than
   existential: the map and the file's data come back UNCHANGED, and a0 is
   [blkmap_get bm fbn].  It is the same 70 instructions and the same proof
   body as [BMAP] -- see ProofBmap.v's [BmapCore], which is parameterised
   by whether the allocation arms are live and is where BOTH contracts come
   from.  Precedent for two contracts over one function: SpecWalk.v's
   [WALK] / [WALK_NOALLOC]. *)
Definition wp_bmap_noalloc_sconf_body
    `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !irefslotG Σ, !pavG Σ, !bioG Σ, !diskGhostG Σ,
      !uartGhostG Σ, !fsLogG Σ, !logG Σ}
    `{GEN : GenId} `{CID : CpuId}
    
    (γs : list gname) (j : nat) (γl : gname)          (* the running process *)
    (γu : uart_names) (γd : disk_names) (γk : gname)  (* disk fabric + lock  *)
    (pd pav pu : mword 64)
    (bn : bio_names)
    (γfs : fs_names)
    (cov : gset Z) (logstart : Z) (dev : mword 32)
    (ip : mword 64) (bm : blkmap) (data : nat -> list (bv 8)) (fbn : nat)
    (pidv : mword 32) (dq dqd : dfrac)
    (m : regfile) (K : nat) (eb : bool)
    (b : bool) (lks : gset string) :=
  let pcE : mword 64 := mword_of_int KernelSyms.bmap in
  let pj := proc_addr j in
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5)) in
  let bnw : mword 32 := mword_of_int (Z.of_nat fbn) in
  (K_bmap <= K)%nat ->
  log_geom_ok cov logstart ->
  (* KILLS THE PANIC ARM *)
  (fbn < MAXFILE)%nat ->
  blkmap_wf cov logstart bm ->
  (* THE NO-ALLOC PREMISE, and the only one this contract adds *)
  bv_unsigned (blkmap_get bm fbn) <> 0 ->
  (j < NPROC)%nat ->
  γs !! j = Some γl ->
  m !!! Regidx (mword_of_int 10 : mword 5) = ip ->
  m !!! Regidx (mword_of_int 11 : mword 5) = sign_extend' 64 bnw ->
  (* the NO-ALLOC bmap never reaches log_write, so its floor is just the
     bread/brelse one -- requiring "log" of its callers would be over-strong. *)
  locks_below lks "bcache" ->
  sie_cap_gpr KT1 m K b pj -∗
  cpu_own 0 eb pj b lks -∗
  (* THE TRAP-CSR COMPLEMENT, NOT THE BARE PAIR -- see the allocating
     contract above; the no-alloc arm still sleeps (bread), so it is a
     pure pass-through here too. *)
  trap_csrs_ext KT1 eb -∗
  cpu_claim_ext eb pj -∗
  kernel_text -∗ kernel_data -∗ pc_is pcE -∗
  panic_env -∗
  bio_ctx bn (fs_view γfs γd dev cov) -∗
  i_dev ip ↦₄{dqd} dev -∗
  inode_map γfs ip bm -∗
  inode_blocks γfs bm data -∗
  p_pid pj ↦₄{dq} pidv -∗
  (* the running-thread bundle: bmap still SLEEPS, in bread *)
  procs_inv γs -∗
  (* the disk fabric *)
  dev_inv γu γd -∗
  disk_geom γd pd pav pu -∗
  is_lock γk d_lock "virtio_disk"%string (disk_res γd pd pav pu) -∗
  (* ONE slot unit: the interior bread's, handed back by brelse *)
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
  ∀ (mf : regfile),
      ⌜callee_saved m mf⌝ -∗
      (* the block the map already named, and nothing else happened *)
      ⌜mf !!! Regidx (mword_of_int 10 : mword 5)
         = sign_extend' 64 (blkmap_get bm fbn : mword 32)⌝ -∗
      sie_cap_gpr KT1 mf K b pj -∗
      cpu_own 0 eb pj b lks -∗
      trap_csrs_ext KT1 eb -∗
      cpu_claim_ext eb pj -∗
      pc_is ret_tgt -∗
      p_pid pj ↦₄{dq} pidv -∗
      i_dev ip ↦₄{dqd} dev -∗
      inode_map γfs ip bm -∗
      inode_blocks γfs bm data -∗
      bslot bn -∗
      WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

Module Type BMAP_NOALLOC.
  Parameter wp_bmap_noalloc_sconf :
    forall `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !irefslotG Σ, !pavG Σ, !bioG Σ, !diskGhostG Σ,
             !uartGhostG Σ, !fsLogG Σ, !logG Σ}
      `{GEN : GenId} `{CID : CpuId}
      
      (γs : list gname) (j : nat) (γl : gname)
      (γu : uart_names) (γd : disk_names) (γk : gname)
      (pd pav pu : mword 64)
      (bn : bio_names)
      (γfs : fs_names)
      (cov : gset Z) (logstart : Z) (dev : mword 32)
      (ip : mword 64) (bm : blkmap) (data : nat -> list (bv 8)) (fbn : nat)
      (pidv : mword 32) (dq dqd : dfrac)
      (m : regfile) (K : nat) (eb : bool)
      (b : bool) (lks : gset string),
      wp_bmap_noalloc_sconf_body γs j γl γu γd γk pd pav pu bn γfs
                                 cov logstart dev ip bm data fbn pidv dq dqd
                                 m K eb b lks.
End BMAP_NOALLOC.
