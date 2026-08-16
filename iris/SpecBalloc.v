(* SpecBalloc.v -- the public interface of balloc, stated independently of
   any proof.  balloc IS PROVEN: [ProofBalloc.v]'s [BallocProof] functor is
   the single instance of the [Module Type] below, and [LinkBalloc.v]
   carries no [Axiom].  A NEW [Parameter] HERE IS THEREFORE A PROOF
   OBLIGATION ON THAT FUNCTOR, not a free contract widening -- widening this
   interface costs work in a 4100-line proof file.  (It is still not an
   assumption in anyone's [Print Assumptions] cone: a [Module Type]
   parameter discharged by a real proof adds nothing.)

     static uint balloc(uint dev) {
       int b, bi, m;
       struct buf *bp = 0;
       for(b = 0; b < sb.size; b += BPB){
         bp = bread(dev, BBLOCK(b, sb));
         for(bi = 0; bi < BPB && b + bi < sb.size; bi++){
           m = 1 << (bi % 8);
           if((bp->data[bi/8] & m) == 0){    // is the block free?
             bp->data[bi/8] |= m;            // mark it in use
             log_write(bp);
             brelse(bp);
             bzero(dev, b + bi);
             return b + bi;
           }
         }
         brelse(bp);
       }
       printf("balloc: out of blocks\n");
       return 0;
     }

   THE CONTRACT (claude-notes/design/fs-inode.md, "balloc's contract").
   Two arms, on the returned a0:

   - SUCCESS -- a nonzero block b, with the two facts every FS-layer
     consumer of a block number needs ([b] is covered, and it is NOT one of
     the log's own storage blocks), plus b's own [fsblock] half at ALL
     ZEROES: bzero has already log_written the block as a zero block, so
     the caller receives a zeroed block and not an arbitrary one.  Spends
     TWO budget units -- the bitmap's log_write plus bzero's.

   - FAILURE -- returns 0, spends nothing, gives nothing: the reservation
     comes back at its full [2 + u].  The arm-dependent budget costs
     nothing to state because the postcondition is already a two-arm
     disjunction on the return value.

   *** THE OUT-OF-BLOCKS ARM IS LIVE, AND IT CALLS printk. ***  Nothing in
   [BitmapInv.bitmap_res] prevents every bit below [sb.size] being set --
   [free_pool] is then the empty big-op and [bitmap_ok] is vacuous -- so the
   scan CAN fall out of the loop and reach
   [auipc a0,0x4 / addi a0,a0,1350 / jal printk] on "balloc: out of blocks".
   That is the GENERAL printk path ([SpecPrintk.v]), not the panic path,
   so this contract takes:

     - [γpr] and the two PERSISTENT credentials [kernel_data] and
       [printk_env γpr γu γd] (the format string itself needs no premise:
       [KernelDataInv.kernel_data_string] mints its persistent [↦ₛ□] out of
       [kernel_data]);
     - printk's contract as a [Prop] HYPOTHESIS
       ([SpecPrintk.printk_gen_contract]), never as a functor argument.

   *** READ THIS BEFORE TRUSTING "THE STANDING SIX". ***  [PRINTK_GEN]'s only
   instance is [LinkPrintk]'s own [Axiom].  Instantiating the functor here
   would put a SEVENTH entry in [Print Assumptions Balloc.wp_balloc_sconf] --
   and, through the ripple, in bmap's and writei's too.  Carrying it as a
   hypothesis keeps all three at the standing six, but that is NOT
   self-containment: balloc's six are modulo a THREADED printk obligation
   that its callers must eventually discharge, exactly the standing that
   [SpecPanic]'s own credentials already have throughout this tree.  A reader who
   takes the six for "depends on nothing else" is misreading it.

   THE BITMAP RIDES THROUGH THE CONTRACT.  balloc reads BOTH superblock
   fields out of memory ([sb.size] at sb+4, [sb.bmapstart] at sb+28) and
   rewrites the bitmap block, so the two cells and [BitmapInv.bitmap_res]
   are premises -- there is no way to discharge the postcondition's
   [fsblock] + [blk_own] without a resource they come out of, and
   [BitmapInv.free_pool] is that resource.  Both cells ride as plain
   FRACTIONAL cells, the way SpecInitlog.v takes [sb + 20] and
   SpecIupdate.v takes [sb + 24]; the bitmap is PASSED IN AND RETURNED
   UPDATED, exactly as InodeInv.inode_map is for bmap, because who owns it
   between calls is the free-space layer's business and is deliberately
   not designed here (claude-notes/design/fs-bitmap.md, "Who owns
   bitmap_res between calls").

   ONE BITMAP BLOCK, AND A THIRD DEAD ARM.  [FSSIZE = 2000 < BPB = 8192],
   so [0 < size <= BPB] is a premise, BBLOCK collapses
   ([BitmapInv.BBLOCK_single]) and the outer loop runs a single iteration:
   b starts at 0, the inner scan exits on [b + bi >= sb.size] or on
   [bi == BPB], and [b += BPB] then makes [b >= sb.size] unconditionally.
   The [0 < size] half of that premise also kills balloc's OWN
   [beqz a5,+0xf6] at +0x12 -- the [sb.size == 0] jump straight to the
   printk, skipping the s2..s8 restore -- which is dead in the same sense
   as log_write's two panics, bmap's "out of range" and bfree's "freeing
   free block": the premise makes the arm unreachable, so it is refuted
   rather than proved.

   balloc SLEEPS (it breads), so it threads the running-process bundle
   exactly as SpecBread.v does: procs_inv / p_pid, the disk fabric
   (dev_inv / disk_geom / the virtio_disk lock), and the trap-CSR complement
   ([trap_csrs_ext eb] / [cpu_claim_ext eb pj], index-free -- see
   claude-notes/completed/eb-generic-sweep.md) that bread's own contract now
   demands.  It enters and returns at noff 0 but PARKS internally, so its
   own crossing is the literal [true], not [b].  The parked scheduler record
   is not threaded -- it lives in the running proc's own [p->lock]. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
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
Require Import BitmapInv.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import ProcAvail.
Import Defs.

Local Open Scope Z_scope.

(* balloc's own frame is 80 bytes (10 slots) -- [c.addi16sp sp,-80] at
   +0x00; its deepest callee is now printk on the out-of-blocks path (48,
   printk_stack).  bread wants 40, log_write 18 and brelse less. *)
Notation K_balloc := (68%nat) (only parsing).
Definition wp_balloc_sconf_body
    `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !irefslotG Σ, !pavG Σ, !bioG Σ, !diskGhostG Σ,
      !uartGhostG Σ, !fsLogG Σ, !logG Σ}
    `{GEN : GenId} `{CID : CpuId}
    
    (γs : list gname) (j : nat) (γl : gname)          (* the running process *)
    (γu : uart_names) (γd : disk_names) (γk : gname)  (* disk fabric + lock  *)
    (pd pav pu : mword 64)
    (bn : bio_names)
    (γ : log_names) (γfs : fs_names)
    (cov : gset Z) (logstart : Z) (bmapstart : Z) (size : Z) (dev : mword 32)
    (used : gset Z)
    (γpr : gname)
    (u : nat)
    (pidv : mword 32) (dq dqb dqs : dfrac)
    (m : regfile) (K : nat) (eb : bool)
    (b : bool) (lks : gset string) :=
  let pcE : mword 64 := mword_of_int KernelSyms.balloc in
  let pj := proc_addr j in
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5)) in
  (K_balloc <= K)%nat ->
  (* the covered range's block-number bounds (bread's 2^31 arithmetic
     premise, and 0 is never a client block) and the fact that the log's
     own storage is covered *)
  log_geom_ok cov logstart ->
  (* THE OUT-OF-BLOCKS ARM'S CALLEE, as a hypothesis and not a functor -- see
     the header for why that is what keeps this proof at the standing six *)
  printk_gen_contract γpr γu γd ->
  (* ONE BITMAP BLOCK (see the header), and the [0 < size] that kills the
     +0x12 arm *)
  0 < size <= BPB ->
  (* the bitmap block is a covered HOME block: bread's premise, and
     log_write's *)
  0 <= bmapstart ->
  bmapstart ∈ cov ->
  ~ (bmapstart ∈ log_region_set logstart) ->
  (j < NPROC)%nat ->
  γs !! j = Some γl ->
  (* the uint argument arrives sign-extended (RV64 ABI) *)
  m !!! Regidx (mword_of_int 10 : mword 5) = sign_extend' 64 dev ->
  (* the order premise, at the LOWEST rank this cone touches; every
     higher one follows by [locks_below_mono]. *)
  locks_below lks "log" ->
  sie_cap_gpr m K b pj -∗
  cpu_own 0 eb pj b lks -∗
  (* THE TRAP-CSR COMPLEMENT, NOT THE BARE PAIR.  balloc holds no lock of its
     own -- every push_off/pop_off pair that can mint or spend an
     [arm_pay 0 eb _] lives inside bread (and, through it, acquiresleep /
     virtio_disk_rw), so balloc is a PURE PASS-THROUGH: it neither mints nor
     spends this complement itself, only threads it down to each bread call
     and takes it back from bread's continuation.  At [eb = true] the
     complement is [emp], so no existing caller gains an obligation; at
     [eb = false] it is the honest pair, held by the caller because the TRAP
     handed it over, and passed to bread exactly as bread's own contract
     wants it.  See claude-notes/completed/sched-hart-generic.md and
     claude-notes/completed/eb-generic-sweep.md. *)
  trap_csrs_ext eb -∗
  cpu_claim_ext eb pj -∗
  kernel_text -∗ pc_is pcE -∗
  (* the general printk path's two PERSISTENT credentials, for the
     out-of-blocks arm *)
  kernel_data -∗
  printk_env γpr γu γd -∗
  bio_ctx bn (fs_view γfs γd dev cov) -∗
  log_ctx γ bn γfs cov logstart dev -∗
  (* the caller's own pid cell (bread's acquiresleep records it) *)
  p_pid pj ↦₄{dq} pidv -∗
  (* the two superblock fields, read at +0x0a and +0xa0 and never written *)
  sb_size ↦₄{dqs} (mword_of_int size : mword 32) -∗
  sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
  (* THE BITMAP, with its free pool: passed in, returned updated *)
  bitmap_res γfs bmapstart cov logstart size used -∗
  (* the running-thread bundle *)
  procs_inv γs -∗
  (* the disk fabric *)
  dev_inv γu γd -∗
  disk_geom γd pd pav pu -∗
  is_lock γk d_lock "virtio_disk"%string (disk_res γd pd pav pu) -∗
  (* TWO slot units: the bitmap buffer is bread and log_written (log_write
     wants a free unit for its bpin) before it is brelsed, and bzero then
     does the same for the data block. *)
  bslots bn 2 -∗
  (* this operation's reservation, at least the two units a success costs *)
  log_op γ (2 + u) -∗
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
      sie_cap_gpr mf K b pj -∗
      cpu_own 0 eb pj b lks -∗
      trap_csrs_ext eb -∗
      cpu_claim_ext eb pj -∗
      pc_is ret_tgt -∗
      p_pid pj ↦₄{dq} pidv -∗
      sb_size ↦₄{dqs} (mword_of_int size : mword 32) -∗
      sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
      bslots bn 2 -∗
      ((* FAILURE: a0 = 0, nothing allocated, nothing spent, the bitmap
          unchanged -- every bit below size was already set *)
       (⌜mf !!! Regidx (mword_of_int 10 : mword 5) = (mword_of_int 0 : mword 64)⌝ ∗
        bitmap_res γfs bmapstart cov logstart size used ∗
        log_op γ (2 + u))
       ∨
       (* SUCCESS: a0 = a nonzero covered home block, zeroed, two units gone *)
       (∃ blk : mword 32,
          ⌜mf !!! Regidx (mword_of_int 10 : mword 5) = sign_extend' 64 blk⌝ ∗
          ⌜bv_unsigned blk <> 0⌝ ∗
          ⌜bv_unsigned blk ∈ cov⌝ ∗
          ⌜~ (bv_unsigned blk ∈ log_region_set logstart)⌝ ∗
          fsblock γfs (bv_unsigned blk) (replicate BSIZE (bv_0 8)) ∗
          (* THE FRESHNESS CLAIM, and the reason it has to be a resource
             rather than a pure fact: [fsblock] is a HALF ghost_map element,
             so two of them at one key compose to a valid full element and
             say nothing about disjointness.  [blk_own] is the FULL element,
             so a caller that also holds one per block its own structures
             name learns, by [FsBlocks.blk_own_ne], that this block is none
             of them -- which is exactly what re-establishes
             [InodeInv.blkmap_wf]'s injectivity at an insertion (see
             [InodeInv.inode_fresh]).  Without it bmap is unprovable. *)
          blk_own γfs (bv_unsigned blk) ∗
          (* ...and the bitmap with exactly that bit newly set *)
          bitmap_res γfs bmapstart cov logstart size
                     (used ∪ {[ bv_unsigned blk ]}) ∗
          log_op γ u)) -∗
      WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

(* ===================================================================== *)
(*  THE CREDITED FORM -- balloc's contract with the LOG'S ALREADY-LOGGED  *)
(*  SET carried through it, [SpecBfree.wp_bfree_gen]'s shape verbatim.    *)
(* ===================================================================== *)

(* WHY.  balloc log_writes exactly TWO blocks, and a caller that is
   allocating several blocks in one transaction pays far less than
   [2 * blocks] for them:

   - THE BITMAP BLOCK.  [BBLOCK] collapses to [bmapstart] for every
     allocatable block ([WriteiBudget.one_bitmap_block], from this
     contract's own [0 < size <= BPB] premise), so EVERY balloc of the
     transaction log_writes THE SAME block.  Only the first pays; the rest
     absorb.  That is what [cr] claims, exactly as in bfree.

   - THE FRESH BLOCK, log_written by the inlined bzero at +0x4c.  It is
     never credited (a freshly allocated block cannot already be in this
     op's set in any way the caller can know), so it always costs one --
     but the caller LEARNS the block is now in the set, and can therefore
     absorb its OWN later log_write of the very same block.  That is the
     data-block absorption without which a four-block chunk of writei does
     not fit MAXOPBLOCKS ([WriteiBudget.wi_cost_noabs_busts]).

   The FAILURE arm log_writes nothing, so both the budget and the set come
   back untouched.  [wp_balloc_sconf] is this at [cr = false] with the set
   forgotten, and is unchanged: every existing caller keeps threading
   [log_op]. *)
Definition wp_balloc_gen_body
    `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !irefslotG Σ, !pavG Σ, !bioG Σ, !diskGhostG Σ,
      !uartGhostG Σ, !fsLogG Σ, !logG Σ}
    `{GEN : GenId} `{CID : CpuId}

    (γs : list gname) (j : nat) (γl : gname)          (* the running process *)
    (γu : uart_names) (γd : disk_names) (γk : gname)  (* disk fabric + lock  *)
    (pd pav pu : mword 64)
    (bn : bio_names)
    (γ : log_names) (γfs : fs_names)
    (cov : gset Z) (logstart : Z) (bmapstart : Z) (size : Z) (dev : mword 32)
    (used : gset Z)
    (γpr : gname)
    (u : nat) (cr : bool) (Sb : gset Z)
    (pidv : mword 32) (dq dqb dqs : dfrac)
    (m : regfile) (K : nat) (eb : bool)
    (b : bool) (lks : gset string) :=
  let pcE : mword 64 := mword_of_int KernelSyms.balloc in
  let pj := proc_addr j in
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5)) in
  (K_balloc <= K)%nat ->
  log_geom_ok cov logstart ->
  printk_gen_contract γpr γu γd ->
  0 < size <= BPB ->
  0 <= bmapstart ->
  bmapstart ∈ cov ->
  ~ (bmapstart ∈ log_region_set logstart) ->
  (* THE CREDIT'S PREMISE: claiming the free arm means claiming this op has
     already logged THE BITMAP BLOCK in this batch.  There is only one. *)
  (cr = true -> bmapstart ∈ Sb) ->
  (j < NPROC)%nat ->
  γs !! j = Some γl ->
  m !!! Regidx (mword_of_int 10 : mword 5) = sign_extend' 64 dev ->
  (* the order premise, at the LOWEST rank this cone touches; every
     higher one follows by [locks_below_mono]. *)
  locks_below lks "log" ->
  sie_cap_gpr m K b pj -∗
  cpu_own 0 eb pj b lks -∗
  (* THE TRAP-CSR COMPLEMENT.  Same pure-pass-through shape as
     [wp_balloc_sconf_body] above.  balloc holds no lock of its own, so it
     never inspects these: it carries them from entry to exit and hands
     them back re-indexed.  Generalizing the CREDITED form (not just the
     counted one) is what lets bmap keep a SINGLE core -- bmap's credited
     path routes here, and a core pinned at [eb = true] would have forced
     a second, independent proof of the same 70 instructions.  See
     claude-notes/completed/eb-generic-sweep.md. *)
  trap_csrs_ext eb -∗
  cpu_claim_ext eb pj -∗
  kernel_text -∗ pc_is pcE -∗
  kernel_data -∗
  printk_env γpr γu γd -∗
  bio_ctx bn (fs_view γfs γd dev cov) -∗
  log_ctx γ bn γfs cov logstart dev -∗
  p_pid pj ↦₄{dq} pidv -∗
  sb_size ↦₄{dqs} (mword_of_int size : mword 32) -∗
  sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
  bitmap_res γfs bmapstart cov logstart size used -∗
  procs_inv γs -∗
  dev_inv γu γd -∗
  disk_geom γd pd pav pu -∗
  is_lock γk d_lock "virtio_disk"%string (disk_res γd pd pav pu) -∗
  bslots bn 2 -∗
  (* THE RESERVATION.  Two units must be in hand either way -- log_write's
     own "a unit in hand" requirement holds on the absorbing arm too. *)
  log_opS γ (2 + u) Sb -∗
  (* THE CROSSING IS THE LITERAL [true], NOT [b] -- balloc's bread/bwrite
     park, and the counted form above already says [true]. *)
  wp_next true pj (fun (CID : CpuId) =>
  ∀ (mf : regfile),
      ⌜callee_saved m mf⌝ -∗
      sie_cap_gpr mf K b pj -∗
      cpu_own 0 eb pj b lks -∗
      trap_csrs_ext eb -∗
      cpu_claim_ext eb pj -∗
      pc_is ret_tgt -∗
      p_pid pj ↦₄{dq} pidv -∗
      sb_size ↦₄{dqs} (mword_of_int size : mword 32) -∗
      sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
      bslots bn 2 -∗
      ((* FAILURE: nothing allocated, NOTHING LOGGED -- budget and set both
          come back exactly as they went in *)
       (⌜mf !!! Regidx (mword_of_int 10 : mword 5) = (mword_of_int 0 : mword 64)⌝ ∗
        bitmap_res γfs bmapstart cov logstart size used ∗
        log_opS γ (2 + u) Sb)
       ∨
       (* SUCCESS: the bitmap block was logged (absorbing if credited) and
          so was the fresh block -- which is what lets the caller absorb its
          own log_write of it later *)
       (∃ blk : mword 32,
          ⌜mf !!! Regidx (mword_of_int 10 : mword 5) = sign_extend' 64 blk⌝ ∗
          ⌜bv_unsigned blk <> 0⌝ ∗
          ⌜bv_unsigned blk ∈ cov⌝ ∗
          ⌜~ (bv_unsigned blk ∈ log_region_set logstart)⌝ ∗
          fsblock γfs (bv_unsigned blk) (replicate BSIZE (bv_0 8)) ∗
          blk_own γfs (bv_unsigned blk) ∗
          bitmap_res γfs bmapstart cov logstart size
                     (used ∪ {[ bv_unsigned blk ]}) ∗
          log_opS γ (if cr then S u else u)
                    (Sb ∪ {[bmapstart]} ∪ {[bv_unsigned blk]}))) -∗
      WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

Module Type BALLOC.
  (* THE CREDITED / GENERAL FORM; [wp_balloc_sconf] below is its
     set-forgetting instance at [cr = false], kept as its own parameter so
     that every existing caller is unchanged. *)
  Parameter wp_balloc_gen :
    forall `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !irefslotG Σ, !pavG Σ, !bioG Σ, !diskGhostG Σ,
             !uartGhostG Σ, !fsLogG Σ, !logG Σ}
      `{GEN : GenId} `{CID : CpuId}

      (γs : list gname) (j : nat) (γl : gname)
      (γu : uart_names) (γd : disk_names) (γk : gname)
      (pd pav pu : mword 64)
      (bn : bio_names)
      (γ : log_names) (γfs : fs_names)
      (cov : gset Z) (logstart : Z) (bmapstart : Z) (size : Z) (dev : mword 32)
      (used : gset Z)
      (γpr : gname)
      (u : nat) (cr : bool) (Sb : gset Z)
      (pidv : mword 32) (dq dqb dqs : dfrac)
      (m : regfile) (K : nat) (eb : bool)
      (b : bool) (lks : gset string),
      wp_balloc_gen_body γs j γl γu γd γk pd pav pu bn γ γfs
                         cov logstart bmapstart size dev used γpr u cr Sb
                         pidv dq dqb dqs m K eb b lks.

  Parameter wp_balloc_sconf :
    forall `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !irefslotG Σ, !pavG Σ, !bioG Σ, !diskGhostG Σ,
             !uartGhostG Σ, !fsLogG Σ, !logG Σ}
      `{GEN : GenId} `{CID : CpuId}
      
      (γs : list gname) (j : nat) (γl : gname)
      (γu : uart_names) (γd : disk_names) (γk : gname)
      (pd pav pu : mword 64)
      (bn : bio_names)
      (γ : log_names) (γfs : fs_names)
      (cov : gset Z) (logstart : Z) (bmapstart : Z) (size : Z) (dev : mword 32)
      (used : gset Z)
      (γpr : gname)
      (u : nat)
      (pidv : mword 32) (dq dqb dqs : dfrac)
      (m : regfile) (K : nat) (eb : bool)
      (b : bool) (lks : gset string),
      wp_balloc_sconf_body γs j γl γu γd γk pd pav pu bn γ γfs
                           cov logstart bmapstart size dev used γpr u
                           pidv dq dqb dqs m K eb b lks.
End BALLOC.
