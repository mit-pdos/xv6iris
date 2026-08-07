(* SpecBalloc.v -- the public interface of balloc, stated independently of
   any proof.  balloc is ASSUMED for now: this file is a [Module Type] with
   no [Proof<F>.v] behind it, the sanctioned pattern already used for
   myproc / panic / kerneltrap (claude-notes/design/spec-modules.md, "An
   ASSUMED callee").  A [Link] file supplies the single instance with an
   [Axiom], so bmap's own proof stays axiom-free and proving balloc later
   replaces exactly one file.

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

   THE OPEN QUESTION THIS DEFERS is where a FREE block's [fsblock] half
   lives while free.  FsBoot mints one per covered block at boot, so they
   exist; proving balloc means designing the bitmap invariant that holds
   them and tying bit b of the bitmap to the claim that block b's half is
   in the pool.  Stating balloc needs none of that, which is exactly why
   it is worth assuming first -- the shape of bmap's proof does not depend
   on it.

   balloc SLEEPS (it breads), so it threads the full running-process
   bundle exactly as SpecBread.v does: procs_inv / scheds_inv / own_ctx /
   park_hlf / p_pid, the disk fabric (dev_inv / disk_geom / the
   virtio_disk lock), and the parking premise eb = true.  It enters and
   returns at noff 0. *)
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
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Import Defs.

Local Open Scope Z_scope.

(* balloc's own frame is 80 bytes (10 slots) -- [c.addi16sp sp,-80] at
   +0x00; its deepest callee is bread (40).  log_write wants 18 and
   brelse less. *)
Definition K_balloc : nat := 50%nat.

Definition wp_balloc_sconf_body
    `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !bioG Σ, !diskGhostG Σ,
      !uartGhostG Σ, !fsLogG Σ, !logG Σ}
    `{GEN : GenId} `{CID : CpuId}
    (Φ : mval -> iProp Σ)
    (γs : list gname) (j : nat) (γl : gname)          (* the running process *)
    (γu : uart_names) (γd : disk_names) (γk : gname)  (* disk fabric + lock  *)
    (pd pav pu : mword 64)
    (bn : bio_names)
    (γ : log_names) (γfs : fs_names)
    (cov : gset Z) (logstart : Z) (dev : mword 32)
    (u : nat)
    (pidv : mword 32) (dq : dfrac)
    (m : regfile) (K : nat) (eb : bool) (C : iProp Σ)
    (b : bool) :=
  let pcE : mword 64 := mword_of_int KernelSyms.balloc in
  let pj := proc_addr j in
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5)) in
  (K_balloc <= K)%nat ->
  (* the covered range's block-number bounds (bread's 2^31 arithmetic
     premise, and 0 is never a client block) and the fact that the log's
     own storage is covered *)
  log_geom_ok cov logstart ->
  (j < NPROC)%nat ->
  γs !! j = Some γl ->
  (* the uint argument arrives sign-extended (RV64 ABI) *)
  m !!! Regidx (mword_of_int 10 : mword 5) = sign_extend' 64 dev ->
  (* PARKING PREMISE (hart-generic scheduler protocol) -- everything below
     sleeps, and a parking thread hands the trap CSRs across the crossing
     only with an enabled base.  See SpecSched.v / SpecSleep.v. *)
  eb = true ->
  sie_cap_gpr m K b pj -∗
  cpu_own 0 eb pj C b -∗
  kernel_text -∗ pc_is pcE -∗
  panic_wp_any -∗
  bio_ctx bn (fs_view γfs γd dev cov) -∗
  log_ctx γ bn γfs cov logstart dev -∗
  (* the caller's own pid cell (bread's acquiresleep records it) *)
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
  (* TWO slot units: the bitmap buffer is bread and log_written (log_write
     wants a free unit for its bpin) before it is brelsed, and bzero then
     does the same for the data block. *)
  bslots bn 2 -∗
  (* this operation's reservation, at least the two units a success costs *)
  log_op γ (2 + u) -∗
  wp_next b pj (fun (CID : CpuId) =>
  ∀ (mf : regfile),
      ⌜callee_saved m mf⌝ -∗
      sie_cap_gpr mf K b pj -∗
      cpu_own 0 eb pj C b -∗
      pc_is ret_tgt -∗
      own_ctx (p_context pj) -∗
      park_hlf j true -∗
      p_pid pj ↦₄{dq} pidv -∗
      bslots bn 2 -∗
      ((* FAILURE: a0 = 0, nothing allocated, nothing spent *)
       (⌜mf !!! Regidx (mword_of_int 10 : mword 5) = (mword_of_int 0 : mword 64)⌝ ∗
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
          log_op γ u)) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
  WP (Loop : expr riscv_lang) {{ Φ }}.

Module Type BALLOC.
  Parameter wp_balloc_sconf :
    forall `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !bioG Σ, !diskGhostG Σ,
             !uartGhostG Σ, !fsLogG Σ, !logG Σ}
      `{GEN : GenId} `{CID : CpuId}
      (Φ : mval -> iProp Σ)
      (γs : list gname) (j : nat) (γl : gname)
      (γu : uart_names) (γd : disk_names) (γk : gname)
      (pd pav pu : mword 64)
      (bn : bio_names)
      (γ : log_names) (γfs : fs_names)
      (cov : gset Z) (logstart : Z) (dev : mword 32)
      (u : nat)
      (pidv : mword 32) (dq : dfrac)
      (m : regfile) (K : nat) (eb : bool) (C : iProp Σ)
      (b : bool),
      wp_balloc_sconf_body Φ γs j γl γu γd γk pd pav pu bn γ γfs
                           cov logstart dev u pidv dq m K eb C b.
End BALLOC.
