(* SpecBfree.v -- the public interface of bfree, stated independently of its
   proof.  Requires only the definitional layer -- never a whole-function
   proof file -- so every function proof can be checked in parallel.

     static void bfree(int dev, uint b) {
       struct buf *bp;
       int bi, m;

       bp = bread(dev, BBLOCK(b, sb));
       bi = b % BPB;
       m = 1 << (bi % 8);
       if((bp->data[bi/8] & m) == 0)
         panic("freeing free block");
       bp->data[bi/8] &= ~m;
       log_write(bp);
       brelse(bp);
     }

   108 bytes, 35 instructions, straight-line apart from the one panic arm.
   [bi] is computed as [(b << 51) >> 54], i.e. [(b mod BPB) / 8] fused with
   the byte index; [m] as [1 << (b & 7)]; the clear as [xori -1] + [and].

   THE CONTRACT (claude-notes/design/fs-bitmap.md).  bfree consumes the
   freed block's logical content half AND its exclusive [blk_own] token and
   returns both to [BitmapInv]'s FREE POOL, clearing bit [b] of the bitmap
   block.  The bitmap resource is PASSED IN AND RETURNED UPDATED, exactly
   as [InodeInv.inode_map] is for bmap -- who owns it between calls is the
   free-space layer's business and is deliberately not designed here.

   THE PANIC IS DEAD, and the bitmap invariant is what kills it.  The
   caller arrives holding [blk_own γfs b] -- a FULL-fraction ghost_map
   element, hence exclusive -- while [free_pool] holds one such token for
   every block below [size] whose bit is CLEAR.  So if bit [b] were clear
   there would be two tokens at one key, which is absurd
   ([BitmapInv.free_pool_own_used]).  The bit is therefore set,
   [bp->data[bi/8] & m] is nonzero ([BitmapEnc.bm_bit_test]), and the
   branch at +0x3a is not taken.  Refuting this panic is the main thing the
   invariant has to buy; the contract still takes [panic_wp_any] because
   bread's own interior panic arm wants one.

   ONE BITMAP BLOCK.  [FSSIZE = 2000 < BPB = 8192], so [size <= BPB] is a
   premise and [BBLOCK b sb = sb.bmapstart] outright
   ([BitmapInv.BBLOCK_single]).  bfree's [srliw a5,a1,0xd] then contributes
   zero and its [(b << 51) >> 54] is just [b / 8].

   THE BUDGET IS SPEND-EXACTLY: [log_op γ (S u)] in, [log_op γ u] out.
   bfree is straight-line and always executes its one log_write, so unlike
   bmap it can promise this (the spend-at-most form is forced only where a
   path can skip the spend).

   TWO SLOT UNITS, in and back out: bread's reference is held across
   log_write, which wants one of its own; brelse gives it back.

   [sb.bmapstart] rides as a plain FRACTIONAL cell, the way SpecInitlog.v
   takes [sb + 20] and SpecIupdate.v takes [sb + 24].  bfree does NOT read
   [sb.size] (only balloc does), so no [sb_size] cell appears here.

   bfree SLEEPS (bread), so it threads the full running-process bundle
   exactly as SpecIupdate.v / SpecBread.v do.  It enters and returns at
   noff 0. *)
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
Require Import PanicStub.
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

(* bfree's own frame is 32 bytes (4 slots) -- [c.addi16sp sp,-32] at +0x00,
   ra/s0/s1/s2 pushed.  Its deepest callee is bread (40); brelse wants 26
   and log_write 18. *)
Notation K_bfree := (62%nat) (only parsing).
Definition wp_bfree_gen_body
    `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !irefslotG Σ, !pavG Σ, !bioG Σ, !diskGhostG Σ,
      !uartGhostG Σ, !fsLogG Σ, !logG Σ}
    `{GEN : GenId} `{CID : CpuId}
    
    (γs : list gname) (j : nat) (γl : gname)          (* the running process *)
    (γu : uart_names) (γd : disk_names) (γk : gname)  (* disk fabric + lock  *)
    (pd pav pu : mword 64)
    (bn : bio_names)
    (γ : log_names) (γfs : fs_names)
    (cov : gset Z) (logstart : Z) (bmapstart : Z) (size : Z) (dev : mword 32)
    (used : gset Z) (bno : mword 32) (bs : list (bv 8))
    (u : nat) (cr : bool) (Sb : gset Z) (e0 : nat)
    (pidv : mword 32) (dq dqb : dfrac)
    (m : regfile) (K : nat) (eb : bool)
    (b : bool) (lks : gset string) :=
  let pcE : mword 64 := mword_of_int KernelSyms.bfree in
  let pj := proc_addr j in
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5)) in
  (K_bfree <= K)%nat ->
  (* the covered range's block-number bounds (bread's 2^31 arithmetic
     premise, and 0 is never a client block) and the fact that the log's own
     storage is covered *)
  log_geom_ok cov logstart ->
  (* ONE BITMAP BLOCK: the mkfs image has FSSIZE = 2000 < BPB = 8192, so
     BBLOCK collapses and the outer geometry never appears *)
  0 < size <= BPB ->
  (* the bitmap block is a covered HOME block: bread's premise, and
     log_write's *)
  0 <= bmapstart ->
  bmapstart ∈ cov ->
  ~ (bmapstart ∈ log_region_set logstart) ->
  (* the block being freed: in range for the bitmap, and a covered home
     block -- the two facts [bitmap_ok] must be re-established with, and
     exactly what the caller's [InodeInv.blkmap_wf] already gives it *)
  0 <= bv_unsigned bno < size ->
  bv_unsigned bno ∈ cov ->
  ~ (bv_unsigned bno ∈ log_region_set logstart) ->
  (* ...and it really is a block's worth of bytes *)
  length bs = BSIZE ->
  (j < NPROC)%nat ->
  γs !! j = Some γl ->
  (* the two uint arguments arrive sign-extended (RV64 ABI) *)
  m !!! Regidx (mword_of_int 10 : mword 5) = sign_extend' 64 dev ->
  m !!! Regidx (mword_of_int 11 : mword 5) = sign_extend' 64 bno ->
  (* bfree reaches log_write, whose bound is at "log" (3); nothing bfree
     touches ranks lower.  One premise covers the whole cone. *)
  locks_below lks "log" ->
  sie_cap_gpr m K b pj -∗
  cpu_own 0 eb pj b lks -∗
  (* THE TRAP-CSR COMPLEMENT, NOT THE BARE PAIR.  bfree does no acquire/
     release of its own -- it is a pure PASS-THROUGH to bread, which is
     push/pop-BALANCED and mints/spends the pair its own interior sleepers
     need.  At [eb = true] the complement is [emp], so no existing caller
     gains an obligation; at [eb = false] it is the honest pair, held by the
     caller because the TRAP handed it over, and bfree just threads it
     unchanged to bread and back.  See
     claude-notes/completed/sched-hart-generic.md and
     claude-notes/completed/eb-generic-sweep.md. *)
  trap_csrs_ext eb -∗
  cpu_claim_ext eb pj -∗
  kernel_text -∗ pc_is pcE -∗
  panic_wp_any -∗
  bio_ctx bn (fs_view γfs γd dev cov) -∗
  log_ctx γ bn γfs cov logstart dev -∗
  (* sb.bmapstart, read once at +0x12 *)
  sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
  (* THE BITMAP, with its free pool *)
  bitmap_res γfs bmapstart cov logstart size used -∗
  (* THE BLOCK BEING FREED: its logical content half and -- the load-bearing
     half of the handshake -- its EXCLUSIVE ownership token.  Holding the
     token is what makes the panic dead. *)
  fsblock γfs (bv_unsigned bno) bs -∗
  blk_own γfs (bv_unsigned bno) -∗
  (* the caller's own pid cell (bread's acquiresleep records it) *)
  p_pid pj ↦₄{dq} pidv -∗
  (* the running-thread bundle *)
  procs_inv γs -∗
  (* the disk fabric *)
  dev_inv γu γd -∗
  disk_geom γd pd pav pu -∗
  is_lock γk d_lock "virtio_disk"%string (disk_res γd pd pav pu) -∗
  (* TWO slot units: bread's reference is held across log_write, which wants
     one of its own; brelse gives it back *)
  bslots bn 2 -∗
  (* THE CREDIT, AS A RESOURCE AT A NAMED EPOCH (fs-log.md §G.19/§G.20).
     Claiming the free arm means claiming THE BITMAP BLOCK is already in
     lh.block[] -- there is only one, FSSIZE = 2000 < BPB = 8192, which is
     why itrunc can free 269 blocks against a single credit -- and
     [LogInv.log_credit] admits both ways of knowing it: this op logged it
     itself ([LogInv.log_credit_own] from the pure claim a counted caller
     already has) or somebody did, this batch, no older than [e0]. *)
  log_credit γ cr Sb e0 bmapstart -∗
  (* THE RESERVATION, WITH THE BIRTH EPOCH NAMED.  A unit must be in hand
     either way (log_write's own requirement -- it is what bounds lh.n).
     Uncredited it is spent on the bitmap block's first log_write of this
     batch; credited, that block is already in the header, log_write
     ABSORBS, and the unit comes back.

     THE EPOCH IS THREADED, NOT CLOSED (fs-log.md §G.20).  itrunc's loops
     free an unknown number of blocks and mean to present a GROUP credit at
     the tail flush; a credit is a claim at a NAMED epoch, so an [∃ e0] on
     the way out would lose the very thing the walk is carrying.  Nothing
     moves an open op's birth epoch, so this is the truth stated: the same
     [e0] comes back. *)
  log_opSe γ (S u) Sb e0 -∗
  (* THE CROSSING IS THE LITERAL [true], NOT [b].  This function can SLEEP
     (its bread / ilock / bwrite does), and a park moves the hart with
     interrupts off, so the crossing has nothing to do with SIE -- the
     porting guide's "a PARKING function's [wp_next] index is [true]
     UNCONDITIONALLY".  Spelled [b] the two coincide at the only instance
     the [eb = true] premise admits, which is why this went unnoticed; once
     [eb = false] is reachable the [b] form would promise the caller it
     comes back on the hart it called from, which a park makes false. *)
  wp_next true pj (fun (CID : CpuId) =>
  ∀ mf : regfile,
      ⌜callee_saved m mf⌝ -∗
      sie_cap_gpr mf K b pj -∗
      cpu_own 0 eb pj b lks -∗
      trap_csrs_ext eb -∗
      cpu_claim_ext eb pj -∗
      pc_is ret_tgt -∗
      p_pid pj ↦₄{dq} pidv -∗
      sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
      (* THE FREE: bit [bno] is clear, and the block's content half and its
         token are back in the pool *)
      bitmap_res γfs bmapstart cov logstart size (used ∖ {[ bv_unsigned bno ]}) -∗
      bslots bn 2 -∗
      log_opSe γ (if cr then S u else u) (Sb ∪ {[bmapstart]}) e0 -∗
      WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

Definition wp_bfree_sconf_body
    `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !irefslotG Σ, !pavG Σ, !bioG Σ, !diskGhostG Σ,
      !uartGhostG Σ, !fsLogG Σ, !logG Σ}
    `{GEN : GenId} `{CID : CpuId}
    
    (γs : list gname) (j : nat) (γl : gname)          (* the running process *)
    (γu : uart_names) (γd : disk_names) (γk : gname)  (* disk fabric + lock  *)
    (pd pav pu : mword 64)
    (bn : bio_names)
    (γ : log_names) (γfs : fs_names)
    (cov : gset Z) (logstart : Z) (bmapstart : Z) (size : Z) (dev : mword 32)
    (used : gset Z) (bno : mword 32) (bs : list (bv 8))
    (u : nat)
    (pidv : mword 32) (dq dqb : dfrac)
    (m : regfile) (K : nat) (eb : bool)
    (b : bool) (lks : gset string) :=
  let pcE : mword 64 := mword_of_int KernelSyms.bfree in
  let pj := proc_addr j in
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5)) in
  (K_bfree <= K)%nat ->
  (* the covered range's block-number bounds (bread's 2^31 arithmetic
     premise, and 0 is never a client block) and the fact that the log's own
     storage is covered *)
  log_geom_ok cov logstart ->
  (* ONE BITMAP BLOCK: the mkfs image has FSSIZE = 2000 < BPB = 8192, so
     BBLOCK collapses and the outer geometry never appears *)
  0 < size <= BPB ->
  (* the bitmap block is a covered HOME block: bread's premise, and
     log_write's *)
  0 <= bmapstart ->
  bmapstart ∈ cov ->
  ~ (bmapstart ∈ log_region_set logstart) ->
  (* the block being freed: in range for the bitmap, and a covered home
     block -- the two facts [bitmap_ok] must be re-established with, and
     exactly what the caller's [InodeInv.blkmap_wf] already gives it *)
  0 <= bv_unsigned bno < size ->
  bv_unsigned bno ∈ cov ->
  ~ (bv_unsigned bno ∈ log_region_set logstart) ->
  (* ...and it really is a block's worth of bytes *)
  length bs = BSIZE ->
  (j < NPROC)%nat ->
  γs !! j = Some γl ->
  (* the two uint arguments arrive sign-extended (RV64 ABI) *)
  m !!! Regidx (mword_of_int 10 : mword 5) = sign_extend' 64 dev ->
  m !!! Regidx (mword_of_int 11 : mword 5) = sign_extend' 64 bno ->
  (* bfree reaches log_write, whose bound is at "log" (3); nothing bfree
     touches ranks lower.  One premise covers the whole cone. *)
  locks_below lks "log" ->
  sie_cap_gpr m K b pj -∗
  cpu_own 0 eb pj b lks -∗
  (* THE TRAP-CSR COMPLEMENT, NOT THE BARE PAIR.  bfree does no acquire/
     release of its own -- it is a pure PASS-THROUGH to bread, which is
     push/pop-BALANCED and mints/spends the pair its own interior sleepers
     need.  At [eb = true] the complement is [emp], so no existing caller
     gains an obligation; at [eb = false] it is the honest pair, held by the
     caller because the TRAP handed it over, and bfree just threads it
     unchanged to bread and back.  See
     claude-notes/completed/sched-hart-generic.md and
     claude-notes/completed/eb-generic-sweep.md. *)
  trap_csrs_ext eb -∗
  cpu_claim_ext eb pj -∗
  kernel_text -∗ pc_is pcE -∗
  panic_wp_any -∗
  bio_ctx bn (fs_view γfs γd dev cov) -∗
  log_ctx γ bn γfs cov logstart dev -∗
  (* sb.bmapstart, read once at +0x12 *)
  sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
  (* THE BITMAP, with its free pool *)
  bitmap_res γfs bmapstart cov logstart size used -∗
  (* THE BLOCK BEING FREED: its logical content half and -- the load-bearing
     half of the handshake -- its EXCLUSIVE ownership token.  Holding the
     token is what makes the panic dead. *)
  fsblock γfs (bv_unsigned bno) bs -∗
  blk_own γfs (bv_unsigned bno) -∗
  (* the caller's own pid cell (bread's acquiresleep records it) *)
  p_pid pj ↦₄{dq} pidv -∗
  (* the running-thread bundle *)
  procs_inv γs -∗
  (* the disk fabric *)
  dev_inv γu γd -∗
  disk_geom γd pd pav pu -∗
  is_lock γk d_lock "virtio_disk"%string (disk_res γd pd pav pu) -∗
  (* TWO slot units: bread's reference is held across log_write, which wants
     one of its own; brelse gives it back *)
  bslots bn 2 -∗
  (* THE RESERVATION, SPEND-EXACTLY: the one log_write always runs *)
  log_op γ (S u) -∗
  (* THE CROSSING IS THE LITERAL [true], NOT [b].  This function can SLEEP
     (its bread / ilock / bwrite does), and a park moves the hart with
     interrupts off, so the crossing has nothing to do with SIE -- the
     porting guide's "a PARKING function's [wp_next] index is [true]
     UNCONDITIONALLY".  Spelled [b] the two coincide at the only instance
     the [eb = true] premise admits, which is why this went unnoticed; once
     [eb = false] is reachable the [b] form would promise the caller it
     comes back on the hart it called from, which a park makes false. *)
  wp_next true pj (fun (CID : CpuId) =>
  ∀ mf : regfile,
      ⌜callee_saved m mf⌝ -∗
      sie_cap_gpr mf K b pj -∗
      cpu_own 0 eb pj b lks -∗
      trap_csrs_ext eb -∗
      cpu_claim_ext eb pj -∗
      pc_is ret_tgt -∗
      p_pid pj ↦₄{dq} pidv -∗
      sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
      (* THE FREE: bit [bno] is clear, and the block's content half and its
         token are back in the pool *)
      bitmap_res γfs bmapstart cov logstart size (used ∖ {[ bv_unsigned bno ]}) -∗
      bslots bn 2 -∗
      log_op γ u -∗
      WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

Module Type BFREE.
  (* THE CREDITED / GENERAL FORM; [wp_bfree_sconf] below is its
     set-forgetting instance at [cr = false], kept as its own parameter so
     that balloc and every other caller is unchanged. *)
  Parameter wp_bfree_gen :
    forall `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !irefslotG Σ, !pavG Σ, !bioG Σ, !diskGhostG Σ,
             !uartGhostG Σ, !fsLogG Σ, !logG Σ}
      `{GEN : GenId} `{CID : CpuId}
      
      (γs : list gname) (j : nat) (γl : gname)
      (γu : uart_names) (γd : disk_names) (γk : gname)
      (pd pav pu : mword 64)
      (bn : bio_names)
      (γ : log_names) (γfs : fs_names)
      (cov : gset Z) (logstart : Z) (bmapstart : Z) (size : Z) (dev : mword 32)
      (used : gset Z) (bno : mword 32) (bs : list (bv 8))
      (u : nat) (cr : bool) (Sb : gset Z) (e0 : nat)
      (pidv : mword 32) (dq dqb : dfrac)
      (m : regfile) (K : nat) (eb : bool)
      (b : bool) (lks : gset string),
      wp_bfree_gen_body γs j γl γu γd γk pd pav pu bn γ γfs
                        cov logstart bmapstart size dev used bno bs u cr Sb e0
                        pidv dq dqb m K eb b lks.

  Parameter wp_bfree_sconf :
    forall `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !irefslotG Σ, !pavG Σ, !bioG Σ, !diskGhostG Σ,
             !uartGhostG Σ, !fsLogG Σ, !logG Σ}
      `{GEN : GenId} `{CID : CpuId}
      
      (γs : list gname) (j : nat) (γl : gname)
      (γu : uart_names) (γd : disk_names) (γk : gname)
      (pd pav pu : mword 64)
      (bn : bio_names)
      (γ : log_names) (γfs : fs_names)
      (cov : gset Z) (logstart : Z) (bmapstart : Z) (size : Z) (dev : mword 32)
      (used : gset Z) (bno : mword 32) (bs : list (bv 8))
      (u : nat)
      (pidv : mword 32) (dq dqb : dfrac)
      (m : regfile) (K : nat) (eb : bool)
      (b : bool) (lks : gset string),
      wp_bfree_sconf_body γs j γl γu γd γk pd pav pu bn γ γfs
                          cov logstart bmapstart size dev used bno bs u
                          pidv dq dqb m K eb b lks.
End BFREE.
