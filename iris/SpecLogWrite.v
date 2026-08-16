(* SpecLogWrite.v -- the public interface of log_write, stated independently
   of its proof.  Requires only the definitional layer -- never a
   whole-function proof file -- so every function proof can be checked in
   parallel.

     void log_write(struct buf *b) {
       int i;
       acquire(&log.lock);
       if (log.lh.n >= LOGBLOCKS)      panic("too big a transaction");
       if (log.outstanding < 1)        panic("log_write outside of trans");
       for (i = 0; i < log.lh.n; i++)
         if (log.lh.block[i] == b->blockno) break;   // log absorption
       log.lh.block[i] = b->blockno;
       if (i == log.lh.n) { bpin(b); log.lh.n++; }
       release(&log.lock);
     }

   log_write does NOT sleep -- it takes only the "log" SPINLOCK and calls
   bpin (which takes the bcache spinlock) -- so it threads no running-process
   bundle: [cpu_own n eb p C b] at the caller's own nesting level, exactly
   like SpecBpin.v.  It does need [panic_wp_any]: both of its own panic arms
   are DEAD (see below), but acquire's own holding-check arm wants a panic
   contract regardless.

   THE CONTRACT (claude-notes/design/fs-log.md, "log_write(b)").  The caller
   arrives holding a buffer it has typically EDITED, so its handle is
   [bio_held] with the traveling bytes [bs] and the payload still indexed at
   the block's old logical content [bsl] -- not [bio_locked], which is
   precisely why it cannot brelse the buffer yet.  log_write moves the
   logged view L(bno) from [bsl] to [bs] (the log lock's authority plus the
   caller's [fsblock] half plus the handle's payload half), so the handle
   comes back RE-INDEXED and DIRTY: [bio_locked ... bs bsd true], which is
   what brelse will accept.

   [d] is the incoming payload polarity, and it decides which path runs:
     d = false -- the first log_write of this block in the current batch.
                  The block is appended to lh.block[], lh.n++, and [bpin]
                  mints the pin that keeps the buffer un-evictable until
                  install_trans installs it.
     d = true  -- log ABSORPTION: the block is already in lh.block[] (its
                  dirty payload carries the earlier bpin's reference), so no
                  bpin runs at all.
   NEITHER PATH COSTS THE CALLER A SLOT UNIT: [bslot bn] goes in and comes
   back out, unconditionally.  On the absorb path it is simply never spent;
   on the append path [bpin] absorbs it and the n++ releases one unit of the
   POOL parked in [log_batch] ([bslots bn ((LOGBLOCKS - n) + 2)]) to replace
   it -- pool + n is invariant, and install_trans's bunpins refill it.  A
   conditional refund would poison every caller proof, which is exactly the
   argument the design doc's decision record makes about the budget unit.

   The BUDGET unit, by contrast, IS spent unconditionally on both paths
   ([log_op (S u)] in, [log_op u] out) -- always-consume is the C code's own
   worst-case MAXOPBLOCKS accounting (design doc, decision record).

   BOTH PANICS ARE DEAD, and the two ledger facts are what kill them:
     "too big a transaction"     -- a unit in hand forces lh.n < LOGBLOCKS
                                    (log_res's sum tie n + op_sum <= 30).
     "log_write outside of trans"-- an op token against the ledger authority
                                    forces log.outstanding >= 1
                                    (LogInv.log_op_positive). *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import excl auth gmap frac numbers.
From iris.base_logic.lib Require Import ghost_var gen_heap invariants ghost_map.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto.
Require Import InstrBytes.
Require Import KernelText.
Require Import RegFile WpNext.
Require Import SmodeCore.
Require Import CalleeSaved.
Require Import WpLock.
Require Import PanicStub.
Require Import IntrDefs.
Require Import CpuOwn.
Require Import DiskPtsto.
Require Import BcacheInv BioInv.
Require Import FsBlocks LogInv.
From Kernel Require KernelSyms.
Local Open Scope Z_scope.

(* log_write's own frame is 4 slots ([c.addi sp,sp,-32] at +0x00); its
   deepest callee is bpin, which wants 14 (its own 4 plus acquire/release's
   10).  acquire/release directly want only 10. *)
Notation K_log_write := (18%nat) (only parsing).
Definition wp_log_write_gen_body
    `{!riscvGS Σ, !lockG Σ, !sieG Σ, !bioG Σ, !diskGhostG Σ, !fsLogG Σ, !logG Σ}
    `{GEN : GenId} `{CID : CpuId}
    (bn : bio_names)
    (γ : log_names) (γfs : fs_names) (γd : disk_names)
    (cov : gset Z) (logstart : Z) (dev : mword 32)
    (k : nat) (pidv bno : mword 32)
    (bs bsl bsd : list (bv 8)) (d : bool) (u : nat)
    (cr : bool) (Sb : gset Z)
    (m : regfile) (n : nat) (eb : bool) (p : mword 64)
    (K : nat) (b : bool) (lks : gset string) :=
  let pcE : mword 64 := mword_of_int KernelSyms.log_write in
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5) : mword 64) in
  (K_log_write <= K)%nat ->
  (* bpin runs UNDER log.lock, i.e. at nesting level S n, and its own
     acquire pushes again: the premise must cover TWO pushes above the
     entry level (the SpecPipeclose/SpecConsoleintr convention -- the +1
     form is underivable at the bpin call site, cpu_cells' own bound at
     level S n gives back only +1). *)
  (Z.of_nat n + 2 < 2 ^ 31)%Z ->
  (* a0 is the buffer being logged *)
  (k < NBUF)%nat ->
  m !!! Regidx (mword_of_int 10 : mword 5) = bnode k ->
  (* the block is a covered HOME block: never the log's own storage.  (The
     covered fact is also carried by the handle below; it is restated here
     because log_batch's own conjunct is what the append path must
     re-establish.) *)
  uint bno ∈ cov ->
  ~ (uint bno ∈ log_region_set logstart) ->
  (* THE CREDIT'S PREMISE: claiming the free arm means claiming this op
     has already appended [bno] in this batch. *)
  (cr = true -> uint bno ∈ Sb) ->
  (* THE FRESHNESS PREMISE, AS A BOUND AT THE LOWEST RANK THIS FUNCTION
     TOUCHES.  log_write acquires "log"(3) itself and its append arm calls
     bpin, which acquires "bcache"(4) UNDER "log" -- and [locks_below] carries
     BOTH in one premise, which is exactly the composition property
     [SpecAcquire.v]'s header argues for: [locks_below_mono] weakens this to
     "bcache" and [locks_below_union_singleton] carries it across log_write's
     own acquire, so bpin's [locks_below ({[rank "log"]} ∪ lks) (rank "bcache")]
     is a consequence rather than a second premise.  Trivial at [lks = ∅],
     which every landed caller is at (a caller of log_write holds sleeplocks,
     not spinlocks). *)
  locks_below lks "log" ->
  sie_cap_gpr m K b p -∗
  cpu_own n eb p b lks -∗
  kernel_text -∗ pc_is pcE -∗
  panic_wp_any -∗
  bio_ctx bn (fs_view γfs γd dev cov) -∗
  log_ctx γ bn γfs cov logstart dev -∗
  (* the slot unit backing the (possible) bpin *)
  bslot bn -∗
  (* THE RESERVATION.  A unit must be IN HAND either way -- that is what
     bounds lh.n below LOGBLOCKS and so keeps the header's next slot
     writable ([nl <= 29]); a caller with an exhausted budget has no
     business in log_write even to absorb.  Uncredited (cr = false) the
     unit is spent and the block joins this op's already-logged set;
     credited (cr = true) the block is already in that set, log_write
     ABSORBS, lh.n does not grow, and THE UNIT COMES BACK. *)
  log_opS γ (S u) Sb -∗
  (* the caller's own view of the block, at its OLD content *)
  fsblock γfs (uint bno) bsl -∗
  (* the checked-out buffer.  [bio_held], NOT [bio_locked]: the caller has
     typically edited the bytes, so bs <> bsl and the payload is still
     indexed at bsl. *)
  bio_held bn (fs_view γfs γd dev cov) k pidv dev bno bs bsl bsd d -∗
  wp_next b p (fun (CID : CpuId) =>
    ∀ mr,
    sie_cap_gpr mr K b p -∗
    cpu_own n eb p b lks -∗
    pc_is ret_tgt -∗
    ⌜ callee_saved m mr ⌝ -∗
    (* the block is in the set either way -- it was already there on the
       credited arm ([Sb ∪ {[bno]} = Sb] under the premise), where the unit
       is also handed straight back *)
    log_opS γ (if cr then S u else u) (Sb ∪ {[uint bno]}) -∗
    (* L(bno) is now the bytes the caller wrote *)
    fsblock γfs (uint bno) bs -∗
    (* the handle re-indexed at those bytes and now DIRTY: brelse-able *)
    bio_locked bn (fs_view γfs γd dev cov) k pidv dev bno bs bsd true -∗
    (* the slot unit comes back UNCONDITIONALLY -- see the header note *)
    bslot bn -∗
    WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

(* THE ATOMIC-UPDATE FORM (claude-notes/design/fs-icache.md, §12): the
   caller's [fsblock] half arrives through a fupd fired at log_write's own
   ghost step instead of sitting in its hands for the whole call.

   WHY THIS EXISTS.  A dinode block's client half lives in the inode
   REGION's invariant (InodeRegion.v) and can never sit in a caller's
   hands across a call: iupdate's own log_write footprint holds every
   per-block exclusive resource, so a §11.4-style checkout window has
   nothing to deposit and is unstatable.  The only sound moment for the
   half to leave the region is the single ghost step where the logged
   view actually moves -- ProofLogWrite's [fsblock_update], a pure ghost
   moment between two instruction dispatches at mask ⊤.  This premise
   opens the caller's invariant exactly there:

   - the fupd surrenders the half at WHATEVER content the invariant
     parked ([bsl'], existential);
   - [fsblock_update]'s own agreement against the handle's payload half
     is what pins [bsl' = bsl] -- the caller never has to know the
     invariant's content in advance;
   - the closing fupd takes the half back at the WRITTEN bytes and pays
     out [Φfsb], the caller's chosen receipt (for iupdate: the retagged
     [dinode_at], via InodeRegion.ireg_write_au).

   A caller that HOLDS the half is the degenerate instance: [Efs := ⊤],
   [Φfsb := fsblock γfs (uint bno) bs], and the fupd is two iModIntros --
   that is [wp_log_write_gen] below, derived, so no existing caller
   moves. *)
Definition wp_log_write_au_body
    `{!riscvGS Σ, !lockG Σ, !sieG Σ, !bioG Σ, !diskGhostG Σ, !fsLogG Σ, !logG Σ}
    `{GEN : GenId} `{CID : CpuId}
    (bn : bio_names)
    (γ : log_names) (γfs : fs_names) (γd : disk_names)
    (cov : gset Z) (logstart : Z) (dev : mword 32)
    (k : nat) (pidv bno : mword 32)
    (bs bsl bsd : list (bv 8)) (d : bool) (u : nat)
    (cr : bool) (Sb : gset Z) (e0 : nat) (vlb : nat)
    (Efs : coPset) (Φfsb : iProp Σ)
    (m : regfile) (n : nat) (eb : bool) (p : mword 64)
    (K : nat) (b : bool) (lks : gset string) :=
  let pcE : mword 64 := mword_of_int KernelSyms.log_write in
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5) : mword 64) in
  (K_log_write <= K)%nat ->
  (Z.of_nat n + 2 < 2 ^ 31)%Z ->
  (* a0 is the buffer being logged *)
  (k < NBUF)%nat ->
  m !!! Regidx (mword_of_int 10 : mword 5) = bnode k ->
  (* the block is a covered HOME block: never the log's own storage *)
  uint bno ∈ cov ->
  ~ (uint bno ∈ log_region_set logstart) ->
  (* THE FRESHNESS BOUND -- see [wp_log_write_gen_body] *)
  locks_below lks "log" ->
  sie_cap_gpr m K b p -∗
  cpu_own n eb p b lks -∗
  kernel_text -∗ pc_is pcE -∗
  panic_wp_any -∗
  bio_ctx bn (fs_view γfs γd dev cov) -∗
  log_ctx γ bn γfs cov logstart dev -∗
  (* the slot unit backing the (possible) bpin *)
  bslot bn -∗
  (* THE CALLER'S EPOCH ANCHOR (fs-log.md §G.17, blocker 4).  Persistent and
     free at [vlb := 0], so it costs a caller that wants no receipt nothing;
     what it buys is the one comparison the whole group-absorption design
     cannot make anywhere else, cashed at the ghost step below against the
     [ln_ep] auth this function is the only client of. *)
  log_epoch_lb γ vlb -∗
  (* THE CREDIT'S PREMISE, RELAXED TO A RESOURCE (fs-log.md §G.19).  Claiming
     the free arm means claiming the block is ALREADY IN lh.block[], and
     [LogInv.log_credit] admits the two ways of knowing that:
       - [uint bno ∈ Sb] -- this op appended it itself (the pure premise this
         used to be, now one disjunct; [LogInv.log_credit_own] is the
         one-step conversion every landed credited caller uses);
       - [logged_at γ e (uint bno)] with [e0 <= e] -- SOMEBODY appended it
         this batch, which is the case the kernel's absorption scan actually
         implements and the model used to under-claim (§G.1).
     The group form is what forces [e0] into the open: it must be ordered
     against the CALLER'S OWN birth epoch, so the ledger premise below is
     [log_opSe] (the epoch named) rather than [log_opS] (it buried).  A
     [cr := false] caller passes [emp] and never sees any of this. *)
  log_credit γ cr Sb e0 (uint bno) -∗
  log_opSe γ (S u) Sb e0 -∗
  (* THE CALLER'S VIEW OF THE BLOCK, AS AN ATOMIC UPDATE -- see the header
     note above.  Fired exactly once, at the ghost step.

     IT CARRIES ITS OWN ANCHOR, AND TAKES THE COMPARISON BACK (fs-log.md
     §G.17, blocker 4; fs-icache.md §20.18's C4).  The fupd surrenders a
     lower bound [log_epoch_lb γ v] BESIDE the half, and the closing wand
     is handed [logged_at γ e0 (uint bno)] and [⌜v <= e0⌝] as inputs.  Two
     things force that shape rather than the outer [vlb] premise's:

     - the anchor of the ONE writer that owes a receipt
       ([InodeRegion.ireg_write_unlink]) is the per-inum observation
       counter, which is INSIDE the invariant the fupd opens -- so its
       value is not nameable at the call site, only under this fupd;
     - the comparison [v <= e0] is unprovable anywhere but the ghost step,
       where the [ln_ep] auth is open (§G.14: two lower bounds on one
       counter are incomparable), and it is free THERE.

     A caller with no receipt to build takes [v := 0] and drops both wand
     inputs -- that is [lw_au_lb0] below, one line, so every landed AU
     supplier is unchanged.  The outer [log_epoch_lb γ vlb] premise and the
     [log_opSwe] post are untouched: they are the DEPOSITOR's tier (a
     receipt ordered against an anchor the caller can name), and this is
     the WRITER's. *)
  (|={⊤, Efs}=> ∃ (bsl' : list (bv 8)) (v : nat),
     fsblock γfs (uint bno) bsl' ∗ log_epoch_lb γ v ∗
     (⌜bsl' = bsl⌝ -∗ logged_at γ e0 (uint bno) -∗ ⌜(v <= e0)%nat⌝ -∗
      fsblock γfs (uint bno) bs ={Efs, ⊤}=∗ Φfsb)) -∗
  (* the checked-out buffer, payload still indexed at the old content *)
  bio_held bn (fs_view γfs γd dev cov) k pidv dev bno bs bsl bsd d -∗
  wp_next b p (fun (CID : CpuId) =>
    ∀ mr,
    sie_cap_gpr mr K b p -∗
    cpu_own n eb p b lks -∗
    pc_is ret_tgt -∗
    ⌜ callee_saved m mr ⌝ -∗
    (* THE ENTRY, WITH ITS BIRTH EPOCH NAMED, PLUS THE LOG WITNESS
       (fs-log.md §G.3/§G.20).  [LogInv.log_opSwe] is [log_opS] with two
       things added at the caller's OWN [e0] -- the birth epoch it handed
       in, LITERALLY the same one -- and [logged_at γ e0 (uint bno)]:
       "this block is in the header of the batch my op belongs to".
       A depositor that only wants to order the witness against its own
       anchor closes the epoch again with [LogInv.log_opSwe_opSw]; a WALKER
       keeps it, which is the whole of the epoch tier.
       The witness's epoch IS the caller's own entry's, which is the only
       shape a later [log_use_group] can spend: an unmoored [∃ e] would be
       satisfied by a dead batch's row and the header's revocation argument
       is exactly what forbids trusting one.  Both arms mint: the append
       arm because it just wrote the slot, the absorb arm because its scan
       FOUND the block already there.  A caller that wants none of this
       applies [LogInv.log_opSw_opS] and is otherwise unchanged. *)
    log_opSwe γ (if cr then S u else u) (Sb ∪ {[uint bno]}) (uint bno) vlb e0 -∗
    (* the caller's receipt: what its closing fupd paid out *)
    Φfsb -∗
    (* the handle re-indexed at the written bytes and now DIRTY *)
    bio_locked bn (fs_view γfs γd dev cov) k pidv dev bno bs bsd true -∗
    (* the slot unit comes back UNCONDITIONALLY *)
    bslot bn -∗
    WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

(* THE DEGENERATE ANCHOR, AS AN ADAPTER (fs-log.md §G.17, blocker 4).
   Every AU supplier that owes NO receipt -- ialloc's [ireg_claim_au],
   iupdate's two ordinary region steps, and the held-fsblock form below --
   states its fupd without an anchor and without the two extra wand inputs.
   This is the whole conversion: park the bound at ZERO, where
   [LogInv.log_epoch_lb_0] mints it for free, and drop both inputs on the
   way back in.  One line at each site, so the atomic-update premise can
   carry the writer's anchor without any of them moving. *)
Lemma lw_au_lb0 `{!riscvGS Σ, !bioG Σ, !diskGhostG Σ, !fsLogG Σ, !logG Σ}
    (γ : log_names) (γfs : fs_names) (bno : Z) (Efs : coPset)
    (bs bsl : list (bv 8)) (Φfsb : iProp Σ) (e0 : nat) :
  (|={⊤, Efs}=> ∃ bsl' : list (bv 8),
     fsblock γfs bno bsl' ∗
     (⌜bsl' = bsl⌝ -∗ fsblock γfs bno bs ={Efs, ⊤}=∗ Φfsb))
  -∗
  (|={⊤, Efs}=> ∃ (bsl' : list (bv 8)) (v : nat),
     fsblock γfs bno bsl' ∗ log_epoch_lb γ v ∗
     (⌜bsl' = bsl⌝ -∗ logged_at γ e0 bno -∗ ⌜(v <= e0)%nat⌝ -∗
      fsblock γfs bno bs ={Efs, ⊤}=∗ Φfsb)).
Proof.
  iIntros "Hau".
  iMod (log_epoch_lb_0 γ) as "#Hlb0".
  iMod "Hau" as (bsl') "[Hfsb Hcl]".
  iModIntro. iExists bsl', 0%nat. iFrame "Hfsb Hlb0".
  iIntros "%Hbs _ _ Hfsb". iApply ("Hcl" with "[//] Hfsb").
Qed.

(* THE EPOCH-EXPOSED GENERAL FORM (fs-log.md §G.20, the epoch tier).
   [wp_log_write_gen] with the birth epoch left OPEN on both sides: the
   ledger premise is [log_opSe] rather than [log_opS], the credit is the
   RESOURCE [log_credit] rather than the pure own-set claim, and the post
   hands the entry back AT THE SAME [e0].

   WHY BOTH SIDES.  A credit is a claim at a NAMED epoch -- its group
   disjunct is [∃ e, logged_at γ e b ∗ ⌜e0 <= e⌝] -- so a caller in the
   middle of a walk that means to spend one later must still be holding the
   entry at the [e0] its observation was ordered against.  [wp_log_write_gen]
   closes that existential on the way out, and once closed it cannot be
   recovered: a re-opened entry yields SOME [e1], and although [e1 = e0] is
   true (the ghost steps update the entry in place, and the epoch's only
   transition is the commit bump, which runs with no live entry), NOTHING in
   the logic relates two lower bounds on one counter (§G.14, §G.20).  So the
   epoch is threaded SYNTACTICALLY, from the observer down to the log_write
   that claims the credit, and this is the bottom of that thread.

   The witness comes out too, at the same epoch: it is free (the atomic-update
   form already mints it on both arms) and it is exactly what makes a SECOND
   write of this block by this op creditable.  A caller that wants neither
   applies [LogInv.log_opSe_opS] and is [wp_log_write_gen] again -- which is
   how that contract is derived, so no landed caller moves. *)
Definition wp_log_write_gene_body
    `{!riscvGS Σ, !lockG Σ, !sieG Σ, !bioG Σ, !diskGhostG Σ, !fsLogG Σ, !logG Σ}
    `{GEN : GenId} `{CID : CpuId}
    (bn : bio_names)
    (γ : log_names) (γfs : fs_names) (γd : disk_names)
    (cov : gset Z) (logstart : Z) (dev : mword 32)
    (k : nat) (pidv bno : mword 32)
    (bs bsl bsd : list (bv 8)) (d : bool) (u : nat)
    (cr : bool) (Sb : gset Z) (e0 : nat)
    (m : regfile) (n : nat) (eb : bool) (p : mword 64)
    (K : nat) (b : bool) (lks : gset string) :=
  let pcE : mword 64 := mword_of_int KernelSyms.log_write in
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5) : mword 64) in
  (K_log_write <= K)%nat ->
  (Z.of_nat n + 2 < 2 ^ 31)%Z ->
  (* a0 is the buffer being logged *)
  (k < NBUF)%nat ->
  m !!! Regidx (mword_of_int 10 : mword 5) = bnode k ->
  (* the block is a covered HOME block: never the log's own storage *)
  uint bno ∈ cov ->
  ~ (uint bno ∈ log_region_set logstart) ->
  (* THE FRESHNESS BOUND -- see [wp_log_write_gen_body] *)
  locks_below lks "log" ->
  sie_cap_gpr m K b p -∗
  cpu_own n eb p b lks -∗
  kernel_text -∗ pc_is pcE -∗
  panic_wp_any -∗
  bio_ctx bn (fs_view γfs γd dev cov) -∗
  log_ctx γ bn γfs cov logstart dev -∗
  (* the slot unit backing the (possible) bpin *)
  bslot bn -∗
  (* THE CREDIT, AS A RESOURCE (fs-log.md §G.19): either this op logged the
     block itself ([uint bno ∈ Sb], which [LogInv.log_credit_own] builds from
     the pure claim every counted caller already has) or SOMEBODY did, this
     batch, no older than this op's birth. *)
  log_credit γ cr Sb e0 (uint bno) -∗
  (* THE RESERVATION, WITH THE BIRTH EPOCH NAMED *)
  log_opSe γ (S u) Sb e0 -∗
  (* the caller's own view of the block, at its OLD content *)
  fsblock γfs (uint bno) bsl -∗
  (* the checked-out buffer, payload still indexed at the old content *)
  bio_held bn (fs_view γfs γd dev cov) k pidv dev bno bs bsl bsd d -∗
  wp_next b p (fun (CID : CpuId) =>
    ∀ mr,
    sie_cap_gpr mr K b p -∗
    cpu_own n eb p b lks -∗
    pc_is ret_tgt -∗
    ⌜ callee_saved m mr ⌝ -∗
    (* THE ENTRY BACK AT THE SAME [e0] -- the whole point -- and this op's
       own registry row for the block it just logged *)
    log_opSe γ (if cr then S u else u) (Sb ∪ {[uint bno]}) e0 -∗
    logged_at γ e0 (uint bno) -∗
    (* L(bno) is now the bytes the caller wrote *)
    fsblock γfs (uint bno) bs -∗
    (* the handle re-indexed at those bytes and now DIRTY: brelse-able *)
    bio_locked bn (fs_view γfs γd dev cov) k pidv dev bno bs bsd true -∗
    (* the slot unit comes back UNCONDITIONALLY *)
    bslot bn -∗
    WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

Definition wp_log_write_sconf_body
    `{!riscvGS Σ, !lockG Σ, !sieG Σ, !bioG Σ, !diskGhostG Σ, !fsLogG Σ, !logG Σ}
    `{GEN : GenId} `{CID : CpuId}
    (bn : bio_names)
    (γ : log_names) (γfs : fs_names) (γd : disk_names)
    (cov : gset Z) (logstart : Z) (dev : mword 32)
    (k : nat) (pidv bno : mword 32)
    (bs bsl bsd : list (bv 8)) (d : bool) (u : nat)
    (m : regfile) (n : nat) (eb : bool) (p : mword 64)
    (K : nat) (b : bool) (lks : gset string) :=
  let pcE : mword 64 := mword_of_int KernelSyms.log_write in
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5) : mword 64) in
  (K_log_write <= K)%nat ->
  (* bpin runs UNDER log.lock, i.e. at nesting level S n, and its own
     acquire pushes again: the premise must cover TWO pushes above the
     entry level (the SpecPipeclose/SpecConsoleintr convention -- the +1
     form is underivable at the bpin call site, cpu_cells' own bound at
     level S n gives back only +1). *)
  (Z.of_nat n + 2 < 2 ^ 31)%Z ->
  (* a0 is the buffer being logged *)
  (k < NBUF)%nat ->
  m !!! Regidx (mword_of_int 10 : mword 5) = bnode k ->
  (* the block is a covered HOME block: never the log's own storage.  (The
     covered fact is also carried by the handle below; it is restated here
     because log_batch's own conjunct is what the append path must
     re-establish.) *)
  uint bno ∈ cov ->
  ~ (uint bno ∈ log_region_set logstart) ->
  (* THE FRESHNESS BOUND -- see [wp_log_write_gen_body] *)
  locks_below lks "log" ->
  sie_cap_gpr m K b p -∗
  cpu_own n eb p b lks -∗
  kernel_text -∗ pc_is pcE -∗
  panic_wp_any -∗
  bio_ctx bn (fs_view γfs γd dev cov) -∗
  log_ctx γ bn γfs cov logstart dev -∗
  (* the slot unit backing the (possible) bpin *)
  bslot bn -∗
  (* one unit of this operation's reservation, spent unconditionally *)
  log_op γ (S u) -∗
  (* the caller's own view of the block, at its OLD content *)
  fsblock γfs (uint bno) bsl -∗
  (* the checked-out buffer.  [bio_held], NOT [bio_locked]: the caller has
     typically edited the bytes, so bs <> bsl and the payload is still
     indexed at bsl. *)
  bio_held bn (fs_view γfs γd dev cov) k pidv dev bno bs bsl bsd d -∗
  wp_next b p (fun (CID : CpuId) =>
    ∀ mr,
    sie_cap_gpr mr K b p -∗
    cpu_own n eb p b lks -∗
    pc_is ret_tgt -∗
    ⌜ callee_saved m mr ⌝ -∗
    (* the unit is gone *)
    log_op γ u -∗
    (* L(bno) is now the bytes the caller wrote *)
    fsblock γfs (uint bno) bs -∗
    (* the handle re-indexed at those bytes and now DIRTY: brelse-able *)
    bio_locked bn (fs_view γfs γd dev cov) k pidv dev bno bs bsd true -∗
    (* the slot unit comes back UNCONDITIONALLY -- see the header note *)
    bslot bn -∗
    WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

Module Type LOG_WRITE.
  (* THE ATOMIC-UPDATE FORM -- the one the whole-function proof proves.
     [wp_log_write_gen] is its degenerate instance at a held fsblock, and
     [wp_log_write_sconf] forgets the credit set on top of that; both are
     kept as their own parameters so no existing caller moves. *)
  Parameter wp_log_write_au :
    forall `{!riscvGS Σ, !lockG Σ, !sieG Σ, !bioG Σ, !diskGhostG Σ, !fsLogG Σ, !logG Σ}
      `{GEN : GenId} `{CID : CpuId} (bn : bio_names)
      (γ : log_names) (γfs : fs_names) (γd : disk_names)
      (cov : gset Z) (logstart : Z) (dev : mword 32)
      (k : nat) (pidv bno : mword 32)
      (bs bsl bsd : list (bv 8)) (d : bool) (u : nat)
      (cr : bool) (Sb : gset Z) (e0 : nat) (vlb : nat)
      (Efs : coPset) (Φfsb : iProp Σ)
      (m : regfile) (n : nat) (eb : bool) (p : mword 64)
      (K : nat) (b : bool) (lks : gset string),
      wp_log_write_au_body bn γ γfs γd cov logstart dev k pidv bno
                           bs bsl bsd d u cr Sb e0 vlb Efs Φfsb m n eb p K b lks.

  (* THE EPOCH-EXPOSED GENERAL FORM (fs-log.md §G.20).  Derived from the
     atomic-update one at a held [fsblock] and the trivial anchor, and it is
     [wp_log_write_gen] that is derived from THIS, by closing the epoch. *)
  Parameter wp_log_write_gene :
    forall `{!riscvGS Σ, !lockG Σ, !sieG Σ, !bioG Σ, !diskGhostG Σ, !fsLogG Σ, !logG Σ}
      `{GEN : GenId} `{CID : CpuId} (bn : bio_names)
      (γ : log_names) (γfs : fs_names) (γd : disk_names)
      (cov : gset Z) (logstart : Z) (dev : mword 32)
      (k : nat) (pidv bno : mword 32)
      (bs bsl bsd : list (bv 8)) (d : bool) (u : nat)
      (cr : bool) (Sb : gset Z) (e0 : nat)
      (m : regfile) (n : nat) (eb : bool) (p : mword 64)
      (K : nat) (b : bool) (lks : gset string),
      wp_log_write_gene_body bn γ γfs γd cov logstart dev k pidv bno
                             bs bsl bsd d u cr Sb e0 m n eb p K b lks.

  (* THE CREDITED / GENERAL FORM.  [wp_log_write_sconf] below is the
     set-forgetting instance of this at [cr = false]; it is kept as its own
     parameter so that every existing caller -- which threads [log_op] and
     neither knows nor cares which blocks this op has logged -- is unchanged. *)
  Parameter wp_log_write_gen :
    forall `{!riscvGS Σ, !lockG Σ, !sieG Σ, !bioG Σ, !diskGhostG Σ, !fsLogG Σ, !logG Σ}
      `{GEN : GenId} `{CID : CpuId} (bn : bio_names)
      (γ : log_names) (γfs : fs_names) (γd : disk_names)
      (cov : gset Z) (logstart : Z) (dev : mword 32)
      (k : nat) (pidv bno : mword 32)
      (bs bsl bsd : list (bv 8)) (d : bool) (u : nat)
      (cr : bool) (Sb : gset Z)
      (m : regfile) (n : nat) (eb : bool) (p : mword 64)
      (K : nat) (b : bool) (lks : gset string),
      wp_log_write_gen_body bn γ γfs γd cov logstart dev k pidv bno
                            bs bsl bsd d u cr Sb m n eb p K b lks.

  Parameter wp_log_write_sconf :
    forall `{!riscvGS Σ, !lockG Σ, !sieG Σ, !bioG Σ, !diskGhostG Σ, !fsLogG Σ, !logG Σ}
      `{GEN : GenId} `{CID : CpuId} (bn : bio_names)
      (γ : log_names) (γfs : fs_names) (γd : disk_names)
      (cov : gset Z) (logstart : Z) (dev : mword 32)
      (k : nat) (pidv bno : mword 32)
      (bs bsl bsd : list (bv 8)) (d : bool) (u : nat)
      (m : regfile) (n : nat) (eb : bool) (p : mword 64)
      (K : nat) (b : bool) (lks : gset string),
      wp_log_write_sconf_body bn γ γfs γd cov logstart dev k pidv bno
                              bs bsl bsd d u m n eb p K b lks.
End LOG_WRITE.
