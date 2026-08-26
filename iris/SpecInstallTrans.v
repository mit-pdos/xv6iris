(* SpecInstallTrans.v -- the public interface of install_trans, stated
   independently of its proof.  Requires only the definitional layer --
   never a whole-function proof file -- so every function proof can be
   checked in parallel.

     static void install_trans(int recovering) {
       for (int tail = 0; tail < log.lh.n; tail++) {
         struct buf *lbuf = bread(log.dev, log.start + tail + 1);
         struct buf *dbuf = bread(log.dev, log.lh.block[tail]);
         memmove(dbuf->data, lbuf->data, BSIZE);
         bwrite(dbuf);
         if (recovering == 0) bunpin(dbuf);
         brelse(lbuf);
         brelse(dbuf);
       }
     }

   (gcc hoisted the [log.lh.n] test ahead of the prologue: at n <= 0 the
   function returns from a bare [c.ret] at +0xca having built no frame at
   all, and the printk of the recovering arm is inside the loop body.)

   THE COMMITTER-ONLY HELPER, WITH ITS FLAG AS A GHOST ARGUMENT.
   install_trans is [static]; end_op's commit calls it with recovering = 0
   and initlog's recover_from_log with recovering = 1, and both callers are
   holding the checked-out [log_state] -- the "log" spinlock is NOT held.
   The [recovering] bool is a ghost argument pinning a0 (the [either_copy]
   precedent).

   THE CONTRACT COVERS BOTH ARMS (durable-disk stage D2; the stage-2
   restriction [recovering = false \/ n = 0] is gone):
     - recovering = false, any n -- end_op's commit-time install: the
       memmove is content-preserving (the home block already holds the
       logged content, per the pure premise), L is frozen, the dirty
       entries flip at each bunpin, and one pin unit per entry comes back;
     - recovering = true, any n -- initlog's crash recovery: the home
       block holds its OLD content, so L MOVES entry by entry to the
       slots' logged contents ([it_rec_L]), nothing is pinned (the bunpin
       is skipped -- no dirty movement, no extra units), and the printk
       arm inside the loop body runs (proved against the real printk
       contract; [panic_env] already carries everything it needs).

   WHAT IT TAKES, AND WHY.  install_trans breads both blocks itself, so per
   write-set entry it wants no handle; it wants the log copy's CLIENT half
   and the log side's DIRTY half of the home block:

     [∗ list] i |-> w in W,
        fs_chalf (log_slot_bno logstart i)   (Lw i) *   (* its log copy    *)
        (uint w) |->[fs_dirty]{1/2} true

   plus the PURE tie for the home side:

     forall i w, W !! i = Some w -> L !! uint w = Some (Lw i)

   A COMMITTER-SIDE CONTRACT WITNESSES HOME CONTENT THROUGH THE AUTHORITY IT
   HOLDS, NOT THROUGH A CLIENT HALF -- a home block's [fs_chalf] is
   UNOBTAINABLE here.  The home blocks' client halves belong to the FS layer
   above by construction (log_write hands each one back to its caller, and
   [log_state] retains only the log REGION's), so end_op -- the only caller
   with a non-empty write set -- could never discharge such a premise.  What
   the committer does hold is [ghost_map_auth (fs_cache γfs) 1 L], and one
   [ghost_map_lookup] against the payload the bread returns pins the home
   block's bytes to [L !! uint w], which the pure premise identifies with
   [Lw i].  The log slot's client half stays a resource: it rides in
   [log_state], so the caller has it for free.

   Both sides therefore land at content [Lw i], which is the write_log
   invariant made a precondition: after write_log ran, log slot i holds
   exactly the logged content of W[i], and the committer's authority has
   FROZEN both ever since.  It is what makes the memmove a
   content-preserving copy and therefore makes the destination handle
   [bio_locked] again (bytes = the payload's index), which is what bwrite
   and brelse demand.  Nothing is assumed about the DISK content of either
   -- bwrite moves the home block's disk cell, which is the whole point of
   the pass.

   [ghost_map_auth (fs_cache γfs) 1 L] rides through UNCHANGED: install writes
   the DISK, not the logical view (the memmove writes bytes already equal to
   the logged content).  [ghost_map_auth (fs_dirty γfs) 1 D] does move: each
   entry's flip true -> false at its bunpin needs the authority plus both
   halves (the payload's, out of the handle, and the log side's, peeled out
   of the batch's big-op by the caller), and the post's authority is
   [dirty_clear D (map uint W)].

   SLOT ACCOUNTING.  install_trans holds two buffers at a time, so it takes
   [bslots 2]; it returns [bslots (2 + length W)].  The surplus is
   real: each entry's [bunpin] frees the pin unit that log_write's [bpin]
   absorbed, and this is where it re-enters circulation.  Its home is the
   POOL parked in [log_state] ([bslots ((LOGBLOCKS - n) + 2)]) -- the
   caller (end_op, or initlog with an empty log) deposits the surplus there
   when it re-forms the batch at n = 0, and the arithmetic is exact because
   length W = n.  Nothing of that shows here: this contract is stated in
   terms of its own two in-flight buffers and says only what it produces.

   install_trans sleeps (bread, bwrite, brelse), so it threads the full
   running-process bundle exactly as SpecBread.v does, plus the disk fabric;
   it enters and returns at noff 0.  It has no panic site of its own, but
   its callees' arms want them. *)
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
Require Import RiscvExtras.
Require Import CalleeSaved KernelText.
Require Import IntrDefs.
Require Import WpNext.
Require Import WpLock.
Require Import KernelDataInv.
Require Import SpecPanic.
Require Import SpecPrintk.  (* the recovering arm's printk *)
Require Import FdSlots.
Require Import ProcGeom.
Require Export SwtchCtx.
Require Import CpuOwn.
Require Import SchedCtx.
Require Import ProcDefs.  (* [proc_priv_bare] *)
Require Import WpUart.
Require Import DiskPtsto DiskInv.
Require Import BioInv.
Require Import FsBlocks LogInv.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import ProcAvail.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Require Import TsoCtx.
Import Defs.

(* install_trans's own frame is 10 slots ([c.addi sp,sp,-80] at +0x0c); its
   deepest callee is bread (40).  memmove/bwrite/bunpin/brelse want less. *)
Notation K_install_trans := (68%nat) (only parsing).

(* THE RECOVERED LOGICAL VIEW (durable-disk stage D2).  At recovering = 1
   the memmove is NOT content-preserving -- the home block holds its OLD
   content and the log slot holds the new one, which is the entire point of
   the pass -- so the logged-view authority MOVES: entry [i]'s home block
   goes to the slot's logged content [Lw i].  A [foldl] over the index list
   so the loop invariant is count-indexed ([it_rec_L_upto_S] below). *)
Definition it_rec_L_step (W : list (SailStdpp.Values.mword 32))
    (Lw : nat -> list (bv 8))
    (acc : gmap Z (list (bv 8))) (i : nat) : gmap Z (list (bv 8)) :=
  match W !! i with
  | Some w => <[uint w := Lw i]> acc
  | None => acc
  end.

(* the view after the first [t] entries -- the loop invariant's index *)
Definition it_rec_L_upto (W : list (SailStdpp.Values.mword 32))
    (Lw : nat -> list (bv 8)) (L : gmap Z (list (bv 8))) (t : nat)
    : gmap Z (list (bv 8)) :=
  foldl (it_rec_L_step W Lw) L (seq 0 t).

Definition it_rec_L (W : list (SailStdpp.Values.mword 32))
    (Lw : nat -> list (bv 8)) (L : gmap Z (list (bv 8)))
    : gmap Z (list (bv 8)) :=
  it_rec_L_upto W Lw L (length W).

Lemma it_rec_L_upto_0 W Lw (L : gmap Z (list (bv 8))) :
  it_rec_L_upto W Lw L 0 = L.
Proof. reflexivity. Qed.

Lemma it_rec_L_upto_S W Lw (L : gmap Z (list (bv 8))) (t : nat)
    (w : SailStdpp.Values.mword 32) :
  W !! t = Some w ->
  it_rec_L_upto W Lw L (S t) = <[uint w := Lw t]> (it_rec_L_upto W Lw L t).
Proof.
  intros Hw. rewrite /it_rec_L_upto seq_S foldl_app /=.
  rewrite /it_rec_L_step Hw //.
Qed.

Lemma it_rec_L_nil (Lw : nat -> list (bv 8)) (L : gmap Z (list (bv 8))) :
  it_rec_L [] Lw L = L.
Proof. reflexivity. Qed.

(* ITS TWO LOOKUPS (durable-disk 1a).  The recovered view is the checkout
   view with the batch's entries overwritten by their slots' contents, so a
   block the pass never wrote reads through and one it did wrote reads the
   slot -- which is what [ProofInitlog]'s boot [log_state] pack needs in
   order to prove row (b) instead of gating it.  Same shape as the mirror
   chain's [LogDefs.lm_install_miss] / [lm_install_hit], because they are
   the same pass seen through two ghosts. *)
Lemma it_map_lookup (W : list (SailStdpp.Values.mword 32)) (i : nat)
    (w : SailStdpp.Values.mword 32) :
  W !! i = Some w -> map uint W !! i = Some (uint w).
Proof.
  intro H. change (map uint W) with (uint <$> W).
  rewrite list_lookup_fmap H. reflexivity.
Qed.

Lemma it_map_lookup_inv (W : list (SailStdpp.Values.mword 32)) (j : nat)
    (b : Z) :
  map uint W !! j = Some b ->
  exists w : SailStdpp.Values.mword 32, W !! j = Some w /\ b = uint w.
Proof.
  intro H. change (map uint W) with (uint <$> W) in H.
  rewrite list_lookup_fmap in H.
  destruct (W !! j) as [w|] eqn:Hw; [| discriminate].
  cbn in H. injection H as <-. by exists w.
Qed.

Lemma it_rec_L_upto_miss (W : list (SailStdpp.Values.mword 32))
    (Lw : nat -> list (bv 8)) (L : gmap Z (list (bv 8))) (t : nat) (c : Z) :
  (forall (i : nat) (w : SailStdpp.Values.mword 32),
     (i < t)%nat -> W !! i = Some w -> uint w <> c) ->
  it_rec_L_upto W Lw L t !! c = L !! c.
Proof.
  induction t as [|t IH]; [reflexivity|]. intros Hne.
  destruct (W !! t) as [w|] eqn:Hw.
  - rewrite (it_rec_L_upto_S W Lw L t w Hw).
    rewrite lookup_insert_ne; [| exact (Hne t w ltac:(lia) Hw)].
    apply IH. intros i v Hi Hv. exact (Hne i v ltac:(lia) Hv).
  - rewrite /it_rec_L_upto seq_S foldl_app /= /it_rec_L_step Hw.
    apply IH. intros i v Hi Hv. exact (Hne i v ltac:(lia) Hv).
Qed.

(* the duplicate-freedom premise is the INJECTIVITY it is used through, not
   a [NoDup]: the bare name resolves to two different inductives in this
   tree, and every caller can supply this shape from whichever it holds. *)
Lemma it_rec_L_upto_hit (W : list (SailStdpp.Values.mword 32))
    (Lw : nat -> list (bv 8)) (L : gmap Z (list (bv 8))) (t j : nat)
    (w : SailStdpp.Values.mword 32) :
  (forall (i k : nat) (v v' : SailStdpp.Values.mword 32),
     W !! i = Some v -> W !! k = Some v' -> uint v = uint v' -> i = k) ->
  (j < t)%nat -> W !! j = Some w ->
  it_rec_L_upto W Lw L t !! uint w = Some (Lw j).
Proof.
  intros Hinj. revert j. induction t as [|t IH]; [lia|]. intros j Hj Hw.
  destruct (decide (j = t)) as [->|Hne].
  - rewrite (it_rec_L_upto_S W Lw L t w Hw) lookup_insert //.
  - destruct (W !! t) as [v|] eqn:Hv.
    + assert (Hneq : uint v <> uint w)
        by (intro Hc; exact (Hne (eq_sym (Hinj t j v w Hv Hw Hc)))).
      rewrite (it_rec_L_upto_S W Lw L t v Hv) lookup_insert_ne; [| exact Hneq].
      apply IH; [lia | exact Hw].
    + rewrite /it_rec_L_upto seq_S foldl_app /= /it_rec_L_step Hv.
      apply IH; [lia | exact Hw].
Qed.

Lemma it_rec_L_miss (W : list (SailStdpp.Values.mword 32))
    (Lw : nat -> list (bv 8)) (L : gmap Z (list (bv 8))) (c : Z) :
  (forall (i : nat) (w : SailStdpp.Values.mword 32),
     W !! i = Some w -> uint w <> c) ->
  it_rec_L W Lw L !! c = L !! c.
Proof.
  intros Hne. rewrite /it_rec_L. apply it_rec_L_upto_miss.
  intros i w _ Hw. exact (Hne i w Hw).
Qed.

Lemma it_rec_L_hit (W : list (SailStdpp.Values.mword 32))
    (Lw : nat -> list (bv 8)) (L : gmap Z (list (bv 8))) (j : nat)
    (w : SailStdpp.Values.mword 32) :
  (forall (i k : nat) (v v' : SailStdpp.Values.mword 32),
     W !! i = Some v -> W !! k = Some v' -> uint v = uint v' -> i = k) ->
  W !! j = Some w ->
  it_rec_L W Lw L !! uint w = Some (Lw j).
Proof.
  intros Hinj Hw. rewrite /it_rec_L.
  apply (it_rec_L_upto_hit W Lw L (length W) j w Hinj
           (lookup_lt_Some W j w Hw) Hw).
Qed.
Definition wp_install_trans_sconf_body
    `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !irefslotG Σ, !pavG Σ} `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}
    
    (γs : list gname) (j : nat) (γl : gname)          (* the running process *)
    (γu : uart_names) (γd : disk_names) (γk : gname)  (* disk fabric + lock  *)
    (pd pav pu : mword 64)
    (bn : bio_names)
    (γfs : fs_names) (γpr : gname)   (* the "pr" lock: the recovering arm's printk *)
    (cov : gset Z) (logstart : Z) (dev : mword 32)
    (recovering : bool)
    (n : nat) (W : list (mword 32)) (Lw : nat -> list (bv 8))
    (Bh : nat -> list (bv 8))
    (L : gmap Z (list (bv 8))) (D : gmap Z bool)
    (pidv : mword 32) (dq : dfrac)
    (m : regfile) (K : nat) (eb : bool)
    (b : bool) (R : nat -> iProp Σ) (lks : gset string) (Vpr : pprivate) :=
  let pcE : mword 64 := mword_of_int KernelSyms.install_trans in
  let pj := proc_addr j in
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5)) in
  (K_install_trans <= K)%nat ->
  (* the covered range's block-number bounds + the log region is covered:
     install_trans breads log slot [tail] as well as the home block *)
  log_geom_ok cov logstart ->
  (j < NPROC)%nat ->
  γs !! j = Some γl ->
  (* a0 is the flag *)
  m !!! Regidx (mword_of_int 10 : mword 5)
    = (mword_of_int (if recovering then 1 else 0) : mword 64) ->
  (* the batch's shape *)
  (n = length W /\ (n <= LOGBLOCKS)%nat) ->
  NoDup (map uint W) ->
  (forall w, w ∈ W -> uint w ∈ cov /\ ~ (uint w ∈ log_region_set logstart)) ->
  (* THE HOME SIDE'S CONTENT WITNESS, as a fact about the authority below:
     a client [fs_chalf] for a home block cannot be had on the committer's
     side (see the header).  COMMIT-TIME ONLY: at recovering = 1 the home
     block holds its OLD content -- the whole point of the pass -- and the
     caller supplies the home CLIENT halves instead (the [if recovering]
     row below), because at boot nobody above the log layer holds them
     yet. *)
  (recovering = false ->
   forall (i : nat) (w : SailStdpp.Values.mword 32),
     W !! i = Some w -> L !! uint w = Some (Lw i)) ->
  (* the recovering arm's home blocks are UNPINNED: a fresh era's dirty map
     holds [false] at every covered block, and the home payload's polarity
     is read off the authority install_trans holds whole *)
  (recovering = true ->
   forall w : SailStdpp.Values.mword 32, w ∈ W -> D !! uint w = Some false) ->
  (* install_trans directly breads/bwrites/brelses/bunpins, all against
     "bcache" (4); it takes no lock of its own and calls no other function
     with a lower bound, so this is the one premise its whole cone needs. *)
  locks_below lks "bcache" ->
  (* the recovering arm's printk, as a PURE Prop hypothesis (the
     [SpecIreclaim] idiom); nothing is owed at recovering = false *)
  (recovering = true -> printk_gen_contract (kt := KT1) γpr γu γd) ->
  sie_cap_gpr KT1 m K b pj -∗
  cpu_own 0 eb pj b lks -∗
  (* THE TRAP-CSR COMPLEMENT, NOT THE BARE PAIR.  install_trans has NO
     acquire/release of its own -- it delegates entirely to bread/bwrite, so
     a parking thread must hand [trap_csrs]/[cpu_claim] across the crossing
     exactly as [SpecBwrite.v] does: at [eb = true] this is [emp] (the
     callee's own acquire mints what it needs) and at [eb = false] it is the
     honest pair, held because the TRAP handed it over.  See
     claude-notes/completed/eb-generic-sweep.md. *)
  trap_csrs_ext KT1 eb -∗
  cpu_claim_ext eb pj -∗
  kernel_text -∗ kernel_data -∗ pc_is pcE -∗
  panic_env -∗
  (* ...and the printk credential itself, on the recovering arm only.
     Boxed, so a proof can park it in the intuitionistic context without
     case-splitting the flag. *)
  □ (if recovering then printk_env γpr γu γd else emp) -∗
  bio_ctx bn (fs_view γfs γd dev cov) -∗
  (* NOT [log_ctx]: this helper holds no lock -- see LogInv.log_frozen *)
  log_frozen logstart dev -∗
  proc_priv_bare pj pidv Vpr -∗
  (* the running-thread bundle *)
  procs_inv γs -∗
  (* the disk fabric *)
  dev_inv γu γd -∗
  disk_geom γd pd pav pu -∗
  is_lock γk d_lock "virtio_disk"%string (λ ξ : CtxId, disk_res (XI := ξ) γd pd pav pu) -∗
  (* ---- the checked-out batch's pieces install_trans touches ---- *)
  (* the in-memory header, READ ONLY (the write set it walks) *)
  lh_n_pa ↦₄ (mword_of_int (Z.of_nat n) : mword 32) -∗
  ([∗ list] i ↦ w ∈ W, lh_block i ↦₄ w) -∗
  (* the logged view's authority: FROZEN at commit time (install writes the
     disk, not L); at recovering = 1 it MOVES, entry by entry, to the slots'
     logged contents ([it_rec_L] -- see its header) *)
  (* THE BYTE VIEW'S ROW (durable-disk 1c-flip step 3/5).  ONLY THE
     RECOVERING ARM uses it, and that arm is the one place in the tree
     where a HOME block's owner-side resource is moved from outside the
     file system: recovery installs the on-disk log's write set over the
     home blocks, so their content really does change and both maps have
     to follow it.  (1a made recovery a ghost no-op for the MIRROR, not for
     the block layer's two content maps; the flip's step 5 asked whether
     the arm could hold nothing, and it cannot -- the mint indexes the byte
     view at the CRASHED disk.)  So the arm now holds each home block's
     EXCLUSIVE byte run and moves it with [FsBlocks.fsblock_update],
     opening [logN] for the crossing; the row is persistent and both
     callers have one (end_op off [LogInv.log_ctx], initlog off fsinit's
     own). *)
  fs_bytes_any γfs -∗
  ghost_map_auth (fs_cache γfs) 1 L -∗
  (* the pinned-set authority: exactly W's entries go back to false at
     commit time; nothing moves at recovery (nothing is pinned in a fresh
     era, and the bunpin is skipped) *)
  ghost_map_auth (fs_dirty γfs) 1 D -∗
  (* per entry: the LOG COPY's client half at the logged content
     (write_log's postcondition, frozen by the authority above), plus
       - commit time: the log side's dirty half of the home block (the
         home content itself comes from the authority, per the pure
         premise -- a client half cannot be had on the committer's side);
       - recovery: the home block's CLIENT half, at whatever the crash
         left there ([Bh i]) -- at boot the log layer still holds every
         covered block's client half, and the L update is what moves it. *)
  ([∗ list] i ↦ w ∈ W,
     fs_chalf γfs (log_slot_bno logstart i) (Lw i) ∗
     (if recovering then fsblock (fs_bytes γfs) (uint w) (Bh i)
      else (uint w) ↪[fs_dirty γfs]{#(1/2)} true)) -∗
  (* two slot units: it holds lbuf and dbuf at the same time *)
  bslots 2 -∗
  (* THE CRASH PERMITS for the home writes (phase C2b/D1 stage 4).  One per
     entry -- but the entries' fupds are SEQUENTIAL, each consuming the
     era-side resource the previous one returned (for the FS client that is
     the log-region mirror half, which is what tells a fupd that the on-disk
     header still names the block it is about to overwrite).  A big-op of
     independent permits could therefore never be supplied: there is one
     such resource, not [n] of them.  So the premise is a REUSABLE GENERATOR
     over the one threaded resource [R], persistent and instantiated at each
     entry in turn; [R] itself is opaque here, which keeps install_trans as
     crash-agnostic as the rest of the log proofs.
     Each generated permit is the SEQUENTIAL one (sector-atomic-disk.md
     §6e): a home block lands one 512-byte sector at a time, and the chain
     threads [R] from one landing to the next.
     THE GENERATOR IS CURSOR-INDEXED (durable-disk flip-B): entry [i]
     consumes [R i] and returns [R (S i)], because a VALUE-chained client
     -- end_op's committer, which carries a picture of the whole durable
     disk -- moves to a different resource at every entry
     ([FsCrash.fs_install_v_seq_permit] at
     [R i := log_mirror_half (Mi i)], the chained [lm_upd]s).  The
     at-form's single [R] is the constant family.  The bytes are NOT
     quantified either: install_trans writes exactly the log copy's
     content [Lw i] (the memmove is a copy of the slot), so naming them
     is what lets the client's [Q] mention them.  Its [▷] is what the
     bwrite's own [▷ Q] postcondition hands back, and a client whose [R]
     is timeless -- the mirror half is -- strips it inside the fupd.) *)
  □ (∀ (i : nat) (w : SailStdpp.Values.mword 32),
       ⌜W !! i = Some w⌝ -∗ ⌜length (Lw i) = 1024%nat⌝ -∗ ▷ R i -∗
       disk_seq_permit gen_id (Some ((1024 * uint w)%Z, Lw i)) (R (S i))) -∗
  ▷ R 0%nat -∗
  (* THE CROSSING IS THE LITERAL [true], NOT [b].  This function can SLEEP
     (its bread / ilock / bwrite does), and a park moves the hart with
     interrupts off, so the crossing has nothing to do with SIE -- the
     porting guide's "a PARKING function's [wp_next] index is [true]
     UNCONDITIONALLY".  Spelled [b] the two would coincide at [eb = true] --
     which is why this went unnoticed while [eb = true] was forced -- but at
     [eb = false] the [b] form would promise the caller it comes back on the
     hart it called from, which a park makes false. *)
  wp_next true pj (fun (CID : CpuId) =>
  ∀ (mf : regfile),
      ⌜callee_saved m mf⌝ -∗
      sie_cap_gpr KT1 mf K b pj -∗
      cpu_own 0 eb pj b lks -∗
      trap_csrs_ext KT1 eb -∗
      cpu_claim_ext eb pj -∗
      pc_is ret_tgt -∗
      proc_priv_bare pj pidv Vpr -∗
      (* the in-memory header, unchanged (lh.n := 0 is the CALLER's store) *)
      lh_n_pa ↦₄ (mword_of_int (Z.of_nat n) : mword 32) -∗
      ([∗ list] i ↦ w ∈ W, lh_block i ↦₄ w) -∗
      ghost_map_auth (fs_cache γfs) 1
        (if recovering then it_rec_L W Lw L else L) -∗
      ghost_map_auth (fs_dirty γfs) 1
        (if recovering then D else dirty_clear D (map uint W)) -∗
      ([∗ list] i ↦ w ∈ W,
         fs_chalf γfs (log_slot_bno logstart i) (Lw i) ∗
         (if recovering then fsblock (fs_bytes γfs) (uint w) (Lw i)
          else (uint w) ↪[fs_dirty γfs]{#(1/2)} false)) -∗
      (* the two units back, PLUS -- at commit time -- one per entry: each
         bunpin frees the pin unit log_write's bpin absorbed.  The bunpin
         is SKIPPED at recovery, so nothing extra comes back there. *)
      bslots (2 + (if recovering then 0%nat else length W)) -∗
      (* the threaded resource, back from the last entry's DMA completion *)
      ▷ R n -∗
      WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

Module Type INSTALL_TRANS.
  Parameter wp_install_trans_sconf :
    forall `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !irefslotG Σ, !pavG Σ} `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}
      
      (γs : list gname) (j : nat) (γl : gname)
      (γu : uart_names) (γd : disk_names) (γk : gname)
      (pd pav pu : mword 64)
      (bn : bio_names)
      (γfs : fs_names) (γpr : gname)
      (cov : gset Z) (logstart : Z) (dev : mword 32)
      (recovering : bool)
      (n : nat) (W : list (mword 32)) (Lw : nat -> list (bv 8))
      (Bh : nat -> list (bv 8))
      (L : gmap Z (list (bv 8))) (D : gmap Z bool)
      (pidv : mword 32) (dq : dfrac)
      (m : regfile) (K : nat) (eb : bool)
      (b : bool) (R : nat -> iProp Σ) (lks : gset string) (Vpr : pprivate),
      wp_install_trans_sconf_body γs j γl γu γd γk pd pav pu bn γfs γpr
                                  cov logstart dev recovering n W Lw Bh L D
                                  pidv dq m K eb b R lks Vpr.
End INSTALL_TRANS.
