(* LogInv.v -- the log layer's lock invariant: struct log's geometry, the
   reservation LEDGER, the batch bundle the committer checks out, and the
   ghost transitions begin_op / log_write / end_op perform.

   Design: claude-notes/design/fs-log.md.  The shape in one paragraph: the
   "log" spinlock seals [log_res].  Always inside: the outstanding /
   committing / ncommit cells, and the ledger -- a ghost map op-id ->
   REMAINING BUDGET whose auth ties the outstanding cell (its size) and
   whose per-entry bound (<= MAXOPBLOCKS) and sum tie
   (lh.n + op_sum <= LOGBLOCKS) make begin_op's guard a mint, kill
   log_write's "too big a transaction" panic, and stay inductive.  A FLAT
   units counter does NOT work: at end_op the global bound
   units <= out * MAXOPBLOCKS cannot be re-established (the returning
   op's budget and the others' are indistinguishable to an auth-nat), so
   the ledger keeps the per-op structure -- which is also exactly the C
   code's own reservation argument.
   Conditionally inside (cmt = false): [log_state] -- the lh cells with
   their write-set reading W, BOTH FsBlocks auths (the freeze-by-auth
   that makes log_write and the committer the ONLY writers of the logged
   view), the log-side dirty halves recording exactly W's membership over
   the whole covered range, and the log-region + header client halves.
   end_op's last-out path flips cmt := 1 and takes [log_state] out
   linearly, mirroring the code running commit with no locks held;
   begin_op sleeps on cmt, so out stays 0 across a commit, and
   ⌜cmt = true -> out = 0⌝ rides as a pure conjunct (what kills end_op's
   own "log.committing" panic: an op token in hand forces out >= 1). *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import auth gmap gset frac.
From iris.base_logic.lib Require Import ghost_map ghost_var invariants mono_nat.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvModelBytes.
Require Import RiscvLang.   (* [GenId]/[gen_id]: [log_ctx]'s swap receipt *)
Require Import RiscvPtsto.
Require Import WpLock.
Require Import BioDefs.
Require Import FsBlocks.
(* BLOCK 1'S PARK (durable-disk lane C-3a).  A one-predicate file, not the
   pure wf layer the next comment is about: it carries the superblock
   block's byte run and the single local fact that run can state.  It is a
   conjunct of [log_ctx] because [log_ctx] is the ONLY persistent bundle
   [SpecEndOp.wp_end_op] holds, and the commit's collection has to reach
   block 1 (durable-fs-plan.md section 4, gap (C) in FsCollect.v). *)
Require Import SbPark.
(* THE FILE SYSTEM'S LAW (durable-disk C-8).  The commit RECONSTRUCTS the
   file-system predicate at quiescence and the WAL stays file-system
   agnostic: what it holds is a PERSISTENT, PURE-FACT-PRODUCING law, parked
   here beside block 1 and never looked inside.  The file it lives in is a
   LEAF over [FsDurSnap] -- the WAL's cone gains the snapshot's PREDICATE
   and nothing above it. *)
Require Import LogSnapLaw.
(* NOTHING IN THE CRASH/LOG LAYER IMPORTS THE PURE WF LAYER any more
   (durable-disk 1d).  [FsImg]/[FsWf]/[FsObj*] were here for row (a) --
   "the logged view is the committed view except at the pending objects" --
   which ruling 3 (claude-notes/design/fs-state.md) deletes outright: there
   is no abstract committed picture, no whole-state well-formedness and no
   per-op finalize.  What the log parks instead is the client's own OPAQUE
   payload, which it never reads. *)
Require Export LogDefs.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
(* The [set_solver] override.  EXPORT, not Import: this import is         *)
(* deliberately "dead" -- the file compiles without it, just far slower --  *)
(* and the nightly dead-import sweep skips [Require Export] lines.         *)
(* It has to be HERE rather than inherited: [Require Export] only          *)
(* propagates through an unbroken chain of Exports, and this tree's        *)
(* intermediate files use [Require Import], so nothing downstream inherits *)
(* it.  See FastSetSolver.v.                                              *)
Require Export FastSetSolver.
Require Export Xv6Cameras.  (* the cameras this file states its theory over *)
Local Open Scope Z_scope.

(* ------------------------------------------------------------------ *)
(*  Geometry (offsets confirmed against kernel-rocq/KernelInstrs.v):    *)
(*  struct log @ KernelSyms.log: spinlock@0 (24B), start@24,            *)
(*  outstanding@28, committing@32, dev@36, ncommit@40, lh.n@44,         *)
(*  lh.block[i]@48+4i (LOGBLOCKS = 30 entries).                         *)
(* ------------------------------------------------------------------ *)

Definition MAXOPBLOCKS : nat := 10%nat.

Definition log_addr : mword 64 := mword_of_int KernelSyms.log.
Definition log_pa : Arch.pa := log_addr.

Definition l_start   : Arch.pa := pa_add log_pa 24.
Definition l_out     : Arch.pa := pa_add log_pa 28.
Definition l_cmt     : Arch.pa := pa_add log_pa 32.
Definition l_dev     : Arch.pa := pa_add log_pa 36.
Definition l_ncommit : Arch.pa := pa_add log_pa 40.
Definition lh_block (i : nat) : Arch.pa := pa_add log_pa (48 + 4 * i)%nat.
Definition lh_n_pa   : Arch.pa := pa_add log_pa 44.

(* ------------------------------------------------------------------ *)
(*  Pure vocabulary the log.c CONTRACTS need (Spec*.v, stage 2).        *)
(*  Definitions only -- nothing here changes any statement above.       *)
(* ------------------------------------------------------------------ *)

(* THE HEADER'S [n] FIELD, as a pure function of the header block's bytes.
   [struct logheader] starts with [int n], so the field is the first
   little-endian 32-bit word of the block -- which is exactly what
   write_head stores at [buf->data + 0] and what initlog's inlined
   read_head loads back from [88(a0)].  Total by construction (a short
   list simply assembles fewer bytes), and deliberately PARTIAL as a
   header decoder: stage 2 only ever needs the [n] field (initlog's
   clean-image premise [hdr_n = 0] and write_head's [hdr_n = n]).  The
   full (n, W) on-disk encoding is stage 4's business -- see
   claude-notes/design/fs-log.md, "Stage 4 -- the crash side". *)
Lemma hdr_n_lt (bs : list (bv 8)) : hdr_n bs < 2 ^ 32.
Proof.
  rewrite /hdr_n.
  pose proof (assemble_bytes_bound (take 4 bs)) as [_ Hhi].
  eapply Z.lt_le_trans; [exact Hhi|].
  apply Z.pow_le_mono_r; [lia|].
  assert (Hl : (length (take 4 bs) <= 4)%nat).
  { rewrite length_take. lia. }
  lia.
Qed.

(* THE BLOCK-NUMBER BOUNDS every log function's interior [bread]s need:
   bread's own arithmetic premise is [uint bno < 2^31] (its sector
   computation doubles the block number in 32 bits), and block 0 is never
   a client block (binit leaves all thirty buffers claiming blockno 0, so
   [bio_init] demands 0 ∉ cov). *)
Definition cov_ok (cov : gset Z) : Prop :=
  forall z : Z, z ∈ cov -> 0 < z < 2 ^ 31.

(* The log's own storage is part of the covered range: the log layer is
   the CLIENT of the header block and the LOGBLOCKS slots (log_state holds
   their [fs_chalf] halves), and write_head / write_log / install_trans
   [bread] them, which needs them covered. *)
Definition log_geom_ok (cov : gset Z) (logstart : Z) : Prop :=
  cov_ok cov /\ log_region_set logstart ⊆ cov.

(* install_trans's effect on the dirty authority: exactly the installed
   write set goes back to false, everything else is untouched. *)
Definition dirty_clear (D : gmap Z bool) (ws : list Z) : gmap Z bool :=
  foldr (fun z m => <[z := false]> m) D ws.

Lemma dirty_clear_in (D : gmap Z bool) (ws : list Z) (z : Z) :
  z ∈ ws -> dirty_clear D ws !! z = Some false.
Proof.
  induction ws as [|w ws IH]; [inversion 1|].
  rewrite elem_of_cons. intros [->|Hz]; cbn [dirty_clear foldr].
  - by rewrite lookup_insert.
  - destruct (decide (w = z)) as [->|Hne].
    + by rewrite lookup_insert.
    + rewrite lookup_insert_ne //. by apply IH.
Qed.

Lemma dirty_clear_out (D : gmap Z bool) (ws : list Z) (z : Z) :
  ~ (z ∈ ws) -> dirty_clear D ws !! z = D !! z.
Proof.
  induction ws as [|w ws IH]; [done|].
  rewrite elem_of_cons. intros Hz. cbn [dirty_clear foldr].
  rewrite lookup_insert_ne; [| intros ->; apply Hz; by left].
  apply IH. intros Hin. apply Hz. by right.
Qed.

(* ------------------------------------------------------------------ *)
(*  The ledger's ghost + pure theory                                    *)
(* ------------------------------------------------------------------ *)

(* A LEDGER ENTRY: the op's remaining budget, and THE SET OF BLOCKS IT HAS
   ALREADY APPENDED to lh.block[] in this batch.

   The set is what makes log ABSORPTION free.  xv6's log_write scans
   lh.block[] and, when the block is already there, does NOT grow lh.n --
   so a second write of a block a transaction has already logged costs the
   log nothing, and charging the caller a budget unit for it is a pure
   over-approximation.  It was a harmless one until itrunc: that function
   frees up to NDIRECT + NINDIRECT + 1 = 269 blocks, every one of them a bit
   in THE SAME bitmap block (FSSIZE = 2000 < BPB = 8192), so the real cost
   is 2 blocks -- one bitmap, one inode -- while always-consume accounting
   demands 270 units against a MAXOPBLOCKS of 10.  itrunc is not provable
   without the credit, and the C code is not wrong; the accounting was.

   WHY THE SET LIVES IN THE OP ENTRY, rather than in a free-floating token.
   The credit is only sound while the block really is in lh.block[], and
   lh.block[] is cleared at commit.  Any client-held witness must therefore
   be revoked by then -- and the ONE handle the log has on a client's
   resources at commit time is the op entry itself, which end_op collects
   ([log_end_step]) and whose absence is what lets commit run at all
   ([cmt = true -> out = 0]).  A token that outlived end_op would still be
   presentable in the NEXT batch, where the block is no longer logged, and
   the absorb arm would then skip a spend while lh.n actually grew.  So the
   set is a field of the entry, and it dies with it. *)
(* ...AND THE BIRTH EPOCH, which is how §G's group extension stays
   revocation-sound WITHOUT revoking anything (fs-log.md §G.2/§G.9).  The
   entry records the epoch it was minted in; [log_res]'s auth invariant
   pins every LIVE entry's [e0] to the current epoch, and the bump at the
   commit re-deposit cannot falsify that because [out = 0] there forces
   [om = ∅].  A witness from an older batch then has [e < e0] of every
   later op and is simply unusable -- indexing instead of revocation.

   NOTE THE RE-ASSOCIATION: [(nat * gset Z * nat)] is
   [((nat * gset Z) * nat)], so the budget is [e.1.1], the already-logged
   set is [e.2] and the birth epoch is [e.2]. *)
(* [op_entry] and [logG] are defined in Xv6Cameras.v; the argument for
   both the SET and the EPOCH field is above.  The epoch reads the
   AMBIENT [mono_natG] off [riscvGS] ([riscvF_genGS], RiscvPtsto.v)
   rather than minting a second instance -- a second [mono_natG] in one
   context is the duplicate-class trap of claude-notes/durable-notes.md:
   the two make propositions that print character-for-character
   identically fail to unify. *)

(* the sum of all remaining budgets -- the SETS play no part in the tie *)
Definition op_sum (om : gmap nat op_entry) : nat :=
  map_fold (fun _ e acc => (e.1.1 + acc)%nat) 0%nat om.

Lemma op_sum_empty : op_sum ∅ = 0%nat.
Proof. reflexivity. Qed.

Lemma op_sum_insert (om : gmap nat op_entry) (i : nat) (e : op_entry) :
  om !! i = None ->
  op_sum (<[i := e]> om) = (e.1.1 + op_sum om)%nat.
Proof.
  intros Hi. rewrite /op_sum.
  apply (map_fold_insert_L
           (fun (_ : nat) (e : op_entry) (acc : nat) => (e.1.1 + acc)%nat));
    [|exact Hi].
  intros j1 j2 z1 z2 y _ _ _. lia.
Qed.

Lemma op_sum_delete (om : gmap nat op_entry) (i : nat) (e : op_entry) :
  om !! i = Some e ->
  op_sum om = (e.1.1 + op_sum (delete i om))%nat.
Proof.
  intros Hi.
  rewrite -{1}(insert_delete om i e Hi).
  apply op_sum_insert, lookup_delete.
Qed.

(* the conservative bound begin_op's guard reasons with: every entry is
   at most b, so the sum is at most size * b *)
Lemma op_sum_bound (om : gmap nat op_entry) (b : nat) :
  (forall i e, om !! i = Some e -> (e.1.1 <= b)%nat) ->
  (op_sum om <= size om * b)%nat.
Proof.
  induction om as [|i e om Hi IH] using map_ind.
  { intros _. rewrite op_sum_empty map_size_empty. lia. }
  intros Hb.
  rewrite op_sum_insert // map_size_insert_None //.
  assert (Hu : (e.1.1 <= b)%nat).
  { apply (Hb i). rewrite lookup_insert //. }
  assert (Hrest : (op_sum om <= size om * b)%nat).
  { apply IH. intros j v Hj. apply (Hb j).
    rewrite lookup_insert_ne; [exact Hj|].
    intros ->. rewrite Hi in Hj. discriminate. }
  lia.
Qed.

(* SPENDING at an entry whose budget is a successor: the sum drops by one.
   Stated on the ENTRY so the set component is free to change at the same
   time, which is exactly what the append path does. *)
Lemma op_sum_spend (om : gmap nat op_entry) (i u : nat) (Sb Sb' : gset Z)
    (e0 : nat) :
  om !! i = Some (S u, Sb, e0) ->
  op_sum (<[i := (u, Sb', e0)]> om) = (op_sum om - 1)%nat.
Proof.
  intros Hi.
  assert (Hj : <[i := (u, Sb', e0)]> om !! i = Some (u, Sb', e0))
    by apply lookup_insert.
  rewrite (op_sum_delete om i (S u, Sb, e0) Hi).
  rewrite (op_sum_delete (<[i := (u, Sb', e0)]> om) i (u, Sb', e0) Hj).
  rewrite delete_insert_delete. cbn. lia.
Qed.

(* ABSORBING changes the set only, so the sum is untouched -- which is the
   whole point: the tie [n + op_sum om <= LOGBLOCKS] survives a log_write
   that does not grow [n]. *)
Lemma op_sum_absorb (om : gmap nat op_entry) (i u : nat) (Sb Sb' : gset Z)
    (e0 : nat) :
  om !! i = Some (u, Sb, e0) ->
  op_sum (<[i := (u, Sb', e0)]> om) = op_sum om.
Proof.
  intros Hi.
  assert (Hj : <[i := (u, Sb', e0)]> om !! i = Some (u, Sb', e0))
    by apply lookup_insert.
  rewrite (op_sum_delete om i (u, Sb, e0) Hi).
  rewrite (op_sum_delete (<[i := (u, Sb', e0)]> om) i (u, Sb', e0) Hj).
  rewrite delete_insert_delete. reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  THE OPEN OPS' PENDING BLOCK SET                                     *)
(*                                                                     *)
(*  The union of every LIVE operation's already-logged BLOCK set.  It   *)
(*  is [log_state]'s [pend] parameter, and nothing in the bundle reads  *)
(*  it: ruling 3 (claude-notes/design/fs-state.md) has no row (a), so   *)
(*  there is no agreement for a pending set to except.  flip-C1's       *)
(*  OBJECT union is deleted with the row it existed for.                *)
(*                                                                     *)
(*  Stated as a [map_fold] rather than a union over [map_to_list] so    *)
(*  every law below is one [map_fold_weak_ind], and so that it is       *)
(*  spelled the way [op_sum] above is.  Everything is derived from the  *)
(*  MEMBERSHIP characterisation [op_pending_elem_of]; nothing unfolds   *)
(*  the fold at a use site, and no law reaches for [set_solver] on a    *)
(*  whole map (durable-notes.md's set_solver rules).                    *)
(* ------------------------------------------------------------------ *)
Definition op_pending (om : gmap nat op_entry) : gset Z :=
  map_fold (fun _ e acc => e.1.2 ∪ acc) ∅ om.

Lemma op_pending_empty : op_pending ∅ = ∅.
Proof. reflexivity. Qed.

(* THE CHARACTERISATION.  Every other law is a corollary. *)
Lemma op_pending_elem_of (om : gmap nat op_entry) (b : Z) :
  b ∈ op_pending om <-> exists i e, om !! i = Some e /\ b ∈ e.1.2.
Proof.
  rewrite /op_pending.
  apply (map_fold_weak_ind
           (fun (r : gset Z) (m : gmap nat op_entry) =>
              b ∈ r <-> exists i e, m !! i = Some e /\ b ∈ e.1.2)).
  - split.
    + intros Hb. exfalso. exact (not_elem_of_empty b Hb).
    + intros (i & e & Hi & _). rewrite lookup_empty in Hi. discriminate.
  - intros i e m r Hi IH. split.
    + intros Hb. apply elem_of_union in Hb as [Hb | Hb].
      * exists i, e. rewrite lookup_insert. done.
      * apply IH in Hb as (j & e' & Hj & Hb).
        exists j, e'. rewrite lookup_insert_ne; [done|].
        intros ->. rewrite Hi in Hj. discriminate.
    + intros (j & e' & Hj & Hb).
      destruct (decide (j = i)) as [->|Hne].
      * rewrite lookup_insert in Hj. injection Hj as <-.
        apply elem_of_union_l. exact Hb.
      * rewrite lookup_insert_ne in Hj; [| exact (not_eq_sym Hne)].
        apply elem_of_union_r. apply IH. exists j, e'. done.
Qed.

(* a live entry's set is pending *)
Lemma op_pending_lookup (om : gmap nat op_entry) (i : nat) (e : op_entry) :
  om !! i = Some e -> e.1.2 ⊆ op_pending om.
Proof.
  intros Hi b Hb. apply op_pending_elem_of. exists i, e. done.
Qed.

(* THE MONOTONICITY LAW THE THREE GROWING TRANSITIONS USE.  [begin_op]'s
   mint (premise vacuous -- [om !! i = None]) and both of [log_write]'s
   ledger steps (the entry's set only grows) are instances; ONE lemma
   rather than an insert/update pair, because the two differ only in how
   the premise is discharged. *)
Lemma op_pending_insert_mono (om : gmap nat op_entry) (i : nat)
    (e' : op_entry) :
  (forall e, om !! i = Some e -> e.1.2 ⊆ e'.1.2) ->
  op_pending om ⊆ op_pending (<[i := e']> om).
Proof.
  intros Hgrow b Hb. apply op_pending_elem_of.
  apply op_pending_elem_of in Hb as (j & e & Hj & Hb).
  destruct (decide (j = i)) as [->|Hne].
  - exists i, e'. rewrite lookup_insert. split; [reflexivity|].
    exact (Hgrow e Hj b Hb).
  - exists j, e. rewrite lookup_insert_ne; [done | exact (not_eq_sym Hne)].
Qed.

(* THE SHRINKING LAW: [end_op]'s retire.  Stated as the exact split rather
   than as a bare inclusion, because that is the shape stage G's per-op
   preservation obligation is discharged against -- the retiring entry's
   own set is the only thing that leaves the pending union. *)
Lemma op_pending_delete (om : gmap nat op_entry) (i : nat) (e : op_entry) :
  om !! i = Some e ->
  op_pending om ⊆ e.1.2 ∪ op_pending (delete i om).
Proof.
  intros Hi b Hb.
  apply op_pending_elem_of in Hb as (j & e' & Hj & Hb).
  destruct (decide (j = i)) as [->|Hne].
  - rewrite Hi in Hj. injection Hj as <-. apply elem_of_union_l. exact Hb.
  - apply elem_of_union_r. apply op_pending_elem_of.
    exists j, e'. rewrite lookup_delete_ne; [done | exact (not_eq_sym Hne)].
Qed.

Lemma op_pending_delete_subseteq (om : gmap nat op_entry) (i : nat) :
  op_pending (delete i om) ⊆ op_pending om.
Proof.
  intros b Hb. apply op_pending_elem_of.
  apply op_pending_elem_of in Hb as (j & e & Hj & Hb).
  rewrite lookup_delete_Some in Hj. exists j, e. tauto.
Qed.

Section LogInv.
  Context `{!riscvGS Σ, !lockG Σ, !diskGhostG Σ, !bioG Σ, !bioslotG Σ, !fsLogG Σ, !logG Σ}.
  (* the ambient generation: [log_ctx] carries this era's SWAP RECEIPT, which
     is what every WAL fupd curries to prove the crash record's arm is its
     own ([FsCrash.fs_arm_acc]).  Implicit, so no spec statement changes. *)
  Context `{GEN : GenId}.

  (* ---------------------------------------------------------------- *)
  (*  An active operation                                              *)
  (* ---------------------------------------------------------------- *)

  (* THE CLIENT-SIDE EPOCH LOWER BOUND (fs-log.md §G.3/§G.13), defined HERE
     rather than beside its two auth lemmas because [log_opSe] bundles it.
     "the batch epoch has reached [e]": PERSISTENT and monotone, so a copy
     taken under the log lock stays true forever outside it -- which is the
     whole point, since a PARKER does not hold the log spinlock and can
     never read the auth. *)
  Definition log_epoch_lb (γ : log_names) (e : nat) : iProp Σ :=
    mono_nat_lb_own (ln_ep γ) e.

  Global Instance log_epoch_lb_persistent γ e : Persistent (log_epoch_lb γ e).
  Proof. apply _. Qed.

  Global Instance log_epoch_lb_timeless γ e : Timeless (log_epoch_lb γ e).
  Proof. apply _. Qed.

  (* MINTING, where the auth is open (every log ghost step, and begin_op's
     in particular).  Free: the auth is handed straight back. *)
  Lemma log_epoch_lb_get (γ : log_names) (E : nat) :
    mono_nat_auth_own (ln_ep γ) 1 E -∗
    mono_nat_auth_own (ln_ep γ) 1 E ∗ log_epoch_lb γ E.
  Proof.
    iIntros "Ha".
    iDestruct (mono_nat_lb_own_get with "Ha") as "#Hlb".
    iFrame "Ha". iApply "Hlb".
  Qed.

  (* ...and USING one, back under the auth: the bound is real. *)
  Lemma log_epoch_lb_le (γ : log_names) (E e : nat) :
    mono_nat_auth_own (ln_ep γ) 1 E -∗ log_epoch_lb γ e -∗ ⌜(e <= E)%nat⌝.
  Proof.
    iIntros "Ha Hl".
    iDestruct (mono_nat_lb_own_valid with "Ha Hl") as %[_ Hle]. done.
  Qed.

  (* one ledger entry with remaining budget u AND the blocks this op has
     already appended; the id is existential -- no client ever needs it,
     and the ghost steps below re-locate the entry by ownership. *)
  (* THE NAMED FORM: the same entry ownership with the birth epoch EXPOSED.
     [log_use_group] cannot be stated without it -- the client has to write
     [e0 <= e] -- and it must NOT be a separate persistent token: such a
     token outlives its op, so a stale small [e0] would admit a stale
     witness and re-open exactly the hole the header's revocation argument
     closes (fs-log.md §G.9, FINDING 1).  Exposing it on the LINEAR entry
     is what keeps it honest: holding this IS holding the live entry.

     ...AND IT CARRIES THE LOWER BOUND (§G.13).  [log_epoch_lb γ e0] is the
     formal referent of §G.4's "the walker's open op freezes the epoch": a
     client outside the log lock can never mint one, and [log_begin_step] is
     the universal point where every op passes with the auth open, so the
     bound is minted there and rides the entry for the op's whole life.
     The bundle is ABI-INVISIBLE because the lb is PERSISTENT: [log_opS]'s
     arity is untouched, every conversion below holds verbatim, and the
     only ghost step that pays for it is the mint itself.  A LOWER bound
     also needs no revocation -- unlike the refuted persistent birth-epoch
     token, a stale copy stays TRUE, and truth is all it claims.

     ...AND IT CARRIES GENESIS-POSITIVITY (fs-log.md §G.20).  [⌜1 <= e0⌝]
     is what kills the region receipt's [⌜v = 0⌝] boot corner at
     [InodeRegion.ireg_ep_use] -- records nobody has ever observed -- and
     NOTHING ELSE CAN CARRY IT to a client: [log_epoch_lb γ e0] bounds
     [e0] from below, and the only lb a context holder could mint on its
     own would be about the CURRENT epoch, not this op's birth.  It is
     free at the mint ([log_begin_step], where the ledger authority's own
     [⌜1 <= E⌝] clause and [e0 = E] give it), pure, and therefore
     ABI-invisible: every landed caller stays byte-stable. *)
  Definition log_opSe (γ : log_names) (u : nat) (Sb : gset Z) (e0 : nat)
    : iProp Σ :=
    ((∃ i : nat, i ↪[ln_ops γ] (u, Sb, e0)) ∗
     log_epoch_lb γ e0 ∗ ⌜(1 <= e0)%nat⌝)%I.

  (* the lb read off an entry, which is what a parker/observer actually
     carries out of the op's scope *)
  Lemma log_opSe_lb (γ : log_names) (u : nat) (Sb : gset Z) (e0 : nat) :
    log_opSe γ u Sb e0 -∗ log_epoch_lb γ e0.
  Proof. iIntros "(_ & #H & _)". iApply "H". Qed.

  (* ...and GENESIS-POSITIVITY, the conjunct's whole purpose: an op's birth
     epoch is at least one, so an observation counter's "never observed"
     zero can never be an epoch this op could have written in. *)
  Lemma log_opSe_pos (γ : log_names) (u : nat) (Sb : gset Z) (e0 : nat) :
    log_opSe γ u Sb e0 -∗ ⌜(1 <= e0)%nat⌝.
  Proof. iIntros "(_ & _ & %H)". iPureIntro. exact H. Qed.

  (* ...AND THE FROZEN ABI.  Three arguments, exactly as before: every
     landed threader ([ProofWritei], [ProofItrunc], [ProofDirlink], and the
     begin/end pair) stays byte-stable, because a client that does not
     compare epochs never names one. *)
  Definition log_opS (γ : log_names) (u : nat) (Sb : gset Z) : iProp Σ :=
    (∃ e0 : nat, log_opSe γ u Sb e0)%I.

  (* THE FORM EVERY EXISTING CALLER USES.  Forgetting the set is what keeps
     this change additive: balloc, bmap, iupdate, writei, begin_op and
     end_op all thread [log_op] and are untouched, because a budget claim
     that says nothing about which blocks were logged is exactly the old
     contract.  Only the two arms that CLAIM the absorption credit --
     log_write's and bfree's -- mention [log_opS], and only itrunc, which
     needs the credit to survive 269 frees, threads it. *)
  Definition log_opb (γ : log_names) (u : nat) : iProp Σ :=
    (∃ Sb : gset Z, log_opS γ u Sb)%I.

  (* ---------------------------------------------------------------- *)
  (*  THE OPEN TRANSACTION (durable-disk lane A, plan section 3)       *)
  (* ---------------------------------------------------------------- *)

  (* One element of [ln_tx] per transaction that is open right now, at the
     unit value -- the element says only that its id EXISTS.  It is minted
     by begin_op and consumed WHOLE by end_op, and while an inode's
     well-formedness row is suspended the element is parked in the locked
     registry ([InodeRegion.ireg_locked]), which is what makes "no
     transaction is open" imply "no row is suspended" at a commit.

     THE ID IS EXISTENTIAL, and no client ever names it: the ending
     transaction does not have to say which id it retires, because
     [log_res] ties the ledger to the transactions by CARDINALITY
     ([size T = size om]) rather than by identity -- a tie that survives
     any retire, and all a commit needs ([om = empty] forces [T = empty]).

     WHY IT IS NOT INSIDE [log_opS]: a suspended row's owner must keep
     WRITING (create's mkdir writes the two dot entries while its child is
     still dotless), so the token it retains across the suspension has to
     be one [log_write] accepts.  That token is the BUDGET half above --
     which is exactly the pre-lane-A [log_op] -- so no callee below
     [log_op] moves at all. *)
  Definition log_tx (γ : log_names) : iProp Σ :=
    (∃ t : nat, t ↪[ln_tx γ] ())%I.

  Definition log_op (γ : log_names) (u : nat) : iProp Σ :=
    (log_opb γ u ∗ log_tx γ)%I.

  Global Instance log_tx_timeless γ : Timeless (log_tx γ).
  Proof. rewrite /log_tx. apply _. Qed.

  Global Instance log_opb_timeless γ u : Timeless (log_opb γ u).
  Proof. rewrite /log_opb. apply _. Qed.

  Global Instance log_opSe_timeless γ u Sb e0 : Timeless (log_opSe γ u Sb e0).
  Proof. apply _. Qed.

  Global Instance log_opS_timeless γ u Sb : Timeless (log_opS γ u Sb).
  Proof. apply _. Qed.

  (* the two conversions; [log_opS_named] is how a client that must compare
     epochs gets a name for its own, and it loses nothing *)
  Lemma log_opSe_opS γ u Sb e0 : log_opSe γ u Sb e0 -∗ log_opS γ u Sb.
  Proof. iIntros "H". iExists e0. iFrame. Qed.

  Lemma log_opS_named γ u Sb : log_opS γ u Sb -∗ ∃ e0, log_opSe γ u Sb e0.
  Proof. iIntros "H". iDestruct "H" as (e0) "H". iExists e0. iFrame. Qed.

  (* ---------------------------------------------------------------- *)
  (*  THE EPOCH AND THE APPEND REGISTRY (fs-log.md §G.2)               *)
  (* ---------------------------------------------------------------- *)

  (* "block [b] was appended to lh in epoch [e]".  PERSISTENT and never
     revoked: a witness from an old batch is not wrong, it is unusable --
     [log_use_group] can only fire when [e] is the CURRENT epoch, and the
     only way to know that is to hold a live entry, whose [e0] the auth
     pins to it.  Persistence is sound precisely because the epoch index,
     not the token's lifetime, carries the soundness. *)
  Definition logged_at (γ : log_names) (e : nat) (b : Z) : iProp Σ :=
    own (ln_lg γ) (◯ ({[(e, b)]} : gset (nat * Z))).

  Global Instance logged_at_persistent γ e b : Persistent (logged_at γ e b).
  Proof. apply _. Qed.

  Global Instance logged_at_timeless γ e b : Timeless (logged_at γ e b).
  Proof. apply _. Qed.

  (* the registry's two operations, over the [gset] auth: minting is an
     allocation into a union (idempotent, so the fragment is core-id and
     the token duplicates for free) and using it is [gset_included]. *)
  Lemma log_mint_logged (γ : log_names) (X : gset (nat * Z)) (e : nat) (b : Z) :
    own (ln_lg γ) (● X) ==∗
    own (ln_lg γ) (● (X ∪ {[(e, b)]})) ∗ logged_at γ e b.
  Proof.
    iIntros "H".
    iMod (own_update _ _ (● (X ∪ {[(e, b)]} : gset (nat * Z))
                          ⋅ ◯ (X ∪ {[(e, b)]} : gset (nat * Z))) with "H")
      as "[$ Hf]".
    { apply auth_update_alloc.
      apply local_update_unital_discrete. intros z _ Hz.
      split; [done|]. rewrite left_id in Hz. rewrite -Hz.
      rewrite /op /cmra_op /=. set_solver. }
    iModIntro. rewrite /logged_at.
    iApply (own_mono with "Hf"). apply auth_frag_mono.
    apply gset_included. set_solver.
  Qed.

  Lemma logged_at_in (γ : log_names) (X : gset (nat * Z)) (e : nat) (b : Z) :
    own (ln_lg γ) (● X) -∗ logged_at γ e b -∗ ⌜(e, b) ∈ X⌝.
  Proof.
    iIntros "Ha Hf".
    iDestruct (own_valid_2 with "Ha Hf") as %Hv.
    iPureIntro.
    apply auth_both_valid_discrete in Hv as [Hincl _].
    apply gset_included in Hincl. set_solver.
  Qed.

  (* ---------------------------------------------------------------- *)
  (*  THE APPEND RECEIPT: log_write's own post-state currency           *)
  (*  (fs-log.md §G.3)                                                  *)
  (* ---------------------------------------------------------------- *)

  (* What [log_write]'s contract hands back: the op's OWN ledger entry with
     a NAME for its birth epoch, AND the witness for the block it just
     logged, minted at exactly that epoch.

     WHY THE EPOCH MUST BE THE CALLER'S OWN, not an existential.  Using a
     witness ([log_use_group]) needs [e0 <= e] against the birth epoch of
     the op that is open at the USE.  A bare [∃ e, logged_at γ e b] cannot
     supply that -- any [e] satisfies it, a dead batch's included, and the
     header's revocation requirement is exactly what forbids trusting one.
     Tying [e] to the entry the caller is holding is what makes the receipt
     CURRENCY: the entry is live, so [log_res]'s soundness clause pins its
     [e0] to the current epoch, and the depositor can therefore stamp the
     witness with an epoch it can later order against (§G.3's
     [ic_epoch_lb]).

     The witness rides UNDER the entry's existential rather than beside it
     precisely because the two must agree on the epoch; splitting them into
     two conjuncts would lose the equality and give back the useless form.

     UNCONDITIONAL IN THE ARM (see the note on [log_mint_logged]'s two call
     sites in ProofLogWrite): a log_write that ABSORBED did not append, but
     the block it names is in the header all the same -- that is what the
     absorb arm's scan result says -- so the registry row it mints is just
     as true and just as usable.  §G.10's "non-absorbed arm only" ruling
     priced the absorbed-arm row as a re-proof "from the credit"; at the
     site it is instead immediate from the SCAN, so the arm distinction
     buys nothing and costs every consumer a case split.

     ...AND IT CARRIES THE CALLER'S EPOCH ANCHOR (fs-log.md §G.17,
     blocker 4).  [v] is a lower bound the caller brought in
     ([log_epoch_lb γ v], a premise of [SpecLogWrite.wp_log_write_au]), and
     [⌜v <= e0⌝] is the ONE fact in the whole absorption design that cannot
     be established anywhere else: it is [v <= E] (by [log_epoch_lb_le])
     composed with [e0 = E] (a live entry is born at the current epoch), and
     BOTH halves need the [ln_ep] auth, which lives inside [log_res] behind
     the log spinlock.  Two lower bounds on one counter are incomparable --
     §G.14's own refutation, one tier up -- so a client holding
     [log_epoch_lb γ v] and its own [log_opSe … e0] can do nothing with the
     pair; the cashing has to happen here, at the ghost step, and it is free
     there.  A caller with no receipt to build passes [v := 0].

     [log_opSw_opS] forgets the whole thing, so a caller that does not want
     a witness threads [log_opS] exactly as before.

     THE EPOCH-NAMED FORM IS THE PRIMITIVE (fs-log.md §G.20, the epoch
     tier), and [log_opSw] is it with the epoch CLOSED.  Closing is what a
     receipt's depositor wants -- it compares against its own anchor [v] and
     never against the op's identity -- but it is exactly what a WALKER
     cannot afford: a caller in the middle of a walk has to get its OWN
     [e0] back, because a credit is a claim at a named epoch and two lower
     bounds on one counter are incomparable (§G.14).  Nothing in the ghost
     steps ever moves an open op's birth epoch (every one of them updates
     the entry IN PLACE at the same [e0], and the counter's only transition
     is the commit bump, which runs with no live entry), so naming it costs
     the log_write proof nothing and is simply the truth stated. *)
  Definition log_opSwe (γ : log_names) (u : nat) (Sb : gset Z)
      (b : Z) (v : nat) (e0 : nat) : iProp Σ :=
    (log_opSe γ u Sb e0 ∗ logged_at γ e0 b ∗ ⌜(v <= e0)%nat⌝)%I.

  Definition log_opSw (γ : log_names) (u : nat) (Sb : gset Z)
      (b : Z) (v : nat) : iProp Σ :=
    (∃ e0 : nat, log_opSwe γ u Sb b v e0)%I.

  Lemma log_opSwe_intro (γ : log_names) (u : nat) (Sb : gset Z)
      (e0 : nat) (b : Z) (v : nat) :
    (v <= e0)%nat ->
    log_opSe γ u Sb e0 -∗ logged_at γ e0 b -∗ log_opSwe γ u Sb b v e0.
  Proof. intros Hv. iIntros "H Hw". iFrame. iPureIntro. exact Hv. Qed.

  (* the epoch closed: what a depositor threads *)
  Lemma log_opSwe_opSw (γ : log_names) (u : nat) (Sb : gset Z)
      (b : Z) (v : nat) (e0 : nat) :
    log_opSwe γ u Sb b v e0 -∗ log_opSw γ u Sb b v.
  Proof. iIntros "H". iExists e0. iFrame. Qed.

  (* ...and the entry alone, at the epoch it came back at: what a WALKER
     threads, and the whole point of the named form *)
  Lemma log_opSwe_opSe (γ : log_names) (u : nat) (Sb : gset Z)
      (b : Z) (v : nat) (e0 : nat) :
    log_opSwe γ u Sb b v e0 -∗ log_opSe γ u Sb e0.
  Proof. iIntros "(H & _ & _)". iFrame. Qed.

  Lemma log_opSw_intro (γ : log_names) (u : nat) (Sb : gset Z)
      (e0 : nat) (b : Z) (v : nat) :
    (v <= e0)%nat ->
    log_opSe γ u Sb e0 -∗ logged_at γ e0 b -∗ log_opSw γ u Sb b v.
  Proof.
    intros Hv. iIntros "H Hw". iExists e0.
    iApply (log_opSwe_intro γ u Sb e0 b v Hv with "H Hw").
  Qed.

  Lemma log_opSw_opS (γ : log_names) (u : nat) (Sb : gset Z) (b : Z) (v : nat) :
    log_opSw γ u Sb b v -∗ log_opS γ u Sb.
  Proof.
    iIntros "H". iDestruct "H" as (e0) "H".
    iApply (log_opSe_opS with "[H]"). iApply (log_opSwe_opSe with "H").
  Qed.

  (* the receipt the region's depositor spends: the witness with the
     caller's own anchor already ordered against it (fs-log.md §G.17). *)
  Lemma log_opSw_witness (γ : log_names) (u : nat) (Sb : gset Z) (b : Z)
      (v : nat) :
    log_opSw γ u Sb b v -∗
    log_opS γ u Sb ∗ ∃ e : nat, logged_at γ e b ∗ ⌜(v <= e)%nat⌝.
  Proof.
    rewrite /log_opSw /log_opSwe.
    iIntros "H". iDestruct "H" as (e0) "(H & #Hw & %Hv)".
    iSplitL "H"; [iExists e0; iFrame |].
    iExists e0. iFrame "Hw". iPureIntro. exact Hv.
  Qed.

  (* ...and the trivial anchor, for every caller that wants none of it *)
  Lemma log_epoch_lb_0 (γ : log_names) : ⊢ |==> log_epoch_lb γ 0.
  Proof. rewrite /log_epoch_lb. iApply mono_nat_lb_own_0. Qed.

  (* ---------------------------------------------------------------- *)
  (*  THE ABSORPTION CREDIT (fs-log.md §G.19)                           *)
  (* ---------------------------------------------------------------- *)

  (* What a caller of [log_write] must hand over to claim the FREE arm --
     i.e. to say "this block is already in lh.block[], absorb it and give my
     unit back".  It has two admissible forms and they are genuinely
     different claims:

     - OWN-SET ([b ∈ Sb]): the block is in MY op's already-logged set.  This
       is the only form the pre-group design had, and it is pure: the
       ledger's own soundness clause ([log_res]: every live entry's set is a
       subset of the header) turns it into membership.  Every landed
       credited caller -- bfree's credited arm, balloc's bitmap write,
       writei's [bool_decide] -- claims exactly this, and [log_credit_own]
       is their conversion.

     - GROUP ([logged_at γ e b] with [e0 <= e], against the caller's OWN
       birth epoch [e0]): the block is in the header because SOMEBODY put it
       there this batch.  This is the form the group extension exists for,
       and it is unstatable without a name for [e0] -- which is why this
       premise travels beside a [log_opSe], not a [log_opS].  A witness from
       a dead batch has [e < e0] and cannot satisfy it; that is the header's
       revocation requirement met by indexing (§G.2).

     PERSISTENT in both arms, so a caller intros it with [#] and it costs
     nothing to keep. *)
  Definition log_credit (γ : log_names) (cr : bool) (Sb : gset Z)
      (e0 : nat) (b : Z) : iProp Σ :=
    (if cr then ⌜b ∈ Sb⌝ ∨ (∃ e : nat, logged_at γ e b ∗ ⌜(e0 <= e)%nat⌝)
     else emp)%I.

  Global Instance log_credit_persistent γ cr Sb e0 b :
    Persistent (log_credit γ cr Sb e0 b).
  Proof. rewrite /log_credit. destruct cr; apply _. Qed.

  Global Instance log_credit_timeless γ cr Sb e0 b :
    Timeless (log_credit γ cr Sb e0 b).
  Proof. rewrite /log_credit. destruct cr; apply _. Qed.

  (* the OWN-SET claimant's conversion: the pure premise every landed
     credited caller already discharges, in one step *)
  Lemma log_credit_own (γ : log_names) (cr : bool) (Sb : gset Z)
      (e0 : nat) (b : Z) :
    (cr = true -> b ∈ Sb) -> ⊢ log_credit γ cr Sb e0 b.
  Proof.
    intros H. rewrite /log_credit. destruct cr.
    - iLeft. iPureIntro. exact (H eq_refl).
    - iEmpIntro.
  Qed.

  (* the GROUP claimant's: a witness at least as new as my op's birth *)
  Lemma log_credit_group (γ : log_names) (cr : bool) (Sb : gset Z)
      (e0 e : nat) (b : Z) :
    (e0 <= e)%nat -> logged_at γ e b -∗ log_credit γ cr Sb e0 b.
  Proof.
    intros Hle. iIntros "#Hw". rewrite /log_credit. destruct cr; [| iEmpIntro].
    iRight. iExists e. iFrame "Hw". iPureIntro. exact Hle.
  Qed.

  (* SET-MONOTONE, exactly as the pure claim it generalises is: a walk that
     has logged MORE blocks since the credit was taken still holds it.  This
     is what itrunc's two tail sites need -- the loops hand the tail their
     RUNNING set, which only grows (fs-log.md §G.20).  The group disjunct
     does not mention the set at all; only the own-set one moves, by
     [elem_of_weaken]. *)
  Lemma log_credit_mono (γ : log_names) (cr : bool) (Sb Sb' : gset Z)
      (e0 : nat) (b : Z) :
    Sb ⊆ Sb' -> log_credit γ cr Sb e0 b -∗ log_credit γ cr Sb' e0 b.
  Proof.
    intros Hsub. rewrite /log_credit. destruct cr; [| iIntros "_"; iEmpIntro].
    iIntros "[%Hin | Hw]".
    - iLeft. iPureIntro. exact (elem_of_weaken _ _ _ Hin Hsub).
    - iRight. iExact "Hw".
  Qed.

  Global Instance log_op_timeless γ u : Timeless (log_op γ u).
  Proof. apply _. Qed.

  (* the forgetful direction, used wherever a credited op is handed to a
     callee that does not care.  It takes the transaction token back
     BESIDE the budget, because the two travel together everywhere except
     inside a suspended row's window. *)
  Lemma log_opS_op γ u Sb : log_opS γ u Sb -∗ log_tx γ -∗ log_op γ u.
  Proof.
    iIntros "H Ht". rewrite /log_op /log_opb. iFrame "Ht". iExists Sb. iFrame.
  Qed.

  (* ...and its budget-only half, for a walk that is between the arm and
     the disarm of a row and therefore holds no transaction token *)
  Lemma log_opS_opb γ u Sb : log_opS γ u Sb -∗ log_opb γ u.
  Proof. iIntros "H". rewrite /log_opb. iExists Sb. iFrame. Qed.

  (* THE OPENING EVERY THREADER USES: the budget at a named set beside the
     transaction token.  Written as one lemma so a caller that used to
     destructure [log_op]'s existential keeps one line. *)
  Lemma log_op_openS γ u : log_op γ u -∗ ∃ Sb, log_opS γ u Sb ∗ log_tx γ.
  Proof.
    iIntros "[Hb Ht]". rewrite /log_opb. iDestruct "Hb" as (Sb) "Hb".
    iExists Sb. iFrame.
  Qed.

  (* ---- THE TOKEN, HALVED ACROSS A HELD WRITE LOCK -------------------
     (durable-fs-plan.md section 3, [ilock]; durable-disk B''-arm)

     A transactional [ilock] parks a SHARE of the transaction's element in
     the escrow's write arm ([IcacheEscrow.ic_arm_tx]), so that [end_op] --
     which consumes the WHOLE element -- cannot commit while the inode is
     write-locked.  The id has to come OUT of [log_tx]'s existential for the
     arm to name it, which is exactly [IcacheTxRefute]'s finding: an
     existentially-keyed share can never be rejoined.  It goes back in at
     the join, so nothing above these two lines ever sees an id. *)
  Lemma log_tx_halve (γ : log_names) :
    log_tx γ -∗ ∃ t : nat,
      t ↪[ln_tx γ]{#(1/2)} () ∗ t ↪[ln_tx γ]{#(1/2)} ().
  Proof.
    iIntros "H". rewrite /log_tx. iDestruct "H" as (t) "Ht".
    iExists t. iDestruct "Ht" as "[$ $]".
  Qed.

  Lemma log_tx_join (γ : log_names) (t : nat) :
    t ↪[ln_tx γ]{#(1/2)} () -∗ t ↪[ln_tx γ]{#(1/2)} () -∗ log_tx γ.
  Proof.
    iIntros "H1 H2". rewrite /log_tx. iExists t.
    iDestruct (ghost_map_elem_combine with "H1 H2") as "[H _]".
    rewrite dfrac_op_own Qp.half_half. iExact "H".
  Qed.

  (* ---- THE ELEMENT AT AN ARBITRARY SHARE (durable-disk B''-tx2) ------
     A walk that write-locks TWO inodes at one transaction parks a QUARTER
     in each escrow ([IcacheEscrow.ic_tx_dep_at]) and keeps the rest, so the
     halving above is one case of a general split.  All three are stated
     with the total as an EQUATION premise rather than as [q1 + q2] in the
     conclusion: a caller then never has to [rewrite] a [Qp] sum inside the
     proofmode, where the split's evar is out of scope (durable-notes,
     [rewrite -(Qp.div_2 q)]). *)
  Lemma log_tx_split (γ : log_names) (t : nat) (q q1 q2 : Qp) :
    q = (q1 + q2)%Qp ->
    t ↪[ln_tx γ]{#q} () -∗
    t ↪[ln_tx γ]{#q1} () ∗ t ↪[ln_tx γ]{#q2} ().
  Proof. intros ->. iIntros "H". iDestruct "H" as "[$ $]". Qed.

  (* ...and its inverse at ARBITRARY fractions ([log_tx_join] above is the
     1/2 + 1/2 reading).  A walk that lends a share of its transaction to a
     callee -- create's [ProofCreateFreshTy] span lends one to the claim box
     it is about to fill (durable-disk C-5) -- needs to put its residue back
     together at whatever fractions it chose. *)
  Lemma log_tx_join_q (γ : log_names) (t : nat) (q q1 q2 : Qp) :
    q = (q1 + q2)%Qp ->
    t ↪[ln_tx γ]{#q1} () -∗ t ↪[ln_tx γ]{#q2} () -∗ t ↪[ln_tx γ]{#q} ().
  Proof.
    intros ->. iIntros "H1 H2".
    iDestruct (ghost_map_elem_combine with "H1 H2") as "[H _]".
    rewrite dfrac_op_own. iExact "H".
  Qed.

  Lemma log_tx_add (γ : log_names) (t : nat) (q q1 q2 : Qp) :
    q = (q1 + q2)%Qp ->
    t ↪[ln_tx γ]{#q1} () -∗ t ↪[ln_tx γ]{#q2} () -∗ t ↪[ln_tx γ]{#q} ().
  Proof.
    intros ->. iIntros "H1 H2".
    iDestruct (ghost_map_elem_combine with "H1 H2") as "[H _]".
    rewrite dfrac_op_own. iExact "H".
  Qed.

  (* the two directions between the WHOLE element and the token, so that a
     walk which has gathered every parked share back can close the id again
     without unfolding the definition *)
  Lemma log_tx_full (γ : log_names) (t : nat) :
    t ↪[ln_tx γ]{#1} () -∗ log_tx γ.
  Proof. iIntros "H". rewrite /log_tx. iExists t. iExact "H". Qed.

  Lemma log_tx_open (γ : log_names) :
    log_tx γ -∗ ∃ t : nat, t ↪[ln_tx γ]{#1} ().
  Proof. iIntros "H". iExact "H". Qed.

  Lemma log_op_split γ u : log_op γ u -∗ log_opb γ u ∗ log_tx γ.
  Proof. iIntros "[$ $]". Qed.

  (* ---- THE SET FORM BESIDE THE TOKEN, AS ONE CONJUNCT ----------------
     (durable-fs-plan.md section 3, [ilock]; durable-disk B''-tx)

     A WALK THAT WRITE-LOCKS carries both: the SET half is what [log_write]
     accepts and what a [log_opS]-shaped callee wants, the TOKEN half is
     what a transactional [ilock] parks in the escrow.  They ride together
     because of durable-notes' bundling rule -- written as two conjuncts
     they would move every pass-through site of the walk-stage statements
     that already thread [log_opS]; written as ONE, in [log_opS]'s own
     position, no stage lemma's arity changes at all.  It is split exactly
     once per locked window, at the [ilock], and rejoined at the release. *)
  Definition log_opSt (γ : log_names) (u : nat) (Sb : gset Z) : iProp Σ :=
    (log_opS γ u Sb ∗ log_tx γ)%I.

  Global Instance log_opSt_timeless γ u Sb : Timeless (log_opSt γ u Sb).
  Proof. rewrite /log_opSt. apply _. Qed.

  Lemma log_opSt_split γ u Sb :
    log_opSt γ u Sb -∗ log_opS γ u Sb ∗ log_tx γ.
  Proof. iIntros "[$ $]". Qed.

  Lemma log_opSt_intro γ u Sb :
    log_opS γ u Sb -∗ log_tx γ -∗ log_opSt γ u Sb.
  Proof. iIntros "H Ht". rewrite /log_opSt. iFrame. Qed.

  Lemma log_op_openSt γ u : log_op γ u -∗ ∃ Sb, log_opSt γ u Sb.
  Proof.
    iIntros "H". iDestruct (log_op_openS with "H") as (Sb) "[H Ht]".
    iExists Sb. iApply (log_opSt_intro with "H Ht").
  Qed.

  Lemma log_opSt_op γ u Sb : log_opSt γ u Sb -∗ log_op γ u.
  Proof.
    iIntros "[H Ht]". iApply (log_opS_op with "H Ht").
  Qed.

  (* ---- THE EPOCH-NAMED SET FORM BESIDE A *NAMED SHARE* --------------
     (durable-disk B''-tx5, plan section 3/4)

     [log_opSt]'s twin one level down, and it is what [SpecIput] threads.
     iput's three windows -- [IcacheEscrow]'s [DepFrz], its mid-free park and
     its authority-side [ic_held] -- each park a SHARE of the freeing
     transaction's element, which is what lets the commit refute them at an
     empty [ln_tx] authority; and a share must be handed back at exactly the
     [(t, q)] it went in at, so the id is a FIELD here where [log_tx] closes
     it existentially ([IcacheTxRefute.tx_two_halves_no_whole] is why).

     Bundled as ONE conjunct in [log_opSe]'s own position for [log_opSt]'s
     reason verbatim: written as two, every threading site of iput's
     contract would move; written as one, they move by substitution. *)
  Definition log_opSet (γ : log_names) (u : nat) (Sb : gset Z) (e0 : nat)
      (t : nat) (q : Qp) : iProp Σ :=
    (log_opSe γ u Sb e0 ∗ t ↪[ln_tx γ]{#q} ())%I.

  Global Instance log_opSet_timeless γ u Sb e0 t q :
    Timeless (log_opSet γ u Sb e0 t q).
  Proof. rewrite /log_opSet. apply _. Qed.

  Lemma log_opSet_split γ u Sb e0 t q :
    log_opSet γ u Sb e0 t q -∗ log_opSe γ u Sb e0 ∗ t ↪[ln_tx γ]{#q} ().
  Proof. iIntros "[$ $]". Qed.

  Lemma log_opSet_intro γ u Sb e0 t q :
    log_opSe γ u Sb e0 -∗ t ↪[ln_tx γ]{#q} () -∗ log_opSet γ u Sb e0 t q.
  Proof. iIntros "H Ht". rewrite /log_opSet. iFrame. Qed.

  Lemma log_opb_op γ u : log_opb γ u -∗ log_tx γ -∗ log_op γ u.
  Proof. iIntros "H Ht". iFrame. Qed.

  (* ---------------------------------------------------------------- *)
  (*  The ERA's half of the log-region MIRROR (phase C2b/D1 stage 2)    *)
  (*                                                                    *)
  (*  [RiscvPtsto.log_mirror] records what the LOG REGION of the         *)
  (*  physical disk holds -- the header's decoding and the slots'        *)
  (*  contents.  The crash record's checked-out arm holds one half       *)
  (*  ([FsCrash.fs_custody]) and the ERA holds the other, and a WAL       *)
  (*  write's fupd meets the two: that is the only way a STATELESS view   *)
  (*  shift can know facts the PREVIOUS writes established ("the on-disk  *)
  (*  header is clean", "the slots hold the logged values").             *)
  (*                                                                     *)
  (*  Which half lives where, and why the value is existential: the era's *)
  (*  half rides [log_state], so it is exactly as available as the batch  *)
  (*  is -- in the lock between commits, checked out by the committer     *)
  (*  during one.  The BETWEEN-COMMITS form carries the pure conjunct     *)
  (*  [lm_hdr M = (0, [])]: with the batch in the lock the on-disk header *)
  (*  is clean, which is what a log-fill fupd reads out of it, and the    *)
  (*  final [write_head] of a commit (the CLEAR) is what re-establishes   *)
  (*  it before the batch goes back.  Both forms keep [M] existential so  *)
  (*  that no statement above this file grows a binder for it.            *)
  (* ---------------------------------------------------------------- *)

  (* THE ERA'S HALF AT A RECORDED HEADER PICTURE.  [h] is the ON-DISK
     header's [hdr_dec] READING of the era's mirror ([LogDefs.lm_hdr]): the
     log-fill kind needs a CLEAN header, the install kind needs the header
     to be the (n, W) the commit just wrote (which is what tells it the
     block it is overwriting is a LOGGED one, so recovery re-installs it
     anyway).  The mirror's full picture (durable-disk stage E2: one total
     block view, homes included) is under the existential; assertions here
     expose only the header reading, so [log_state] reads exactly as
     before.  [ls] locates the header inside the picture. *)
  Definition log_mirror_clean (ls : Z) : iProp Σ :=
    log_mirror_at ls (0%nat, []).

  (* ---------------------------------------------------------------- *)
  (*  ROW (b): THE MIRROR TIE (durable-disk stage G1; UNGATED, 1b)      *)
  (*                                                                    *)
  (*  OUTSIDE THE BATCH, THE ERA'S PICTURE OF THE DURABLE DISK IS THE     *)
  (*  LOGGED VIEW.  A home block that is not in [LB] has not been         *)
  (*  written since the last commit, so its home block on the physical    *)
  (*  disk -- which is what [lm_view M] records -- still holds the        *)
  (*  logged bytes.  It is what turns the commit's [D' = L|home] into an  *)
  (*  equation about the PHYSICAL pre-image, i.e. what lets the commit    *)
  (*  permit ([FsCrash.fs_commit_L_seq_permit]) conclude the new          *)
  (*  committed view generically instead of at each of end_op's 26 exit   *)
  (*  arms.                                                              *)
  (*                                                                     *)
  (*  IT IS THE REAL ROW: [log_state] carries this body, there is no      *)
  (*  gate, and both establishment sites prove it --                      *)
  (*                                                                     *)
  (*   - end_op's DEPOSIT ([ProofEndOp.eo_open_to_batch], through         *)
  (*     [log_mirror_tie_deposit] below): the committer chains the        *)
  (*     mirror's VALUE across the fills, the commit, the installs and    *)
  (*     the clear, so the deposit is arithmetic -- an install writes     *)
  (*     [L]'s bytes to the home block of every [b ∈ LB] and touches      *)
  (*     nothing else, so the post-commit picture agrees with [L] on the  *)
  (*     WHOLE home set.                                                  *)
  (*                                                                     *)
  (*   - boot ([ProofInitlog]).  The era's mirror is born at the picture  *)
  (*     of the disk it boots on and its custody arm is installed in the  *)
  (*     same fupd, so the boot's whole write chain is value-carrying and *)
  (*     the pack computes the row off it.                                *)
  (*                                                                     *)
  (*  Every MAINTENANCE site (log_write's two arms, begin_op) is free,    *)
  (*  which is what row (b) is designed to be: [log_write] moves [L]      *)
  (*  only at a block it puts into [LB] in the same critical section, so  *)
  (*  the row's domain only shrinks.                                      *)
  (* ---------------------------------------------------------------- *)
  Definition log_mirror_tie_body (M : log_mirror) (L : gmap Z (list (bv 8)))
      (cov : gset Z) (ls : Z) (LB : gset Z) : Prop :=
    forall b : Z, b ∈ fs_home_set cov ls -> b ∉ LB ->
      L !! b = Some (lm_view M b).

  (* THE DEPOSIT, proved: once end_op's committer carries the mirror's
     VALUE across the commit cycle -- which it does, through [FsCrash]'s
     value-chained permits -- row (b) at the deposit is pure bookkeeping
     over the chain.  The three chain facts it asks for are exactly what
     [ProofEndOp]'s [eo_minst_hit] / [eo_minst_miss] / [eo_ext] invariants
     deliver:

       - every LOGGED home block ends at its logged content (the install
         pass wrote [Lw j] there),
       - every OTHER home block is where it was at the checkout (no write in
         the cycle touches it: the fills go to slots, the commit and the
         clear to the header, the installs to [W]'s blocks alone),
       - and the logged view agrees with [Lw] at every entry (the copy
         loop's own ghost step). *)
  Lemma log_mirror_tie_deposit (M M' : log_mirror) (L : gmap Z (list (bv 8)))
      (cov : gset Z) (ls : Z) (LB : gset Z) (W : list Z)
      (Lw : nat -> list (bv 8)) :
    LB = list_to_set W ->
    log_mirror_tie_body M L cov ls LB ->
    (* the install pass's effect at the logged blocks... *)
    (forall (j : nat) (b : Z), W !! j = Some b -> lm_view M' b = Lw j) ->
    (* ...and its absence everywhere else on the home set *)
    (forall b : Z, b ∈ fs_home_set cov ls -> b ∉ LB -> lm_view M' b = lm_view M b) ->
    (* the logged view, at the entries the batch wrote *)
    (forall (j : nat) (b : Z), W !! j = Some b -> L !! b = Some (Lw j)) ->
    log_mirror_tie_body M' L cov ls ∅.
  Proof.
    intros -> Htie Hhit Hmiss HLw b Hb _.
    destruct (decide (b ∈ (list_to_set W : gset Z))) as [Hin|Hout].
    - apply elem_of_list_to_set, elem_of_list_lookup in Hin as [j Hj].
      rewrite (HLw j b Hj) (Hhit j b Hj) //.
    - rewrite (Hmiss b Hb Hout). exact (Htie b Hb Hout).
  Qed.

  (* ---------------------------------------------------------------- *)
  (*  The batch bundle (checked out wholesale by the committer)        *)
  (* ---------------------------------------------------------------- *)

  (* Parameters: bn -- the bio layer's names (for the SLOT POOL); γfs --
     the FsBlocks ghosts; cov -- the covered range the bio layer runs at;
     logstart -- the sb's log start block.  [n] is a parameter (not an
     existential) because the ledger's sum tie in [log_res] mentions it.
     [pend] is the OPEN OPS' pending BLOCK set ([op_pending om] at the one
     call site, [log_res]) and THE BUNDLE DOES NOT READ IT: ruling 3
     (claude-notes/design/fs-state.md §3) has no row (a) -- no abstract
     committed picture, no per-op finalize -- so there is no agreement for
     a pending set to except.  It stays a parameter because [log_res] is
     where the ledger authority lives and the two moves the transitions
     need ([log_state_pend_mono] for the three growing steps,
     [log_state_fin] for end_op's retire) are stated over it; both are now
     the identity.

     THE MIRROR RIDES HERE (durable-disk stage G1's fusion).  [M] was an
     existential inside [log_mirror_clean]; it is a binder of this bundle
     so that row (b) -- which relates the era's picture of the durable
     disk to the logged view -- can be stated at all.  The header reading
     is unchanged, so nothing above this file grew a binder. *)
  Definition log_state (bn : bio_names) (γfs : fs_names) (cov : gset Z)
      (logstart : Z) (n : nat) (LB : gset Z) (pend : gset Z) : iProp Σ :=
    (∃ (W : list (SailStdpp.Values.mword 32))
       (L : gmap Z (list (bv 8))) (D : gmap Z bool) (M : log_mirror),
       ⌜n = length W /\ (n <= LOGBLOCKS)%nat⌝ ∗
       (* LB IS EXPOSED, not existential, so that [log_res] -- which is
          where the ledger authority lives -- can state that every op's
          already-logged set is really a set of logged blocks.  Without
          lifting it out of the existential the two halves of that tie sit
          in different resources and cannot be related. *)
       ⌜LB = list_to_set (map uint W)⌝ ∗
       ⌜NoDup (map uint W)⌝ ∗
       (* logged blocks are covered HOME blocks: never the log's own
          storage, never the header -- AND NEVER BLOCK 1 (durable-disk lane
          E-blk1, plan section 5's "one small fact the mint needs").
          [fsinit] reads the superblock off the RAW disk before [initlog]
          runs, while the snapshot the boot mint reads describes the
          RECOVERED view, so the two are one record only if recovery leaves
          block 1 alone.  It is not a premise on anybody: [SbPark.sb_parked]
          -- a conjunct of [log_ctx] -- holds block 1's run at fraction 1,
          [log_write]'s byte-range update holds the caller's window at
          fraction 1, and two full owners of one byte are inconsistent
          ([SbPark.sb_parked_bno_ne], read at the append arm).  The third
          conjunct is LAST inside the row so that no site which passes the
          row through moves.  [FsCrash.hdr_wf] carries the same clause, which
          is what makes it survive a power cycle. *)
       ⌜forall w, w ∈ W -> uint w ∈ cov /\
          ~ (uint w ∈ log_region_set logstart) /\
          uint w <> FsImg.SB_BNO⌝ ∗
       lh_n_pa ↦₄ (mword_of_int (Z.of_nat n) : mword 32) ∗
       ([∗ list] i ↦ w ∈ W, lh_block i ↦₄ w) ∗
       ([∗ list] i ∈ seq n (LOGBLOCKS - n),
          ∃ junk : SailStdpp.Values.mword 32, lh_block i ↦₄ junk) ∗
       (* the freeze-by-auth: both FsBlocks auths live HERE *)
       ghost_map_auth (fs_cache γfs) 1 L ∗
       ghost_map_auth (fs_dirty γfs) 1 D ∗
       (* the log side's dirty halves, over the WHOLE covered range,
          recording exactly W's membership (the bio payloads hold the
          other halves) *)
       ([∗ set] b ∈ cov,
          b ↪[fs_dirty γfs]{#(1/2)} (bool_decide (b ∈ map uint W))) ∗
       (* the log region's CLIENT halves: the log is its own client for
          the header block and the LOGBLOCKS slots *)
       (∃ bsh, fs_chalf γfs (log_hdr_bno logstart) bsh) ∗
       ([∗ list] i ∈ seq 0 LOGBLOCKS,
          ∃ bs, fs_chalf γfs (log_slot_bno logstart i) bs) ∗
       (* THE SLOT POOL: one [bslot] per free log slot, plus a working
          margin of 2 (the committer's two in-flight breads; the copy
          loop and install both hold at most two buffers at once).  This
          is what makes log_write's refund UNCONDITIONAL -- the append
          path's n++ releases a pool unit to replace the one bpin
          absorbed, the absorb path never takes one -- and what lets
          install_trans's bunpins deposit their freed units back instead
          of end_op dropping them: pool + n = LOGBLOCKS + 2 is
          inductive. *)
       bslots ((LOGBLOCKS - n) + 2)%nat ∗
       (* THE ERA'S MIRROR HALF, at the between-commits picture -- the
          header reading is [log_mirror_clean]'s, spelled out because [M]
          is this bundle's own binder now. *)
       log_mirror_half M ∗ ⌜lm_hdr M logstart = (0%nat, [])⌝ ∗
       (* ROW (b) -- see [log_mirror_tie_body] above *)
       ⌜log_mirror_tie_body M L cov logstart LB⌝)%I.

  (* THE PENDING SET MOVES, in the two shapes the transitions need, and
     BOTH ARE THE IDENTITY (durable-disk 1d): the bundle does not read
     [pend].  The names and statements are kept because they are where the
     three growing transitions and end_op's retire say what they do to the
     ledger's union, and because a future row over the pending set -- if
     ruling 3 ever grows one -- would land here and nowhere else.

     GROWTH: [begin_op]'s mint and [log_write]'s two ledger steps. *)
  Lemma log_state_pend_mono (bn : bio_names) (γfs : fs_names) (cov : gset Z)
      (logstart : Z) (n : nat) (LB pend pend' : gset Z) :
    pend ⊆ pend' ->
    log_state bn γfs cov logstart n LB pend -∗
    log_state bn γfs cov logstart n LB pend'.
  Proof. intros _. rewrite /log_state. iIntros "H". iExact "H". Qed.

  (* SHRINKAGE -- [end_op]'s retire, where the ending op's already-logged
     BLOCKS leave the pending union.  flip-C1's [end_op_fin] bundle
     argument is GONE with row (a): the retiring op owes the log nothing
     ([SpecEndOp] has no FS-facing premise at all now), and the fast path
     closes with [op_pending_delete] alone. *)
  Lemma log_state_fin (bn : bio_names) (γfs : fs_names) (cov : gset Z)
      (logstart : Z) (n : nat) (LB F pend : gset Z) :
    log_state bn γfs cov logstart n LB pend -∗
    log_state bn γfs cov logstart n LB (pend ∖ F).
  Proof. rewrite /log_state. iIntros "H". iExact "H". Qed.

  (* ---------------------------------------------------------------- *)
  (*  The lock's resource                                              *)
  (* ---------------------------------------------------------------- *)

  Definition log_res (γ : log_names) (bn : bio_names) (γfs : fs_names)
      (cov : gset Z) (logstart : Z) : iProp Σ :=
    (∃ (out : nat) (cmt : bool) (nc : SailStdpp.Values.mword 32)
       (om : gmap nat op_entry) (E : nat) (X : gset (nat * Z))
       (T : gmap nat unit),
       l_out ↦₄ (mword_of_int (Z.of_nat out) : mword 32) ∗
       l_cmt ↦₄ (mword_of_int (if cmt then 1 else 0) : mword 32) ∗
       l_ncommit ↦₄ nc ∗
       ghost_map_auth (ln_ops γ) 1 om ∗
       ⌜size om = out⌝ ∗
       ⌜forall i e, om !! i = Some e -> (e.1.1 <= MAXOPBLOCKS)%nat⌝ ∗
       (* from the guard: (out+1)*MAXOPBLOCKS <= LOGBLOCKS at every
          increment, so the cell word stays a faithful small int *)
       ⌜(out <= 3)%nat⌝ ∗
       ⌜cmt = true -> out = 0%nat⌝ ∗
       (* THE EPOCH AND THE APPEND REGISTRY (fs-log.md §G.2/§G.9) *)
       mono_nat_auth_own (ln_ep γ) 1 E ∗
       (* GENESIS IS EPOCH ONE, AND THE COUNTER NEVER GOES BACK (§G.20).
          [log_epoch_alloc] starts at one on purpose, but a [mono_nat] auth
          says nothing about its own value, so without this clause the fact
          is unreachable from anywhere -- and [log_begin_step], the one mint
          point every op passes through, is where an op's birth epoch has to
          inherit it ([log_opSe]'s [⌜1 <= e0⌝], which is what refutes the
          region receipt's never-observed zero).  Maintained for free:
          initlog establishes it at [E = 1] and the only transition is the
          commit bump, [E -> S E]. *)
       ⌜(1 <= E)%nat⌝ ∗
       own (ln_lg γ) (● X) ∗
       (* THE SOUNDNESS CORE: every LIVE entry was born in the CURRENT
          epoch.  Maintained for free by the bump's placement -- the commit
          re-deposit runs with [out = 0], hence [om = ∅], so a bump never
          has a live entry to falsify (ProofEndOp's own [Hommt]). *)
       ⌜forall i e, om !! i = Some e -> e.2 = E⌝ ∗
       (* ...and the registry never runs ahead of the epoch: every row was
          minted at the epoch current when it was minted, and the epoch only
          grows.  This is the half that turns [e0 <= e] into [e = E]. *)
       ⌜forall e' b', ((e', b') : nat * Z) ∈ X -> (e' <= E)%nat⌝ ∗
       (* THE OPEN TRANSACTIONS (durable-disk lane A, plan section 3).
          OUTSIDE the committing arm -- a commit is exactly the instant this
          authority has to be READABLE, and [log_state] is checked out then.
          It sits here rather than in [log_state] for that reason and for one
          more: it is the ledger's own twin, and the ledger's authority is
          here.  It is the LAST conjunct that is not the committing arm,
          which is the cheapest position: the arm is what every opener
          destructures further, so a conjunct after it would cost each of
          them a restructuring rather than one name in a pattern.

          THE TIE IS CARDINALITY, not identity ([log_tx_retire]'s note): a
          retiring transaction hands back an element whose id it never
          named, so nothing can relate that id to the ledger entry the same
          end_op retires -- but both retires drop exactly one row, which is
          all the commit reads ([log_tx_empty_of_ops]). *)
       ghost_map_auth (ln_tx γ) 1 T ∗
       ⌜size T = size om⌝ ∗
       (if cmt then emp
        else ∃ (n : nat) (LB : gset Z),
          ⌜(n + op_sum om <= LOGBLOCKS)%nat⌝ ∗
          (* THE CREDIT'S SOUNDNESS CLAUSE.  An op may only claim to have
             already logged blocks that really are in lh.block[].  Without
             it a client could present a bogus credit, log_write's code
             would take the APPEND path (the block not being in the header
             after all), lh.n would grow, and no budget unit would be
             spent -- breaking the tie above.  Vacuous while committing,
             where out = 0 forces om = empty. *)
          ⌜forall i e, om !! i = Some e -> e.1.2 ⊆ LB⌝ ∗
          (* ...and the registry's twin of it: a witness minted THIS epoch
             names a block that really is in the header.  Older rows are
             unconstrained, which is exactly the self-invalidation -- they
             can never be used, because using one needs [e = E]. *)
          ⌜forall b : Z, (E, b) ∈ X -> b ∈ LB⌝ ∗
          log_state bn γfs cov logstart n LB (op_pending om)))%I.

  (* the persistent bundle every log function shares: the sealed lock and
     the two cells initlog wrote once and froze.

     IT NAMES NO FILE-SYSTEM PAYLOAD.  The existential closure over a
     parked [Psi] is gone with the payload itself (plan sections 3 and 8):
     a [log_write] proves nothing about the file system, so the log's lock
     resource carries no client proposition and this bundle carries no
     client law.  The arity is the one the 75 files that thread it already
     have. *)
  Definition log_ctx (γ : log_names) (bn : bio_names) (γfs : fs_names)
      (cov : gset Z) (logstart : Z)
      (dev : SailStdpp.Values.mword 32) : iProp Σ :=
    (is_lock (ln_lk γ) log_addr "log"%string
       (log_res γ bn γfs cov logstart) ∗
     l_dev ↦₄□ dev ∗
     l_start ↦₄□ (mword_of_int logstart : mword 32) ∗
     (* THE ERA'S SWAP RECEIPT (phase C2b/D1 stage 3).  [initlog]'s swap
        produced it and every later WAL fupd needs it: it is the LOWER bound
        that, against the started-generations auth the DMA completion threads
        in, pins the crash record's arm to THIS era ([FsCrash.fs_arm_acc]'s
        squeeze).  Persistent, so it rides the context every log function
        already threads. *)
     swap_lb (S gen_id) ∗
     (* THE BYTE VIEW'S INVARIANT ROW (durable-disk 1c-flip step 3/4).
        Every home block's owner above the log now holds the EXCLUSIVE
        [FsBlocks.fsblock] rather than the cache's parked half, so the
        auth-free half/half agreement a [bread] client used to close by
        entailment is gone: it opens THIS invariant instead.  It rides
        [log_ctx] because [log_ctx] is already threaded to [log_write] and
        already carries [cov] and [logstart], so not one call site moves. *)
     fs_bytes_inv (fs_bytes γfs) (fs_cache γfs)
                  (fs_home_set cov logstart) ∗
     (* BLOCK 1, OWNED (durable-disk lane C-3a).  The superblock's byte run
        at FULL fraction, parked in [SbPark.sbN] with its parse; initlog
        allocates it out of the run fsinit hands down and this is where the
        commit reaches it.  LAST, so no pattern that opens this bundle
        moves. *)
     sb_parked γfs ∗
     (* THE FILE SYSTEM'S LAW (durable-disk C-8, plan section 3's "Commit").
        Given the byte authority at the logged view and "no transaction is
        open", it yields [∃ S, snap_ok S L] and hands both authorities back.
        ARITY-FREE for [sb_parked]'s reason verbatim: the mask it runs in is
        CLOSED OVER, with the one fact a committer needs beside it (that
        [fsbN] is not in it -- a committer runs the law with the byte view
        already open).  The WAL supplies nothing to it and reads nothing out
        of it but a pure proposition, so the log's lock resource still
        carries no client payload.  LAST, after the park, so no pattern that
        opens this bundle moves. *)
     snap_law γ γfs cov logstart)%I.

  Global Instance log_ctx_persistent γ bn γfs cov logstart dev :
    Persistent (log_ctx γ bn γfs cov logstart dev).
  Proof. apply _. Qed.

  Lemma log_ctx_lock γ bn γfs cov logstart dev :
    log_ctx γ bn γfs cov logstart dev -∗
    is_lock (ln_lk γ) log_addr "log"%string (log_res γ bn γfs cov logstart).
  Proof. rewrite /log_ctx. iIntros "($ & _)". Qed.

  (* THE FROZEN CELLS ALONE -- log_ctx minus the lock.  The COMMITTER-ONLY
     helpers (write_head, install_trans) run with NO lock held (that is what
     the committing flag buys) and touch only log.dev and log.start, so this
     is the whole of the log context they need.  Giving them [log_ctx]
     instead would make initlog unprovable: initlog CALLS both of them
     before the "log" spinlock can be sealed (sealing it means depositing
     [log_state] -- including the very lh cells those two callees want in
     hand), so [is_lock] does not yet exist at either call site. *)
  Definition log_frozen (logstart : Z)
      (dev : SailStdpp.Values.mword 32) : iProp Σ :=
    (l_dev ↦₄□ dev ∗ l_start ↦₄□ (mword_of_int logstart : mword 32))%I.

  Global Instance log_frozen_persistent logstart dev :
    Persistent (log_frozen logstart dev).
  Proof. apply _. Qed.

  Lemma log_ctx_frozen γ bn γfs cov logstart dev :
    log_ctx γ bn γfs cov logstart dev -∗ log_frozen logstart dev.
  Proof. rewrite /log_ctx /log_frozen. iIntros "(_ & $ & $ & _)". Qed.

  (* the byte view's row, off the context every log function threads *)
  Lemma log_ctx_bytes γ bn γfs cov logstart dev :
    log_ctx γ bn γfs cov logstart dev -∗
    fs_bytes_inv (fs_bytes γfs) (fs_cache γfs) (fs_home_set cov logstart).
  Proof. rewrite /log_ctx. iIntros "(_ & _ & _ & _ & $ & _)". Qed.

  (* ...and the home-set-free form every bread client above takes *)
  Lemma log_ctx_bytes_any γ bn γfs cov logstart dev :
    log_ctx γ bn γfs cov logstart dev -∗ fs_bytes_any γfs.
  Proof.
    iIntros "H". iPoseProof (log_ctx_bytes with "H") as "Hb".
    rewrite /fs_bytes_any. iExists (fs_home_set cov logstart). iExact "Hb".
  Qed.

  Lemma log_ctx_swap γ bn γfs cov logstart dev :
    log_ctx γ bn γfs cov logstart dev -∗ swap_lb (S gen_id).
  Proof. rewrite /log_ctx. iIntros "(_ & _ & _ & $ & _ & _)". Qed.

  (* BLOCK 1'S PARK, off the context end_op already threads (durable-disk
     lane C-3a).  This is the whole of what the commit's collection needs of
     the superblock: [SbPark.sb_park_acc] then opens it for the one ghost
     step the collection runs in. *)
  Lemma log_ctx_sb γ bn γfs cov logstart dev :
    log_ctx γ bn γfs cov logstart dev -∗ sb_parked γfs.
  Proof. rewrite /log_ctx. iIntros "(_ & _ & _ & _ & _ & $ & _)". Qed.

  (* THE LAW, off the context end_op already threads (durable-disk C-8).
     This is the whole of what the commit needs of the file system: it runs
     the law at its own ghost step, gets a pure fact, and hands both
     authorities back.  [LogSnapLaw.snap_law_run] is the reading. *)
  Lemma log_ctx_snap_law γ bn γfs cov logstart dev :
    log_ctx γ bn γfs cov logstart dev -∗ snap_law γ γfs cov logstart.
  Proof. rewrite /log_ctx. iIntros "(_ & _ & _ & _ & _ & _ & $)". Qed.

  (* ---------------------------------------------------------------- *)
  (*  The three ledger transitions                                      *)
  (* ---------------------------------------------------------------- *)

  (* begin_op's grant: mint a fresh op at full budget.  The caller has
     just read the guard true, so it holds
     n + (out+1) * MAXOPBLOCKS <= LOGBLOCKS; [log_reserve_ok] below turns
     that into the new sum tie. *)
  (* ...AND IT IS THE LB'S UNIVERSAL MINT POINT (§G.13).  Every operation
     in the system passes through here with the [ln_ep] auth open, and no
     client can ever mint an lb anywhere else -- the auth lives inside
     [log_res], behind the log spinlock, and a parker does not hold it.  So
     the auth is taken and handed straight back, and [log_epoch_lb_get]
     pays for the bound with nothing. *)
  Lemma log_begin_step (γ : log_names) (om : gmap nat op_entry) (E : nat) :
    (1 <= E)%nat ->
    ghost_map_auth (ln_ops γ) 1 om -∗
    mono_nat_auth_own (ln_ep γ) 1 E ==∗
    ∃ i, ⌜om !! i = None⌝ ∗
      ghost_map_auth (ln_ops γ) 1 (<[i := (MAXOPBLOCKS, ∅, E)]> om) ∗
      mono_nat_auth_own (ln_ep γ) 1 E ∗
      log_opSe γ MAXOPBLOCKS ∅ E.
  Proof.
    intros Hpos. iIntros "Ha Hep".
    set (i := fresh (dom om)).
    assert (Hi : om !! i = None).
    { apply not_elem_of_dom. apply is_fresh. }
    iMod (ghost_map_insert i (MAXOPBLOCKS, (∅ : gset Z), E) Hi
           with "Ha") as "[Ha He]".
    iDestruct (log_epoch_lb_get with "Hep") as "[Hep #Hlb]".
    iModIntro. iExists i. iSplitR; [done|]. iFrame "Ha Hep".
    rewrite /log_opSe. iSplitL "He"; [iExists i; iFrame|].
    iSplitR; [iApply "Hlb"|]. iPureIntro. exact Hpos.
  Qed.

  (* the guard arithmetic: with every entry bounded, the conservative
     (out+1)*MAXOPBLOCKS test implies the exact sum tie after the mint *)
  Lemma log_reserve_ok (n out : nat) (om : gmap nat op_entry) :
    size om = out ->
    (forall i e, om !! i = Some e -> (e.1.1 <= MAXOPBLOCKS)%nat) ->
    (n + (out + 1) * MAXOPBLOCKS <= LOGBLOCKS)%nat ->
    (n + (MAXOPBLOCKS + op_sum om) <= LOGBLOCKS)%nat.
  Proof.
    intros Hsz Hb Hg.
    pose proof (op_sum_bound om MAXOPBLOCKS Hb) as Hsum.
    rewrite Hsz in Hsum. lia.
  Qed.

  (* log_write's APPEND spend: one unit of the op's budget burns, and the
     block joins the op's already-logged set so the NEXT write of it is
     free.  This is the path taken when the block is not yet in
     lh.block[] -- lh.n grows by one and the tie is preserved because the
     sum drops by one ([op_sum_spend]). *)
  Lemma log_spend_step γ (om : gmap nat op_entry) (u : nat) (Sb : gset Z)
      (e0 : nat) (b : Z) :
    ghost_map_auth (ln_ops γ) 1 om -∗ log_opSe γ (S u) Sb e0 ==∗
    ∃ i, ⌜om !! i = Some (S u, Sb, e0)⌝ ∗
      ghost_map_auth (ln_ops γ) 1 (<[i := (u, Sb ∪ {[b]}, e0)]> om) ∗
      log_opSe γ u (Sb ∪ {[b]}) e0.
  Proof.
    iIntros "Ha He". rewrite /log_opSe.
    (* the lb is PERSISTENT and the positivity clause PURE, so every step
       below is a re-pack, not a transfer: both survive the update
       untouched at the SAME [e0] *)
    iDestruct "He" as "(He & #Hlb & %Hpos)". iDestruct "He" as (i) "He".
    iDestruct (ghost_map_lookup with "Ha He") as %Hi.
    iMod (ghost_map_update (u, Sb ∪ {[b]}, e0) with "Ha He")
      as "[Ha He]".
    iModIntro. iExists i. iSplitR; [done|]. iFrame "Ha".
    iSplitL "He"; [iExists i; iFrame|].
    iSplitR; [iApply "Hlb"|]. iPureIntro. exact Hpos.
  Qed.

  (* log_write's ABSORB read: an op that holds a credit for [b] really has
     [b] in lh.block[].  Pure lookup -- nothing is spent and nothing moves;
     the caller combines the returned entry with [log_res]'s
     [e.1.2 ⊆ LB] clause to place [b] in the header. *)
  Lemma log_absorb_step γ (om : gmap nat op_entry) (u : nat) (Sb : gset Z)
      (e0 : nat) :
    ghost_map_auth (ln_ops γ) 1 om -∗ log_opSe γ u Sb e0 -∗
    ∃ i, ⌜om !! i = Some (u, Sb, e0)⌝.
  Proof.
    iIntros "Ha (He & _ & _)". iDestruct "He" as (i) "He".
    iDestruct (ghost_map_lookup with "Ha He") as %Hi.
    iExists i. done.
  Qed.

  (* log_write's GROUP absorb (fs-log.md §G.19): the block is in lh.block[]
     already -- put there by this op's own earlier append or by ANOTHER
     op's, which is the whole point of the group extension -- so no unit
     burns and lh.n does not move, but the block joins THIS op's set all the
     same, exactly as the append path leaves it.  The sum is untouched
     ([op_sum_absorb]), which is what keeps the header tie
     [n + op_sum om <= LOGBLOCKS] across a log_write that does not grow [n].

     The own-set case is the degenerate instance ([Sb ∪ {[b]} = Sb], so the
     insert is the identity map) -- which is why the credited arm needs no
     case split on WHICH credit was presented. *)
  Lemma log_record_step γ (om : gmap nat op_entry) (u : nat) (Sb : gset Z)
      (e0 : nat) (b : Z) :
    ghost_map_auth (ln_ops γ) 1 om -∗ log_opSe γ u Sb e0 ==∗
    ∃ i, ⌜om !! i = Some (u, Sb, e0)⌝ ∗
      ghost_map_auth (ln_ops γ) 1 (<[i := (u, Sb ∪ {[b]}, e0)]> om) ∗
      log_opSe γ u (Sb ∪ {[b]}) e0.
  Proof.
    iIntros "Ha He". rewrite /log_opSe.
    (* the lb is PERSISTENT and the positivity clause PURE, so this is a
       re-pack, not a transfer *)
    iDestruct "He" as "(He & #Hlb & %Hpos)". iDestruct "He" as (i) "He".
    iDestruct (ghost_map_lookup with "Ha He") as %Hi.
    iMod (ghost_map_update (u, Sb ∪ {[b]}, e0) with "Ha He")
      as "[Ha He]".
    iModIntro. iExists i. iSplitR; [done|]. iFrame "Ha".
    iSplitL "He"; [iExists i; iFrame|].
    iSplitR; [iApply "Hlb"|]. iPureIntro. exact Hpos.
  Qed.

  (* end_op's retire: the whole entry goes -- SET AND ALL, which is what
     revokes every absorption credit this op handed out -- and the sum
     drops by exactly the returned budget *)
  (* ...AND THE ALREADY-LOGGED BLOCK SET COMES BACK WITH IT, which is what
     end_op's re-deposit shrinks [op_pending] by ([op_pending_delete]). *)
  Lemma log_end_step γ (om : gmap nat op_entry) (u : nat) :
    ghost_map_auth (ln_ops γ) 1 om -∗ log_opb γ u ==∗
    ∃ i Sb e0, ⌜om !! i = Some (u, Sb, e0)⌝ ∗
      ghost_map_auth (ln_ops γ) 1 (delete i om).
  Proof.
    iIntros "Ha He". rewrite /log_opb /log_opS /log_opSe.
    iDestruct "He" as (Sb e0) "(He & _ & _)". iDestruct "He" as (i) "He".
    iDestruct (ghost_map_lookup with "Ha He") as %Hi.
    iMod (ghost_map_delete with "Ha He") as "Ha".
    iModIntro. iExists i, Sb, e0. by iFrame.
  Qed.

  (* ---------------------------------------------------------------- *)
  (*  THE TRANSACTION AUTHORITY'S TWO STEPS (durable-disk lane A)      *)
  (* ---------------------------------------------------------------- *)

  (* begin_op's mint, beside the ledger's.  Free: allocation at a fresh id,
     and the id never leaves this proof. *)
  Lemma log_tx_mint (γ : log_names) (T : gmap nat unit) :
    ghost_map_auth (ln_tx γ) 1 T ==∗
    ∃ t, ⌜T !! t = None⌝ ∗
      ghost_map_auth (ln_tx γ) 1 (<[t := tt]> T) ∗ log_tx γ.
  Proof.
    iIntros "Ha".
    set (t := fresh (dom T)).
    assert (Ht : T !! t = None).
    { apply not_elem_of_dom. apply is_fresh. }
    iMod (ghost_map_insert t tt Ht with "Ha") as "[Ha He]".
    iModIntro. iExists t. iSplitR; [done|]. iFrame "Ha".
    rewrite /log_tx. iExists t. iExact "He".
  Qed.

  (* end_op's retire, and the reason the tie is cardinality: the token is
     the FULL element, so the id it carries really is a live row -- but the
     token never named it, so no lemma can relate it to the ledger entry
     this same end_op retires.  Both retires drop exactly one row, which is
     what [log_res]'s [size T = size om] is stated to survive. *)
  Lemma log_tx_retire (γ : log_names) (T : gmap nat unit) :
    ghost_map_auth (ln_tx γ) 1 T -∗ log_tx γ ==∗
    ∃ t, ⌜T !! t = Some tt⌝ ∗ ghost_map_auth (ln_tx γ) 1 (delete t T).
  Proof.
    iIntros "Ha He". rewrite /log_tx. iDestruct "He" as (t) "He".
    iDestruct (ghost_map_lookup with "Ha He") as %Ht.
    iMod (ghost_map_delete with "Ha He") as "Ha".
    iModIntro. iExists t. iSplitR; [by destruct (T !! t) as [[]|]; simplify_eq|].
    iExact "Ha".
  Qed.

  (* THE COMMIT'S READING (durable-disk lane A item 5, plan section 4b).
     No open ledger entry means no open transaction, so no share of any
     transaction id can exist anywhere -- which is what the locked registry
     turns into "every inode is well-formed"
     ([InodeRegion.ireg_clean_acc], read as [snap_local] by
     [IregClean.ireg_snap_local_of_ops], which is this lemma's one
     consumer).  It is the cardinality tie read at zero, and nothing else
     in the ledger is consulted. *)
  Lemma log_tx_empty_of_ops (om : gmap nat op_entry) (T : gmap nat unit) :
    size T = size om ->
    om = ∅ ->
    T = ∅.
  Proof.
    intros Hsz ->. rewrite map_size_empty in Hsz.
    by apply map_size_empty_iff.
  Qed.

  (* ...AND THE LAW, READ AT THE LEDGER (durable-disk C-8).  This is the
     form the commit meets: [log_res] carries the transaction authority
     beside the ledger's with [size T = size om], a commit is exactly the
     step at which the ledger is empty, and the byte authority is the one
     the committer has just taken out of [fs_bytes_inv].  It moves NO
     durable resource -- both authorities come straight back -- so the
     commit runs it at its own ghost step. *)
  Lemma log_ctx_snap_law_of_ops (γ : log_names) (bn : bio_names)
      (γfs : fs_names) (cov : gset Z) (logstart : Z)
      (dev : SailStdpp.Values.mword 32)
      (om : gmap nat op_entry) (T : gmap nat unit)
      (Lb : gmap Z (bv 8)) (C : gmap Z (list (bv 8))) :
    size T = size om ->
    om = ∅ ->
    dom C = fs_home_set cov logstart ->
    (forall (b : Z) (bs : list (bv 8)),
       lookup b C = Some bs -> length bs = BioDefs.BSIZE) ->
    bytes_tie Lb C ->
    bytes_dom Lb (fs_home_set cov logstart) ->
    log_ctx γ bn γfs cov logstart dev -∗
    ghost_map_auth (fs_bytes γfs) 1 Lb -∗
    ghost_map_auth (ln_tx γ) 1 T ={⊤ ∖ ↑fsbN}=∗
      ⌜snap_law_ok C (fs_home_set cov logstart)⌝
      ∗ ghost_map_auth (fs_bytes γfs) 1 Lb
      ∗ ghost_map_auth (ln_tx γ) 1 T.
  Proof.
    intros Hsz Hom Hdom Hlens Htie Hdm. iIntros "#Hctx Hb Ht".
    rewrite (log_tx_empty_of_ops om T Hsz Hom).
    iDestruct (log_ctx_snap_law with "Hctx") as "#Hlaw".
    iApply (snap_law_run γ γfs cov logstart Lb C Hdom Hlens Htie Hdm
              with "Hlaw Hb Ht").
  Qed.

  (* an op token against the authority: out >= 1 (kills log_write's
     "outside of trans" panic and end_op's "log.committing" one, via the
     cmt -> out = 0 conjunct) *)
  (* the same fact against a CREDITED op token, at the epoch-exposed form
     (log_write holds THAT one, §G.19) and at the ABI one, which is its
     existential *)
  Lemma log_opSe_positive γ (om : gmap nat op_entry) (u : nat) (Sb : gset Z)
      (e0 : nat) :
    ghost_map_auth (ln_ops γ) 1 om -∗ log_opSe γ u Sb e0 -∗
    ⌜(1 <= size om)%nat⌝.
  Proof.
    iIntros "Ha He". rewrite /log_opSe.
    iDestruct "He" as "(He & _ & _)". iDestruct "He" as (i) "He".
    iDestruct (ghost_map_lookup with "Ha He") as %Hi.
    iPureIntro.
    assert (Hne : om ≠ ∅).
    { intros ->. rewrite lookup_empty in Hi. done. }
    assert (Hs : size om ≠ 0%nat).
    { intros Hz. apply Hne. by apply map_size_empty_iff. }
    lia.
  Qed.

  Lemma log_opS_positive γ (om : gmap nat op_entry) (u : nat) (Sb : gset Z) :
    ghost_map_auth (ln_ops γ) 1 om -∗ log_opS γ u Sb -∗
    ⌜(1 <= size om)%nat⌝.
  Proof.
    iIntros "Ha He". rewrite /log_opS. iDestruct "He" as (e0) "He".
    iApply (log_opSe_positive with "Ha He").
  Qed.

  Lemma log_op_positive γ (om : gmap nat op_entry) (u : nat) :
    ghost_map_auth (ln_ops γ) 1 om -∗ log_op γ u -∗
    ⌜(1 <= size om)%nat⌝.
  Proof.
    iIntros "Ha [He _]". rewrite /log_opb /log_opS.
    iDestruct "He" as (Sb e0) "He".
    iApply (log_opSe_positive with "Ha He").
  Qed.

  (* ...and the same fact off the BUDGET half alone, which is what a walk
     between the arm and the disarm of a row holds *)
  Lemma log_opb_positive γ (om : gmap nat op_entry) (u : nat) :
    ghost_map_auth (ln_ops γ) 1 om -∗ log_opb γ u -∗
    ⌜(1 <= size om)%nat⌝.
  Proof.
    iIntros "Ha He". rewrite /log_opb /log_opS.
    iDestruct "He" as (Sb e0) "He".
    iApply (log_opSe_positive with "Ha He").
  Qed.

  (* ---------------------------------------------------------------- *)
  (*  THE GROUP-ABSORPTION USE LEMMA (fs-log.md §G.2)                   *)
  (* ---------------------------------------------------------------- *)

  (* "a witness at least as new as my op's birth names a block that is in
     the header RIGHT NOW".  Stated over the OPENED authority, because that
     is where every log_write ghost step already runs -- under the log
     spinlock, with [log_res] taken apart.

     THE ARGUMENT, in three steps: my entry is live, so the auth pins its
     birth epoch to the current one ([e0 = E]); the registry never runs
     ahead ([e <= E]); and [e0 <= e] closes the sandwich, so [e = E] and the
     row is one of THIS batch's.  A witness from an older batch has
     [e < E = e0] and fails the premise -- which is the header's revocation
     requirement met by INDEXING, with nothing ever revoked. *)
  Lemma log_use_group (γ : log_names) (om : gmap nat op_entry) (E : nat)
      (X : gset (nat * Z)) (LB : gset Z)
      (u : nat) (Sb : gset Z) (e0 e : nat) (b : Z) :
    (forall i x, om !! i = Some x -> x.2 = E) ->
    (forall e' b', ((e', b') : nat * Z) ∈ X -> (e' <= E)%nat) ->
    (forall c : Z, ((E, c) : nat * Z) ∈ X -> c ∈ LB) ->
    (e0 <= e)%nat ->
    ghost_map_auth (ln_ops γ) 1 om -∗
    own (ln_lg γ) (● X) -∗
    log_opSe γ u Sb e0 -∗
    logged_at γ e b -∗
    ⌜b ∈ LB⌝.
  Proof.
    intros Hlive Hcap Hreg Hle.
    iIntros "Hao Hax He Hw".
    iDestruct (log_absorb_step γ om u Sb e0 with "Hao He") as (i) "%Hi".
    assert (He0 : e0 = E) by exact (Hlive i (u, Sb, e0) Hi).
    iDestruct (logged_at_in with "Hax Hw") as %Hin.
    assert (HeE : (e <= E)%nat) by exact (Hcap e b Hin).
    assert (Hee : e = E) by lia.
    rewrite Hee in Hin. iPureIntro. exact (Hreg b Hin).
  Qed.

  (* THE CREDIT, CASHED (fs-log.md §G.19).  Both admissible forms of
     [log_credit] land on the one fact log_write's absorb path needs -- the
     block is in the header RIGHT NOW -- by different routes, and this is
     the only place either can be spent, because both routes go through the
     opened ledger authority:

     - the OWN-SET form through [log_res]'s credit-soundness clause
       ([Hsub]: a live entry's set is a subset of the header);
     - the GROUP form through [log_use_group]'s epoch sandwich.

     Nothing is consumed: the conclusion is pure, so the caller keeps the
     authority and the entry it handed in. *)
  Lemma log_credit_use (γ : log_names) (om : gmap nat op_entry) (E : nat)
      (X : gset (nat * Z)) (LB : gset Z)
      (u : nat) (Sb : gset Z) (e0 : nat) (b : Z) (cr : bool) :
    (forall i x, om !! i = Some x -> x.2 = E) ->
    (forall e' b', ((e', b') : nat * Z) ∈ X -> (e' <= E)%nat) ->
    (forall c : Z, ((E, c) : nat * Z) ∈ X -> c ∈ LB) ->
    (forall i x, om !! i = Some x -> x.1.2 ⊆ LB) ->
    ghost_map_auth (ln_ops γ) 1 om -∗
    own (ln_lg γ) (● X) -∗
    log_opSe γ u Sb e0 -∗
    log_credit γ cr Sb e0 b -∗
    ⌜cr = true -> b ∈ LB⌝.
  Proof.
    intros Hlive Hcap Hreg Hsub.
    iIntros "Hao Hax He Hcr". rewrite /log_credit.
    destruct cr; [| iPureIntro; discriminate].
    iDestruct "Hcr" as "[%Hin | Hw]".
    - (* own-set: my entry's set is in the header *)
      iDestruct (log_absorb_step γ om u Sb e0 with "Hao He") as (i) "%Hi".
      pose proof (Hsub i (u, Sb, e0) Hi) as Hs. cbn in Hs.
      iPureIntro. intros _. exact (elem_of_weaken _ _ _ Hin Hs).
    - (* group: a witness no older than my op's birth *)
      iDestruct "Hw" as (e) "[#Hw %Hle]".
      iDestruct (log_use_group γ om E X LB u Sb e0 e b Hlive Hcap Hreg Hle
                   with "Hao Hax He Hw") as %Hb.
      iPureIntro. intros _. exact Hb.
  Qed.

  (* ---------------------------------------------------------------- *)
  (*  THE CLIENT-SIDE EPOCH LOWER BOUND (fs-log.md §G.3)                *)
  (* ---------------------------------------------------------------- *)

  (* [log_epoch_lb] and its two auth-facing lemmas are defined up beside
     [log_opSe], which BUNDLES the bound (§G.13) -- [log_begin_step] mints
     it, and that lemma is above this point. *)


  (* THE BUMP, at the commit re-deposit (ProofEndOp's [Hommt] arm): nothing
     physical moves, and no live entry can be falsified because [out = 0]
     there forces [om = ∅]. *)
  Lemma log_epoch_bump (γ : log_names) (E : nat) :
    mono_nat_auth_own (ln_ep γ) 1 E ==∗ mono_nat_auth_own (ln_ep γ) 1 (S E).
  Proof.
    iIntros "H". iMod (mono_nat_own_update (S E) with "H") as "[$ _]";
      [lia | done].
  Qed.

  (* ---------------------------------------------------------------- *)
  (*  Allocation                                                       *)
  (* ---------------------------------------------------------------- *)

  (* GENESIS IS EPOCH ONE, NOT ZERO (fs-log.md §G.17).  The region's
     zero-receipt carries a [⌜v = 0⌝] disjunct for the mkfs image's FREE
     inodes -- records nobody has ever observed and for which no witness
     exists or could exist -- and the only place it must be refuted is
     [InodeRegion.ireg_ep_use], by [1 <= e0 <= v].  That needs every op's
     birth epoch to be at least one, i.e. the epoch counter to start ABOVE
     the observation counter's own "never observed" value.  Nothing else in
     the log ever compares an epoch to a literal: the invariant's clauses
     are [e0 = E] and [e' <= E], and the bump only raises. *)
  Lemma log_epoch_alloc :
    ⊢ |==> ∃ γe : gname, mono_nat_auth_own γe 1 1%nat.
  Proof.
    iMod (mono_nat_own_alloc 1%nat) as (γ) "[Ha _]".
    iModIntro. iExists γ. iFrame.
  Qed.

  Lemma log_reg_alloc :
    ⊢ |==> ∃ γl : gname, own γl (● (∅ : gset (nat * Z))).
  Proof.
    iMod (own_alloc (● (∅ : gset (nat * Z)))) as (γ) "Ha".
    { apply auth_auth_valid. done. }
    iModIntro. iExists γ. iFrame.
  Qed.

  Lemma log_ledger_alloc :
    ⊢ |==> ∃ γops : gname, ghost_map_auth γops 1 (∅ : gmap nat op_entry).
  Proof.
    iMod (ghost_map_alloc_empty (K:=nat) (V:=op_entry)) as (γ) "Ha".
    iModIntro. iExists γ. iFrame.
  Qed.

End LogInv.
