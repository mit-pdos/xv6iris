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
   Conditionally inside (cmt = false): [log_batch] -- the lh cells with
   their write-set reading W, BOTH FsBlocks auths (the freeze-by-auth
   that makes log_write and the committer the ONLY writers of the logged
   view), the log-side dirty halves recording exactly W's membership over
   the whole covered range, and the log-region + header client halves.
   end_op's last-out path flips cmt := 1 and takes [log_batch] out
   linearly, mirroring the code running commit with no locks held;
   begin_op sleeps on cmt, so out stays 0 across a commit, and
   ⌜cmt = true -> out = 0⌝ rides as a pure conjunct (what kills end_op's
   own "log.committing" panic: an op token in hand forces out >= 1). *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import auth gmap frac.
From iris.base_logic.lib Require Import ghost_map ghost_var invariants.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvModelBytes.
Require Import RiscvLang.   (* [GenId]/[gen_id]: [log_ctx]'s swap receipt *)
Require Import RiscvPtsto.
Require Import WpLock.
Require Import DiskPtsto.
Require Import BioInv.
Require Import FsBlocks.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Local Open Scope Z_scope.

(* ------------------------------------------------------------------ *)
(*  Geometry (offsets confirmed against kernel-rocq/KernelInstrs.v):    *)
(*  struct log @ KernelSyms.log: spinlock@0 (24B), start@24,            *)
(*  outstanding@28, committing@32, dev@36, ncommit@40, lh.n@44,         *)
(*  lh.block[i]@48+4i (LOGBLOCKS = 30 entries).                         *)
(* ------------------------------------------------------------------ *)

Definition MAXOPBLOCKS : nat := 10%nat.
Definition LOGBLOCKS : nat := 30%nat.

Definition log_addr : mword 64 := mword_of_int KernelSyms.log.
Definition log_pa : Arch.pa := log_addr.

Definition l_start   : Arch.pa := pa_add log_pa 24.
Definition l_out     : Arch.pa := pa_add log_pa 28.
Definition l_cmt     : Arch.pa := pa_add log_pa 32.
Definition l_dev     : Arch.pa := pa_add log_pa 36.
Definition l_ncommit : Arch.pa := pa_add log_pa 40.
Definition lh_block (i : nat) : Arch.pa := pa_add log_pa (48 + 4 * i)%nat.
Definition lh_n_pa   : Arch.pa := pa_add log_pa 44.

(* the on-disk block-number layout, from the superblock the boot client
   read: the header at [logstart], the LOGBLOCKS slots right after. *)
Definition log_hdr_bno (logstart : Z) : Z := logstart.
Definition log_slot_bno (logstart : Z) (i : nat) : Z :=
  logstart + 1 + Z.of_nat i.
Definition log_region_set (logstart : Z) : gset Z :=
  list_to_set ((fun i => log_slot_bno logstart i) <$> seq 0 LOGBLOCKS)
  ∪ {[ log_hdr_bno logstart ]}.

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
Definition hdr_n (bs : list (bv 8)) : Z := assemble_bytes (take 4 bs).

Lemma hdr_n_nonneg (bs : list (bv 8)) : 0 <= hdr_n bs.
Proof. rewrite /hdr_n. apply assemble_bytes_bound. Qed.

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
   the CLIENT of the header block and the LOGBLOCKS slots (log_batch holds
   their [fsblock] halves), and write_head / write_log / install_trans
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
Definition op_entry : Type := (nat * gset Z)%type.

Class logG (Σ : gFunctors) := LogG {
  logops_inG :: ghost_mapG Σ nat op_entry;
}.
Definition logΣ : gFunctors := #[ghost_mapΣ nat op_entry].
Global Instance subG_logΣ {Σ} : subG logΣ Σ -> logG Σ.
Proof. solve_inG. Qed.

Record log_names := MkLogNames {
  ln_lk  : gname;   (* the "log" spinlock *)
  ln_ops : gname;   (* the ledger: op id -> (budget, blocks already logged) *)
}.

(* the sum of all remaining budgets -- the SETS play no part in the tie *)
Definition op_sum (om : gmap nat op_entry) : nat :=
  map_fold (fun _ e acc => (e.1 + acc)%nat) 0%nat om.

Lemma op_sum_empty : op_sum ∅ = 0%nat.
Proof. reflexivity. Qed.

Lemma op_sum_insert (om : gmap nat op_entry) (i : nat) (e : op_entry) :
  om !! i = None ->
  op_sum (<[i := e]> om) = (e.1 + op_sum om)%nat.
Proof.
  intros Hi. rewrite /op_sum.
  apply (map_fold_insert_L
           (fun (_ : nat) (e : op_entry) (acc : nat) => (e.1 + acc)%nat));
    [|exact Hi].
  intros j1 j2 z1 z2 y _ _ _. lia.
Qed.

Lemma op_sum_delete (om : gmap nat op_entry) (i : nat) (e : op_entry) :
  om !! i = Some e ->
  op_sum om = (e.1 + op_sum (delete i om))%nat.
Proof.
  intros Hi.
  rewrite -{1}(insert_delete om i e Hi).
  apply op_sum_insert, lookup_delete.
Qed.

(* the conservative bound begin_op's guard reasons with: every entry is
   at most b, so the sum is at most size * b *)
Lemma op_sum_bound (om : gmap nat op_entry) (b : nat) :
  (forall i e, om !! i = Some e -> (e.1 <= b)%nat) ->
  (op_sum om <= size om * b)%nat.
Proof.
  induction om as [|i e om Hi IH] using map_ind.
  { intros _. rewrite op_sum_empty map_size_empty. lia. }
  intros Hb.
  rewrite op_sum_insert // map_size_insert_None //.
  assert (Hu : (e.1 <= b)%nat).
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
Lemma op_sum_spend (om : gmap nat op_entry) (i u : nat) (Sb Sb' : gset Z) :
  om !! i = Some (S u, Sb) ->
  op_sum (<[i := (u, Sb')]> om) = (op_sum om - 1)%nat.
Proof.
  intros Hi.
  assert (Hj : <[i := (u, Sb')]> om !! i = Some (u, Sb'))
    by apply lookup_insert.
  rewrite (op_sum_delete om i (S u, Sb) Hi).
  rewrite (op_sum_delete (<[i := (u, Sb')]> om) i (u, Sb') Hj).
  rewrite delete_insert_delete. cbn. lia.
Qed.

(* ABSORBING changes the set only, so the sum is untouched -- which is the
   whole point: the tie [n + op_sum om <= LOGBLOCKS] survives a log_write
   that does not grow [n]. *)
Lemma op_sum_absorb (om : gmap nat op_entry) (i u : nat) (Sb Sb' : gset Z) :
  om !! i = Some (u, Sb) ->
  op_sum (<[i := (u, Sb')]> om) = op_sum om.
Proof.
  intros Hi.
  assert (Hj : <[i := (u, Sb')]> om !! i = Some (u, Sb'))
    by apply lookup_insert.
  rewrite (op_sum_delete om i (u, Sb) Hi).
  rewrite (op_sum_delete (<[i := (u, Sb')]> om) i (u, Sb') Hj).
  rewrite delete_insert_delete. reflexivity.
Qed.

Section LogInv.
  Context `{!riscvGS Σ, !lockG Σ, !diskGhostG Σ, !bioG Σ, !fsLogG Σ, !logG Σ}.
  (* the ambient generation: [log_ctx] carries this era's SWAP RECEIPT, which
     is what every WAL fupd curries to prove the crash record's arm is its
     own ([FsCrash.fs_arm_acc]).  Implicit, so no spec statement changes. *)
  Context `{GEN : GenId}.

  (* ---------------------------------------------------------------- *)
  (*  An active operation                                              *)
  (* ---------------------------------------------------------------- *)

  (* one ledger entry with remaining budget u AND the blocks this op has
     already appended; the id is existential -- no client ever needs it,
     and the ghost steps below re-locate the entry by ownership. *)
  Definition log_opS (γ : log_names) (u : nat) (Sb : gset Z) : iProp Σ :=
    (∃ i : nat, i ↪[ln_ops γ] (u, Sb))%I.

  (* THE FORM EVERY EXISTING CALLER USES.  Forgetting the set is what keeps
     this change additive: balloc, bmap, iupdate, writei, begin_op and
     end_op all thread [log_op] and are untouched, because a budget claim
     that says nothing about which blocks were logged is exactly the old
     contract.  Only the two arms that CLAIM the absorption credit --
     log_write's and bfree's -- mention [log_opS], and only itrunc, which
     needs the credit to survive 269 frees, threads it. *)
  Definition log_op (γ : log_names) (u : nat) : iProp Σ :=
    (∃ Sb : gset Z, log_opS γ u Sb)%I.

  Global Instance log_opS_timeless γ u Sb : Timeless (log_opS γ u Sb).
  Proof. apply _. Qed.

  Global Instance log_op_timeless γ u : Timeless (log_op γ u).
  Proof. apply _. Qed.

  (* the forgetful direction, used wherever a credited op is handed to a
     callee that does not care *)
  Lemma log_opS_op γ u Sb : log_opS γ u Sb -∗ log_op γ u.
  Proof. iIntros "H". rewrite /log_op. iExists Sb. iFrame. Qed.

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
  (*  half rides [log_batch], so it is exactly as available as the batch  *)
  (*  is -- in the lock between commits, checked out by the committer     *)
  (*  during one.  The BETWEEN-COMMITS form carries the pure conjunct     *)
  (*  [lm_hdr M = (0, [])]: with the batch in the lock the on-disk header *)
  (*  is clean, which is what a log-fill fupd reads out of it, and the    *)
  (*  final [write_head] of a commit (the CLEAR) is what re-establishes   *)
  (*  it before the batch goes back.  Both forms keep [M] existential so  *)
  (*  that no statement above this file grows a binder for it.            *)
  (* ---------------------------------------------------------------- *)

  (* the whole variable, as the era boot bundle mints it: no custody has
     been taken yet, so both halves are the era's *)
  Definition log_mirror_full : iProp Σ :=
    (∃ M : log_mirror, ghost_var mirror_name 1 M)%I.

  (* THE ERA'S HALF AT A RECORDED HEADER PICTURE.  [h] is the ON-DISK
     header's [FsCrash.hdr_dec] reading, and it is the ONLY field a WAL fupd
     ever reads out of the mirror: the log-fill kind needs a CLEAN header,
     the install kind needs the header to be the (n, W) the commit just
     wrote (which is what tells it the block it is overwriting is a LOGGED
     one, so recovery re-installs it anyway).  The slot contents are recorded
     too ([RiscvPtsto.log_mirror]'s second field) but no fupd has to read
     them -- [FsCrash.fs_recovery_install] does not depend on the value a
     home write stores.
     Kept ONE definition, indexed by [h], because the commit and clear kinds
     move the picture: [log_mirror_clean] is its [(0, [])] instance and
     [log_batch] therefore reads exactly as before. *)
  Definition log_mirror_at (h : nat * list Z) : iProp Σ :=
    (∃ M : log_mirror,
       ghost_var mirror_name (1/2) M ∗ ⌜lm_hdr M = h⌝)%I.

  Global Instance log_mirror_at_timeless h : Timeless (log_mirror_at h).
  Proof. rewrite /log_mirror_at. apply _. Qed.

  Definition log_mirror_clean : iProp Σ := log_mirror_at (0%nat, []).

  (* ---------------------------------------------------------------- *)
  (*  The batch bundle (checked out wholesale by the committer)        *)
  (* ---------------------------------------------------------------- *)

  (* Parameters: bn -- the bio layer's names (for the SLOT POOL); γfs --
     the FsBlocks ghosts; cov -- the covered range the bio layer runs at;
     logstart -- the sb's log start block.  [n] is a parameter (not an
     existential) because the ledger's sum tie in [log_res] mentions it. *)
  Definition log_batch (bn : bio_names) (γfs : fs_names) (cov : gset Z)
      (logstart : Z) (n : nat) (LB : gset Z) : iProp Σ :=
    (∃ (W : list (SailStdpp.Values.mword 32))
       (L : gmap Z (list (bv 8))) (D : gmap Z bool),
       ⌜n = length W /\ (n <= LOGBLOCKS)%nat⌝ ∗
       (* LB IS EXPOSED, not existential, so that [log_res] -- which is
          where the ledger authority lives -- can state that every op's
          already-logged set is really a set of logged blocks.  Without
          lifting it out of the existential the two halves of that tie sit
          in different resources and cannot be related. *)
       ⌜LB = list_to_set (map uint W)⌝ ∗
       ⌜NoDup (map uint W)⌝ ∗
       (* logged blocks are covered HOME blocks: never the log's own
          storage, never the header *)
       ⌜forall w, w ∈ W -> uint w ∈ cov /\
          ~ (uint w ∈ log_region_set logstart)⌝ ∗
       lh_n_pa ↦₄ (mword_of_int (Z.of_nat n) : mword 32) ∗
       ([∗ list] i ↦ w ∈ W, lh_block i ↦₄ w) ∗
       ([∗ list] i ∈ seq n (LOGBLOCKS - n),
          ∃ junk : SailStdpp.Values.mword 32, lh_block i ↦₄ junk) ∗
       (* the freeze-by-auth: both FsBlocks auths live HERE *)
       ghost_map_auth (fs_L γfs) 1 L ∗
       ghost_map_auth (fs_dirty γfs) 1 D ∗
       (* the log side's dirty halves, over the WHOLE covered range,
          recording exactly W's membership (the bio payloads hold the
          other halves) *)
       ([∗ set] b ∈ cov,
          b ↪[fs_dirty γfs]{#(1/2)} (bool_decide (b ∈ map uint W))) ∗
       (* the log region's CLIENT halves: the log is its own client for
          the header block and the LOGBLOCKS slots *)
       (∃ bsh, fsblock γfs (log_hdr_bno logstart) bsh) ∗
       ([∗ list] i ∈ seq 0 LOGBLOCKS,
          ∃ bs, fsblock γfs (log_slot_bno logstart i) bs) ∗
       (* THE SLOT POOL: one [bslot] per free log slot, plus a working
          margin of 2 (the committer's two in-flight breads; the copy
          loop and install both hold at most two buffers at once).  This
          is what makes log_write's refund UNCONDITIONAL -- the append
          path's n++ releases a pool unit to replace the one bpin
          absorbed, the absorb path never takes one -- and what lets
          install_trans's bunpins deposit their freed units back instead
          of end_op dropping them: pool + n = LOGBLOCKS + 2 is
          inductive. *)
       bslots bn ((LOGBLOCKS - n) + 2)%nat ∗
       (* THE ERA'S MIRROR HALF, at the between-commits picture *)
       log_mirror_clean)%I.

  (* ---------------------------------------------------------------- *)
  (*  The lock's resource                                              *)
  (* ---------------------------------------------------------------- *)

  Definition log_res (γ : log_names) (bn : bio_names) (γfs : fs_names)
      (cov : gset Z) (logstart : Z) : iProp Σ :=
    (∃ (out : nat) (cmt : bool) (nc : SailStdpp.Values.mword 32)
       (om : gmap nat op_entry),
       l_out ↦₄ (mword_of_int (Z.of_nat out) : mword 32) ∗
       l_cmt ↦₄ (mword_of_int (if cmt then 1 else 0) : mword 32) ∗
       l_ncommit ↦₄ nc ∗
       ghost_map_auth (ln_ops γ) 1 om ∗
       ⌜size om = out⌝ ∗
       ⌜forall i e, om !! i = Some e -> (e.1 <= MAXOPBLOCKS)%nat⌝ ∗
       (* from the guard: (out+1)*MAXOPBLOCKS <= LOGBLOCKS at every
          increment, so the cell word stays a faithful small int *)
       ⌜(out <= 3)%nat⌝ ∗
       ⌜cmt = true -> out = 0%nat⌝ ∗
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
          ⌜forall i e, om !! i = Some e -> e.2 ⊆ LB⌝ ∗
          log_batch bn γfs cov logstart n LB))%I.

  (* the persistent bundle every log function shares: the sealed lock and
     the two cells initlog wrote once and froze *)
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
     swap_lb (S gen_id))%I.

  Global Instance log_ctx_persistent γ bn γfs cov logstart dev :
    Persistent (log_ctx γ bn γfs cov logstart dev).
  Proof. apply _. Qed.

  (* THE FROZEN CELLS ALONE -- log_ctx minus the lock.  The COMMITTER-ONLY
     helpers (write_head, install_trans) run with NO lock held (that is what
     the committing flag buys) and touch only log.dev and log.start, so this
     is the whole of the log context they need.  Giving them [log_ctx]
     instead would make initlog unprovable: initlog CALLS both of them
     before the "log" spinlock can be sealed (sealing it means depositing
     [log_batch] -- including the very lh cells those two callees want in
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

  Lemma log_ctx_swap γ bn γfs cov logstart dev :
    log_ctx γ bn γfs cov logstart dev -∗ swap_lb (S gen_id).
  Proof. rewrite /log_ctx. iIntros "(_ & _ & _ & $)". Qed.

  (* ---------------------------------------------------------------- *)
  (*  The three ledger transitions                                      *)
  (* ---------------------------------------------------------------- *)

  (* begin_op's grant: mint a fresh op at full budget.  The caller has
     just read the guard true, so it holds
     n + (out+1) * MAXOPBLOCKS <= LOGBLOCKS; [log_reserve_ok] below turns
     that into the new sum tie. *)
  Lemma log_begin_step γ (om : gmap nat op_entry) :
    ghost_map_auth (ln_ops γ) 1 om ==∗
    ∃ i, ⌜om !! i = None⌝ ∗
      ghost_map_auth (ln_ops γ) 1 (<[i := (MAXOPBLOCKS, ∅)]> om) ∗
      log_opS γ MAXOPBLOCKS ∅.
  Proof.
    iIntros "Ha".
    set (i := fresh (dom om)).
    assert (Hi : om !! i = None).
    { apply not_elem_of_dom. apply is_fresh. }
    iMod (ghost_map_insert i (MAXOPBLOCKS, ∅) Hi with "Ha") as "[Ha He]".
    iModIntro. iExists i. iSplitR; [done|]. iFrame "Ha".
    rewrite /log_opS. iExists i. iFrame.
  Qed.

  (* the guard arithmetic: with every entry bounded, the conservative
     (out+1)*MAXOPBLOCKS test implies the exact sum tie after the mint *)
  Lemma log_reserve_ok (n out : nat) (om : gmap nat op_entry) :
    size om = out ->
    (forall i e, om !! i = Some e -> (e.1 <= MAXOPBLOCKS)%nat) ->
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
      (b : Z) :
    ghost_map_auth (ln_ops γ) 1 om -∗ log_opS γ (S u) Sb ==∗
    ∃ i, ⌜om !! i = Some (S u, Sb)⌝ ∗
      ghost_map_auth (ln_ops γ) 1 (<[i := (u, Sb ∪ {[b]})]> om) ∗
      log_opS γ u (Sb ∪ {[b]}).
  Proof.
    iIntros "Ha He". rewrite /log_opS. iDestruct "He" as (i) "He".
    iDestruct (ghost_map_lookup with "Ha He") as %Hi.
    iMod (ghost_map_update (u, Sb ∪ {[b]}) with "Ha He") as "[Ha He]".
    iModIntro. iExists i. iSplitR; [done|]. iFrame "Ha".
    iExists i. iFrame.
  Qed.

  (* log_write's ABSORB read: an op that holds a credit for [b] really has
     [b] in lh.block[].  Pure lookup -- nothing is spent and nothing moves;
     the caller combines the returned entry with [log_res]'s
     [e.2 ⊆ LB] clause to place [b] in the header. *)
  Lemma log_absorb_step γ (om : gmap nat op_entry) (u : nat) (Sb : gset Z) :
    ghost_map_auth (ln_ops γ) 1 om -∗ log_opS γ u Sb -∗
    ∃ i, ⌜om !! i = Some (u, Sb)⌝.
  Proof.
    iIntros "Ha He". rewrite /log_opS. iDestruct "He" as (i) "He".
    iDestruct (ghost_map_lookup with "Ha He") as %Hi.
    iExists i. done.
  Qed.

  (* end_op's retire: the whole entry goes -- SET AND ALL, which is what
     revokes every absorption credit this op handed out -- and the sum
     drops by exactly the returned budget *)
  Lemma log_end_step γ (om : gmap nat op_entry) (u : nat) :
    ghost_map_auth (ln_ops γ) 1 om -∗ log_op γ u ==∗
    ∃ i Sb, ⌜om !! i = Some (u, Sb)⌝ ∗
      ghost_map_auth (ln_ops γ) 1 (delete i om).
  Proof.
    iIntros "Ha He". rewrite /log_op /log_opS.
    iDestruct "He" as (Sb i) "He".
    iDestruct (ghost_map_lookup with "Ha He") as %Hi.
    iMod (ghost_map_delete with "Ha He") as "Ha".
    iModIntro. iExists i, Sb. by iFrame.
  Qed.

  (* an op token against the authority: out >= 1 (kills log_write's
     "outside of trans" panic and end_op's "log.committing" one, via the
     cmt -> out = 0 conjunct) *)
  (* the same fact against a CREDITED op token *)
  Lemma log_opS_positive γ (om : gmap nat op_entry) (u : nat) (Sb : gset Z) :
    ghost_map_auth (ln_ops γ) 1 om -∗ log_opS γ u Sb -∗
    ⌜(1 <= size om)%nat⌝.
  Proof.
    iIntros "Ha He". rewrite /log_opS. iDestruct "He" as (i) "He".
    iDestruct (ghost_map_lookup with "Ha He") as %Hi.
    iPureIntro.
    assert (Hne : om ≠ ∅).
    { intros ->. rewrite lookup_empty in Hi. done. }
    assert (Hs : size om ≠ 0%nat).
    { intros Hz. apply Hne. by apply map_size_empty_iff. }
    lia.
  Qed.

  Lemma log_op_positive γ (om : gmap nat op_entry) (u : nat) :
    ghost_map_auth (ln_ops γ) 1 om -∗ log_op γ u -∗
    ⌜(1 <= size om)%nat⌝.
  Proof.
    iIntros "Ha He". rewrite /log_op /log_opS.
    iDestruct "He" as (Sb i) "He".
    iDestruct (ghost_map_lookup with "Ha He") as %Hi.
    iPureIntro.
    assert (Hne : om ≠ ∅).
    { intros ->. rewrite lookup_empty in Hi. done. }
    assert (Hs : size om ≠ 0%nat).
    { intros Hz. apply Hne. by apply map_size_empty_iff. }
    lia.
  Qed.

  (* ---------------------------------------------------------------- *)
  (*  Allocation                                                       *)
  (* ---------------------------------------------------------------- *)

  Lemma log_ledger_alloc :
    ⊢ |==> ∃ γops : gname, ghost_map_auth γops 1 (∅ : gmap nat op_entry).
  Proof.
    iMod (ghost_map_alloc_empty (K:=nat) (V:=op_entry)) as (γ) "Ha".
    iModIntro. iExists γ. iFrame.
  Qed.

End LogInv.
