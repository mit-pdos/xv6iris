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
From iris.algebra Require Import auth gmap gset frac.
From iris.base_logic.lib Require Import ghost_map ghost_var invariants mono_nat.
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
(* ...AND THE BIRTH EPOCH, which is how §G's group extension stays
   revocation-sound WITHOUT revoking anything (fs-log.md §G.2/§G.9).  The
   entry records the epoch it was minted in; [log_res]'s auth invariant
   pins every LIVE entry's [e0] to the current epoch, and the bump at the
   commit re-deposit cannot falsify that because [out = 0] there forces
   [om = ∅].  A witness from an older batch then has [e < e0] of every
   later op and is simply unusable -- indexing instead of revocation.

   NOTE THE RE-ASSOCIATION: [(nat * gset Z * nat)] is
   [((nat * gset Z) * nat)], so the budget is [e.1.1], the already-logged
   set is [e.1.2] and the birth epoch is [e.2]. *)
Definition op_entry : Type := (nat * gset Z * nat)%type.

(* THE EPOCH USES THE AMBIENT [mono_natG] FROM [riscvGS] (the power layer's
   [riscvF_genGS], RiscvPtsto.v) -- NOT a new field here.  A second
   [mono_natG] in the same context is the duplicate-class trap of
   claude-notes/durable-notes.md: the two instances make propositions that
   print character-for-character identically fail to unify.  Only the
   [logged_at] registry needs a new functor. *)
Class logG (Σ : gFunctors) := LogG {
  logops_inG :: ghost_mapG Σ nat op_entry;
  loglg_inG :: inG Σ (authR (gsetUR (nat * Z)));
}.
Definition logΣ : gFunctors :=
  #[ghost_mapΣ nat op_entry; GFunctor (authR (gsetUR (nat * Z)))].
Global Instance subG_logΣ {Σ} : subG logΣ Σ -> logG Σ.
Proof. solve_inG. Qed.

Record log_names := MkLogNames {
  ln_lk  : gname;   (* the "log" spinlock *)
  ln_ops : gname;   (* the ledger: op id -> (budget, logged set, birth epoch) *)
  ln_ep  : gname;   (* the BATCH EPOCH, a mono_nat: bumped at every commit *)
  ln_lg  : gname;   (* the append registry: which (epoch, block) pairs were
                       appended.  Fragments are the persistent [logged_at]. *)
}.

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

Section LogInv.
  Context `{!riscvGS Σ, !lockG Σ, !diskGhostG Σ, !bioG Σ, !fsLogG Σ, !logG Σ}.
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
    ((∃ i : nat, i ↪[ln_ops γ] (u, Sb, e0)) ∗ log_epoch_lb γ e0 ∗
     ⌜(1 <= e0)%nat⌝)%I.

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
  Definition log_op (γ : log_names) (u : nat) : iProp Σ :=
    (∃ Sb : gset Z, log_opS γ u Sb)%I.

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
       (om : gmap nat op_entry) (E : nat) (X : gset (nat * Z)),
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
    iMod (ghost_map_insert i (MAXOPBLOCKS, ∅, E) Hi with "Ha") as "[Ha He]".
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
    iMod (ghost_map_update (u, Sb ∪ {[b]}, e0) with "Ha He") as "[Ha He]".
    iModIntro. iExists i. iSplitR; [done|]. iFrame "Ha".
    iSplitL "He"; [iExists i; iFrame|].
    iSplitR; [iApply "Hlb"|]. iPureIntro. exact Hpos.
  Qed.

  (* log_write's ABSORB read: an op that holds a credit for [b] really has
     [b] in lh.block[].  Pure lookup -- nothing is spent and nothing moves;
     the caller combines the returned entry with [log_res]'s
     [e.2 ⊆ LB] clause to place [b] in the header. *)
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
    iMod (ghost_map_update (u, Sb ∪ {[b]}, e0) with "Ha He") as "[Ha He]".
    iModIntro. iExists i. iSplitR; [done|]. iFrame "Ha".
    iSplitL "He"; [iExists i; iFrame|].
    iSplitR; [iApply "Hlb"|]. iPureIntro. exact Hpos.
  Qed.

  (* end_op's retire: the whole entry goes -- SET AND ALL, which is what
     revokes every absorption credit this op handed out -- and the sum
     drops by exactly the returned budget *)
  Lemma log_end_step γ (om : gmap nat op_entry) (u : nat) :
    ghost_map_auth (ln_ops γ) 1 om -∗ log_op γ u ==∗
    ∃ i Sb e0, ⌜om !! i = Some (u, Sb, e0)⌝ ∗
      ghost_map_auth (ln_ops γ) 1 (delete i om).
  Proof.
    iIntros "Ha He". rewrite /log_op /log_opS /log_opSe.
    iDestruct "He" as (Sb e0) "(He & _ & _)". iDestruct "He" as (i) "He".
    iDestruct (ghost_map_lookup with "Ha He") as %Hi.
    iMod (ghost_map_delete with "Ha He") as "Ha".
    iModIntro. iExists i, Sb, e0. by iFrame.
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
    iIntros "Ha He". rewrite /log_op /log_opS /log_opSe.
    iDestruct "He" as (Sb e0) "(He & _ & _)". iDestruct "He" as (i) "He".
    iDestruct (ghost_map_lookup with "Ha He") as %Hi.
    iPureIntro.
    assert (Hne : om ≠ ∅).
    { intros ->. rewrite lookup_empty in Hi. done. }
    assert (Hs : size om ≠ 0%nat).
    { intros Hz. apply Hne. by apply map_size_empty_iff. }
    lia.
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
