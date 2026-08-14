(* IcacheInv.v -- the INODE CACHE's definitional layer: the [itable]'s
   geometry, the reference-count ghost state, the two homes the physical
   cells live in (the itable spinlock and a shared invariant over the [ref]
   words), and the pure facts about an inode that the model owed [itrunc].
   Design: claude-notes/design/fs-icache.md.

   Nothing here proves a step about any instruction and nothing here is a
   function contract: iget / idup / iput are owned by another effort, and
   this file is what their contracts will be stated over.

   ---- WHY THE [ref] WORDS ARE IN AN INVARIANT, NOT IN THE LOCK ---------

   xv6's own comment says [itable.lock] protects [ref], [dev] and [inum].
   That is true of every WRITE, and it is what the ftable does
   (claude-notes/design/file-table.md), but it is NOT true of every read:
   [ilock] and [iunlock] load [ip->ref] holding no spinlock at all, purely
   to refute their [panic] arms.  A cell a lock's resource owns cannot be
   read by a thread that does not hold the lock, and a cell whose fraction
   has been handed out to reference holders cannot be WRITTEN by
   [iget]/[idup]/[iput], which do hold the lock.  So the [ref] words go in
   an Iris invariant and the authority is SPLIT: half inside the invariant,
   half inside the lock's resource.  Holding the lock's half is what pins
   [M] across a read-modify-write ([lw; addiw; sw]); holding a reference
   fragment is what lets a lock-free reader conclude its slot's count is at
   least one.  [dev] and [inum] keep the ftable's discipline exactly --
   fractional, immutable while the entry is live.

   ---- AND WHY THE LIVENESS POOL IS IN THE SAME INVARIANT ---------------

   A SHARE ([IcacheRef.inode_shr], design §14.6) is an identity slice with
   NO count fragment -- [positiveR] has no zero, so under this algebra a
   share simply is not an [icacheUR] element (§14.5).  It therefore cannot
   use [iref_lookup] to learn its slot is live, and a share-holding
   [ilock] still has to refute the [ref < 1] panic holding no lock.

   [live_pool] is what it uses instead: ONE fractional unit per slot, whose
   WHOLE is held right here whenever the slot is free.  Owning any slice of
   it therefore refutes freeness ([live_slot_live]) -- the support clause
   is OWNED, not asserted, so no [dom]-inclusion invariant has to be carried
   or re-established.  A live slot's unit is split [qt] to the reference
   holders (inside [iref_tok], canonically paired with their identity
   fraction) and [1 - qt] to this invariant's arm, so the LAST close
   reassembles the whole unit out of the closer's own slice plus the arm and
   RETIRES the slot -- §14.6's "mass conservation IS the witness", and the
   reason [ProofIput]'s REF-1 derivations did not have to change.

   ---- WHAT IS DELIBERATELY NOT HERE -----------------------------------

   The per-entry CONTENT (ip->valid, the five metadata cells, the thirteen
   addrs cells, the file's blocks) lives in [IcacheEscrow.ic_escrow], the
   three-armed per-entry escrow built ON TOP of this file: the sleeplock
   keeps only that escrow's checkout token.  This file supplies the pieces
   it is keyed by -- the identity cells, the reference algebra and the
   [ref]-word invariant -- and nothing above them.                         *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.algebra Require Import auth gmap frac numbers.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap invariants own ghost_var.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvPtsto RiscvExtras.
Require Import WpLock SleepLock.
Require Import LogInv.
Require Export IcacheRef.   (* the geometry, the algebra, [inode_ref] *)
Require Import InodeInv.
Require Import IrefSlots.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.

Local Open Scope Z_scope.

(* ===================================================================== *)
(*  1.  THE itable's GEOMETRY, read off the image                         *)
(* ===================================================================== *)

(*    struct { struct spinlock lock; struct inode inode[NINODE]; } itable;

   Three instructions in the tracked image pin all of it, and none of them
   is a transcription of the C:

     iget +0x22   addi s1,s1,-1796  # 80020888 <itable+0x18>
                       s1 = &itable.inode[0]        ==> the lock is 24 B
     iget +0x3c   addi s1,s1,136    the scan's stride  ==> sizeof = 136
     iget +0x40   beq  s1,a3,...    with
          +0x2e   addi a3,a3,900    # 80022318 <log>
                       &itable.inode[NINODE] IS the address of the next
                       symbol, so 24 + 136*NINODE = log - itable.

   iinit's loop corroborates both from the other end: it starts at
   [itable+0x28] = &inode[0].lock (entry + 16, the sleeplock's own offset,
   [InodeInv.i_lock]) and stops at [log+0x10] = &inode[NINODE].lock.

   24 is [sizeof(struct spinlock)] -- uint + 4 bytes of padding + two
   pointers -- and 136 is [sizeof(struct inode)] = 132 rounded up to the 8
   the embedded sleeplock forces (InodeInv.v's header).                    *)

(* [NINODE], [itable_lock], [ISLOTSZ], [ientry] and its four arithmetic
   corollaries now live in [IcacheRef.v] (re-exported below) -- the file
   table needs them and sits underneath this one.  See its header. *)

(* ===================================================================== *)
(*  2.  WHERE itrunc's FIRST OWED PREMISE LIVES: [cov] BOUNDS THE FS      *)
(* ===================================================================== *)

(* [bfree] needs [0 <= b < size] of every block it frees, and
   [SpecItrunc.v] takes that, slot by slot, as a hypothesis the model
   cannot supply -- recorded as owed in claude-notes/design/fs-inode.md,
   which guesses it belongs either in [blkmap_wf] (which would then have to
   take [size]) or in whatever invariant ilock establishes.

   NEITHER IS NEEDED.  [blkmap_wf] ALREADY says every block an inode names
   is in [cov]; what is missing is one PURE geometry fact relating [cov] to
   the file system's size -- of exactly the same character as
   [LogInv.log_geom_ok], and supplied from the same place.  With it the
   owed premise is a two-line corollary and no invariant moves.

   It is true by construction: [FsBoot.fs_cov_in cov ndisk] already bounds
   every covered block by the disk image's length, and [size] is [sb.size],
   the same number mkfs wrote.                                             *)
Definition cov_below (cov : gset Z) (size : Z) : Prop :=
  forall z : Z, z ∈ cov -> z < size.

(* ...and it IS dischargeable, which is the standard this project holds a
   new premise to.  The hypothesis below is [FsBoot.fs_cov_in cov ndisk]
   spelled out (restated rather than imported, so this file stays under the
   boot layer): every covered block lies inside the disk image.  With the
   superblock's [size] field describing that same image -- mkfs writes
   [sb.size = FSSIZE] and lays the image out in exactly that many blocks --
   [cov_below] follows by arithmetic and nothing has to be assumed. *)
Lemma cov_below_of_image (cov : gset Z) (ndisk : nat) (size : Z) :
  (forall b : Z, b ∈ cov -> 0 < b /\ 1024 * (b + 1) <= Z.of_nat ndisk) ->
  Z.of_nat ndisk <= 1024 * size ->
  cov_below cov size.
Proof. intros Hin Hsz z Hz. destruct (Hin z Hz) as [_ Hb]. lia. Qed.

(* EXACTLY [SpecItrunc.v]'s premise (its [0 <] half comes free from
   [cov_ok]), so a caller already holding [log_geom_ok] -- every one of
   them does -- supplies the whole thing from [cov_below] alone. *)
Lemma blkmap_slot_inrange (cov : gset Z) (logstart size : Z) (bm : blkmap) :
  cov_ok cov -> cov_below cov size -> blkmap_wf cov logstart bm ->
  forall i : nat, (i <= MAXFILE)%nat -> bv_unsigned (bm_slot bm i) <> 0 ->
    0 < bv_unsigned (bm_slot bm i) < size.
Proof.
  intros Hok Hbel (_ & _ & _ & Hcov & _) i Hi Hnz.
  destruct (Hcov i Hi Hnz) as [Hin _].
  split; [exact (proj1 (Hok _ Hin)) | exact (Hbel _ Hin)].
Qed.

(* the same fact in the two spellings a caller of [bfree] normally has *)
Lemma blkmap_get_inrange (cov : gset Z) (logstart size : Z) (bm : blkmap) (i : nat) :
  cov_ok cov -> cov_below cov size -> blkmap_wf cov logstart bm ->
  (i < MAXFILE)%nat -> bv_unsigned (blkmap_get bm i) <> 0 ->
  0 < bv_unsigned (blkmap_get bm i) < size.
Proof.
  intros Hok Hbel Hwf Hi Hnz.
  rewrite -(bm_slot_lt bm i Hi).
  apply (blkmap_slot_inrange cov logstart size bm Hok Hbel Hwf i ltac:(lia)).
  rewrite (bm_slot_lt bm i Hi). exact Hnz.
Qed.

Lemma blkmap_ind_inrange (cov : gset Z) (logstart size : Z) (bm : blkmap) :
  cov_ok cov -> cov_below cov size -> blkmap_wf cov logstart bm ->
  bv_unsigned (bm_ind bm) <> 0 ->
  0 < bv_unsigned (bm_ind bm) < size.
Proof.
  intros Hok Hbel Hwf Hnz.
  rewrite -bm_slot_top.
  apply (blkmap_slot_inrange cov logstart size bm Hok Hbel Hwf MAXFILE ltac:(lia)).
  rewrite bm_slot_top. exact Hnz.
Qed.

(* ===================================================================== *)
(*  3.  WHERE itrunc's SECOND OWED PREMISE LIVES: A BLOCK IS BSIZE BYTES  *)
(* ===================================================================== *)

(* MOVED to [InodeInv.v] by design §13.12(b), together with its three laws
   ([inode_sized], [inode_sized_zero], [inode_sized_insert],
   [inode_sized_of_alloc]).  It became a conjunct of [InodeLock.inode_ok],
   and [InodeLock.v] is this file's SIBLING -- both import [InodeInv.v] and
   neither imports the other -- so the only home from which [inode_ok] can
   name it is their common parent.  Nothing else moved; this file still
   sees all four through [InodeInv].                                       *)

(* ===================================================================== *)
(*  4.  THE REFERENCE-COUNT ALGEBRA                                       *)
(* ===================================================================== *)

(* RustBelt's Arc algebra, exactly as [FileInv.frefUR] uses it for
   [struct file]: [M !! k = Some (q, n)] means "itable slot [k] is live,
   with [n] outstanding references holding [q] of its identity fields
   between them"; [k ∉ dom M] means the slot is FREE.

   The frac x count pairing is the whole trick and it is what the design
   note calls REF-1 EXCLUSIVITY: [fracR] has no unit and [positiveR] has no
   zero, so [Some (q,1) ≼ Some (qt,n)] forces [n = 1 -> q = qt].  A thread
   that holds a reference and reads [ip->ref == 1] therefore holds the
   WHOLE outstanding share -- there is no other reference in the system.
   That is [iref_lookup], and it is the algebraic half of the theorem
   xv6's comment above iput asserts.                                      *)
(* [icacheUR], [icacheG] and [icacheΣ] moved to [IcacheRef.v]; the
   comment that explained them travelled with them. *)

(* the word in [ip->ref]: zero exactly on a free slot.  [FileInv]'s
   [fref_word_zero] / [fref_word_nonzero] / [fref_word_spos] read the two
   branch tests off this shape and are reusable verbatim -- they are about
   a count in an [int] field, not about struct file. *)
Definition iref_word (M : gmap nat (Qp * positive)) (k : nat) : mword 32 :=
  match M !! k with
  | None => mword_of_int 0
  | Some (_, n) => mword_of_int (Z.pos n)
  end.

(* the two things the authority's map may never do.  The count bound is not
   bookkeeping: it is what makes the [lw]/[sext.w] the code performs mean
   the count, and it is what kills ilock's and iunlock's [ref < 1] panic. *)
Definition icM_wf (M : gmap nat (Qp * positive)) : Prop :=
  (forall k : nat, is_Some (M !! k) -> (k < NINODE)%nat)
  /\ (forall (k : nat) (q : Qp) (n : positive),
        M !! k = Some (q, n) -> Z.pos n < 2 ^ 31).

Lemma icM_wf_count (M : gmap nat (Qp * positive)) (k : nat) (q : Qp) (n : positive) :
  icM_wf M -> M !! k = Some (q, n) -> Z.pos n < 2 ^ 31.
Proof. intros [_ H]. apply H. Qed.

(* the count component's [⋅] IS [Pos.add]; naming it lets [lia] see the
   arithmetic in the local-update side conditions *)
Lemma ic_pos_op_add (a b : positive) : (a ⋅ b) = (a + b)%positive.
Proof. reflexivity. Qed.

Lemma ic_pos_succ_1_add (b : positive) : Pos.succ (1 + b) = (2 + b)%positive.
Proof. lia. Qed.

(* ---- the cache-HIT increment, as pure algebra (BioInv.bio_incr_lu) ----

   iget's hit arm runs [ref++] holding NO reference of its own, so unlike
   [iref_dup_step] (idup's shape) nothing can come out of a caller's
   fragment: the entry GROWS by exactly the minted [(qn,1)], taken from the
   share the table retained.  That makes the update an allocation keyed
   pointwise rather than a [singleton_local_update].

   Stated OUTSIDE the Iris section so the [own_update] below is handed a
   CLOSED update -- BioInv.v's header explains why an evar-headed target
   makes [apply auth_update_alloc] search forever. *)
Local Lemma ic_incr_lu (M : gmap nat (Qp * positive)) (k : nat)
    (qt qn : Qp) (n : positive) :
  M !! k = Some (qt, n) ->
  ✓ (qt + qn)%Qp ->
  @local_update _ (gmapUR nat (prodR fracR positiveR))
    (M, ∅) (<[k := ((qt + qn)%Qp, Pos.succ n)]> M, {[ k := (qn, 1%positive) ]}).
Proof.
  intros HM Hq.
  apply gmap_local_update. intros i.
  destruct (decide (i = k)) as [->|Hne]; last first.
  { rewrite lookup_insert_ne // lookup_singleton_ne //. }
  rewrite lookup_insert lookup_singleton lookup_empty HM.
  apply local_update_unital_discrete. intros z Hv Hz.
  rewrite left_id in Hz. rewrite -Hz.
  split.
  { apply Some_valid. split; cbn; [exact Hq | done]. }
  rewrite -Some_op -pair_op frac_op ic_pos_op_add.
  by rewrite (Qp.add_comm qn qt) Pos.add_1_l.
Qed.

Local Lemma ic_incr_upd (M : gmap nat (Qp * positive)) (k : nat)
    (qt qn : Qp) (n : positive) :
  M !! k = Some (qt, n) ->
  ✓ (qt + qn)%Qp ->
  (● M : icacheUR) ~~>
  ● (<[k := ((qt + qn)%Qp, Pos.succ n)]> M) ⋅ ◯ {[ k := (qn, 1%positive) ]}.
Proof. intros HM Hq. apply auth_update_alloc. by apply ic_incr_lu. Qed.

(* the first reference's allocation, likewise closed (§13.1b's budget makes
   the minted fraction a parameter, so the caller's [1/2 - q] side of the
   split is what fixes it) *)
Local Lemma ic_alloc_upd (M : gmap nat (Qp * positive)) (k : nat) (q : Qp) :
  M !! k = None ->
  ✓ q ->
  (● M : icacheUR) ~~>
  ● (<[k := (q, 1%positive)]> M) ⋅ ◯ {[ k := (q, 1%positive) ]}.
Proof.
  intros HM Hq. apply auth_update_alloc.
  apply (alloc_singleton_local_update _ k (q, 1%positive)); [done|].
  split; [exact Hq | done].
Qed.

(* the ref word of a LIVE slot is positive and in range: precisely the two
   bounds [InodeLock.inode_ref_spos] turns into "the panic is dead". *)
Lemma iref_word_live (M : gmap nat (Qp * positive)) (k : nat) (q : Qp) (n : positive) :
  icM_wf M -> M !! k = Some (q, n) ->
  0 < bv_unsigned (iref_word M k) < 2 ^ 31.
Proof.
  intros Hwf HM.
  pose proof (icM_wf_count M k q n Hwf HM) as Hn.
  assert (E31 : (2 ^ 31 = 2147483648)%Z) by (vm_compute; reflexivity).
  assert (E32 : (2 ^ 32 = 4294967296)%Z) by (vm_compute; reflexivity).
  rewrite E31 in Hn.
  rewrite /iref_word HM moi32_small; [|rewrite E32; lia].
  rewrite E31. split; lia.
Qed.

Local Lemma seq_ninode_lookup (k : nat) :
  (k < NINODE)%nat -> seq 0 NINODE !! k = Some k.
Proof. intros Hk. apply lookup_seq. split; [lia|exact Hk]. Qed.

Section IcacheGhost.
  Context `{!icacheG Σ, !lockG Σ}.
  Context `{ICFG : icfg}.

  (* [itable_half], [iref_frag], [iref_tok] and [live_frac] are
     [IcacheRef.v]'s. *)

  (* ================================================================== *)
  (*  THE LIVENESS POOL, SLOT BY SLOT (design §14.6)                     *)
  (* ================================================================== *)

  (* WHERE SLOT [k]'s ONE UNIT IS.  A FREE slot's WHOLE unit sits here, in
     the invariant, and that IS the support clause -- OWNED rather than
     asserted, which is what lets a lock-free share-holder conclude
     [k ∈ dom M] ([live_slot_live]) with no [dom]-inclusion side condition
     anywhere.  A LIVE slot's unit is split [qt] to the reference holders
     (inside their [iref_tok]s, canonically paired -- see [IcacheRef.v]'s
     header) and [1 - qt] to this arm.

     THAT SPLIT IS WHAT RETIRES THE POOL AT THE LAST CLOSE: the closer's own
     slice is the whole [qt] (REF-1), the arm is [1 - qt], and they join to
     the entire unit -- exactly a free slot's shape.  §14.6's "mass
     conservation IS the witness", as four lines of [Qp] arithmetic
     ([live_slot_close_last]).

     THE [None] ARM IS [False], for [islot_rest_at]'s reason (§13.8): it
     makes "the outstanding total is strictly below one" RESOURCE-CARRIED,
     so no wf clause has to mention fractions and every step re-establishes
     it automatically.

     ---- THE RESTATED LEDGER (§17.2 piece 4, as repaired by §17.3 (A)) ----

     A LIVE slot's unit is now split THREE ways, not two:

         1  =  qt (the reference holders and their shares)
             + ½  (the ESCROW ARM, at the slot's generation)
             + (½ - qt) (this arm)

     so the live case below is [1/2 - qt], which is [islot_rest_at]'s shape
     EXACTLY -- the liveness ledger and the identity ledger became the same
     shape, and that congruence is the real endorsement of the restatement.
     A FREE slot's WHOLE unit still sits here: the escrow's EMPTY arm holds
     no slice, which is what keeps [live_slot_live] (and therefore
     [iref_live_load_au], ilock's [ref < 1] guard) exactly as it was.

     §17.2 put the ½ in [ic_loaded], i.e. in the CHECKED-OUT thread's hand;
     §17.3 (A) showed that kills [IcacheEscrow.ic_open_auth_ref]'s REF-1
     refutation of the OUT/[DepShr] arm, because the invariant's arm is then
     no longer the exact complement of what the opener holds.  With the ½ in
     the ARM, every live arm an opener can meet holds the exact complement
     again, and [live_whole_share_absurd] merely gains a [live_frac k (1/2)]
     premise that the opener supplies from the arm it has just destructed. *)
  Definition live_slot (M : gmap nat (Qp * positive)) (k : nat) : iProp Σ :=
    match M !! k with
    | None => live_frac k 1%Qp
    | Some (qt, _) =>
        match (1/2 - qt)%Qp with
        | Some c => live_frac k c
        | None => False%I
        end
    end.

  Definition live_pool (M : gmap nat (Qp * positive)) : iProp Σ :=
    ([∗ list] k ∈ seq 0 NINODE, live_slot M k)%I.

  Global Instance live_slot_timeless M k : Timeless (live_slot M k).
  Proof.
    rewrite /live_slot. destruct (M !! k) as [[qt n]|];
      [destruct (1/2 - qt)%Qp|]; apply _.
  Qed.
  Global Instance live_pool_timeless M : Timeless (live_pool M).
  Proof. apply _. Qed.

  (* the two shapes, as equations, so every move below is a rewrite *)
  Lemma live_slot_none M k : M !! k = None -> live_slot M k = live_frac k 1%Qp.
  Proof. intros H. by rewrite /live_slot H. Qed.

  Lemma live_slot_some M k qt n c :
    M !! k = Some (qt, n) -> (1/2 - qt)%Qp = Some c ->
    live_slot M k = live_frac k c.
  Proof. intros H1 H2. by rewrite /live_slot H1 /= H2. Qed.

  Lemma live_slot_some_inv M k qt n :
    M !! k = Some (qt, n) ->
    live_slot M k -∗ ∃ c : Qp, ⌜(1/2 - qt)%Qp = Some c⌝ ∗ live_frac k c.
  Proof.
    intros HM. rewrite /live_slot HM /=.
    destruct (1/2 - qt)%Qp as [c|] eqn:E; [| iIntros "[]"].
    iIntros "H". iExists c. by iFrame.
  Qed.

  (* THE SHARE'S READER, in its purest form: any slice of slot [k]'s unit
     proves the slot is LIVE, because a free one's unit is entire. *)
  Lemma live_slot_live M k s :
    live_frac k s -∗ live_slot M k -∗ ⌜is_Some (M !! k)⌝.
  Proof.
    iIntros "Hs Hsl". rewrite /live_slot.
    destruct (M !! k) as [e|] eqn:E; [iPureIntro; by eexists|].
    iDestruct (live_frac_full_excl with "Hsl Hs") as "[]".
  Qed.

  (* the same, with the generation NAMED -- the form [SpecIlock] v4's
     guard read needs, since its share arrives generation-named (design
     §17.3 (A)) and [live_frac]'s existential cannot be re-introduced
     afterwards. *)
  Lemma live_slot_live_gen M k s g :
    live_gen k s g -∗ live_slot M k -∗ ⌜is_Some (M !! k)⌝.
  Proof.
    iIntros "Hs Hsl". rewrite /live_slot.
    destruct (M !! k) as [e|] eqn:E; [iPureIntro; by eexists|].
    rewrite /live_frac. iDestruct "Hsl" as (g') "Hsl".
    iDestruct (live_gen_bound with "Hsl Hs") as %Hle.
    iPureIntro. exfalso.
    apply (irreflexivity Qp.lt 1%Qp).
    eapply Qp.lt_le_trans; [| exact Hle].
    apply Qp.lt_sum. by exists s.
  Qed.

  Lemma live_pool_live_gen M k s g :
    (k < NINODE)%nat ->
    live_gen k s g -∗ live_pool M -∗ ⌜is_Some (M !! k)⌝.
  Proof.
    intros Hk. iIntros "Hs Hp".
    iDestruct (big_sepL_lookup (fun (_ : nat) (j : nat) => live_slot M j)
                 (seq 0 NINODE) k k (seq_ninode_lookup k Hk) with "Hp") as "Hsl".
    iApply (live_slot_live_gen with "Hs Hsl").
  Qed.

  Lemma live_pool_live M k s :
    (k < NINODE)%nat ->
    live_frac k s -∗ live_pool M -∗ ⌜is_Some (M !! k)⌝.
  Proof.
    intros Hk. iIntros "Hs Hp".
    iDestruct (big_sepL_lookup (fun (_ : nat) (j : nat) => live_slot M j)
                 (seq 0 NINODE) k k (seq_ninode_lookup k Hk) with "Hp") as "Hsl".
    iApply (live_slot_live with "Hs Hsl").
  Qed.

  (* the pool's slot accessor -- [islots_acc_upd]'s shape and proof, and it
     covers deletion as well as insertion because the wand takes ANY [M']
     that agrees away from [k]. *)
  Lemma live_pool_acc_upd (M : gmap nat (Qp * positive)) (k : nat) :
    (k < NINODE)%nat ->
    live_pool M -∗
      live_slot M k ∗
      (∀ M' : gmap nat (Qp * positive),
         ⌜forall j, j <> k -> M' !! j = M !! j⌝ -∗
         live_slot M' k -∗ live_pool M').
  Proof.
    intros Hk. rewrite /live_pool. iIntros "Hs".
    iDestruct (big_sepL_delete _ (seq 0 NINODE) k k (seq_ninode_lookup k Hk)
                with "Hs") as "[Hslot Hrest]".
    iFrame "Hslot". iIntros (M') "%Hagree Hslot".
    iApply (big_sepL_delete _ (seq 0 NINODE) k k (seq_ninode_lookup k Hk)).
    iFrame "Hslot".
    iApply (big_sepL_impl with "Hrest").
    iIntros "!>" (j x Hjx) "H".
    destruct (decide (j = k)) as [->|Hne]; [iExact "H"|].
    apply lookup_seq in Hjx as [Hx _].
    assert (Hxk : x <> k) by lia.
    iEval (rewrite /live_slot) in "H".
    rewrite /live_slot (Hagree x Hxk). iExact "H".
  Qed.

  Lemma live_pool_empty :
    ([∗ list] k ∈ seq 0 NINODE, live_frac k 1%Qp) ⊢ live_pool ∅.
  Proof.
    rewrite /live_pool. iIntros "H". iApply (big_sepL_mono with "H").
    intros idx k _. by rewrite (live_slot_none ∅ k (lookup_empty k)).
  Qed.

  (* ==================================================================== *)
  (*  THE SLEEPLOCK SHARE'S AUTHORITY, PER SLOT.                           *)
  (* ==================================================================== *)
  (* [IcacheRef.iref_frag k q] carries [slh_tok (icfg_isl k) q] -- a q-share
     of "somebody may hold slot [k]'s sleeplock".  The authority that counts
     those shares is parked here, coupled to [M] DEFINITIONALLY: the total
     outstanding share IS the [qt] the reference algebra records, and [None]
     -- SleepLock's AUTHORITATIVE ZERO -- for a free slot.

     That is what turns REF-1 into access.  REF-1 says a reader holding
     [iref_tok k q] at count 1 has the WHOLE outstanding [qt]; so returning
     its share to this authority leaves [None], i.e. no share of the lock
     exists anywhere, i.e. nobody holds it -- which is exactly the premise
     [Acquiresleep.wp_acquiresleep_nb_sconf] takes in place of a rank bound
     (claude-notes/projects/iput-acquiresleep.md).

     Shaped as [live_slot]/[live_pool] and accessed the same way, because it
     moves at exactly the same four points they do. *)
  Definition isl_slot (M : gmap nat (Qp * positive)) (k : nat) : iProp Σ :=
    slh_auth (icfg_isl k) (fst <$> M !! k).

  Definition isl_pool (M : gmap nat (Qp * positive)) : iProp Σ :=
    ([∗ list] k ∈ seq 0 NINODE, isl_slot M k)%I.

  Global Instance isl_slot_timeless M k : Timeless (isl_slot M k).
  Proof. apply _. Qed.

  Lemma isl_slot_none M k : M !! k = None -> isl_slot M k = slh_auth (icfg_isl k) None.
  Proof. intros HM. by rewrite /isl_slot HM. Qed.

  Lemma isl_slot_some M k qt n :
    M !! k = Some (qt, n) -> isl_slot M k = slh_auth (icfg_isl k) (Some qt).
  Proof. intros HM. by rewrite /isl_slot HM. Qed.

  (* the accessor, [live_pool_acc_upd] verbatim *)
  Lemma isl_pool_acc_upd (M : gmap nat (Qp * positive)) (k : nat) :
    (k < NINODE)%nat ->
    isl_pool M -∗
      isl_slot M k ∗
      (∀ M' : gmap nat (Qp * positive),
         ⌜forall j, j <> k -> M' !! j = M !! j⌝ -∗
         isl_slot M' k -∗ isl_pool M').
  Proof.
    intros Hk. rewrite /isl_pool. iIntros "Hs".
    iDestruct (big_sepL_delete _ (seq 0 NINODE) k k (seq_ninode_lookup k Hk)
                with "Hs") as "[Hslot Hrest]".
    iFrame "Hslot". iIntros (M') "%Hagree Hslot".
    iApply (big_sepL_delete _ (seq 0 NINODE) k k (seq_ninode_lookup k Hk)).
    iFrame "Hslot".
    iApply (big_sepL_impl with "Hrest").
    iIntros "!>" (j x Hjx) "H".
    destruct (decide (j = k)) as [->|Hne]; [iExact "H"|].
    apply lookup_seq in Hjx as [Hx _].
    assert (Hxk : x <> k) by lia.
    iEval (rewrite /isl_slot) in "H".
    rewrite /isl_slot (Hagree x Hxk). iExact "H".
  Qed.

  Lemma isl_pool_empty :
    ([∗ list] k ∈ seq 0 NINODE, slh_auth (icfg_isl k) None) ⊢ isl_pool ∅.
  Proof.
    rewrite /isl_pool. iIntros "H". iApply (big_sepL_mono with "H").
    intros idx k _. by rewrite (isl_slot_none ∅ k (lookup_empty k)).
  Qed.

  (* ---- THE FOUR MOVES OF A SLOT'S UNIT ------------------------------
     Between them they are the whole liveness story, and not one of them is
     a ghost UPDATE: the pool has no authority, so a slice is always taken
     from, or given back to, a unit somebody already owns. *)

  (* iget's recycle: the free slot's WHOLE unit splits THREE ways -- the
     first reference's [q], the escrow arm's ½ and the table's remainder --
     and the budget that makes the remainder exist is now [q < 1/2], which
     is [islot_rest_at]'s identity budget verbatim (design §17.3 (A2)).

     IT IS ALSO WHERE THE GENERATION IS BORN.  A bump needs the slot's whole
     unit and this is the only place it exists (§17.2 piece 2), so the
     recycle mints a fresh generation and its PENDING one-shot here; ilock's
     fill spends the token against [di_type dn] at the only instruction that
     knows the type.  That is why this lemma, alone among the four, is a
     fupd. *)
  Lemma live_slot_alloc M k q :
    M !! k = None -> (q < 1/2)%Qp ->
    live_slot M k ==∗ ∃ g : gname,
      live_frac k q ∗ live_gen k (1/2)%Qp g ∗ ity_pending g ∗
      live_slot (<[k := (q, 1%positive)]> M) k.
  Proof.
    intros HM Hq.
    apply Qp.lt_sum in Hq as [c Hc].          (* 1/2 = q + c *)
    assert (Hsum : (q + ((1/2)%Qp + c))%Qp = 1%Qp).
    { rewrite (Qp.add_comm (1/2)%Qp c) Qp.add_assoc -Hc. apply Qp.half_half. }
    iIntros "Hsl".
    rewrite (live_slot_none M k HM).
    iMod (live_frac_bump k with "Hsl") as (g) "[Hg Hp]".
    rewrite (live_slot_some (<[k := (q, 1%positive)]> M) k q 1%positive c
               (lookup_insert M k (q, 1%positive))
               (proj2 (Qp.sub_Some (1/2)%Qp q c) Hc)).
    iEval (rewrite -Hsum) in "Hg".
    rewrite live_gen_split. iDestruct "Hg" as "[Hq Hg]".
    rewrite live_gen_split. iDestruct "Hg" as "[Hh Hc]".
    iModIntro. iExists g. iFrame "Hp Hh".
    iSplitL "Hq"; [iExists g; iExact "Hq" | iExists g; iExact "Hc"].
  Qed.

  (* iget's cache HIT: the new reference's slice comes out of the ARM, not
     out of any caller -- exactly as its identity fraction comes out of
     [islot_rest].  [qt + qn < 1] is the arm's counterpart of that budget,
     and is why this wrapper's caller has one more side condition than the
     [✓ (qt + qn)] it used to carry. *)
  Lemma live_slot_incr M k qt qn (n : positive) :
    M !! k = Some (qt, n) -> (qt + qn < 1/2)%Qp ->
    live_slot M k -∗
      live_frac k qn ∗ live_slot (<[k := ((qt + qn)%Qp, Pos.succ n)]> M) k.
  Proof.
    intros HM Hlt.
    apply Qp.lt_sum in Hlt as [c Hc].
    assert (Hpre : ((1/2)%Qp - qt)%Qp = Some (qn + c)%Qp).
    { apply Qp.sub_Some. by rewrite Hc Qp.add_assoc. }
    rewrite (live_slot_some M k qt n (qn + c)%Qp HM Hpre).
    rewrite (live_slot_some (<[k := ((qt + qn)%Qp, Pos.succ n)]> M) k
               (qt + qn)%Qp (Pos.succ n) c
               (lookup_insert M k ((qt + qn)%Qp, Pos.succ n))
               (proj2 (Qp.sub_Some (1/2)%Qp (qt + qn) c) Hc)).
    rewrite live_frac_split. iIntros "[$ $]".
  Qed.

  (* iput's NON-last close: the departing reference's slice rejoins the arm,
     which is the pool's mirror of the identity fraction rejoining
     [islot_rest]. *)
  Lemma live_slot_close M k q qt qr (n : positive) :
    M !! k = Some (qt, Pos.succ n) -> (qt - q)%Qp = Some qr ->
    live_slot M k -∗ live_frac k q -∗ live_slot (<[k := (qr, n)]> M) k.
  Proof.
    intros HM Hsub. iIntros "Hsl Hq".
    iDestruct (live_slot_some_inv M k qt (Pos.succ n) HM with "Hsl")
      as (c) "[%Epre Hc]".
    apply Qp.sub_Some in Hsub. apply Qp.sub_Some in Epre.
    assert (Hpost : ((1/2)%Qp - qr)%Qp = Some (q + c)%Qp).
    { apply Qp.sub_Some.
      by rewrite Epre Hsub Qp.add_assoc (Qp.add_comm q qr). }
    rewrite (live_slot_some (<[k := (qr, n)]> M) k qr n (q + c)%Qp
               (lookup_insert M k (qr, n)) Hpost).
    iApply (live_frac_join with "Hq Hc").
  Qed.

  (* iput's LAST close: THE RETIREMENT.  REF-1 says the closer's slice is the
     whole outstanding [qt]; the arm is [1 - qt]; the join is the unit a FREE
     slot's arm holds.  Nothing is counted and nothing is refuted -- had a
     share been outstanding, its own slice could not have coexisted with the
     two halves this lemma consumes.  §14.6, in four lines. *)
  Lemma live_slot_close_last M k (qt : Qp) :
    M !! k = Some (qt, 1%positive) ->
    live_slot M k -∗ live_frac k qt -∗ live_frac k (1/2)%Qp -∗
    live_slot (delete k M) k.
  Proof.
    intros HM. iIntros "Hsl Hq Hh".
    iDestruct (live_slot_some_inv M k qt 1%positive HM with "Hsl")
      as (c) "[%Epre Hc]".
    apply Qp.sub_Some in Epre.                (* 1/2 = qt + c *)
    rewrite (live_slot_none (delete k M) k (lookup_delete M k)).
    assert (Hsum : (qt + c + (1/2)%Qp)%Qp = 1%Qp).
    { rewrite -Epre. apply Qp.half_half. }
    iDestruct (live_frac_join with "Hq Hc") as "Hqc".
    iDestruct (live_frac_join with "Hqc Hh") as "Hone".
    iEval (rewrite Hsum) in "Hone". iExact "Hone".
  Qed.

  Lemma itable_half_agree M1 M2 :
    itable_half M1 -∗ itable_half M2 -∗ ⌜M1 = M2⌝.
  Proof.
    rewrite /itable_half. iIntros "H1 H2".
    iDestruct (own_valid_2 with "H1 H2") as %Hv.
    iPureIntro.
    apply auth_auth_dfrac_op_valid in Hv as (_ & Heq & _).
    by apply leibniz_equiv.
  Qed.

  (* the two halves ARE the authority: this is how a lock holder that has
     opened the [ref]-word invariant gets the right to update. *)
  Lemma itable_half_op M :
    itable_half M ∗ itable_half M ⊣⊢ own icfg_iref (● M).
  Proof.
    rewrite /itable_half -own_op -auth_auth_dfrac_op dfrac_op_own Qp.half_half.
    done.
  Qed.

  Lemma itable_half_join M :
    itable_half M -∗ itable_half M -∗ own icfg_iref (● M).
  Proof.
    iIntros "H1 H2". iApply itable_half_op. iFrame.
  Qed.

  Lemma itable_half_split M :
    own icfg_iref (● M) -∗ itable_half M ∗ itable_half M.
  Proof. iIntros "H". by iApply itable_half_op. Qed.

  (* ------------------------------------------------------------------ *)
  (*  REF-1 EXCLUSIVITY -- the algebraic half of iput's theorem           *)
  (* ------------------------------------------------------------------ *)

  (* A reference's fragment read against EITHER half of the authority.  The
     third conjunct is the one the whole design turns on: if the slot's
     count is one then the reader's [q] is the entire outstanding share, so
     no other reference to this inode exists anywhere in the system.  The
     fourth is its converse, which is what tells a would-be last closer that
     it is NOT the last one. *)
  Lemma iref_lookup M k q :
    itable_half M -∗ iref_tok k q -∗
    ⌜∃ (qt : Qp) (n : positive), M !! k = Some (qt, n) /\ (qt ≤ 1)%Qp /\
       (n = 1%positive -> q = qt) /\ (q = qt -> n = 1%positive)⌝.
  Proof.
    rewrite /itable_half /iref_tok /iref_frag. iIntros "Ha [[Hf _] _]".
    iDestruct (own_valid_2 with "Ha Hf")
      as %[_ [Hincl Hval]]%auth_both_dfrac_valid_discrete.
    iPureIntro.
    apply singleton_included_l in Hincl as [y [Hy Hle]].
    apply leibniz_equiv in Hy. destruct y as [qt n]. exists qt, n.
    split; [exact Hy|].
    split.
    { specialize (Hval k). rewrite Hy in Hval.
      destruct Hval as [Hvq _]; simpl in Hvq. by apply frac_valid in Hvq. }
    apply Some_included in Hle as [Heq | Hlt].
    - destruct Heq as [Hq Hn]; cbn in Hq, Hn.
      split; [by intros _ | by intros _; rewrite -Hn].
    - apply pair_included in Hlt as [Hq Hn]; cbn in Hq, Hn.
      apply frac_included in Hq. apply pos_included in Hn.
      split.
      + intros Hc. exfalso. rewrite Hc in Hn. lia.
      + intros Hc. exfalso. rewrite Hc in Hq. by apply (irreflexivity Qp.lt qt).
  Qed.

  (* A reference fragment against an authority showing NO reference at all:
     the refutation every AUTHORITY-SIDE opener uses (design §10.3 -- iget's
     recycle holds [itable.lock] at [M !! k = None] and refutes the escrow's
     checked-out arm with this, holding no checkout token of its own).
     BioInv.bref_tok_free_absurd's mirror, against the HALF authority --
     [singleton_included_l] reads through any dfrac, exactly as in
     [iref_lookup] above. *)
  Lemma iref_tok_free_absurd M k q :
    M !! k = None ->
    itable_half M -∗ iref_tok k q -∗ False.
  Proof.
    rewrite /itable_half /iref_tok /iref_frag. iIntros (HM) "Ha [[Hf _] _]".
    iDestruct (own_valid_2 with "Ha Hf")
      as %[_ [Hincl _]]%auth_both_dfrac_valid_discrete.
    iPureIntro.
    apply singleton_included_l in Hincl as [y [Hy _]].
    rewrite HM in Hy. inversion Hy.
  Qed.

  (* TWO reference fragments at one slot force the count to be at least two.
     This is REF-1 EXCLUSIVITY used as a refutation rather than as a
     conclusion: a thread that has read [ip->ref == 1] (so [n = 1] by
     [iref_lookup]) and holds one reference can rule out the existence of
     any second one -- which is how iput's authority-side opening of the
     escrow kills the checked-out arm.  The count component's inclusion is
     the whole content: [(q1,1) ⋅ (q2,1) = (q1+q2, 2)]. *)
  Lemma iref_tok_two_lookup M k q1 q2 :
    itable_half M -∗ iref_tok k q1 -∗ iref_tok k q2 -∗
    ⌜∃ (qt : Qp) (n : positive), M !! k = Some (qt, n) /\ (2 <= Pos.to_nat n)%nat⌝.
  Proof.
    rewrite /itable_half /iref_tok /iref_frag. iIntros "Ha [[H1 _] _] [[H2 _] _]".
    assert (Hop : (◯ {[ k := (q1, 1%positive) ]} ⋅ ◯ {[ k := (q2, 1%positive) ]}
                   : icacheUR)
                  = ◯ {[ k := ((q1 + q2)%Qp, 2%positive) ]}).
    { rewrite -auth_frag_op singleton_op -pair_op frac_op. reflexivity. }
    iAssert (own icfg_iref (◯ {[ k := ((q1 + q2)%Qp, 2%positive) ]})) with "[H1 H2]" as "Hf".
    { rewrite -Hop own_op. iFrame. }
    iDestruct (own_valid_2 with "Ha Hf")
      as %[_ [Hincl _]]%auth_both_dfrac_valid_discrete.
    iPureIntro.
    apply singleton_included_l in Hincl as [y [Hy Hle]].
    apply leibniz_equiv in Hy. destruct y as [qt n]. exists qt, n.
    split; [exact Hy|].
    apply Some_included in Hle as [Heq | Hlt].
    - destruct Heq as [_ Hn]; cbn in Hn.
      assert (Hn' : (2%positive : positive) = n) by exact Hn. lia.
    - apply pair_included in Hlt as [_ Hn]; cbn in Hn.
      apply pos_included in Hn. lia.
  Qed.

  (* a reference's slot is in range -- what the scan's index bound needs *)
  Lemma iref_tok_in_range M k q :
    icM_wf M -> itable_half M -∗ iref_tok k q -∗ ⌜(k < NINODE)%nat⌝.
  Proof.
    intros [Hdom _]. iIntros "Ha Hf".
    iDestruct (iref_lookup with "Ha Hf") as %(qt & n & HM & _).
    iPureIntro. apply Hdom. by eexists.
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  The four ghost steps, at the ALGEBRA level                          *)
  (* ------------------------------------------------------------------ *)

  (* They are stated over the JOINED authority because every one of them
     happens under itable.lock with the [ref]-word invariant open -- that
     is the only moment both halves are in one place, and it is exactly the
     moment the physical [sw] to [ip->ref] happens.  The points-to side (the
     [dev]/[inum] fractions moving in and out of [islot]) is one lemma per
     step and belongs with the contracts that consume them. *)

  (* iget, recycling a free entry: [ref = 0] -> [ref = 1], minting the first
     reference at fraction [q].

     [q] IS A PARAMETER, and the old [q = 1] form is gone (design §12.5): a
     first reference holding the whole outstanding share leaves [islot_rest]
     empty, and a later cache-HIT [iget] then has no retained share to mint
     a new reference from -- its hit arm holds no caller token to split, so
     [iref_dup_step] (idup's shape) cannot serve.  The budget of §13.1b caps
     the minted fraction at 1/2, because the escrow's parked arm owns the
     other half of [i_inum] permanently. *)
  Lemma iref_alloc_step M k (q : Qp) :
    M !! k = None ->
    (q < 1/2)%Qp ->
    own icfg_iref (● M) -∗ live_slot M k -∗ isl_slot M k ==∗
    ∃ g : gname,
    own icfg_iref (● (<[k := (q, 1%positive)]> M)) ∗
    live_slot (<[k := (q, 1%positive)]> M) k ∗
    isl_slot (<[k := (q, 1%positive)]> M) k ∗ iref_tok k q ∗
    live_gen k (1/2)%Qp g ∗ ity_pending g.
  Proof.
    iIntros (HM Hq) "Ha Hsl Hisl".
    (* the slot is FREE, so its share authority is the zero; the first
       reference mints the whole outstanding share out of it. *)
    rewrite (isl_slot_none M k HM).
    iMod (slh_mint_none (icfg_isl k) q with "Hisl") as "[Hisl Hshare]".
    assert (Hv : ✓ q).
    { apply frac_valid. etrans; [apply Qp.lt_le_incl; exact Hq | compute_done]. }
    iMod (live_slot_alloc M k q HM Hq with "Hsl") as (g) "(Hlv & Hh & Hp & Hsl)".
    iMod (own_update _ _ _ (ic_alloc_upd M k q HM Hv) with "Ha") as "H".
    rewrite own_op. iDestruct "H" as "[Ha Hfr]".
    iModIntro. iExists g. iFrame "Ha Hsl Hh Hp".
    rewrite (isl_slot_some (<[k := (q, 1%positive)]> M) k q 1%positive
               (lookup_insert M k (q, 1%positive))).
    iFrame "Hisl".
    rewrite /iref_tok /iref_frag. iFrame.
  Qed.

  (* iget's cache-HIT arm: [ref++] on a live entry, minting a fresh
     reference at fraction [qn] taken from the table's RETAINED share.  The
     incrementer holds no reference of its own, so the entry grows by exactly
     the minted amount -- BioInv.bio_incr_step verbatim. *)
  Lemma iref_incr_step M k qt (n : positive) (qn : Qp) :
    M !! k = Some (qt, n) ->
    (qt + qn < 1/2)%Qp ->
    own icfg_iref (● M) -∗ live_slot M k -∗ isl_slot M k ==∗
    own icfg_iref (● (<[k := ((qt + qn)%Qp, Pos.succ n)]> M)) ∗
    live_slot (<[k := ((qt + qn)%Qp, Pos.succ n)]> M) k ∗
    isl_slot (<[k := ((qt + qn)%Qp, Pos.succ n)]> M) k ∗ iref_tok k qn.
  Proof.
    iIntros (HM Hlt) "Ha Hsl Hisl".
    rewrite (isl_slot_some M k qt n HM).
    iMod (slh_mint (icfg_isl k) qt qn with "Hisl") as "[Hisl Hshare]".
    assert (Hq : ✓ (qt + qn)%Qp).
    { apply frac_valid. etrans;
        [apply Qp.lt_le_incl; exact Hlt | compute_done]. }
    iDestruct (live_slot_incr M k qt qn n HM Hlt with "Hsl") as "[Hlv Hsl]".
    iMod (own_update _ _ _ (ic_incr_upd M k qt qn n HM Hq) with "Ha") as "H".
    rewrite own_op. iDestruct "H" as "[Ha Hfr]".
    iModIntro. iFrame "Ha Hsl".
    rewrite (isl_slot_some (<[k := ((qt + qn)%Qp, Pos.succ n)]> M) k
               (qt + qn)%Qp (Pos.succ n)
               (lookup_insert M k ((qt + qn)%Qp, Pos.succ n))).
    iFrame "Hisl".
    rewrite /iref_tok /iref_frag. iFrame.
  Qed.

  (* idup, and iget's cache-hit arm: [ref++].  The new reference's fraction
     comes out of the CALLER's own -- nothing is conjured, which is why the
     invariant's leftover share is untouched. *)
  Lemma iref_dup_step M k q qt (n : positive) :
    M !! k = Some (qt, n) ->
    own icfg_iref (● M) -∗ iref_tok k q -∗ isl_slot M k ==∗
    own icfg_iref (● (<[k := (qt, Pos.succ n)]> M)) ∗
    isl_slot (<[k := (qt, Pos.succ n)]> M) k ∗
    iref_tok k (q/2)%Qp ∗ iref_tok k (q/2)%Qp.
  Proof.
    iIntros (HM) "Ha [[Hf Hsh] Hlv] Hisl".
    (* the TOTAL is unchanged -- nothing is minted, the caller's own share
       halves along with its count fragment -- so the authority only has to
       be re-read at the updated map. *)
    rewrite (isl_slot_some M k qt n HM)
            (isl_slot_some (<[k := (qt, Pos.succ n)]> M) k qt (Pos.succ n)
               (lookup_insert M k (qt, Pos.succ n))).
    iAssert (slh_tok (icfg_isl k) (q/2)%Qp ∗ slh_tok (icfg_isl k) (q/2)%Qp)%I
      with "[Hsh]" as "[Hs1 Hs2]".
    { rewrite -slh_tok_split Qp.div_2. iExact "Hsh". }
    iDestruct (live_frac_halve with "Hlv") as "[Hl1 Hl2]".
    iMod (own_update_2 _ _ _ (● (<[k := (qt, Pos.succ n)]> M)
                              ⋅ ◯ {[k := (q, 2%positive)]}) with "Ha Hf") as "H".
    { apply auth_update.
      apply (singleton_local_update _ k (qt, n) (q, 1%positive)
                                      (qt, Pos.succ n) (q, 2%positive) HM).
      apply local_update_discrete. intros mz Hv Hz.
      destruct Hv as [Hvq Hvn]. split; [by split|].
      destruct mz as [[qf nf]|]; destruct Hz as [Hq Hn]; simpl in Hq, Hn.
      - split; simpl; [exact Hq|].
        rewrite Hn !ic_pos_op_add. apply ic_pos_succ_1_add.
      - split; simpl; [exact Hq|]. by rewrite Hn. }
    rewrite own_op. iDestruct "H" as "[$ Hfrag]".
    rewrite /iref_tok.
    assert (Hsp : ({[k := (q, 2%positive)]} : gmap nat (Qp * positive))
                  = {[k := ((q/2)%Qp, 1%positive)]} ⋅ {[k := ((q/2)%Qp, 1%positive)]}).
    { rewrite singleton_op. f_equal. rewrite -pair_op.
      by rewrite frac_op Qp.div_2. }
    rewrite Hsp auth_frag_op own_op. iDestruct "Hfrag" as "[Hf1 Hf2]".
    iModIntro. iFrame "Hisl". rewrite /iref_tok /iref_frag. iFrame.
  Qed.

  (* iput, [--ref > 0]: the departing reference's fraction has to go
     SOMEWHERE, and it goes back into the outstanding total.  That is why
     the frac component tracks OUTSTANDING share rather than being pinned
     at 1. *)
  Lemma iref_close_step M k q qt (n : positive) (qr : Qp) :
    M !! k = Some (qt, Pos.succ n) ->
    (qt - q)%Qp = Some qr ->
    own icfg_iref (● M) -∗ iref_tok k q -∗ live_slot M k -∗ isl_slot M k ==∗
    own icfg_iref (● (<[k := (qr, n)]> M)) ∗ live_slot (<[k := (qr, n)]> M) k ∗
    isl_slot (<[k := (qr, n)]> M) k.
  Proof.
    iIntros (HM Hsub) "Ha [[Hf Hsh] Hlv] Hsl Hisl".
    iDestruct (live_slot_close M k q qt qr n HM Hsub with "Hsl Hlv") as "Hsl".
    iFrame "Hsl".
    apply Qp.sub_Some in Hsub.       (* qt = q + qr *)
    (* the departing reference's share goes back into the outstanding total,
       exactly as its fraction does. *)
    rewrite (isl_slot_some M k qt (Pos.succ n) HM)
            (isl_slot_some (<[k := (qr, n)]> M) k qr n
               (lookup_insert M k (qr, n))).
    rewrite Hsub (comm Qp.add q qr).
    iMod (slh_return (icfg_isl k) qr q with "Hisl Hsh") as "$".
    rewrite /iref_frag.
    iApply (own_update_2 _ _ _ (● (<[k := (qr, n)]> M)) with "Ha Hf").
    apply auth_update_dealloc, gmap_local_update. intros i.
    destruct (decide (i = k)) as [->|Hne]; last first.
    { assert (Hki : k <> i) by auto.
      pose proof (lookup_singleton_ne (M:=gmap nat) k i (q, 1%positive) Hki) as Hs.
      pose proof (lookup_insert_ne M k i (qr, n) Hki) as Hm.
      apply local_update_discrete. intros mz Hv Hz.
      rewrite Hs in Hz. rewrite Hm. split; [exact Hv | exact Hz]. }
    pose proof (lookup_singleton (M:=gmap nat) k (q, 1%positive)) as Hs.
    pose proof (lookup_insert M k (qr, n)) as Hm.
    apply local_update_discrete. intros mz Hv Hz.
    rewrite HM in Hz, Hv. rewrite Hs in Hz. rewrite Hm.
    destruct mz as [[[qf nf]|]|]; simpl in Hz.
    - apply Some_equiv_inj in Hz. destruct Hz as [Hq Hn]; simpl in Hq, Hn.
      rewrite ic_pos_op_add in Hn.
      assert (Hn' : Pos.succ n = (1 + nf)%positive) by exact Hn.
      assert (Hnf : nf = n) by lia.
      rewrite frac_op in Hq.
      assert (Hqf : qf = qr).
      { apply (inj (Qp.add q)). by rewrite -Hq -Hsub. }
      subst nf qf. split; last first.
      { by constructor. }
      destruct Hv as [Hvq _]; simpl in Hvq. apply frac_valid in Hvq.
      split; simpl; [|done].
      apply frac_valid. etrans; [|exact Hvq]. rewrite Hsub. apply Qp.le_add_r.
    - exfalso. rewrite right_id in Hz. apply Some_equiv_inj in Hz.
      destruct Hz as [_ Hn]; simpl in Hn.
      assert (Hn' : Pos.succ n = 1%positive) by exact Hn. lia.
    - exfalso. apply Some_equiv_inj in Hz.
      destruct Hz as [_ Hn]; simpl in Hn.
      assert (Hn' : Pos.succ n = 1%positive) by exact Hn. lia.
  Qed.

  (* iput, [--ref == 0]: the entry is DELETED.  Stated at an arbitrary [qt]
     -- the [qt = 1] version is unusable, because after any earlier close
     the outstanding total has already shrunk.  What makes this closer the
     last one is the COUNT: [positiveR] has no unit, so no frame can sit
     beside a fragment recording count 1. *)
  Lemma iref_close_last_step M k (qt : Qp) :
    M !! k = Some (qt, 1%positive) ->
    own icfg_iref (● M) -∗ iref_tok k qt -∗ live_frac k (1/2)%Qp -∗
    live_slot M k -∗ isl_slot M k ==∗
    own icfg_iref (● (delete k M)) ∗ live_slot (delete k M) k ∗
    isl_slot (delete k M) k.
  Proof.
    iIntros (HM) "Ha [[Hf Hsh] Hlv] Hh Hsl Hisl".
    iDestruct (live_slot_close_last M k qt HM with "Hsl Hlv Hh") as "Hsl".
    iFrame "Hsl".
    (* THE LAST reference's share returns and leaves the AUTHORITATIVE ZERO,
       which is what a free slot's [isl_slot] is -- and what iput needs. *)
    rewrite (isl_slot_some M k qt 1%positive HM)
            (isl_slot_none (delete k M) k (lookup_delete M k)).
    iMod (slh_return_last (icfg_isl k) qt with "Hisl Hsh") as "$".
    rewrite /iref_frag.
    iApply (own_update_2 _ _ _ (● (delete k M)) with "Ha Hf").
    apply auth_update_dealloc, gmap_local_update. intros i.
    destruct (decide (i = k)) as [->|Hne]; last first.
    { assert (Hki : k <> i) by auto.
      pose proof (lookup_singleton_ne (M:=gmap nat) k i (qt, 1%positive) Hki) as Hs.
      pose proof (lookup_delete_ne M k i Hki) as Hm.
      apply local_update_discrete. intros mz Hv Hz.
      rewrite Hs in Hz. rewrite Hm. split; [exact Hv | exact Hz]. }
    pose proof (lookup_singleton (M:=gmap nat) k (qt, 1%positive)) as Hs.
    pose proof (lookup_delete M k) as Hm.
    apply local_update_discrete. intros mz Hv Hz.
    rewrite HM in Hz. rewrite Hs in Hz. rewrite Hm.
    destruct mz as [[[qf nf]|]|]; simpl in Hz.
    - exfalso. apply Some_equiv_inj in Hz. destruct Hz as [_ Hn]; simpl in Hn.
      rewrite ic_pos_op_add in Hn.
      assert (Hn' : 1%positive = (1 + nf)%positive) by exact Hn. lia.
    - split; done.
    - split; done.
  Qed.

End IcacheGhost.

(* ===================================================================== *)
(*  5.  THE [ref] WORDS: A SHARED INVARIANT, NOT THE LOCK'S RESOURCE      *)
(* ===================================================================== *)

Section IcacheRefInv.
  Context `{!riscvGS Σ, !icacheG Σ, !lockG Σ}.
  Context `{ICFG : icfg}.
  Context `{GEN : GenId}.

  Definition icacheN : namespace := nroot .@ "icache".

  Definition iref_cells (M : gmap nat (Qp * positive)) : iProp Σ :=
    ([∗ list] k ∈ seq 0 NINODE, i_ref (ientry k) ↦₄ iref_word M k)%I.

  (* The invariant's half of the authority sits BESIDE the cells, so the
     cells and the counts can never disagree, and a thread holding the
     other half (the itable lock's) is the only one that can move either. *)
  (* THE LIVENESS POOL SITS BESIDE THE REF WORDS (design §14.6).  It is the
     fourth conjunct rather than a separate invariant because every move it
     makes happens in the same opening as a [ref]-word store: a recycle
     hands its unit out, a close gives a slice back, and the LAST close
     reassembles the unit and retires the slot.  A share-holder that opens
     this invariant with nothing but a slice learns the slot is live -- see
     [iref_live_load_au]. *)
  Definition itable_body : iProp Σ :=
    (∃ M : gmap nat (Qp * positive),
       itable_half M ∗ ⌜icM_wf M⌝ ∗ iref_cells M ∗ live_pool M ∗
       isl_pool M)%I.

  Definition itable_inv : iProp Σ := inv icacheN itable_body.

  Global Instance itable_inv_persistent : Persistent itable_inv.
  Proof. apply _. Qed.

  Lemma iref_cells_acc (M : gmap nat (Qp * positive)) (k : nat) :
    (k < NINODE)%nat ->
    iref_cells M -∗
      i_ref (ientry k) ↦₄ iref_word M k ∗
      (i_ref (ientry k) ↦₄ iref_word M k -∗ iref_cells M).
  Proof.
    intros Hk. rewrite /iref_cells.
    iApply (big_sepL_lookup_acc
              (fun (_ : nat) (j : nat) => (i_ref (ientry j) ↦₄ iref_word M j)%I)
              (seq 0 NINODE) k k (seq_ninode_lookup k Hk)).
  Qed.

  (* The same accessor, but permitting the cell to come back at a DIFFERENT
     value -- which is what a [ref++] needs.  [iref_cells_acc] cannot serve:
     its wand rebuilds [iref_cells M] at the very [M] it opened.  Only slot
     [k]'s word moves, so the remainder is literally the same separating
     conjunction at [M] and at [<[k:=e]> M]; [big_sepL_delete] is what lets
     that be said, and the element of [seq 0 NINODE] at index [j] being [j]
     is what turns "index ≠ k" into "the entry we rewrite is not this one". *)
  Lemma iref_cells_acc_upd (M : gmap nat (Qp * positive)) (k : nat) :
    (k < NINODE)%nat ->
    iref_cells M -∗
      i_ref (ientry k) ↦₄ iref_word M k ∗
      (∀ e : Qp * positive,
         i_ref (ientry k) ↦₄ iref_word (<[k := e]> M) k -∗
         iref_cells (<[k := e]> M)).
  Proof.
    intros Hk. rewrite /iref_cells. iIntros "Hc".
    iDestruct (big_sepL_delete _ (seq 0 NINODE) k k (seq_ninode_lookup k Hk)
                with "Hc") as "[Hcell Hrest]".
    iFrame "Hcell". iIntros (e) "Hcell".
    iApply (big_sepL_delete _ (seq 0 NINODE) k k (seq_ninode_lookup k Hk)).
    iFrame "Hcell".
    iApply (big_sepL_impl with "Hrest").
    iIntros "!>" (j x Hjx) "H".
    destruct (decide (j = k)) as [->|Hne]; [iExact "H"|].
    apply lookup_seq in Hjx as [Hx _].
    assert (Hxk : k <> x) by lia.
    rewrite /iref_word lookup_insert_ne; [iExact "H" | exact Hxk].
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  The lock-free guard read                                           *)
  (* ------------------------------------------------------------------ *)

  (* ilock's and iunlock's [lw a5,8(a0)] happen with NO lock held, and this
     is the resource they need: the atomic-update argument
     [WpSconfMem.wp_load_s_sconf_au] takes at width 4, with
     [Em := Eo ∖ ↑icacheN] and
     [Ψ v := ⌜0 < bv_unsigned v < 2^31⌝ ∗ iref_tok k q].

     The two bounds are exactly what [InodeLock.inode_ref_spos] turns into
     "[bge x0,a5] falls through", i.e. into "the panic is dead" -- so this
     lemma REPLACES [SpecIlock.v]'s [i_ref ip ↦₄{dqr} refv] premise, which
     no icache can supply (see the file header and the design note).       *)
  Lemma iref_load_au (Eo : coPset) (k : nat) (q : Qp) :
    ↑icacheN ⊆ Eo ->
    itable_inv -∗ iref_tok k q -∗
    |={Eo, Eo ∖ ↑icacheN}=> ∃ v : mword 32,
      i_ref (ientry k) ↦₄ v ∗
      (i_ref (ientry k) ↦₄ v ={Eo ∖ ↑icacheN, Eo}=∗
         ⌜0 < bv_unsigned v < 2 ^ 31⌝ ∗ iref_tok k q).
  Proof.
    iIntros (HE) "#Hinv Htok".
    iMod (inv_acc Eo icacheN with "Hinv") as "[Hbody Hclose]"; [exact HE|].
    iDestruct "Hbody" as (M) "(>Ha & >%Hwf & >Hcells & >Hpool & >Hipool)".
    iDestruct (iref_lookup with "Ha Htok") as %(qt & n & HMk & _ & _ & _).
    assert (Hk : (k < NINODE)%nat) by (apply (proj1 Hwf); by eexists).
    iDestruct (iref_cells_acc M k Hk with "Hcells") as "[Hcell Hback]".
    iModIntro. iExists (iref_word M k). iFrame "Hcell".
    iIntros "Hcell".
    iMod ("Hclose" with "[Ha Hcell Hback Hpool Hipool]") as "_".
    { iNext. iExists M. iFrame "Ha". iSplitR; [iPureIntro; exact Hwf|].
      iFrame "Hpool Hipool". iApply ("Hback" with "Hcell"). }
    iModIntro. iFrame "Htok". iPureIntro.
    exact (iref_word_live M k qt n Hwf HMk).
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  The two halves of a [ref++], for a thread that HOLDS itable.lock    *)
  (* ------------------------------------------------------------------ *)

  (* THE READ.  Unlike [iref_load_au] this one is for a lock holder, and it
     delivers the value as a function of the holder's OWN [M] rather than as
     an opaque word with bounds: the lock's half pins the authority, so the
     map inside the invariant IS [M] ([itable_half_agree]) and the word the
     [lw] sees is [iref_word M k].  That is what makes the [addiw] between
     the load and the store mean "the count, plus one". *)
  Lemma iref_load_locked_au (Eo : coPset) 
      (M : gmap nat (Qp * positive)) (k : nat) :
    ↑icacheN ⊆ Eo -> (k < NINODE)%nat ->
    itable_inv -∗ itable_half M -∗
    |={Eo, Eo ∖ ↑icacheN}=>
      i_ref (ientry k) ↦₄ iref_word M k ∗
      (i_ref (ientry k) ↦₄ iref_word M k ={Eo ∖ ↑icacheN, Eo}=∗ itable_half M).
  Proof.
    iIntros (HE Hk) "#Hinv Hhalf".
    iMod (inv_acc Eo icacheN with "Hinv") as "[Hbody Hclose]"; [exact HE|].
    iDestruct "Hbody" as (M') "(>Ha & >%Hwf & >Hcells & >Hpool & >Hipool)".
    iDestruct (itable_half_agree with "Ha Hhalf") as %->.
    iDestruct (iref_cells_acc M k Hk with "Hcells") as "[Hcell Hback]".
    iModIntro. iFrame "Hcell". iIntros "Hcell".
    iMod ("Hclose" with "[Ha Hcell Hback Hpool Hipool]") as "_".
    { iNext. iExists M. iFrame "Ha". iSplitR; [iPureIntro; exact Hwf|].
      iFrame "Hpool Hipool". iApply ("Hback" with "Hcell"). }
    iModIntro. iFrame.
  Qed.

  (* THE WRITE.  The [sw] and the ghost step happen in the SAME invariant
     opening, which is the whole reason the read-modify-write is atomic in
     the proof: the lock's half stops any other thread moving [M], and the
     two halves meet only here, which is exactly the moment the physical
     word changes.  [Hno] -- that the incremented count is still an [int] --
     is what re-establishes [icM_wf]; it is NOT provable here and comes from
     the caller's [IrefSlots.iref_slots_no_overflow]. *)
  Lemma iref_dup_store_au (Eo : coPset) 
      (M : gmap nat (Qp * positive)) (k : nat) (q qt : Qp) (n : positive) :
    ↑icacheN ⊆ Eo ->
    M !! k = Some (qt, n) ->
    (Z.pos (Pos.succ n) < 2 ^ 31)%Z ->
    itable_inv -∗ itable_half M -∗ iref_tok k q -∗
    |={Eo, Eo ∖ ↑icacheN}=>
      i_ref (ientry k) ↦₄ iref_word M k ∗
      (i_ref (ientry k) ↦₄ (mword_of_int (Z.pos (Pos.succ n)) : mword 32)
         ={Eo ∖ ↑icacheN, Eo}=∗
         itable_half (<[k := (qt, Pos.succ n)]> M) ∗
         iref_tok k (q/2)%Qp ∗ iref_tok k (q/2)%Qp).
  Proof.
    iIntros (HE HMk Hno) "#Hinv Hhalf Htok".
    iMod (inv_acc Eo icacheN with "Hinv") as "[Hbody Hclose]"; [exact HE|].
    iDestruct "Hbody" as (M') "(>Ha & >%Hwf & >Hcells & >Hpool & >Hipool)".
    iDestruct (itable_half_agree with "Ha Hhalf") as %->.
    assert (Hk : (k < NINODE)%nat) by (apply (proj1 Hwf); by eexists).
    iDestruct (iref_cells_acc_upd M k Hk with "Hcells") as "[Hcell Hback]".
    iDestruct (live_pool_acc_upd M k Hk with "Hpool") as "[Hslot Hpback]".
    iDestruct (isl_pool_acc_upd M k Hk with "Hipool") as "[Hislot Hipback]".
    iModIntro. iFrame "Hcell". iIntros "Hcell".
    iDestruct (itable_half_join with "Ha Hhalf") as "Hauth".
    iMod (iref_dup_step M k q qt n HMk with "Hauth Htok Hislot")
      as "(Hauth & Hislot & Ht1 & Ht2)".
    iDestruct (itable_half_split with "Hauth") as "[Ha Hhalf]".
    iAssert (live_slot (<[k := (qt, Pos.succ n)]> M) k) with "[Hslot]" as "Hslot".
    { iDestruct (live_slot_some_inv M k qt n HMk with "Hslot")
        as (c) "[%Ec Hc]".
      by rewrite (live_slot_some (<[k := (qt, Pos.succ n)]> M) k qt (Pos.succ n) c
                    (lookup_insert M k (qt, Pos.succ n)) Ec). }
    iMod ("Hclose" with "[Ha Hcell Hback Hslot Hpback Hislot Hipback]") as "_".
    { iNext. iExists (<[k := (qt, Pos.succ n)]> M). iFrame "Ha".
      iSplitR.
      { iPureIntro. destruct Hwf as [Hdom Hcnt]. split.
        - intros j Hj. destruct (decide (j = k)) as [->|Hne]; [exact Hk|].
          rewrite lookup_insert_ne in Hj; [|by apply not_eq_sym]. by apply Hdom.
        - intros j qj nj Hj. destruct (decide (j = k)) as [->|Hne].
          + rewrite lookup_insert in Hj. apply Some_inj in Hj.
            injection Hj as _ Hn. subst nj. exact Hno.
          + rewrite lookup_insert_ne in Hj; [|by apply not_eq_sym].
            by apply (Hcnt j qj). }
      iSplitL "Hcell Hback".
      { iApply ("Hback" $! (qt, Pos.succ n)).
        rewrite /iref_word lookup_insert. iExact "Hcell". }
      iSplitL "Hslot Hpback".
      { iApply ("Hpback" $! (<[k := (qt, Pos.succ n)]> M) with "[%] Hslot").
        intros j Hj. rewrite lookup_insert_ne; [reflexivity | by apply not_eq_sym]. }
      iApply ("Hipback" $! (<[k := (qt, Pos.succ n)]> M) with "[%] Hislot").
      intros j Hj. rewrite lookup_insert_ne; [reflexivity | by apply not_eq_sym]. }
    iModIntro. iFrame.
  Qed.

  (* THE SAME WRITE, FOR AN INCREMENTER THAT HOLDS NO REFERENCE.
     [iref_dup_store_au] above is idup's shape: a caller token goes in and
     two halves come out.  [iget]'s cache-HIT arm has no token of its own --
     it found the entry by SCANNING -- so the new reference cannot be split
     off anything the opener brought, and is minted from the share the TABLE
     retained instead ([islot_rest_at], design §13.1b/§13.1e).  That is
     exactly [iref_incr_step] rather than [iref_dup_step], and it is why the
     entry's outstanding fraction GROWS by [qn] here where it stayed put in
     idup.  BioInv's [bio_incr_step] and its store wrapper are the precedent.

     Both side conditions are the CALLER's, for the same reasons as above:
     [✓ (qt + qn)] is the fraction budget (the caller takes [qn] out of the
     table's [1/2 - qt], so the sum never passes 1/2), and [Hno] -- that the
     incremented count is still an [int] -- comes from
     [IrefSlots.iref_slots_no_overflow] exactly as in ProofIdup. *)
  Lemma iref_incr_store_au (Eo : coPset) 
      (M : gmap nat (Qp * positive)) (k : nat) (qt qn : Qp) (n : positive) :
    ↑icacheN ⊆ Eo ->
    M !! k = Some (qt, n) ->
    (qt + qn < 1/2)%Qp ->
    (Z.pos (Pos.succ n) < 2 ^ 31)%Z ->
    itable_inv -∗ itable_half M -∗
    |={Eo, Eo ∖ ↑icacheN}=>
      i_ref (ientry k) ↦₄ iref_word M k ∗
      (i_ref (ientry k) ↦₄ (mword_of_int (Z.pos (Pos.succ n)) : mword 32)
         ={Eo ∖ ↑icacheN, Eo}=∗
         itable_half (<[k := ((qt + qn)%Qp, Pos.succ n)]> M) ∗
         iref_tok k qn).
  Proof.
    iIntros (HE HMk Hq Hno) "#Hinv Hhalf".
    iMod (inv_acc Eo icacheN with "Hinv") as "[Hbody Hclose]"; [exact HE|].
    iDestruct "Hbody" as (M') "(>Ha & >%Hwf & >Hcells & >Hpool & >Hipool)".
    iDestruct (itable_half_agree with "Ha Hhalf") as %->.
    assert (Hk : (k < NINODE)%nat) by (apply (proj1 Hwf); by eexists).
    iDestruct (iref_cells_acc_upd M k Hk with "Hcells") as "[Hcell Hback]".
    iDestruct (live_pool_acc_upd M k Hk with "Hpool") as "[Hslot Hpback]".
    iDestruct (isl_pool_acc_upd M k Hk with "Hipool") as "[Hislot Hipback]".
    iModIntro. iFrame "Hcell". iIntros "Hcell".
    iDestruct (itable_half_join with "Ha Hhalf") as "Hauth".
    iMod (iref_incr_step M k qt n qn HMk Hq with "Hauth Hslot Hislot")
      as "(Hauth & Hslot & Hislot & Htok)".
    iDestruct (itable_half_split with "Hauth") as "[Ha Hhalf]".
    iMod ("Hclose" with "[Ha Hcell Hback Hslot Hpback Hislot Hipback]") as "_".
    { iNext. iExists (<[k := ((qt + qn)%Qp, Pos.succ n)]> M). iFrame "Ha".
      iSplitR.
      { iPureIntro. destruct Hwf as [Hdom Hcnt]. split.
        - intros j Hj. destruct (decide (j = k)) as [->|Hne]; [exact Hk|].
          rewrite lookup_insert_ne in Hj; [|by apply not_eq_sym]. by apply Hdom.
        - intros j qj nj Hj. destruct (decide (j = k)) as [->|Hne].
          + rewrite lookup_insert in Hj. apply Some_inj in Hj.
            injection Hj as _ Hn. subst nj. exact Hno.
          + rewrite lookup_insert_ne in Hj; [|by apply not_eq_sym].
            by apply (Hcnt j qj). }
      iSplitL "Hcell Hback".
      { iApply ("Hback" $! ((qt + qn)%Qp, Pos.succ n)).
        rewrite /iref_word lookup_insert. iExact "Hcell". }
      iSplitL "Hslot Hpback".
      { iApply ("Hpback" $! (<[k := ((qt + qn)%Qp, Pos.succ n)]> M) with "[%] Hslot").
        intros j Hj. rewrite lookup_insert_ne; [reflexivity | by apply not_eq_sym]. }
      iApply ("Hipback" $! (<[k := ((qt + qn)%Qp, Pos.succ n)]> M) with "[%] Hislot").
      intros j Hj. rewrite lookup_insert_ne; [reflexivity | by apply not_eq_sym]. }
    iModIntro. iFrame.
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  The two halves of iput's [ref--] (design §13.9)                     *)
  (* ------------------------------------------------------------------ *)

  (* THE DELETE-FLAVOURED CELL ACCESSOR.  [iref_cells_acc_upd]'s wand
     rebuilds at [<[k := e]> M], which is every SURVIVING slot's shape;
     iput's LAST close removes the key outright and [delete k M] is not of
     that form.  Same [big_sepL_delete] argument, with [lookup_delete_ne]
     where the other had [lookup_insert_ne]. *)
  Lemma iref_cells_acc_del (M : gmap nat (Qp * positive)) (k : nat) :
    (k < NINODE)%nat ->
    iref_cells M -∗
      i_ref (ientry k) ↦₄ iref_word M k ∗
      (i_ref (ientry k) ↦₄ (mword_of_int 0 : mword 32) -∗
       iref_cells (delete k M)).
  Proof.
    intros Hk. rewrite /iref_cells. iIntros "Hc".
    iDestruct (big_sepL_delete _ (seq 0 NINODE) k k (seq_ninode_lookup k Hk)
                with "Hc") as "[Hcell Hrest]".
    iFrame "Hcell". iIntros "Hcell".
    iApply (big_sepL_delete _ (seq 0 NINODE) k k (seq_ninode_lookup k Hk)).
    iSplitL "Hcell".
    { rewrite /iref_word lookup_delete. iExact "Hcell". }
    iApply (big_sepL_impl with "Hrest").
    iIntros "!>" (j x Hjx) "H".
    destruct (decide (j = k)) as [->|Hne]; [iExact "H"|].
    apply lookup_seq in Hjx as [Hx _].
    assert (Hxk : k <> x) by lia.
    rewrite /iref_word lookup_delete_ne; [iExact "H" | exact Hxk].
  Qed.

  (* iput's [ref--] WHEN IT IS NOT THE LAST: the count goes [Pos.succ n] to
     [n] and the departing reference's fraction [q] rejoins the outstanding
     total, leaving [qr] with [qt = q + qr].  The [sw] and the ghost step
     are in ONE invariant opening, exactly as in [iref_dup_store_au] and
     for the same reason -- the lock's half pins [M] across the
     [lw; addiw; sw], and the two halves meet only here.

     There is no [Hno] side condition and there cannot be one: the count
     goes DOWN, so [icM_wf]'s bound is re-established from the bound the
     invariant already carried ([icM_wf_count] at [Pos.succ n]).  That
     asymmetry with the two increment wrappers is the whole difference. *)
  Lemma iref_close_store_au (Eo : coPset) 
      (M : gmap nat (Qp * positive)) (k : nat) (q qt qr : Qp) (n : positive) :
    ↑icacheN ⊆ Eo ->
    M !! k = Some (qt, Pos.succ n) ->
    (qt - q)%Qp = Some qr ->
    itable_inv -∗ itable_half M -∗ iref_tok k q -∗
    |={Eo, Eo ∖ ↑icacheN}=>
      i_ref (ientry k) ↦₄ iref_word M k ∗
      (i_ref (ientry k) ↦₄ (mword_of_int (Z.pos n) : mword 32)
         ={Eo ∖ ↑icacheN, Eo}=∗
         itable_half (<[k := (qr, n)]> M)).
  Proof.
    iIntros (HE HMk Hsub) "#Hinv Hhalf Htok".
    iMod (inv_acc Eo icacheN with "Hinv") as "[Hbody Hclose]"; [exact HE|].
    iDestruct "Hbody" as (M') "(>Ha & >%Hwf & >Hcells & >Hpool & >Hipool)".
    iDestruct (itable_half_agree with "Ha Hhalf") as %->.
    assert (Hk : (k < NINODE)%nat) by (apply (proj1 Hwf); by eexists).
    iDestruct (iref_cells_acc_upd M k Hk with "Hcells") as "[Hcell Hback]".
    iDestruct (live_pool_acc_upd M k Hk with "Hpool") as "[Hslot Hpback]".
    iDestruct (isl_pool_acc_upd M k Hk with "Hipool") as "[Hislot Hipback]".
    iModIntro. iFrame "Hcell". iIntros "Hcell".
    iDestruct (itable_half_join with "Ha Hhalf") as "Hauth".
    iMod (iref_close_step M k q qt n qr HMk Hsub with "Hauth Htok Hslot Hislot")
      as "(Hauth & Hslot & Hislot)".
    iDestruct (itable_half_split with "Hauth") as "[Ha Hhalf]".
    iMod ("Hclose" with "[Ha Hcell Hback Hslot Hpback Hislot Hipback]") as "_".
    { iNext. iExists (<[k := (qr, n)]> M). iFrame "Ha".
      iSplitR.
      { iPureIntro. destruct Hwf as [Hdom Hcnt]. split.
        - intros i Hi. destruct (decide (i = k)) as [->|Hne]; [exact Hk|].
          rewrite lookup_insert_ne in Hi; [|by apply not_eq_sym]. by apply Hdom.
        - intros i qi ni Hi. destruct (decide (i = k)) as [->|Hne].
          + rewrite lookup_insert in Hi. apply Some_inj in Hi.
            injection Hi as _ Hn. subst ni.
            pose proof (Hcnt k qt (Pos.succ n) HMk) as Hb. lia.
          + rewrite lookup_insert_ne in Hi; [|by apply not_eq_sym].
            by apply (Hcnt i qi). }
      iSplitL "Hcell Hback".
      { iApply ("Hback" $! (qr, n)).
        rewrite /iref_word lookup_insert. iExact "Hcell". }
      iSplitL "Hslot Hpback".
      { iApply ("Hpback" $! (<[k := (qr, n)]> M) with "[%] Hslot").
        intros j Hj. rewrite lookup_insert_ne; [reflexivity | by apply not_eq_sym]. }
      iApply ("Hipback" $! (<[k := (qr, n)]> M) with "[%] Hislot").
      intros j Hj. rewrite lookup_insert_ne; [reflexivity | by apply not_eq_sym]. }
    iModIntro. iFrame.
  Qed.

  (* iput's [ref--] WHEN IT IS THE LAST: the slot leaves [M] entirely and
     the word goes to zero, which is [iref_word]'s [None] branch -- i.e.
     the free-slot shape iget's scan looks for.  The closer must present
     the WHOLE outstanding share [qt]; REF-1 ([iref_lookup] at count one)
     is what tells it that its own [q] is that share. *)
  Lemma iref_close_last_store_au (Eo : coPset) 
      (M : gmap nat (Qp * positive)) (k : nat) (qt : Qp) :
    ↑icacheN ⊆ Eo ->
    M !! k = Some (qt, 1%positive) ->
    itable_inv -∗ itable_half M -∗ iref_tok k qt -∗ live_frac k (1/2)%Qp -∗
    |={Eo, Eo ∖ ↑icacheN}=>
      i_ref (ientry k) ↦₄ iref_word M k ∗
      (i_ref (ientry k) ↦₄ (mword_of_int 0 : mword 32)
         ={Eo ∖ ↑icacheN, Eo}=∗
         itable_half (delete k M)).
  Proof.
    iIntros (HE HMk) "#Hinv Hhalf Htok Hh".
    iMod (inv_acc Eo icacheN with "Hinv") as "[Hbody Hclose]"; [exact HE|].
    iDestruct "Hbody" as (M') "(>Ha & >%Hwf & >Hcells & >Hpool & >Hipool)".
    iDestruct (itable_half_agree with "Ha Hhalf") as %->.
    assert (Hk : (k < NINODE)%nat) by (apply (proj1 Hwf); by eexists).
    iDestruct (iref_cells_acc_del M k Hk with "Hcells") as "[Hcell Hback]".
    iDestruct (live_pool_acc_upd M k Hk with "Hpool") as "[Hslot Hpback]".
    iDestruct (isl_pool_acc_upd M k Hk with "Hipool") as "[Hislot Hipback]".
    iModIntro. iFrame "Hcell". iIntros "Hcell".
    iDestruct (itable_half_join with "Ha Hhalf") as "Hauth".
    iMod (iref_close_last_step M k qt HMk with "Hauth Htok Hh Hslot Hislot")
      as "(Hauth & Hslot & Hislot)".
    iDestruct (itable_half_split with "Hauth") as "[Ha Hhalf]".
    iMod ("Hclose" with "[Ha Hcell Hback Hslot Hpback Hislot Hipback]") as "_".
    { iNext. iExists (delete k M). iFrame "Ha".
      iSplitR.
      { iPureIntro. destruct Hwf as [Hdom Hcnt]. split.
        - intros i Hi. apply Hdom.
          destruct Hi as [e He]. exists e.
          rewrite lookup_delete_Some in He. apply He.
        - intros i qi ni Hi.
          rewrite lookup_delete_Some in Hi. destruct Hi as [_ Hi].
          by apply (Hcnt i qi). }
      iSplitL "Hcell Hback"; [iApply ("Hback" with "Hcell") |].
      iSplitL "Hslot Hpback".
      { iApply ("Hpback" $! (delete k M) with "[%] Hslot").
        intros j Hj. rewrite lookup_delete_ne; [reflexivity | by apply not_eq_sym]. }
      iApply ("Hipback" $! (delete k M) with "[%] Hislot").
      intros j Hj. rewrite lookup_delete_ne; [reflexivity | by apply not_eq_sym]. }
    iModIntro. iFrame.
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  THE SHARE'S SIDE (design §14.6; C8/B2's ilock, B3's idup)          *)
  (* ------------------------------------------------------------------ *)

  (* THE LOCK-FREE GUARD READ, FOR A HOLDER THAT HAS NO REFERENCE.
     [iref_load_au] is the same read for a reference holder, and it gets its
     liveness from [iref_lookup] -- a count fragment names its own slot in
     [M].  A SHARE cannot: [positiveR] has no zero (design §14.5), so a
     share carries no fragment at all.  What it carries is a slice of the
     slot's liveness unit, and the invariant's own arm at a FREE slot is the
     WHOLE unit -- so the slice's mere existence refutes freeness
     ([live_pool_live]).  That is the pool's entire reason to exist.

     [k < NINODE] is a PREMISE here where [iref_load_au] derived it from
     [icM_wf], for the same reason: a share names no map entry until the
     pool has spoken.  Every caller has it from the entry address. *)
  (* the generation-named twin, for [SpecIlock] v4 (design §17.3 (A)): its
     caller's share names the slot's generation, and [live_frac]'s
     existential is not re-introducible once opened. *)
  Lemma iref_live_gen_load_au (Eo : coPset) (k : nat) (s : Qp) (g : gname) :
    ↑icacheN ⊆ Eo -> (k < NINODE)%nat ->
    itable_inv -∗ live_gen k s g -∗
    |={Eo, Eo ∖ ↑icacheN}=> ∃ v : mword 32,
      i_ref (ientry k) ↦₄ v ∗
      (i_ref (ientry k) ↦₄ v ={Eo ∖ ↑icacheN, Eo}=∗
         ⌜0 < bv_unsigned v < 2 ^ 31⌝ ∗ live_gen k s g).
  Proof.
    iIntros (HE Hk) "#Hinv Hlv".
    iMod (inv_acc Eo icacheN with "Hinv") as "[Hbody Hclose]"; [exact HE|].
    iDestruct "Hbody" as (M) "(>Ha & >%Hwf & >Hcells & >Hpool & >Hipool)".
    iDestruct (live_pool_live_gen M k s g Hk with "Hlv Hpool") as %[[qt n] HMk].
    iDestruct (iref_cells_acc M k Hk with "Hcells") as "[Hcell Hback]".
    iModIntro. iExists (iref_word M k). iFrame "Hcell".
    iIntros "Hcell".
    iMod ("Hclose" with "[Ha Hcell Hback Hpool Hipool]") as "_".
    { iNext. iExists M. iFrame "Ha". iSplitR; [iPureIntro; exact Hwf|].
      iFrame "Hpool Hipool". iApply ("Hback" with "Hcell"). }
    iModIntro. iFrame "Hlv". iPureIntro.
    exact (iref_word_live M k qt n Hwf HMk).
  Qed.

  Lemma iref_live_load_au (Eo : coPset) (k : nat) (s : Qp) :
    ↑icacheN ⊆ Eo -> (k < NINODE)%nat ->
    itable_inv -∗ live_frac k s -∗
    |={Eo, Eo ∖ ↑icacheN}=> ∃ v : mword 32,
      i_ref (ientry k) ↦₄ v ∗
      (i_ref (ientry k) ↦₄ v ={Eo ∖ ↑icacheN, Eo}=∗
         ⌜0 < bv_unsigned v < 2 ^ 31⌝ ∗ live_frac k s).
  Proof.
    iIntros (HE Hk) "#Hinv Hlv".
    iMod (inv_acc Eo icacheN with "Hinv") as "[Hbody Hclose]"; [exact HE|].
    iDestruct "Hbody" as (M) "(>Ha & >%Hwf & >Hcells & >Hpool & >Hipool)".
    iDestruct (live_pool_live M k s Hk with "Hlv Hpool") as %[[qt n] HMk].
    iDestruct (iref_cells_acc M k Hk with "Hcells") as "[Hcell Hback]".
    iModIntro. iExists (iref_word M k). iFrame "Hcell".
    iIntros "Hcell".
    iMod ("Hclose" with "[Ha Hcell Hback Hpool Hipool]") as "_".
    { iNext. iExists M. iFrame "Ha". iSplitR; [iPureIntro; exact Hwf|].
      iFrame "Hpool Hipool". iApply ("Hback" with "Hcell"). }
    iModIntro. iFrame "Hlv". iPureIntro.
    exact (iref_word_live M k qt n Hwf HMk).
  Qed.

  (* NO SHARE CAN COEXIST WITH A HOLDER OF THE SLOT'S WHOLE OUTSTANDING MASS
     (design §14.8's corrected REF-1 refutation).

     §14.6 stated iput's refutation of a share-shaped escrow arm over IDENTITY
     mass, and that does not close: in the checked-out state the arm holds only
     the share's [s] of each identity cell (the parked ½ is in the CHECKED-OUT
     THREAD's hand -- SpecIlock hands it out), so the sum never passes one.
     The LIVE mass does close, and this is it: a reference holder whose own
     [q] IS the map's [qt] (which is what REF-1 gives, [iref_lookup]) carries
     [live_frac k qt]; the invariant's arm at a live slot is exactly the
     complement [1 - qt] ([live_slot]); the two are already the WHOLE unit, so
     any further slice at all is over budget.

     Stated as a fupd because [live_slot] lives inside [itable_inv] and the
     opener is holding no piece of it -- which is why [IcacheEscrow]'s two
     authority-side openers had to become fupds too.  The count is irrelevant
     here: what does the work is [q = qt], not [n = 1]. *)
  Lemma live_whole_share_absurd (Eo : coPset) (M : gmap nat (Qp * positive))
      (k : nat) (qt s : Qp) (n : positive) :
    ↑icacheN ⊆ Eo ->
    M !! k = Some (qt, n) ->
    itable_inv -∗ itable_half M -∗ live_frac k qt -∗ live_frac k (1/2)%Qp -∗
    live_frac k s ={Eo}=∗ False.
  Proof.
    iIntros (HE HMk) "#Hinv Hhalf Hq Hh Hs".
    iMod (inv_acc Eo icacheN with "Hinv") as "[Hbody _]"; [exact HE|].
    iDestruct "Hbody" as (M') "(>Ha & >%Hwf & >_ & >Hpool & >Hipool)".
    iDestruct (itable_half_agree with "Ha Hhalf") as %->.
    assert (Hk : (k < NINODE)%nat) by (apply (proj1 Hwf); by eexists).
    iDestruct (big_sepL_lookup (fun (_ : nat) (j : nat) => live_slot M j)
                 (seq 0 NINODE) k k (seq_ninode_lookup k Hk) with "Hpool") as "Hsl".
    iDestruct (live_slot_some_inv M k qt n HMk with "Hsl") as (c) "[%Ec Hc]".
    apply Qp.sub_Some in Ec.                  (* 1/2 = qt + c *)
    assert (Hsum : (qt + c + (1/2)%Qp)%Qp = 1%Qp).
    { rewrite -Ec. apply Qp.half_half. }
    iDestruct (live_frac_join with "Hq Hc") as "Hqc".
    iDestruct (live_frac_join with "Hqc Hh") as "Hone".
    iEval (rewrite Hsum) in "Hone".
    iDestruct (live_frac_full_excl with "Hone Hs") as "[]".
  Qed.

  (* THE SECOND GENERATION BUMP (design §17.6, ratified §17.7) -- and it is
     [live_whole_share_absurd] read in the POSITIVE direction.

     A generation may see AT MOST ONE FILL, or the type witness it carries is
     not a function of the generation.  iget's recycle gives the FIRST fill
     its own generation ([live_slot_alloc]); §17.6.1 exhibits a REACHABLE
     second one -- iput's free path re-parks UNLOADED, ialloc's claim retags
     the very same inum through the buffer, its [iget] hits the still-cached
     entry, and [ProofIlock]'s third fill branch completes on the marker.  So
     the free path must RETIRE the generation before it re-parks.

     A bump needs the slot's WHOLE unit, and this is the second (and last)
     instant at which it exists: at iput's REF-1 free window the closer's [qt]
     is its own ([iref_lookup] off [M !! k = Some (qt, n)]), the escrow arm's
     1/2 is in its hand (handed out with the payload by [ic_open_auth_ref],
     since [ic_held] holds no slice -- §17.5's forced deviation), and the
     table's [1/2 - qt] is in [live_slot].  Those are exactly the three
     summands [live_whole_share_absurd] adds to a contradiction; here they are
     added to ONE and spent on [live_frac_bump].

     THE COUNT [n] IS A PARAMETER THIS LEMMA NEVER READS, exactly as in
     [live_whole_share_absurd]: REF-1 is only how the caller comes to know
     [q = qt].  And the itable lock -- held by iput from its [acquire] through
     +0x5c, with this call inside that window -- is what makes the bump
     airtight: every reference minted afterwards, INCLUDING the claim's, is
     minted at the new generation, and every reference that existed before is
     refuted by REF-1.

     [live_slot]'s text does not move: it is stated over [live_frac], whose
     generation is existential, so the table's remainder simply comes back
     naming [g'] instead of [g]. *)
  Lemma live_slot_regen (Eo : coPset) (M : gmap nat (Qp * positive))
      (k : nat) (qt : Qp) (n : positive) :
    ↑icacheN ⊆ Eo ->
    M !! k = Some (qt, n) ->
    itable_inv -∗ itable_half M -∗ live_frac k qt -∗ live_frac k (1/2)%Qp
    ={Eo}=∗ ∃ g' : gname,
      itable_half M ∗ live_gen k qt g' ∗ live_gen k (1/2)%Qp g' ∗
      ity_pending g'.
  Proof.
    iIntros (HE HMk) "#Hinv Hhalf Hq Hh".
    iMod (inv_acc Eo icacheN with "Hinv") as "[Hbody Hclose]"; [exact HE|].
    iDestruct "Hbody" as (M') "(>Ha & >%Hwf & >Hcells & >Hpool & >Hipool)".
    iDestruct (itable_half_agree with "Ha Hhalf") as %->.
    assert (Hk : (k < NINODE)%nat) by (apply (proj1 Hwf); by eexists).
    iDestruct (live_pool_acc_upd M k Hk with "Hpool") as "[Hsl Hback]".
    iDestruct (live_slot_some_inv M k qt n HMk with "Hsl") as (c) "[%Ec Hc]".
    pose proof (proj1 (Qp.sub_Some (1/2)%Qp qt c) Ec) as Ec'. (* 1/2 = qt + c *)
    assert (Hsum : (qt + c + (1/2)%Qp)%Qp = 1%Qp).
    { rewrite -Ec'. apply Qp.half_half. }
    iDestruct (live_frac_join with "Hq Hc") as "Hqc".
    iDestruct (live_frac_join with "Hqc Hh") as "Hone".
    iEval (rewrite Hsum) in "Hone".
    iMod (live_frac_bump k with "Hone") as (g') "[Hg Hp]".
    iEval (rewrite -Hsum) in "Hg".
    rewrite live_gen_split. iDestruct "Hg" as "[Hqc' Hh']".
    rewrite live_gen_split. iDestruct "Hqc'" as "[Hq' Hc']".
    iMod ("Hclose" with "[Ha Hcells Hback Hc' Hipool]") as "_".
    { iNext. iExists M. iFrame "Ha". iSplitR; [iPureIntro; exact Hwf|].
      iFrame "Hcells". iSplitR "Hipool"; [| iFrame "Hipool" ].
      iApply ("Hback" $! M with "[%] [Hc']").
      - intros j _. reflexivity.
      - rewrite (live_slot_some M k qt n c HMk Ec). iExists g'. iExact "Hc'". }
    iModIntro. iExists g'. iFrame.
  Qed.

  (* THE SAME FACT FOR A LOCK HOLDER -- origin's [iref_share_lookup], ported.
     Theirs read a count-0 fragment against [itable_half] and needed no
     invariant; ours is a pool slice, so it opens [itable_inv] (and closes it
     again immediately -- no cell moves).  idup's [lw]/[sw] pair needs
     exactly this and nothing more. *)
  Lemma iref_share_lookup_au (Eo : coPset) (M : gmap nat (Qp * positive))
      (k : nat) (s : Qp) :
    ↑icacheN ⊆ Eo -> (k < NINODE)%nat ->
    itable_inv -∗ itable_half M -∗ live_frac k s
    ={Eo}=∗ ⌜is_Some (M !! k)⌝ ∗ itable_half M ∗ live_frac k s.
  Proof.
    iIntros (HE Hk) "#Hinv Hhalf Hlv".
    iMod (inv_acc Eo icacheN with "Hinv") as "[Hbody Hclose]"; [exact HE|].
    iDestruct "Hbody" as (M') "(>Ha & >%Hwf & >Hcells & >Hpool & >Hipool)".
    iDestruct (itable_half_agree with "Ha Hhalf") as %->.
    iDestruct (live_pool_live M k s Hk with "Hlv Hpool") as %HMk.
    iMod ("Hclose" with "[Ha Hcells Hpool Hipool]") as "_".
    { iNext. iExists M. iFrame "Ha Hcells Hpool Hipool". iPureIntro. exact Hwf. }
    iModIntro. by iFrame.
  Qed.

  (* THE UPGRADE (share -> reference), for B3's idup -- AND WHAT IT IS NOT.

     Origin's [iref_upgrade_step] moved a count-0 fragment to count 1 at the
     SAME fraction: under [natR] a share IS authority mass, so upgrading it
     conjures nothing.  Under [positiveR] it is not, and the accounting
     forbids the analogous move: the table's retained identity share is
     [1/2 - qt] against the authority's [qt] (§13.1b), so a new fragment at
     [s] must be matched by [s] of identity coming OUT OF THE TABLE.  The
     share's own [s] is already spoken for -- it is the hole in its parent's
     identity slice.  So a share cannot BECOME a reference; the fractions do
     not line up, and any lemma that claimed otherwise would have to conjure
     [s] of [i_dev]/[i_inum].

     WHAT idup ACTUALLY NEEDS is weaker and already true: the share is a
     LIVENESS WITNESS (it proves the slot is live, and it keeps it live,
     because its parent cannot close while short of identity), and the new
     reference is minted from the table's retained share exactly as iget's
     cache-hit arm mints one -- [iref_incr_store_au].  This wrapper is that
     step with the share carried through, so B3's call site reads as the
     upgrade it is: share in, share + reference out.

     The consequence for B3: idup's postcondition returns the share BESIDE
     the new reference, and kfork's parent gathers it back
     ([IcacheRef.inode_ref_gather]) instead of losing it. *)
  Lemma iref_upgrade_store_au (Eo : coPset)
      (M : gmap nat (Qp * positive)) (k : nat) (qt qn s : Qp) (n : positive) :
    ↑icacheN ⊆ Eo ->
    M !! k = Some (qt, n) ->
    (qt + qn < 1/2)%Qp ->
    (Z.pos (Pos.succ n) < 2 ^ 31)%Z ->
    itable_inv -∗ itable_half M -∗ live_frac k s -∗
    |={Eo, Eo ∖ ↑icacheN}=>
      i_ref (ientry k) ↦₄ iref_word M k ∗
      (i_ref (ientry k) ↦₄ (mword_of_int (Z.pos (Pos.succ n)) : mword 32)
         ={Eo ∖ ↑icacheN, Eo}=∗
         itable_half (<[k := ((qt + qn)%Qp, Pos.succ n)]> M) ∗
         iref_tok k qn ∗ live_frac k s).
  Proof.
    iIntros (HE HMk Hq Hno) "#Hinv Hhalf Hlv".
    iMod (iref_incr_store_au Eo M k qt qn n HE HMk Hq Hno with "Hinv Hhalf")
      as "[Hcell Hback]".
    iModIntro. iFrame "Hcell". iIntros "Hcell".
    iMod ("Hback" with "Hcell") as "[Hhalf Htok]".
    iModIntro. iFrame.
  Qed.

End IcacheRefInv.

(* ===================================================================== *)
(*  6.  THE itable LOCK'S RESOURCE: dev / inum, AND WHAT A REFERENCE IS   *)
(* ===================================================================== *)

Section IcacheTable.
  Context `{!riscvGS Σ, !lockG Σ, !icacheG Σ, !irefslotG Σ}.
  Context `{ICFG : icfg}.
  Context `{GEN : GenId}.

  (* [inode_ident] and [inode_ref] are [IcacheRef.v]'s; only the JOIN
     helper below stayed, because [islot_rest_join] uses it. *)
  (* the fraction JOIN for one cell, as a wand.  A bare
     [rewrite word4_pointsto_frac_split] at a call site rewrites the whole
     [envs_entails] -- hypotheses included -- and silently re-splits the very
     fragments being joined (durable-notes' proofmode rule); inside this
     lemma the two hypotheses' dfracs are bare variables, so the pattern
     matches the goal only. *)
  Local Lemma word4_frac_join (a : Arch.pa) (q1 q2 : Qp) (w : bv 32) :
    a ↦₄{DfracOwn q1} w -∗ a ↦₄{DfracOwn q2} w -∗ a ↦₄{DfracOwn (q1 + q2)} w.
  Proof. iIntros "H1 H2". rewrite word4_pointsto_frac_split. iFrame. Qed.

  (* ---- THE IDENTITY BUDGET (design §13.1b, as corrected by §13.1e) ----

     The escrow's PARKED arm owns HALF of BOTH identity cells permanently.
     For [i_inum] that half is what ties the arm's [dinode_at] to the entry
     the cells name, and the ½-versus-FULL split of THAT cell is what
     distinguishes the parked arm from the recycle-window arm (§13.1c -- the
     inum cell remains the sole parked/mid discriminator).  For [i_dev] the
     half exists for a different reason, and §13.1b's "the dev cell needs no
     arm tie" was wrong: a checked-out [ilock] has deposited its WHOLE
     reference, so without a dev half handed back at checkout it could not
     read [ip->dev] for its own [bread] (ilock+0x48), and [iunlock] could not
     return the caller's reference AT THE CALLER'S DEVICE.  [BioInv]'s
     [buf_parked] holds [b_dev ↦₄{½}] for exactly these two reasons.  So the
     budget is SYMMETRIC:

         i_dev  :  1  =  ½ (the escrow, forever)
                      +  q (the references)  +  (½ - q)  (the table)
         i_inum :  1  =  ½ (the escrow, forever)
                      +  q (the references)  +  (½ - q)  (the table)

     and a reference's fraction therefore ranges in (0, ½) -- STRICTLY, and
     that is what the [None] arm below is about.  The table's retained share
     is now an [inode_ident] like every other share.

     [islot_rest_at] pins the two values (the pool's slot->inum map wants
     them pinned, §13.2); [islot_rest] is the ∃-bound form the plain
     [itable_res] uses.

     THE [None] ARM IS [False], NOT [emp] (design §13.8, C5's blocker B).
     [None] is the [q ≥ ½] case -- the whole shared half handed out, the
     table keeping nothing of either cell.  Written [emp] that state is
     PERMITTED, and then two things become unprovable at a slot in it: iget's
     cache-hit arm, which must mint a positive identity fraction OUT of the
     retained share ([IcacheInv.iref_incr_store_au] supplies only the count
     fragment), and any plain read of [ip->dev] / [ip->inum] under the lock,
     which iget's scan does fifty times.  The state is unreachable in the
     code -- [iref_alloc_step] mints at ¼, a hit mints strictly less than the
     remainder, [iref_dup_step] does not move [q] and [iref_close_step]
     shrinks it -- but "unreachable" is not a fact any invariant here states.
     Writing [False] makes the positivity RESOURCE-CARRIED, so it is
     re-established automatically at every split and no wf clause has to
     mention fractions. *)
  Definition islot_rest_at (k : nat) (q : Qp) (dev inum : mword 32) : iProp Σ :=
    match (1/2 - q)%Qp with
    | Some q' => inode_ident k (DfracOwn q') dev inum
    | None => False%I
    end.

  Definition islot_rest (k : nat) (q : Qp) : iProp Σ :=
    (∃ dev inum : mword 32, islot_rest_at k q dev inum)%I.

  (* ...and a FREE slot's share: each identity cell's other half (the escrow
     keeps one half of each; iget's [sw]s at +0x6e and +0x72 join them, which
     is why NEITHER store can happen without opening the escrow -- §13.1c,
     §13.1e). *)
  Definition islot_free_at (k : nat) (dev inum : mword 32) : iProp Σ :=
    inode_ident k (DfracOwn (1/2)) dev inum.

  Definition islot_free (k : nat) : iProp Σ :=
    (∃ dev inum : mword 32, islot_free_at k dev inum)%I.

  (* A LIVE slot also parks one iref-slot unit per outstanding reference.
     That is what lets a thread about to run [ref++] weigh the count against
     the supply without leaving the lock: [IrefSlots.iref_slots_no_overflow]
     against the [iref_slots_auth] below.  Exactly [FileInv]'s arrangement
     for [fd_slots] -- see [IrefSlots.v]'s header for why an unconditional
     increment needs it and why no axiom may replace it. *)
  Definition islot (M : gmap nat (Qp * positive)) (k : nat) : iProp Σ :=
    match M !! k with
    | None => islot_free k
    | Some (q, n) => (islot_rest k q ∗ iref_slots (Pos.to_nat n))%I
    end.

  Definition itable_res : iProp Σ :=
    (∃ M : gmap nat (Qp * positive),
       itable_half M ∗ ⌜icM_wf M⌝ ∗ iref_slots_auth ∗
       [∗ list] k ∈ seq 0 NINODE, islot M k)%I.

  Definition is_itable (γl : gname) : iProp Σ :=
    is_lock γl itable_lock "itable"%string itable_res.

  Global Instance is_itable_persistent γl : Persistent (is_itable γl).
  Proof. apply _. Qed.

  (* The lock resource's slot accessor, in the form a WRITER needs: the map
     may come back CHANGED, provided it changed only at [k].  Same shape and
     same proof as [iref_cells_acc_upd] one section up -- [big_sepL_delete]
     splits index [k] off, and the element of [seq 0 NINODE] at index [j]
     being [j] is what turns "index ≠ k" into "this slot did not move". *)
  Lemma islots_acc_upd (M : gmap nat (Qp * positive)) (k : nat) :
    (k < NINODE)%nat ->
    ([∗ list] j ∈ seq 0 NINODE, islot M j) -∗
      islot M k ∗
      (∀ M' : gmap nat (Qp * positive),
         ⌜forall j, j <> k -> M' !! j = M !! j⌝ -∗
         islot M' k -∗ [∗ list] j ∈ seq 0 NINODE, islot M' j).
  Proof.
    intros Hk. iIntros "Hs".
    iDestruct (big_sepL_delete _ (seq 0 NINODE) k k
                 ltac:(apply lookup_seq; split; [lia|exact Hk]) with "Hs")
      as "[Hslot Hrest]".
    iFrame "Hslot". iIntros (M') "%Hagree Hslot".
    iApply (big_sepL_delete _ (seq 0 NINODE) k k
              ltac:(apply lookup_seq; split; [lia|exact Hk])).
    iFrame "Hslot".
    iApply (big_sepL_impl with "Hrest").
    iIntros "!>" (j x Hjx) "H".
    destruct (decide (j = k)) as [->|Hne]; [iExact "H"|].
    apply lookup_seq in Hjx as [Hx _].
    assert (Hxk : x <> k) by lia.
    iEval (rewrite /islot) in "H".
    rewrite /islot (Hagree x Hxk). iExact "H".
  Qed.

  (* THE LAST CLOSER'S JOIN, and the second half of REF-1 EXCLUSIVITY at
     the points-to level: [iref_lookup] forced [q = qt] on a slot whose
     count is one, so the closer's share plus whatever the table kept is
     everything the TABLE can ever hold of this entry -- half of each
     identity cell.  That is exactly [islot_free_at], i.e. the slot handed
     back to iget as free; each cell's OTHER half stays in the escrow's
     parked arm forever (§13.1b/§13.1e) and is joined in only by the
     recycler, inside the escrow openings that perform the [sw]s at +0x6e
     and +0x72. *)
  Lemma islot_rest_join k (qt : Qp) dev inum :
    (qt ≤ 1/2)%Qp ->
    inode_ident k (DfracOwn qt) dev inum -∗ islot_rest k qt -∗
    islot_free_at k dev inum.
  Proof.
    intros Hle. rewrite /islot_rest /islot_rest_at /islot_free_at /inode_ident.
    destruct (1/2 - qt)%Qp as [q'|] eqn:Et.
    - apply Qp.sub_Some in Et.        (* 1/2 = qt + q' *)
      iIntros "[Hd Hn] (%d & %n & [Hd' Hn'])".
      iDestruct (word4_pointsto_agree with "Hd Hd'") as %->.
      iDestruct (word4_pointsto_agree with "Hn Hn'") as %->.
      iSplitL "Hd Hd'".
      + iDestruct (word4_frac_join with "Hd Hd'") as "H".
        iEval (rewrite -Et) in "H". iExact "H".
      + iDestruct (word4_frac_join with "Hn Hn'") as "H".
        iEval (rewrite -Et) in "H". iExact "H".
    - (* [q ≥ 1/2] is now [False] in the arm itself (§13.8), so there is
         nothing to reason about: the retained share is never empty. *)
      iIntros "_ (%d0 & %n0 & [])".
  Qed.

End IcacheTable.
