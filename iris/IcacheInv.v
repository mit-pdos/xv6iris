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
From iris.algebra Require Import auth gmap frac numbers excl.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap invariants own ghost_var.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvPtsto RiscvExtras.
Require Import WpLock SleepLock.
Require Import LogInv.
Require Export IcacheRef.   (* the geometry, the algebra, [inode_ref] *)
Require Import InodeInv.
(* THE COUNT COUPLING (iclaim-ledger.md §2.2) is why this file now knows the
   inode REGION: every count move has to reach the [icnt] half that rides in
   [InodeRegion.ireg_slot], so the five [*_store_au] wrappers below take
   [ireg_inv] and nest an [↑iregN] open inside their [↑icacheN] one (the
   ZZProbeIcnt probe's proven pattern, §2.9's structural mask verdict).  The
   dependency is new but acyclic -- [InodeRegion] requires [IcacheRef],
   [EscrowDefs] and [LogInv], none of which requires this file -- and the
   lemmas that need it live in their own section at the end, so no landed
   consumer of [Section IcacheRefInv] gains a typeclass premise. *)
(* THE THREE CLASSES THAT ARE NOT WHERE THEY LOOK ([ProofFilewrite]'s note,
   one tier up): [diskGhostG], [fsLogG] and [iregG] live in [DiskPtsto],
   [FsBlocks] and [InodeRegion], and none of them is re-exported by anything
   else here -- without these lines the section [Context] below invents FRESH
   variables of those names and every [ireg_inv] in the file comes out an
   unresolved evar. *)
Require Import DiskPtsto.
Require Import DinodeEnc.  (* [islot]/[islot_lt]: the inum's slot in its block *)
Require Import FsBlocks.    (* [fs_names], which [ireg_inv] is keyed by *)
Require Import InodeRegion.
(* iclaim-ledger.md §3.1's licence table -- the up-count movers refute a
   standing [FrzPre] with [IgetLic.iname_not_frozen] instead of with a
   freeze token they cannot have (RULING A's custody clause).  No cycle:
   [IgetLic] sits over [InodeRegion]/[IcacheRef]/[DirLinks] and knows
   nothing of the itable. *)
Require Import IgetLic.
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
  (* ---- RULING R-e (iclaim-ledger.md §5⁗⁗): the arm is a DISJUNCTION ----

     The ORDINARY alternative is exactly what the three-way split above
     describes and is what every landed move reads.  The FROZEN one holds the
     slot's WHOLE unit -- the freezer's own [qt], the escrow arm's ½ and this
     arm's own [½ - qt], joined at iput's mint inside the one [itable_inv]
     opening [live_slot_regen] already takes -- and it is what R-e buys:

       * a reader with the escrow tail's [frzsel] half and ANY positive
         [live_frac k s'] kills it by [live_frac_full_excl], with NO lock, NO
         licence, NO region open and NO index ([frz_slot_kill]) -- which is
         ProofIlock:2422 and ProofIdup's decider, both;
       * the mass is NOT in anybody's hand for the whole lock-free span, so
         that span's foreign readers see the invariant and nothing else.

     THE SELECTOR ([IcacheRef.frzsel]) is what makes the disjunction DECIDE,
     and its ledger is:

       FREE            this arm 1  false
       LIVE, unfrozen  this arm ½  false  +  [frz_park]'s OFF arm  ½ false
       LIVE, frozen    this arm ½  true   +  the escrow's frozen tail ½ true

     so the two weapons are (i) any positive live slice, which refutes the
     frozen alternative outright, and (ii) the OFF half, which refutes it by
     [IcacheRef.frzsel_agree] -- and (ii) is what the LICENSED up-count needs,
     being the one mover that holds no live slice of its own (see
     [iref_incr_step]).

     [1/2 - qt] is factored OUT of the disjunction, so both alternatives carry
     it: the retirement still needs it, and the frozen alternative would
     otherwise lose the [q < 1/2] budget the reclaim reads. *)
  Definition live_norm (M : gmap nat (Qp * positive)) (k : nat) : iProp Σ :=
    match M !! k with
    | None => (live_frac k 1%Qp ∗ frzsel k 1%Qp false)%I
    | Some (qt, _) =>
        match (1/2 - qt)%Qp with
        | Some c => (live_frac k c ∗ frzsel k (1/2)%Qp false)%I
        | None => False%I
        end
    end.

  Definition live_frzn (M : gmap nat (Qp * positive)) (k : nat) : iProp Σ :=
    match M !! k with
    | None => False%I
    | Some (qt, _) =>
        match (1/2 - qt)%Qp with
        | Some _ => (live_frac k 1%Qp ∗ frzsel k (1/2)%Qp true)%I
        | None => False%I
        end
    end.

  Definition live_slot (M : gmap nat (Qp * positive)) (k : nat) : iProp Σ :=
    (live_norm M k ∨ live_frzn M k)%I.

  Definition live_pool (M : gmap nat (Qp * positive)) : iProp Σ :=
    ([∗ list] k ∈ seq 0 NINODE, live_slot M k)%I.

  Global Instance live_norm_timeless M k : Timeless (live_norm M k).
  Proof.
    rewrite /live_norm. destruct (M !! k) as [[qt n]|];
      [destruct (1/2 - qt)%Qp|]; apply _.
  Qed.
  Global Instance live_frzn_timeless M k : Timeless (live_frzn M k).
  Proof.
    rewrite /live_frzn. destruct (M !! k) as [[qt n]|];
      [destruct (1/2 - qt)%Qp|]; apply _.
  Qed.
  Global Instance live_slot_timeless M k : Timeless (live_slot M k).
  Proof. rewrite /live_slot. apply _. Qed.
  Global Instance live_pool_timeless M : Timeless (live_pool M).
  Proof. apply _. Qed.

  (* the shapes, as equations, so every move below is a rewrite *)
  Lemma live_norm_none M k :
    M !! k = None -> live_norm M k = (live_frac k 1%Qp ∗ frzsel k 1%Qp false)%I.
  Proof. intros H. by rewrite /live_norm H. Qed.

  Lemma live_norm_some M k qt n c :
    M !! k = Some (qt, n) -> (1/2 - qt)%Qp = Some c ->
    live_norm M k = (live_frac k c ∗ frzsel k (1/2)%Qp false)%I.
  Proof. intros H1 H2. by rewrite /live_norm H1 /= H2. Qed.

  Lemma live_frzn_none M k : M !! k = None -> live_frzn M k = False%I.
  Proof. intros H. by rewrite /live_frzn H. Qed.

  Lemma live_frzn_some M k qt n c :
    M !! k = Some (qt, n) -> (1/2 - qt)%Qp = Some c ->
    live_frzn M k = (live_frac k 1%Qp ∗ frzsel k (1/2)%Qp true)%I.
  Proof. intros H1 H2. by rewrite /live_frzn H1 /= H2. Qed.

  Lemma live_slot_of_norm M k : live_norm M k -∗ live_slot M k.
  Proof. iIntros "H". by iLeft. Qed.

  Lemma live_slot_of_frzn M k : live_frzn M k -∗ live_slot M k.
  Proof. iIntros "H". by iRight. Qed.

  (* a move that changes only the COUNT leaves the arm literally where it is:
     both alternatives are stated over [M !! k]'s FRACTION alone. *)
  Lemma live_slot_recount M k qt (n n' : positive) :
    M !! k = Some (qt, n) ->
    live_slot M k = live_slot (<[k := (qt, n')]> M) k.
  Proof.
    intros HM. rewrite /live_slot /live_norm /live_frzn HM.
    by rewrite (lookup_insert M k (qt, n')).
  Qed.

  (* WEAPON (i): any positive live slice refutes the frozen alternative --
     it holds the whole unit.  This is [frz_slot_kill]'s local half. *)
  Lemma live_slot_norm_of_lv M k s :
    live_frac k s -∗ live_slot M k -∗ live_frac k s ∗ live_norm M k.
  Proof.
    iIntros "Hs [Hn | Hf]"; [by iFrame |].
    rewrite /live_frzn. destruct (M !! k) as [[qt n]|];
      [| iDestruct "Hf" as "[]"].
    destruct (1/2 - qt)%Qp; [| iDestruct "Hf" as "[]"].
    iDestruct "Hf" as "[Hone _]".
    iDestruct (live_frac_full_excl with "Hone Hs") as "[]".
  Qed.

  (* WEAPON (ii): the selector's OFF half, for the mover that holds no slice *)
  Lemma live_slot_norm_of_sel M k q :
    frzsel k q false -∗ live_slot M k -∗ frzsel k q false ∗ live_norm M k.
  Proof.
    iIntros "Hsel [Hn | Hf]"; [by iFrame |].
    rewrite /live_frzn. destruct (M !! k) as [[qt n]|];
      [| iDestruct "Hf" as "[]"].
    destruct (1/2 - qt)%Qp; [| iDestruct "Hf" as "[]"].
    iDestruct "Hf" as "[_ Hst]".
    iDestruct (frzsel_agree with "Hsel Hst") as %Hb. discriminate.
  Qed.

  (* ...and its mirror, for the freezer's own reclaim *)
  Lemma live_slot_frzn_of_sel M k q :
    frzsel k q true -∗ live_slot M k -∗ frzsel k q true ∗ live_frzn M k.
  Proof.
    iIntros "Hsel [Hn | Hf]"; [| by iFrame].
    rewrite /live_norm. destruct (M !! k) as [[qt n]|].
    - destruct (1/2 - qt)%Qp; [| iDestruct "Hn" as "[]"].
      iDestruct "Hn" as "[_ Hsf]".
      iDestruct (frzsel_agree with "Hsel Hsf") as %Hb. discriminate.
    - iDestruct "Hn" as "[_ Hsf]".
      iDestruct (frzsel_agree with "Hsel Hsf") as %Hb. discriminate.
  Qed.

  Lemma live_slot_none M k :
    M !! k = None -> live_slot M k -∗ live_frac k 1%Qp ∗ frzsel k 1%Qp false.
  Proof.
    intros H. rewrite /live_slot (live_frzn_none M k H) (live_norm_none M k H).
    iIntros "[$ | []]".
  Qed.

  Lemma live_slot_none_intro M k :
    M !! k = None -> live_frac k 1%Qp -∗ frzsel k 1%Qp false -∗ live_slot M k.
  Proof.
    intros H. iIntros "Hone Hsel". iApply live_slot_of_norm.
    rewrite (live_norm_none M k H). iFrame.
  Qed.

  Lemma live_norm_some_inv M k qt n :
    M !! k = Some (qt, n) ->
    live_norm M k -∗
      ∃ c : Qp, ⌜(1/2 - qt)%Qp = Some c⌝ ∗ live_frac k c ∗ frzsel k (1/2)%Qp false.
  Proof.
    intros HM. rewrite /live_norm HM /=.
    destruct (1/2 - qt)%Qp as [c|] eqn:E; [| iIntros "[]"].
    iIntros "H". iExists c. by iFrame.
  Qed.

  (* the landed shape of this lemma, at the alternative every legacy caller
     is in: it holds a positive slice, so [live_slot_norm_of_lv] applies. *)
  Lemma live_slot_some_inv M k qt n s :
    M !! k = Some (qt, n) ->
    live_slot M k -∗ live_frac k s -∗
      ∃ c : Qp, ⌜(1/2 - qt)%Qp = Some c⌝ ∗
        live_frac k c ∗ frzsel k (1/2)%Qp false ∗ live_frac k s.
  Proof.
    intros HM. iIntros "Hsl Hs".
    iDestruct (live_slot_norm_of_lv with "Hs Hsl") as "[Hs Hn]".
    iDestruct (live_norm_some_inv M k qt n HM with "Hn") as (c) "[%Ec [Hc Hsel]]".
    iExists c. by iFrame.
  Qed.

  (* THE SHARE'S READER, in its purest form: any slice of slot [k]'s unit
     proves the slot is LIVE, because a free one's unit is entire. *)
  Lemma live_slot_live M k s :
    live_frac k s -∗ live_slot M k -∗ ⌜is_Some (M !! k)⌝.
  Proof.
    iIntros "Hs Hsl".
    iDestruct (live_slot_norm_of_lv with "Hs Hsl") as "[Hs Hsl]".
    rewrite /live_norm.
    destruct (M !! k) as [e|] eqn:E; [iPureIntro; by eexists|].
    iDestruct "Hsl" as "[Hone _]".
    iDestruct (live_frac_full_excl with "Hone Hs") as "[]".
  Qed.

  (* the same, with the generation NAMED -- the form [SpecIlock] v4's
     guard read needs, since its share arrives generation-named (design
     §17.3 (A)) and [live_frac]'s existential cannot be re-introduced
     afterwards. *)
  Lemma live_slot_live_gen M k s g :
    live_gen k s g -∗ live_slot M k -∗ ⌜is_Some (M !! k)⌝.
  Proof.
    iIntros "Hs Hsl".
    iAssert (live_frac k s) with "[Hs]" as "Hsf"; [by iExists g |].
    iDestruct (live_slot_norm_of_lv with "Hsf Hsl") as "[Hsf Hsl]".
    rewrite /live_norm.
    destruct (M !! k) as [e|] eqn:E; [iPureIntro; by eexists|].
    iDestruct "Hsl" as "[Hone _]".
    iDestruct (live_frac_full_excl with "Hone Hsf") as "[]".
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
    iEval (rewrite /live_slot /live_norm /live_frzn) in "H".
    rewrite /live_slot /live_norm /live_frzn (Hagree x Hxk). iExact "H".
  Qed.

  (* BOOT (RULING R-e).  The reserved half of [IcacheRef.live_boot_map]'s
     keyspace arrives beside the pool's own units and is retagged to the
     [false] literal here -- which is the ONLY reason this is a fupd. *)
  Lemma live_pool_empty :
    ([∗ list] k ∈ seq 0 (NINODE + NINODE), live_frac k 1%Qp) ==∗ live_pool ∅.
  Proof.
    rewrite /live_pool. iIntros "H".
    rewrite seq_app big_sepL_app. iDestruct "H" as "[Hl Hr]".
    rewrite -(fmap_add_seq NINODE 0 NINODE) big_sepL_fmap.
    iDestruct (big_sepL_sep_2 with "Hl Hr") as "H".
    iApply big_sepL_bupd.
    iApply (big_sepL_mono with "H"). intros idx k _.
    iIntros "[Hone Hr]".
    iMod (frzsel_boot k with "Hr") as "Hs".
    iModIntro. iApply (live_slot_none_intro ∅ k (lookup_empty k) with "Hone Hs").
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
  (* RULING R-e: the free arm's WHOLE selector splits here -- one half stays
     with the arm, and the other goes OUT, to [frz_park]'s OFF alternative in
     [IcacheEscrow.islot2]'s live arm.  That half is what the licensed
     up-count later spends to refute the frozen alternative. *)
  Lemma live_slot_alloc M k q :
    M !! k = None -> (q < 1/2)%Qp ->
    live_slot M k ==∗ ∃ g : gname,
      live_frac k q ∗ live_gen k (1/2)%Qp g ∗ ity_pending g ∗
      frzsel k (1/2)%Qp false ∗
      live_slot (<[k := (q, 1%positive)]> M) k.
  Proof.
    intros HM Hq.
    apply Qp.lt_sum in Hq as [c Hc].          (* 1/2 = q + c *)
    assert (Hsum : (q + ((1/2)%Qp + c))%Qp = 1%Qp).
    { rewrite (Qp.add_comm (1/2)%Qp c) Qp.add_assoc -Hc. apply Qp.half_half. }
    iIntros "Hsl".
    iDestruct (live_slot_none M k HM with "Hsl") as "[Hone Hsel]".
    iMod (live_frac_bump k with "Hone") as (g) "[Hg Hp]".
    iEval (rewrite -Hsum) in "Hg".
    rewrite live_gen_split. iDestruct "Hg" as "[Hq Hg]".
    rewrite live_gen_split. iDestruct "Hg" as "[Hh Hc]".
    iEval (rewrite -Qp.half_half) in "Hsel".
    rewrite frzsel_split. iDestruct "Hsel" as "[Harm Hout]".
    iModIntro. iExists g. iFrame "Hp Hh Hout".
    iSplitL "Hq"; [iExists g; iExact "Hq" |].
    iApply live_slot_of_norm.
    rewrite (live_norm_some (<[k := (q, 1%positive)]> M) k q 1%positive c
               (lookup_insert M k (q, 1%positive))
               (proj2 (Qp.sub_Some (1/2)%Qp q c) Hc)).
    iFrame "Harm". iExists g. iExact "Hc".
  Qed.

  (* iget's cache HIT: the new reference's slice comes out of the ARM, not
     out of any caller -- exactly as its identity fraction comes out of
     [islot_rest].  [qt + qn < 1] is the arm's counterpart of that budget,
     and is why this wrapper's caller has one more side condition than the
     [✓ (qt + qn)] it used to carry. *)
  (* RULING R-e: THE HARDEST MOVER.  The incrementer holds NO live slice of
     its own, so it cannot refute the frozen alternative by mass; what it
     spends instead is the selector's OFF half, which [frz_park_lic_off] (or
     [frz_park_shr_off]) has just handed it out of [islot2]'s live arm.  ONE
     extra in/out premise, no new open, no new mask, no new region contact. *)
  Lemma live_slot_incr M k qt qn (n : positive) :
    M !! k = Some (qt, n) -> (qt + qn < 1/2)%Qp ->
    frzsel k (1/2)%Qp false -∗ live_slot M k -∗
      frzsel k (1/2)%Qp false ∗ live_frac k qn ∗
      live_slot (<[k := ((qt + qn)%Qp, Pos.succ n)]> M) k.
  Proof.
    intros HM Hlt.
    apply Qp.lt_sum in Hlt as [c Hc].
    assert (Hpre : ((1/2)%Qp - qt)%Qp = Some (qn + c)%Qp).
    { apply Qp.sub_Some. by rewrite Hc Qp.add_assoc. }
    iIntros "Hsel Hsl".
    iDestruct (live_slot_norm_of_sel with "Hsel Hsl") as "[$ Hn]".
    rewrite (live_norm_some M k qt n (qn + c)%Qp HM Hpre).
    iDestruct "Hn" as "[Hmass Harm]".
    rewrite live_frac_split. iDestruct "Hmass" as "[$ Hc]".
    iApply live_slot_of_norm.
    rewrite (live_norm_some (<[k := ((qt + qn)%Qp, Pos.succ n)]> M) k
               (qt + qn)%Qp (Pos.succ n) c
               (lookup_insert M k ((qt + qn)%Qp, Pos.succ n))
               (proj2 (Qp.sub_Some (1/2)%Qp (qt + qn) c) Hc)).
    iFrame.
  Qed.

  (* the SAME up-count for a mover that DOES hold a slice (idup's upgrade and
     its licence-free twin): its own share is the weapon, so it needs no
     selector -- [live_slot_norm_of_lv] in place of [live_slot_norm_of_sel]. *)
  Lemma live_slot_incr_lv M k qt qn (s : Qp) (n : positive) :
    M !! k = Some (qt, n) -> (qt + qn < 1/2)%Qp ->
    live_frac k s -∗ live_slot M k -∗
      live_frac k s ∗ live_frac k qn ∗
      live_slot (<[k := ((qt + qn)%Qp, Pos.succ n)]> M) k.
  Proof.
    intros HM Hlt.
    apply Qp.lt_sum in Hlt as [c Hc].
    assert (Hpre : ((1/2)%Qp - qt)%Qp = Some (qn + c)%Qp).
    { apply Qp.sub_Some. by rewrite Hc Qp.add_assoc. }
    iIntros "Hs Hsl".
    iDestruct (live_slot_norm_of_lv with "Hs Hsl") as "[$ Hn]".
    rewrite (live_norm_some M k qt n (qn + c)%Qp HM Hpre).
    iDestruct "Hn" as "[Hmass Harm]".
    rewrite live_frac_split. iDestruct "Hmass" as "[$ Hc]".
    iApply live_slot_of_norm.
    rewrite (live_norm_some (<[k := ((qt + qn)%Qp, Pos.succ n)]> M) k
               (qt + qn)%Qp (Pos.succ n) c
               (lookup_insert M k ((qt + qn)%Qp, Pos.succ n))
               (proj2 (Qp.sub_Some (1/2)%Qp (qt + qn) c) Hc)).
    iFrame.
  Qed.

  (* iput's NON-last close: the departing reference's slice rejoins the arm,
     which is the pool's mirror of the identity fraction rejoining
     [islot_rest]. *)
  Lemma live_slot_close M k q qt qr (n : positive) :
    M !! k = Some (qt, Pos.succ n) -> (qt - q)%Qp = Some qr ->
    live_slot M k -∗ live_frac k q -∗ live_slot (<[k := (qr, n)]> M) k.
  Proof.
    intros HM Hsub. iIntros "Hsl Hq".
    iDestruct (live_slot_some_inv M k qt (Pos.succ n) q HM with "Hsl Hq")
      as (c) "(%Epre & Hc & Harm & Hq)".
    apply Qp.sub_Some in Hsub. apply Qp.sub_Some in Epre.
    assert (Hpost : ((1/2)%Qp - qr)%Qp = Some (q + c)%Qp).
    { apply Qp.sub_Some.
      by rewrite Epre Hsub Qp.add_assoc (Qp.add_comm q qr). }
    iApply live_slot_of_norm.
    rewrite (live_norm_some (<[k := (qr, n)]> M) k qr n (q + c)%Qp
               (lookup_insert M k (qr, n)) Hpost).
    iFrame "Harm". iApply (live_frac_join with "Hq Hc").
  Qed.

  (* iput's LAST close: THE RETIREMENT.  REF-1 says the closer's slice is the
     whole outstanding [qt]; the arm is [1 - qt]; the join is the unit a FREE
     slot's arm holds.  Nothing is counted and nothing is refuted -- had a
     share been outstanding, its own slice could not have coexisted with the
     two halves this lemma consumes.  §14.6, in four lines. *)
  Lemma live_slot_close_last M k (qt : Qp) :
    M !! k = Some (qt, 1%positive) ->
    live_slot M k -∗ frzsel k (1/2)%Qp false -∗
    live_frac k qt -∗ live_frac k (1/2)%Qp -∗
    live_slot (delete k M) k.
  Proof.
    intros HM. iIntros "Hsl Hsel Hq Hh".
    iDestruct (live_slot_some_inv M k qt 1%positive qt HM with "Hsl Hq")
      as (c) "(%Epre & Hc & Harm & Hq)".
    apply Qp.sub_Some in Epre.                (* 1/2 = qt + c *)
    assert (Hsum : (qt + c + (1/2)%Qp)%Qp = 1%Qp).
    { rewrite -Epre. apply Qp.half_half. }
    iDestruct (live_frac_join with "Hq Hc") as "Hqc".
    iDestruct (live_frac_join with "Hqc Hh") as "Hone".
    iEval (rewrite Hsum) in "Hone".
    iDestruct (frzsel_join with "Harm Hsel") as "Hs".
    iEval (rewrite Qp.half_half) in "Hs".
    iApply (live_slot_none_intro (delete k M) k (lookup_delete M k)
              with "Hone Hs").
  Qed.

  (* RULING R-e's FROZEN RETIREMENT (iput+0x8a).  The one count move that runs
     with a freeze HELD consumes NO live slice at all: the mass is already in
     the arm, and what retires the slot is the SELECTOR coming home -- the
     [frz_park]'s ON quarter reclaimed at +0x82 and the escrow tail's, handed
     back by the eviction.  This is where R-e is strictly CHEAPER than the
     landed design: [frz_evict_mass]'s three-way reconciliation is gone. *)
  Lemma live_slot_close_last_frz M k (qt : Qp) :
    M !! k = Some (qt, 1%positive) ->
    live_slot M k -∗ frzsel k (1/2)%Qp true ==∗ live_slot (delete k M) k.
  Proof.
    intros HM. iIntros "Hsl Hsel".
    iDestruct (live_slot_frzn_of_sel with "Hsel Hsl") as "[Hsel Hf]".
    rewrite /live_frzn HM.
    destruct (1/2 - qt)%Qp as [c|] eqn:Epre; [| iDestruct "Hf" as "[]"].
    iDestruct "Hf" as "[Hone Harm]".
    iDestruct (frzsel_join with "Harm Hsel") as "Hs".
    iEval (rewrite Qp.half_half) in "Hs".
    iMod (frzsel_flip k true false with "Hs") as "Hs".
    iModIntro.
    iApply (live_slot_none_intro (delete k M) k (lookup_delete M k)
              with "Hone Hs").
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
    rewrite /itable_half /iref_tok /iref_frag. iIntros "Ha (Hf & _ & _)".
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
    rewrite /itable_half /iref_tok /iref_frag. iIntros (HM) "Ha (Hf & _ & _)".
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
  (* the same at the bare COUNT FRAGMENTS, which is all the proof reads.  An
     opener that meets an escrow arm's reference cannot use the [iref_tok]
     form any more: the arm holds [inode_ref_gen_bare], whose sleeplock slice
     is in the entry's lock rather than in the arm
     (claude-notes/projects/iput-acquiresleep.md). *)
  (* ...and the SAME READ off the bare count fragment (iclaim-ledger.md
     §3.16).  Under A⁗ the free path parks its reference's LIVE slice in
     [islot2]'s frozen park at the mint and carries only the fragment and the
     identity across the window, so at the +0x82 re-acquire it has no
     [iref_tok] to look the map up with -- and it never needed one: the proof
     above reads the fragment alone and ignores the other two conjuncts. *)
  Lemma iref_frag_lookup M k q :
    itable_half M -∗ iref_frag k q -∗
    ⌜∃ (qt : Qp) (n : positive), M !! k = Some (qt, n) /\ (qt ≤ 1)%Qp /\
       (n = 1%positive -> q = qt) /\ (q = qt -> n = 1%positive)⌝.
  Proof.
    rewrite /itable_half /iref_frag. iIntros "Ha Hf".
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

  Lemma iref_frag_two_lookup M k q1 q2 :
    itable_half M -∗ iref_frag k q1 -∗ iref_frag k q2 -∗
    ⌜∃ (qt : Qp) (n : positive), M !! k = Some (qt, n) /\ (2 <= Pos.to_nat n)%nat⌝.
  Proof.
    rewrite /itable_half /iref_frag. iIntros "Ha H1 H2".
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

  Lemma iref_tok_two_lookup M k q1 q2 :
    itable_half M -∗ iref_tok k q1 -∗ iref_tok k q2 -∗
    ⌜∃ (qt : Qp) (n : positive), M !! k = Some (qt, n) /\ (2 <= Pos.to_nat n)%nat⌝.
  Proof.
    rewrite /itable_half /iref_tok /iref_frag. iIntros "Ha (H1 & _ & _) (H2 & _ & _)".
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
    live_gen k (1/2)%Qp g ∗ ity_pending g ∗ frzsel k (1/2)%Qp false.
  Proof.
    iIntros (HM Hq) "Ha Hsl Hisl".
    (* the slot is FREE, so its share authority is the zero; the first
       reference mints the whole outstanding share out of it. *)
    rewrite (isl_slot_none M k HM).
    iMod (slh_mint_none (icfg_isl k) q with "Hisl") as "[Hisl Hshare]".
    assert (Hv : ✓ q).
    { apply frac_valid. etrans; [apply Qp.lt_le_incl; exact Hq | compute_done]. }
    iMod (live_slot_alloc M k q HM Hq with "Hsl") as (g) "(Hlv & Hh & Hp & Hsel & Hsl)".
    iMod (own_update _ _ _ (ic_alloc_upd M k q HM Hv) with "Ha") as "H".
    rewrite own_op. iDestruct "H" as "[Ha Hfr]".
    iModIntro. iExists g. iFrame "Ha Hsl Hh Hp Hsel".
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
    own icfg_iref (● M) -∗ frzsel k (1/2)%Qp false -∗
    live_slot M k -∗ isl_slot M k ==∗
    own icfg_iref (● (<[k := ((qt + qn)%Qp, Pos.succ n)]> M)) ∗
    frzsel k (1/2)%Qp false ∗
    live_slot (<[k := ((qt + qn)%Qp, Pos.succ n)]> M) k ∗
    isl_slot (<[k := ((qt + qn)%Qp, Pos.succ n)]> M) k ∗ iref_tok k qn.
  Proof.
    iIntros (HM Hlt) "Ha Hsel Hsl Hisl".
    rewrite (isl_slot_some M k qt n HM).
    iMod (slh_mint (icfg_isl k) qt qn with "Hisl") as "[Hisl Hshare]".
    assert (Hq : ✓ (qt + qn)%Qp).
    { apply frac_valid. etrans;
        [apply Qp.lt_le_incl; exact Hlt | compute_done]. }
    iDestruct (live_slot_incr M k qt qn n HM Hlt with "Hsel Hsl")
      as "(Hsel & Hlv & Hsl)".
    iMod (own_update _ _ _ (ic_incr_upd M k qt qn n HM Hq) with "Ha") as "H".
    rewrite own_op. iDestruct "H" as "[Ha Hfr]".
    iModIntro. iFrame "Ha Hsel Hsl".
    rewrite (isl_slot_some (<[k := ((qt + qn)%Qp, Pos.succ n)]> M) k
               (qt + qn)%Qp (Pos.succ n)
               (lookup_insert M k ((qt + qn)%Qp, Pos.succ n))).
    iFrame "Hisl".
    rewrite /iref_tok /iref_frag. iFrame.
  Qed.

  (* the share-weaponed twin, for idup's two upgrades *)
  Lemma iref_incr_step_lv M k qt (n : positive) (qn s : Qp) :
    M !! k = Some (qt, n) ->
    (qt + qn < 1/2)%Qp ->
    own icfg_iref (● M) -∗ live_frac k s -∗
    live_slot M k -∗ isl_slot M k ==∗
    own icfg_iref (● (<[k := ((qt + qn)%Qp, Pos.succ n)]> M)) ∗
    live_frac k s ∗
    live_slot (<[k := ((qt + qn)%Qp, Pos.succ n)]> M) k ∗
    isl_slot (<[k := ((qt + qn)%Qp, Pos.succ n)]> M) k ∗ iref_tok k qn.
  Proof.
    iIntros (HM Hlt) "Ha Hs Hsl Hisl".
    rewrite (isl_slot_some M k qt n HM).
    iMod (slh_mint (icfg_isl k) qt qn with "Hisl") as "[Hisl Hshare]".
    assert (Hq : ✓ (qt + qn)%Qp).
    { apply frac_valid. etrans;
        [apply Qp.lt_le_incl; exact Hlt | compute_done]. }
    iDestruct (live_slot_incr_lv M k qt qn s n HM Hlt with "Hs Hsl")
      as "(Hs & Hlv & Hsl)".
    iMod (own_update _ _ _ (ic_incr_upd M k qt qn n HM Hq) with "Ha") as "H".
    rewrite own_op. iDestruct "H" as "[Ha Hfr]".
    iModIntro. iFrame "Ha Hs Hsl".
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
    iIntros (HM) "Ha (Hf & Hlv & Hsh) Hisl".
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
    iIntros (HM Hsub) "Ha (Hf & Hlv & Hsh) Hsl Hisl".
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
    frzsel k (1/2)%Qp false -∗
    live_slot M k -∗ isl_slot M k ==∗
    own icfg_iref (● (delete k M)) ∗ live_slot (delete k M) k ∗
    isl_slot (delete k M) k.
  Proof.
    iIntros (HM) "Ha (Hf & Hlv & Hsh) Hh Hsel Hsl Hisl".
    iDestruct (live_slot_close_last M k qt HM with "Hsl Hsel Hlv Hh") as "Hsl".
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

  (* RULING R-e's FROZEN LAST CLOSE (iput+0x8a, the ONE count move that runs
     inside a freeze window).  It surrenders NO live slice: the dying
     reference's [q] and the escrow arm's ½ have been in the INVARIANT's
     frozen alternative since the mint at +0x50, and what retires the slot is
     the SELECTOR coming home -- the [frz_park] quarter reclaimed at +0x82
     joined with the escrow tail's, which the eviction hands back.  The
     authority's dealloc is [iref_close_last_step]'s verbatim; only the
     liveness half of [iref_tok] is missing, which is why the fragment and
     the sleeplock share arrive spelled out. *)
  Lemma iref_close_last_frz_step M k (qt : Qp) :
    M !! k = Some (qt, 1%positive) ->
    own icfg_iref (● M) -∗ iref_frag k qt -∗ slh_tok (icfg_isl k) qt -∗
    frzsel k (1/2)%Qp true -∗
    live_slot M k -∗ isl_slot M k ==∗
    own icfg_iref (● (delete k M)) ∗ live_slot (delete k M) k ∗
    isl_slot (delete k M) k.
  Proof.
    iIntros (HM) "Ha Hf Hsh Hsel Hsl Hisl".
    iMod (live_slot_close_last_frz M k qt HM with "Hsl Hsel") as "Hsl".
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
       itable_half M ∗ ⌜icM_wf M⌝ ∗ iref_cells M ∗ live_pool M)%I.

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
    iDestruct "Hbody" as (M) "(>Ha & >%Hwf & >Hcells & >Hpool)".
    iDestruct (iref_lookup with "Ha Htok") as %(qt & n & HMk & _ & _ & _).
    assert (Hk : (k < NINODE)%nat) by (apply (proj1 Hwf); by eexists).
    iDestruct (iref_cells_acc M k Hk with "Hcells") as "[Hcell Hback]".
    iModIntro. iExists (iref_word M k). iFrame "Hcell".
    iIntros "Hcell".
    iMod ("Hclose" with "[Ha Hcell Hback Hpool]") as "_".
    { iNext. iExists M. iFrame "Ha". iSplitR; [iPureIntro; exact Hwf|].
      iFrame "Hpool". iApply ("Hback" with "Hcell"). }
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
    iDestruct "Hbody" as (M') "(>Ha & >%Hwf & >Hcells & >Hpool)".
    iDestruct (itable_half_agree with "Ha Hhalf") as %->.
    iDestruct (iref_cells_acc M k Hk with "Hcells") as "[Hcell Hback]".
    iModIntro. iFrame "Hcell". iIntros "Hcell".
    iMod ("Hclose" with "[Ha Hcell Hback Hpool]") as "_".
    { iNext. iExists M. iFrame "Ha". iSplitR; [iPureIntro; exact Hwf|].
      iFrame "Hpool". iApply ("Hback" with "Hcell"). }
    iModIntro. iFrame.
  Qed.

  (* THE TWO INCREMENT WRITES ([iref_dup_store_au], [iref_incr_store_au])
     MOVED to [Section IcacheRefInvReg] at the end of this file: since
     iclaim-ledger.md §2.2 every count move opens the inode REGION as well
     as the itable, and that needs typeclass context this section does not
     carry (and that its other consumers must not be made to carry). *)


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

  (* THE TWO CLOSE WRITES ([iref_close_store_au], [iref_close_last_store_au])
     MOVED to [Section IcacheRefInvReg] at the end of this file -- same
     reason as the two increments above (iclaim-ledger.md §2.2/§2.3). *)


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
    iDestruct "Hbody" as (M) "(>Ha & >%Hwf & >Hcells & >Hpool)".
    iDestruct (live_pool_live_gen M k s g Hk with "Hlv Hpool") as %[[qt n] HMk].
    iDestruct (iref_cells_acc M k Hk with "Hcells") as "[Hcell Hback]".
    iModIntro. iExists (iref_word M k). iFrame "Hcell".
    iIntros "Hcell".
    iMod ("Hclose" with "[Ha Hcell Hback Hpool]") as "_".
    { iNext. iExists M. iFrame "Ha". iSplitR; [iPureIntro; exact Hwf|].
      iFrame "Hpool". iApply ("Hback" with "Hcell"). }
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
    iDestruct "Hbody" as (M) "(>Ha & >%Hwf & >Hcells & >Hpool)".
    iDestruct (live_pool_live M k s Hk with "Hlv Hpool") as %[[qt n] HMk].
    iDestruct (iref_cells_acc M k Hk with "Hcells") as "[Hcell Hback]".
    iModIntro. iExists (iref_word M k). iFrame "Hcell".
    iIntros "Hcell".
    iMod ("Hclose" with "[Ha Hcell Hback Hpool]") as "_".
    { iNext. iExists M. iFrame "Ha". iSplitR; [iPureIntro; exact Hwf|].
      iFrame "Hpool". iApply ("Hback" with "Hcell"). }
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
    iDestruct "Hbody" as (M') "(>Ha & >%Hwf & >_ & >Hpool)".
    iDestruct (itable_half_agree with "Ha Hhalf") as %->.
    assert (Hk : (k < NINODE)%nat) by (apply (proj1 Hwf); by eexists).
    iDestruct (big_sepL_lookup (fun (_ : nat) (j : nat) => live_slot M j)
                 (seq 0 NINODE) k k (seq_ninode_lookup k Hk) with "Hpool") as "Hsl".
    iDestruct (live_slot_some_inv M k qt n qt HMk with "Hsl Hq")
      as (c) "(%Ec & Hc & _ & Hq)".
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
    iDestruct "Hbody" as (M') "(>Ha & >%Hwf & >Hcells & >Hpool)".
    iDestruct (itable_half_agree with "Ha Hhalf") as %->.
    assert (Hk : (k < NINODE)%nat) by (apply (proj1 Hwf); by eexists).
    iDestruct (live_pool_acc_upd M k Hk with "Hpool") as "[Hsl Hback]".
    iDestruct (live_slot_some_inv M k qt n qt HMk with "Hsl Hq")
      as (c) "(%Ec & Hc & Harm & Hq)".
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
    iMod ("Hclose" with "[Ha Hcells Hback Hc' Harm]") as "_".
    { iNext. iExists M. iFrame "Ha". iSplitR; [iPureIntro; exact Hwf|].
      iFrame "Hcells".
      iApply ("Hback" $! M with "[%] [Hc' Harm]").
      - intros j _. reflexivity.
      - iApply live_slot_of_norm.
        rewrite (live_norm_some M k qt n c HMk Ec).
        iFrame "Harm". iExists g'. iExact "Hc'". }
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
    iDestruct "Hbody" as (M') "(>Ha & >%Hwf & >Hcells & >Hpool)".
    iDestruct (itable_half_agree with "Ha Hhalf") as %->.
    iDestruct (live_pool_live M k s Hk with "Hlv Hpool") as %HMk.
    iMod ("Hclose" with "[Ha Hcells Hpool]") as "_".
    { iNext. iExists M. iFrame "Ha Hcells Hpool". iPureIntro. exact Hwf. }
    iModIntro. by iFrame.
  Qed.

  (* THE UPGRADE ([iref_upgrade_store_au]) MOVED to
     [Section IcacheRefInvReg] at the end of this file with the increment
     write it wraps (iclaim-ledger.md §2.2). *)

  (* ------------------------------------------------------------------ *)
  (*  THE FROZEN PARK (iclaim-ledger.md §3.16, RULING A⁗; ZZProbeFrz)     *)
  (* ------------------------------------------------------------------ *)

  (* [IcacheEscrow.islot2]'s LIVE arm carries this disjunction at the arm's
     own table share [q].  Its left alternative is the ordinary state (the
     mirror down, nothing parked); its right one is THE FROZEN PARK, minted
     by [ip_free_entry] at +0x50 under the FIRST itable-lock hold out of the
     freezer's own holdings -- [iref_tok k q] carries [live_frac k q] by
     definition and the payload checkout carries the [1/2] -- and reclaimed
     by the last close at +0x8a.

     WHY AT THE MINT AND NOT LATER, which is the whole of A⁗ over A‴: those
     two slices are NOT idle after +0x5e (the deposit scatters them into the
     escrow's OUT arm, and +0x76 hands the reference back to the freezer's
     hand while the itable lock is not even held).  At +0x50 they are both in
     one hand, so the park is buildable exactly there and nowhere else.

     WHAT IT BUYS: the arm becomes a BRANCH the region's mirror clause
     selects, so (a) the mint decides it LEFT from its own mass with no open
     at all, (b) the +0x8a close decides it RIGHT off [ifreeze_pre], and (c)
     a foreign up-count at a frozen inum inherits [live_whole_share_absurd]'s
     contradiction, which is [ProofIdup]'s OPEN(2.6b). *)
  (* THE PARKED SLICE IS STATED AT [q] FROM BELOW, and that is not slack:
     [islot2]'s live arm re-parks at a MOVED [q] at two of the five count
     movers, and only one of them (the up-count) can pay for a decision.  The
     ordinary close shrinks [q] and rides through by [frz_park_mono]; the mint
     parks at exactly [q = qt], so the bound is tight where 2.6b reads it. *)
  (* ---- RULING R-e: THE PARK IS NOW A MIRROR AND A SELECTOR, NO MASS ----

     A⁗ put the freezer's two live slices HERE, in [IcacheEscrow.islot2]'s
     live arm, i.e. on the ITABLE-LOCK side -- and §5⁗″.2 then found that
     ProofIlock's checkout, which holds no lock, cannot reach them.  R-e moves
     the mass into [live_slot]'s frozen alternative (above), where a
     lock-free reader meets it by opening [itable_inv] alone.  What stays here
     is the MIRROR BIT and the SELECTOR's other half:

       OFF   [frzm_h z false] ∗ [frzsel k ½ false]
       ON    [frzm_h z true ] ∗ [frzsel k (½/2) true]

     and the ON arm's quarter is exactly what the +0x82 reclaim brings home,
     to be joined with the escrow tail's at the +0x8a retirement.

     THE PARK CARRIES NO MASS, so it is indexed by the slot and the inum
     alone -- [islot2]'s live arm re-parks it across every count move with no
     accompanying fraction. *)
  Definition frz_park (k : nat) (z : Z) : iProp Σ :=
    ((frzm_h z false ∗ frzsel k (1/2)%Qp false)
     ∨ (frzm_h z true ∗ frzsel k ((1/2)/2)%Qp true))%I.

  Global Instance frz_park_timeless k z : Timeless (frz_park k z).
  Proof. rewrite /frz_park. apply _. Qed.

  (* a slice at [s] contains one at any [q <= s] *)
  Lemma live_frac_weaken (k : nat) (q s : Qp) :
    (q ≤ s)%Qp -> live_frac k s -∗ live_frac k q.
  Proof.
    intros Hle. iIntros "H".
    apply Qp.le_lteq in Hle. destruct Hle as [Hlt | ->]; [| iExact "H"].
    apply Qp.lt_sum in Hlt as [c ->].
    iDestruct "H" as (g) "H".
    rewrite live_gen_split.
    iDestruct "H" as "[H _]". iExists g. iExact "H".
  Qed.

  (* the mass overflow, kept because the escrow's own openers still name it *)
  Lemma frz_mass_absurd (k : nat) (q : Qp) :
    live_frac k (1/2)%Qp -∗ live_frac k (1/2)%Qp -∗ live_frac k q -∗ False.
  Proof.
    iIntros "Ha Hb Hq".
    iDestruct (live_frac_join with "Ha Hb") as "Hab".
    iEval (rewrite Qp.half_half) in "Hab".
    iApply (live_frac_full_excl with "Hab Hq").
  Qed.

  (* ================================================================== *)
  (*  RULING R-e's TWO NEW MOVES ON [live_slot]'s FROZEN ALTERNATIVE      *)
  (* ================================================================== *)

  (* (a) THE MINT (iput+0x62, [IputFreeLockedDev]:844).  The satisfiability
     witness §5⁗⁗ made binding, and its premises are LITERALLY what the walk
     has in hand at that instant:

       [HMk1]  [Mt !! k = Some (q, 1)]        REF-1, off [iref_lookup]
       [Hhalf] [itable_half Mt]               the itable lock
       [Hlvr]  [live_frac k q]                the dying reference's own slice
       [Hlvh]  [live_frac k (1/2)]            the escrow arm's, out of the
                                              payload checkout
       [Hsel]  [frzsel k (1/2) false]         [frz_park]'s OFF arm, decided at
                                              the +0x3a window-entering read

     and the join happens inside ONE [itable_inv] opening -- the one
     [live_slot_regen] takes four lines earlier -- so nothing about the mask,
     the lock or the order of the walk moves.  What comes out is the two
     quarters: one for [frz_park]'s ON arm, one for the escrow's frozen
     tail. *)
  Lemma frz_slot_freeze (Eo : coPset) (M : gmap nat (Qp * positive))
      (k : nat) (q : Qp) (n : positive) :
    ↑icacheN ⊆ Eo ->
    M !! k = Some (q, n) ->
    itable_inv -∗ itable_half M -∗
    live_frac k q -∗ live_frac k (1/2)%Qp -∗ frzsel k (1/2)%Qp false
    ={Eo}=∗ itable_half M ∗
            frzsel k ((1/2)/2)%Qp true ∗ frzsel k ((1/2)/2)%Qp true.
  Proof.
    iIntros (HE HMk) "#Hinv Hhalf Hq Hh Hsel".
    iMod (inv_acc Eo icacheN with "Hinv") as "[Hbody Hclose]"; [exact HE|].
    iDestruct "Hbody" as (M') "(>Ha & >%Hwf & >Hcells & >Hpool)".
    iDestruct (itable_half_agree with "Ha Hhalf") as %->.
    assert (Hk : (k < NINODE)%nat) by (apply (proj1 Hwf); by eexists).
    iDestruct (live_pool_acc_upd M k Hk with "Hpool") as "[Hsl Hback]".
    iDestruct (live_slot_norm_of_sel with "Hsel Hsl") as "[Hsel Hn]".
    iDestruct (live_norm_some_inv M k q n HMk with "Hn") as (c) "(%Ec & Hc & Harm)".
    pose proof (proj1 (Qp.sub_Some (1/2)%Qp q c) Ec) as Ec'.
    assert (Hsum : (q + c + (1/2)%Qp)%Qp = 1%Qp)
      by (rewrite -Ec'; apply Qp.half_half).
    iDestruct (live_frac_join with "Hq Hc") as "Hqc".
    iDestruct (live_frac_join with "Hqc Hh") as "Hone".
    iEval (rewrite Hsum) in "Hone".
    iDestruct (frzsel_join with "Harm Hsel") as "Hs".
    iEval (rewrite Qp.half_half) in "Hs".
    iMod (frzsel_flip k false true with "Hs") as "Hs".
    iEval (rewrite -Qp.half_half) in "Hs".
    rewrite frzsel_split. iDestruct "Hs" as "[Hsarm Hsout]".
    iDestruct (frzsel_halve with "Hsout") as "[Hs1 Hs2]".
    iMod ("Hclose" with "[Ha Hcells Hback Hone Hsarm]") as "_".
    { iNext. iExists M. iFrame "Ha". iSplitR; [iPureIntro; exact Hwf |].
      iFrame "Hcells".
      iApply ("Hback" $! M with "[%] [Hone Hsarm]");
        [intros j _; reflexivity |].
      iApply live_slot_of_frzn.
      rewrite (live_frzn_some M k q n c HMk Ec). iFrame. }
    iModIntro. iFrame.
  Qed.

  (* (b) THE KILL.  A positive foreign slice against the frozen alternative --
     NO lock, NO licence, NO region open, NO index.  This ONE lemma is
     ProofIlock:2422's discharge (its weapon is the live slice inside the
     deposit [ic_swap_checkout] hands back on the frozen branch) AND
     ProofIdup's decider AND [frz_park_ref1_off]/[frz_park_shr_off]'s new
     engine -- which is exactly R-e's claim: the mass decides everything from
     the invariant, uniformly, at any index flavour. *)
  Lemma frz_slot_kill (Eo : coPset) (k : nat) (qs s' : Qp) :
    ↑icacheN ⊆ Eo -> (k < NINODE)%nat ->
    itable_inv -∗ frzsel k qs true -∗ live_frac k s' ={Eo}=∗ False.
  Proof.
    iIntros (HE Hk) "#Hinv Hsel Hs".
    iMod (inv_acc Eo icacheN with "Hinv") as "[Hbody _]"; [exact HE|].
    iDestruct "Hbody" as (M) "(>Ha & >%Hwf & >Hcells & >Hpool)".
    iDestruct (live_pool_acc_upd M k Hk with "Hpool") as "[Hsl _]".
    iDestruct (live_slot_frzn_of_sel with "Hsel Hsl") as "[_ Hf]".
    rewrite /live_frzn. destruct (M !! k) as [[qt nn]|];
      [| iDestruct "Hf" as "[]"].
    destruct (1/2 - qt)%Qp; [| iDestruct "Hf" as "[]"].
    iDestruct "Hf" as "[Hone _]".
    iDestruct (live_frac_full_excl with "Hone Hs") as "[]".
  Qed.

  (* (c) THE THAW's LOCAL HALF: the escrow tail's quarter, joined with the
     park's, is the ½ [live_slot_close_last_frz] retires the slot with. *)
  Lemma frz_slot_quarters (k : nat) :
    frzsel k ((1/2)/2)%Qp true -∗ frzsel k ((1/2)/2)%Qp true -∗
    frzsel k (1/2)%Qp true.
  Proof. iIntros "H1 H2". iApply (frzsel_quarters with "H1 H2"). Qed.

  (* ---- the park's own moves, at the slimmed shape ---- *)

  (* THE +0x82 RECLAIM (S1b): with the mirror's own [true] half in hand the
     OFF alternative dies on [frzm_agree], and what comes home is the ON arm's
     quarter of the selector -- the mass itself never left the invariant. *)
  Lemma frz_park_reclaim (k : nat) (z : Z) :
    frzm_h z true -∗ frz_park k z -∗
    frzm_h z true ∗ frzsel k ((1/2)/2)%Qp true.
  Proof.
    rewrite /frz_park. iIntros "Hb [[Hoff _] | [_ Hs]]".
    - iDestruct (frzm_agree with "Hb Hoff") as %Hbad. discriminate Hbad.
    - iFrame.
  Qed.

  Lemma frz_park_intro_on (k : nat) (z : Z) :
    frzm_h z true -∗ frzsel k ((1/2)/2)%Qp true -∗ frz_park k z.
  Proof. rewrite /frz_park. iIntros "Hb Hs". iRight. iFrame. Qed.

  Lemma frz_park_intro_off (k : nat) (z : Z) :
    frzm_h z false -∗ frzsel k (1/2)%Qp false -∗ frz_park k z.
  Proof. rewrite /frz_park. iIntros "Hb Hs". iLeft. iFrame. Qed.

  (* THE WINDOW-ENTERING DECIDER AT REF-1 (iput+0x3a) and THE FOREIGN SHARE
     HOLDER's (idup's OPEN(2.6b)) ARE NOW ONE LEMMA, and that is R-e's whole
     point: neither needs REF-1, a licence or the count.  Any positive slice
     kills the ON arm through the INVARIANT ([frz_slot_kill]) -- the arm's own
     quarter says the slot is frozen, and a frozen slot's unit is entire.

     [k < NINODE] is an explicit premise where A⁗'s versions read it off
     [icM_wf] inside their own open; every caller has it from the entry
     address, exactly as [iref_live_load_au]'s callers do. *)
  Lemma frz_park_shr_off (Eo : coPset)
      (k : nat) (z : Z) (s : Qp) :
    ↑icacheN ⊆ Eo -> (k < NINODE)%nat ->
    itable_inv -∗ live_frac k s -∗ frz_park k z ={Eo}=∗
      live_frac k s ∗ frzm_h z false ∗ frzsel k (1/2)%Qp false.
  Proof.
    iIntros (HE Hk) "#Hinv Hs Hpark".
    rewrite /frz_park.
    iDestruct "Hpark" as "[[Hoff Hsel] | [_ Hq]]".
    - iModIntro. iFrame.
    - iMod (frz_slot_kill Eo k ((1/2)/2)%Qp s HE Hk with "Hinv Hq Hs") as "[]".
  Qed.

  Lemma frz_park_ref1_off (Eo : coPset)
      (k : nat) (z : Z) (qt : Qp) :
    ↑icacheN ⊆ Eo -> (k < NINODE)%nat ->
    itable_inv -∗ live_frac k qt -∗ frz_park k z ={Eo}=∗
      live_frac k qt ∗ frzm_h z false ∗ frzsel k (1/2)%Qp false.
  Proof.
    iIntros (HE Hk) "#Hinv Hq Hpark".
    iApply (frz_park_shr_off Eo k z qt HE Hk with "Hinv Hq Hpark").
  Qed.

  (* ZZProbeFrz P5's mass reconciliation, kept for the ORDINARY last close --
     the FROZEN one no longer needs it, the unit never having left the arm. *)
  Lemma frz_evict_mass (k : nat) (q c : Qp) :
    (1/2 - q)%Qp = Some c ->
    live_frac k q -∗ live_frac k (1/2)%Qp -∗ live_frac k c -∗ live_frac k 1%Qp.
  Proof.
    iIntros (Hc) "Hq Hh Hc".
    apply Qp.sub_Some in Hc.
    iDestruct (live_frac_join with "Hq Hc") as "Hqc".
    iDestruct (live_frac_join with "Hh Hqc") as "H".
    rewrite -Hc Qp.half_half. iFrame.
  Qed.

End IcacheRefInv.

(* ===================================================================== *)
(*  5b. THE COUNT MOVES, COUPLED TO THE INODE REGION                      *)
(*      (iclaim-ledger.md §2.2/§2.3, ZZProbeIcnt §2b/§2c)                  *)
(* ===================================================================== *)

(* WHY THESE FIVE LIVE IN THEIR OWN SECTION.  Since §2.2 every count move
   has to reach the [icnt] half that rides in [InodeRegion.ireg_slot], so
   these wrappers -- and only these -- need the region's typeclass context
   ([iregG], [fsLogG], [diskGhostG], [logG]).  Keeping them apart is what
   stops every landed consumer of [iref_load_au] / [iref_share_lookup_au] /
   [live_slot_regen] from gaining four instance premises it has no use for.

   THE MASK, AND WHY IT COSTS NOTHING (§2.9, probed).  Every count move in
   the tree is a [ref]-word store through [WpAu4.wp_sw_au_s_sconf], whose
   outer mask is HARD-CODED at [⊤ ∖ ↑minstretN] and whose hole [Em] is the
   caller's to choose subject to [↑kptN ⊆ Em].  So [↑iregN] is available at
   every site by the store rule's own signature, and no invariant can be held
   open across one of these instructions (the rule concludes a WP at the full
   mask).  The hole widens from [⊤ ∖ ↑minstretN ∖ ↑icacheN] to
   [⊤ ∖ ↑minstretN ∖ ↑icacheN ∖ ↑iregN] and every side condition still goes
   by [solve_ndisj].  The §13.1-style lock-held-auth indirection is NOT
   needed and is strictly worse (probe §2e).

   WHAT THE REGION OPEN HAS TO GIVE BACK is one pure clause,
   [InodeRegion.ireg_frz_ok f m] at the NEW count -- §2.3's phased freeze
   pin.  Three of these five discharge it from a token the mover already has
   to hold, one discharges it from arithmetic, and the fifth STEPS the phase:

     [iref_dup_store_au] / [iref_incr_store_au] / [iref_upgrade_store_au]
       count goes UP, so [FrzPre] (which pins it at one) is not refutable by
       arithmetic and has to be refuted by exclusivity: the mover presents
       the inum's "right to freeze" [ifreeze_off], which pins f at [FrzOff],
       at which the clause is vacuous.  That token is §2.6's currency and it
       comes back out untouched.
     [iref_close_store_au]
       count goes from [Pos.succ n >= 2] DOWN, and both frozen phases pin it
       at one or zero -- so f is [None] or [FrzOff] by arithmetic alone
       ([ireg_frz_ok_ge2]) and the mover needs no token at all.
     [iref_close_last_store_au]
       the 1 -> 0 move, the ONLY one that runs with a freeze possibly HELD
       (iput's free path mints at +0x50 and retires at the deposit, so +0x8a
       is strictly inside the window -- this is exactly what refuted §2.3's
       original strict [icnt = 1] clause).  It threads the freeze token and
       steps its phase [FrzPre -> FrzPost] inside the region open it already
       takes, which re-establishes the pin at zero.  [FrzOff] passes through
       unchanged, which is what lets the ORDINARY last close (ref 1, nlink
       nonzero -- no freeze anywhere) use the same lemma. *)

Section IcacheRefInvReg.
  (* [InodeRegion]'s own context plus [lockG] -- and every one of these
     classes has to be IN SCOPE (see the preamble's import note), or the
     backtick generalisation quietly invents a same-named variable instead. *)
  Context `{!riscvGS Σ, !diskGhostG Σ, !fsLogG Σ, !iregG Σ, !icacheG Σ,
            !logG Σ, !lockG Σ}.
  Context `{ICFG : icfg}.
  Context `{GEN : GenId}.

  (* ------------------------------------------------------------------ *)
  (*  THE PIN's TWO PURE FACTS                                           *)
  (* ------------------------------------------------------------------ *)

  (* AT TWO OR MORE REFERENCES NO FREEZE IS STANDING, so the pin says
     nothing and survives any move of the count.  This is the whole reason
     [iref_close_store_au] needs no token: [FrzPre] pins the count at one
     and [FrzPost] at zero, and the not-last close comes in at
     [Pos.succ n >= 2]. *)
  (* SINCE RULING A the pin is record-parametric, so this is the packaging
     of [InodeRegion.ireg_frz_ok_ge2] (which concludes at the COLUMN) into
     the shape the closer's continuation asks for: the pin at any new count,
     at the same record. *)
  Local Lemma ireg_frz_ok_ge2_any (f : frzUR) (a b : nat) (d : dinode) :
    (2 <= a)%nat -> ireg_frz_ok f a d -> ireg_frz_ok f b d.
  Proof.
    intros Ha Hok.
    exact (ireg_frz_ok_of_off f b d (ireg_frz_ok_ge2 f a d Ha Hok)).
  Qed.

  (* THE PHASE THE LAST CLOSE LEAVES BEHIND (§2.3's [FrzPre -> FrzPost]).
     Identity on the two phases that are not the window's first half, so
     the ordinary (unfrozen) last close threads [FrzOff] through it. *)
  Definition frz_close (ph : frz) : frz :=
    match ph with
    | FrzPre rg => FrzPost rg
    | _ => ph
    end.

  (* RULING G' (iclaim-ledger.md §6''): the close steps the PHASE and leaves
     the regime index exactly where it found it, which is what lets the slot's
     boot-shelter arm ride through the step ([InodeRegion.ireg_fsh_step]). *)
  Lemma frz_close_reg (ph : frz) : frz_reg (frz_close ph) = frz_reg ph.
  Proof. destruct ph; reflexivity. Qed.

  (* ---- THE FREEZE RECEIPT, PHASE-INDEXED (iclaim-ledger.md §3.14 as
     built) ------------------------------------------------------------

     [InodeRegion.ireg_slot] parks [IcacheRef.frzown z] at every phase but
     [FrzPre].  So an accessor that OPENS at [ph] finds the receipt exactly
     when [ph <> FrzPre], and one that CLOSES at [ph'] owes it exactly when
     [ph' <> FrzPre].  These two [match]es are those two facts, written so
     that a mover's signature says nothing at the phases where the receipt
     is not in play -- [emp] is a free argument at every call site that does
     not step through [FrzPre].

     Their sum is the receipt itself ([frz_rcpt_split] below), which is what
     the mint and the [FrzPre -> FrzPost] step trade across. *)
  Definition frz_rcpt (ph : frz) (z : Z) : iProp Σ :=
    match ph with FrzPre _ => emp | _ => frzown z end.

  Definition frz_rcpt_pre (ph : frz) (z : Z) : iProp Σ :=
    match ph with FrzPre _ => frzown z | _ => emp end.

  Global Instance frz_rcpt_timeless ph z : Timeless (frz_rcpt ph z).
  Proof. rewrite /frz_rcpt. destruct ph; apply _. Qed.
  Global Instance frz_rcpt_pre_timeless ph z : Timeless (frz_rcpt_pre ph z).
  Proof. rewrite /frz_rcpt_pre. destruct ph; apply _. Qed.

  Lemma frz_rcpt_split (ph : frz) (z : Z) :
    frz_rcpt ph z -∗ frz_rcpt_pre ph z -∗ frzown z.
  Proof.
    rewrite /frz_rcpt /frz_rcpt_pre.
    destruct ph;
      [ iIntros "H _"; iExact "H"
      | iIntros "_ H"; iExact "H"
      | iIntros "H _"; iExact "H" ].
  Qed.

  (* the slot's clause, read at a KNOWN phase and back again *)
  Lemma frz_rcpt_of_clause (ph : frz) (z : Z) :
    (⌜frz_preb (Some (Excl ph)) = true⌝ ∨ frzown z) -∗ frz_rcpt ph z.
  Proof.
    rewrite /frz_rcpt.
    destruct ph;
      [ iIntros "[%Hc | H]"; [discriminate Hc | iExact "H"]
      | iIntros "_"; done
      | iIntros "[%Hc | H]"; [discriminate Hc | iExact "H"] ].
  Qed.

  (* every phase [frz_close] can produce is one the region parks the receipt
     at, so the last close always OWES it -- and always has it, out of the
     open plus (at [FrzPre]) the caller's own. *)
  Lemma frz_rcpt_close (ph : frz) (z : Z) :
    frzown z -∗ frz_rcpt (frz_close ph) z.
  Proof.
    rewrite /frz_rcpt /frz_close.
    destruct ph; iIntros "H"; iExact "H".
  Qed.

  Lemma frz_rcpt_to_clause (ph : frz) (z : Z) :
    frz_rcpt ph z -∗ (⌜frz_preb (Some (Excl ph)) = true⌝ ∨ frzown z).
  Proof.
    rewrite /frz_rcpt.
    destruct ph;
      [ iIntros "H"; iRight; iExact "H"
      | iIntros "_"; iLeft; iPureIntro; reflexivity
      | iIntros "H"; iRight; iExact "H" ].
  Qed.

  (* ---- THE FREEZE MIRROR, PHASE-INDEXED (iclaim-ledger.md §3.16, A⁗) ---

     [InodeRegion.ireg_frzc] pins the region's mirror half to the column
     ([ireg_frzm_ok]), so a slot at [ph] carries the bit [frz_bit ph].  The
     LOCK's half rides in [IcacheEscrow.islot2]'s live arm, where it selects
     the frozen-park disjunct, and in the free pool's bundle at [false].

     The phase-step accessor below therefore has to TRADE that half at the one
     step where it moves, and at no other -- written in [frz_rcpt]'s own
     "[emp] where the resource is not in play" style, so that every caller
     whose phase is not [FrzPre] passes and receives nothing and its
     signature is unchanged in substance.  The two directions are not
     symmetric because the accessor NEVER MINTS a freeze (that is
     [InodeRegion.ireg_freeze_au]'s, which holds the itable lock AND the
     region open, the only combination [frzm_update] admits): so the half
     comes IN only at [ph = FrzPre] and goes back OUT at the phase the step
     lands on, whatever that is. *)
  Definition frz_bit (ph : frz) : bool :=
    match ph with FrzPre _ => true | _ => false end.

  Definition frz_mir (ph : frz) (z : Z) : iProp Σ :=
    match ph with FrzPre _ => frzm_h z true | _ => emp end.

  Definition frz_mir_back (ph ph' : frz) (z : Z) : iProp Σ :=
    match ph with FrzPre _ => frzm_h z (frz_bit ph') | _ => emp end.

  Global Instance frz_mir_timeless ph z : Timeless (frz_mir ph z).
  Proof. rewrite /frz_mir. destruct ph; apply _. Qed.
  Global Instance frz_mir_back_timeless ph ph' z :
    Timeless (frz_mir_back ph ph' z).
  Proof. rewrite /frz_mir_back. destruct ph; apply _. Qed.

  (* the region's half at the old phase + the caller's trade = the region's
     half at the new phase + the caller's trade back.  ZZProbeFrz P6, at the
     phase-indexed altitude. *)
  Lemma frz_mir_step (ph ph' : frz) (z : Z) :
    (frz_bit ph' = true -> frz_bit ph = true) ->
    frzm_h z (frz_bit ph) -∗ frz_mir ph z ==∗
    frzm_h z (frz_bit ph') ∗ frz_mir_back ph ph' z.
  Proof.
    intros Hmint.
    assert (Hoff : frz_bit ph = false -> frz_bit ph' = false).
    { intros Hne. destruct ph'; cbn [frz_bit]; [reflexivity | | reflexivity].
      exfalso. rewrite (Hmint eq_refl) in Hne. discriminate Hne. }
    destruct ph; cbn [frz_bit frz_mir frz_mir_back].
    - rewrite (Hoff ltac:(reflexivity)). iIntros "Hr _ !>". iFrame.
    - iIntros "Hr Hl".
      iMod (frzm_update z true (frz_bit ph') with "Hr Hl") as "[$ $]". done.
    - rewrite (Hoff ltac:(reflexivity)). iIntros "Hr _ !>". iFrame.
  Qed.

  (* the region's half READ OFF the slot's clause: [ireg_frzm_ok] at a known
     phase IS "[b] is [frz_bit ph]" *)
  Lemma ireg_frzm_ok_bit (b : bool) (ph : frz) :
    ireg_frzm_ok b (Some (Excl ph)) -> b = frz_bit ph.
  Proof. intros ->. destruct ph; reflexivity. Qed.

  (* ------------------------------------------------------------------ *)
  (*  THE REGION's SIDE OF A COUNT MOVE, AS AN ACCESSOR                   *)
  (* ------------------------------------------------------------------ *)

  (* ONE [↑iregN] OPEN, the slot's [icnt] half in, the moved half out.  The
     shape is an accessor rather than an [InodeRegion]-style AU because it
     nests INSIDE the [↑icacheN] opening the count move already does: the
     caller opens the itable, calls this at [Eo ∖ ↑icacheN], hands out the
     [ref] cell, takes it back, moves the itable ghost, then closes the
     REGION first (inner mask first) and the itable after.  That is
     [ZZProbeIcnt.iref_close_last_freeze_store_au]'s choreography verbatim.

     The [f] column comes out EXISTENTIALLY with the pin it currently
     satisfies, and the closing continuation demands the pin at the new
     count.  Nothing else about the slot moves -- the record, the ledger's
     six other columns, the claim pin, both boot-shelter clauses and the
     whole registry/pending arm go back exactly as they came. *)
  Lemma ireg_icnt_acc (E : coPset) (γi : gname) (γfs : fs_names)
      (inodestart : Z) (nib : nat) (inum : bv 32) (n : nat) :
    ↑iregN ⊆ E ->
    bv_unsigned inum < 16 * Z.of_nat nib ->
    ireg_inv γi γfs inodestart nib -∗
    icnt_half (bv_unsigned inum) n
    ={E, E ∖ ↑iregN}=∗
      (* THE SLOT'S RECORD COMES OUT WITH THE COLUMN since RULING A: the pin
         is a fact about BOTH, so the continuation's obligation has to be
         stated at the record the open actually found.  Existential, because
         no count mover knows or cares which record that is -- all three
         discharges below are about the column alone. *)
      ∃ (f : frzUR) (d : dinode),
        ⌜ireg_frz_ok f n d⌝ ∗
        (* RULING R, WIRED (iclaim-ledger.md §5''.3, item 7a-wire).  This
           accessor's ONE caller is iput's non-last close, a DOWN count, so
           it SURRENDERS the closing reference's provenance unit at whichever
           flavour it was minted (no count mover knows or needs to know
           which), and [S m = n] is what makes the surrender exact under
           (R1).  The discharge inside is one line,
           [InodeRegion.ireg_rcol_spend]. *)
        (∀ (m : nat) (bfl : bool), ⌜ireg_frz_ok f m d⌝ -∗ ⌜S m = n⌝ -∗
           runit bfl (bv_unsigned inum) -∗
           |={E ∖ ↑iregN, E}=> icnt_half (bv_unsigned inum) m).
  Proof.
    iIntros (HE Hin) "#Hinv Hhalf".
    pose proof (islot_lt inum) as Hsl.
    assert (Hkey : (16 * Z.of_nat (ireg_bi inum) + Z.of_nat (islot inum))%Z
                   = bv_unsigned inum) by (symmetry; apply ireg_key_split).
    iMod (inv_acc E iregN with "Hinv") as "[Hbody Hclose]"; [exact HE |].
    iDestruct "Hbody" as (mrg) "(>Ha & Hblks & >Hreg)".
    pose proof (ireg_bi_lt inum nib Hin) as Hbi.
    iDestruct (ireg_blks_acc_upd γi γfs inodestart mrg nib (ireg_bi inum) Hbi
                with "Hblks") as "[Hblk Hback]".
    iDestruct "Hblk" as (ds) "(>%Hwf & >%Hcp & >Hfsb & >Hsls)".
    assert (Hlen16 : length ds = 16%nat) by (destruct Hwf as [Hl _]; exact Hl).
    iDestruct (ireg_slots_acc_upd γi (ireg_bi inum) ds (islot inum) Hsl Hlen16
                with "Hsls") as "[Hslot Hslback]".
    iEval (rewrite Hkey) in "Hslot".
    iDestruct "Hslot" as "[(%wl & %wdu & %wdt & %gl & %rl & %cl & %pl & %fz & %cn & Hla & %Hlok & %Hrt & %Hdir & %Hwl0 & %Hpar & #Hdisj & Hcnt & %Hclm & %Hfrz & Hfdisj & Hfrcp & Harm) Hep]".
    iDestruct (icnt_agree with "Hcnt Hhalf") as %->.
    assert (Hins : <[islot inum := ds !!! islot inum]> ds = ds).
    { apply list_insert_id, list_lookup_lookup_total_lt. lia. }
    iModIntro. iExists fz, (ds !!! islot inum).
    iSplitR; [iPureIntro; exact Hfrz |].
    (* RULING R's SPEND: the count goes down by one and the unit the closing
       reference carried goes back into the ledger in the same step. *)
    iIntros (m bfl) "%Hfrz' <- Hu".
    iMod (ireg_rcol_spend bfl (bv_unsigned inum) wl wdu wdt gl cl rl pl fz m
            (ds !!! islot inum) with "Hla Hu") as (rl') "Hla".
    iMod (icnt_update (bv_unsigned inum) _ m with "Hcnt Hhalf") as "[Hcnt Hhalf]".
    iMod ("Hclose" with "[Ha Hreg Hfsb Harm Hla Hep Hslback Hback Hcnt Hfdisj Hfrcp]")
      as "_".
    { iNext. iExists mrg. iFrame "Ha Hreg".
      iApply ("Hback" $! mrg with "[%] [Hfsb Harm Hla Hep Hslback Hcnt Hfdisj Hfrcp]");
        [done |].
      iExists ds. iSplitR; [done |]. iSplitR; [done |].
      iSplitL "Hfsb"; [iExact "Hfsb" |].
      iEval (rewrite -Hins).
      iApply ("Hslback" $! (ds !!! islot inum) with "[Harm Hla Hep Hcnt Hfdisj Hfrcp]").
      rewrite Hkey.
      iApply (ireg_slot_intro γi (bv_unsigned inum) (ds !!! islot inum)
                wl wdu wdt gl cl rl' pl fz m
                Hlok Hrt Hdir Hwl0 Hpar Hclm Hfrz'
                with "Hla Hep Hdisj Hcnt Hfdisj Hfrcp Harm"). }
    iModIntro. iExact "Hhalf".
  Qed.

  (* THE SAME OPEN, WITH THE FREEZE TOKEN IN HAND.  Holding [ifreeze ph]
     pins the f column at [Some (Excl ph)] ([link_freeze_agree]), so the pin
     comes out as a fact about a KNOWN phase and the continuation may also
     STEP that phase ([link_freeze_step], fragment-side -- no new mask).

     The second premise of the continuation is §2.3's boot-shelter clause,
     discharged from what the arm already holds: at [ph' = FrzOff] the
     clause's own left disjunct is free, and at [ph <> FrzOff] the arm's
     left disjunct is contradictory, so its [ireg_open ∨ ireg_boot] is in
     hand and rides straight back.  The one combination it refuses --
     minting a freeze at a slot whose column was [FrzOff] -- is
     [InodeRegion.ireg_freeze_au]'s, which takes the shelter as a premise
     because it has to. *)
  Lemma ireg_icnt_frz_acc (E : coPset) (γi : gname) (γfs : fs_names)
      (inodestart : Z) (nib : nat) (inum : bv 32) (ph : frz) (n : nat) :
    ↑iregN ⊆ E ->
    bv_unsigned inum < 16 * Z.of_nat nib ->
    ireg_inv γi γfs inodestart nib -∗
    ifreeze ph (bv_unsigned inum) -∗
    icnt_half (bv_unsigned inum) n -∗
    (* THE MIRROR's LOCK HALF, IN PLAY ONLY AT [FrzPre] (§3.16).  [emp] at
       the other two phases, so every caller but the free path's last close
       passes nothing. *)
    frz_mir ph (bv_unsigned inum)
    ={E, E ∖ ↑iregN}=∗
      ∃ d : dinode,
      ⌜ireg_frz_ok (Some (Excl ph)) n d⌝ ∗
      (* THE RECEIPT AT THE OLD PHASE comes OUT, and the one at the new
         phase goes back IN (iclaim-ledger.md §3.14 as built).  At every
         mover whose phase does not cross [FrzPre] both are [emp] and the
         signature is unchanged in substance; the mint and the
         [FrzPre -> FrzPost] step are the two that actually trade. *)
      frz_rcpt ph (bv_unsigned inum) ∗
      (∀ (ph' : frz) (m : nat) (bfl : bool),
         ⌜ireg_frz_ok (Some (Excl ph')) m d⌝ -∗
         (* RULING G' (iclaim-ledger.md §6''): STRENGTHENED from
            [ph' = FrzOff \/ ph <> FrzOff] to say that a step which stays in
            the window keeps the REGIME INDEX it found.  Every caller in the
            tree steps by [frz_close], which does exactly that
            ([frz_close_reg]); and at [ph = FrzOff] the clause still forces
            [ph' = FrzOff], so the old reading is recovered verbatim.  It is
            what lets the slot's boot-shelter arm ride the step. *)
         ⌜ph' = FrzOff \/ frz_reg ph' = frz_reg ph⌝ -∗
         (* RULING R, WIRED (§5''.3): this accessor is iput's LAST close --
            a DOWN count -- so the dying reference's provenance unit is
            surrendered in the same step, at whatever flavour it was
            minted, and [S m = n] makes the surrender exact under (R1). *)
         ⌜S m = n⌝ -∗
         runit bfl (bv_unsigned inum) -∗
         (* THIS ACCESSOR NEVER MINTS A FREEZE (§3.16).  The clause above
            already refuses [FrzOff -> anything but FrzOff]; this one refuses
            the remaining entry into the window, [FrzPost -> FrzPre], which
            nothing in the tree performs and which the mirror could not pay
            for (the caller would have to hand in a [false] half it does not
            hold).  Minting is [InodeRegion.ireg_freeze_au]'s, alone. *)
         ⌜frz_bit ph' = true -> frz_bit ph = true⌝ -∗
         frz_rcpt ph' (bv_unsigned inum) -∗
         |={E ∖ ↑iregN, E}=>
           ifreeze ph' (bv_unsigned inum) ∗ icnt_half (bv_unsigned inum) m ∗
           frz_mir_back ph ph' (bv_unsigned inum)).
  Proof.
    iIntros (HE Hin) "#Hinv Hfz Hhalf Hmir".
    pose proof (islot_lt inum) as Hsl.
    assert (Hkey : (16 * Z.of_nat (ireg_bi inum) + Z.of_nat (islot inum))%Z
                   = bv_unsigned inum) by (symmetry; apply ireg_key_split).
    iMod (inv_acc E iregN with "Hinv") as "[Hbody Hclose]"; [exact HE |].
    iDestruct "Hbody" as (mrg) "(>Ha & Hblks & >Hreg)".
    pose proof (ireg_bi_lt inum nib Hin) as Hbi.
    iDestruct (ireg_blks_acc_upd γi γfs inodestart mrg nib (ireg_bi inum) Hbi
                with "Hblks") as "[Hblk Hback]".
    iDestruct "Hblk" as (ds) "(>%Hwf & >%Hcp & >Hfsb & >Hsls)".
    assert (Hlen16 : length ds = 16%nat) by (destruct Hwf as [Hl _]; exact Hl).
    iDestruct (ireg_slots_acc_upd γi (ireg_bi inum) ds (islot inum) Hsl Hlen16
                with "Hsls") as "[Hslot Hslback]".
    iEval (rewrite Hkey) in "Hslot".
    iDestruct "Hslot" as "[(%wl & %wdu & %wdt & %gl & %rl & %cl & %pl & %fz & %cn & Hla & %Hlok & %Hrt & %Hdir & %Hwl0 & %Hpar & #Hdisj & Hcnt & %Hclm & %Hfrz & Hfdisj & Hfrcp & Harm) Hep]".
    iDestruct (ireg_rcol_freeze_agree with "Hla Hfz") as %->.
    iDestruct (icnt_agree with "Hcnt Hhalf") as %->.
    assert (Hins : <[islot inum := ds !!! islot inum]> ds = ds).
    { apply list_insert_id, list_lookup_lookup_total_lt. lia. }
    (* THE CONJUNCT SPLITS INTO ITS TWO HANDLES (§3.16): the receipt, which
       §3.14's [frz_rcpt] pair trades, and the mirror half, which the clause
       pins to [frz_bit ph]. *)
    iDestruct "Hfrcp" as "[Hfrcp Hmr]".
    iDestruct "Hmr" as (b0) "[Hmr %Hmok]".
    rewrite (ireg_frzm_ok_bit b0 ph Hmok).
    iModIntro. iExists (ds !!! islot inum).
    iSplitR; [iPureIntro; exact Hfrz |].
    iSplitL "Hfrcp"; [iApply (frz_rcpt_of_clause with "Hfrcp") |].
    iIntros (ph' m bfl) "%Hfrz' %Hsh <- Hu %Hmint Hfrcp".
    iDestruct (frz_rcpt_to_clause ph' (bv_unsigned inum) with "Hfrcp") as "Hfrcp".
    iMod (frz_mir_step ph ph' (bv_unsigned inum) Hmint with "Hmr Hmir")
      as "[Hmr Hmir]".
    assert (Hmok' : ireg_frzm_ok (frz_bit ph') (Some (Excl ph'))).
    { destruct ph' as [| rg' | rg']; reflexivity. }
    iMod (icnt_update (bv_unsigned inum) _ m with "Hcnt Hhalf") as "[Hcnt Hhalf]".
    (* RULING R, WIRED: the phase step moves the f column, and the count goes
       DOWN by one, so the closing reference's unit is spent in the same
       breath ([InodeRegion.ireg_rcol_spend]).  The SPEND runs at the OLD
       phase column and the freeze step at the new one; they commute, so the
       order here is only a matter of which peel is cheaper. *)
    iMod (ireg_rcol_spend bfl (bv_unsigned inum) wl wdu wdt gl cl rl pl
            (Some (Excl ph)) m (ds !!! islot inum) with "Hla Hu")
      as (rl') "Hla".
    iDestruct "Hla" as (rcl) "[Hla %Href]".
    iMod (link_freeze_step _ _ _ _ _ _ _ _ ph ph' with "Hla Hfz") as "[Hla Hfz]".
    iDestruct (ireg_rcol_intro (bv_unsigned inum) wl wdu wdt gl cl rl' pl
                 (Some (Excl ph')) m rcl (ds !!! islot inum) Href with "Hla")
      as "Hla".
    (* THE CLAIM CLAUSE ACROSS A PHASE STEP (RULING A's new conjunct), and
       it is SELF-REFUTING: a claimed slot's column already reads [FrzOff],
       so the only phase step that can happen at [c = Some] is the identity
       one -- [Hsh]'s own disjunction then forces the new phase to [FrzOff]
       too, and the clause carries.  A mover therefore never has to know
       whether it is at a claim box. *)
    assert (Hclm' : ireg_claim_ok cl (Some (Excl ph')) (ds !!! islot inum)).
    { destruct cl as [x |]; [| exact I].
      destruct Hclm as [Hfs [Hoff Hty]].
      assert (Hph : ph = FrzOff) by (by simplify_eq).
      assert (Hp' : ph' = FrzOff).
      { destruct Hsh as [Hp' | Hr]; [exact Hp' |].
        rewrite Hph in Hr. cbn in Hr.
        destruct ph' as [| rg' | rg']; [reflexivity | discriminate Hr
                                       | discriminate Hr]. }
      rewrite Hp'. split_and!; [exact Hfs | reflexivity | exact Hty]. }
    iAssert (ireg_fsh (Some (Excl ph')))%I with "[Hfdisj]" as "Hfdisj'".
    { iApply (ireg_fsh_step ph ph' Hsh with "Hfdisj"). }
    iMod ("Hclose" with "[Ha Hreg Hfsb Harm Hla Hep Hslback Hback Hcnt Hfdisj' Hfrcp Hmr]")
      as "_".
    { iNext. iExists mrg. iFrame "Ha Hreg".
      iApply ("Hback" $! mrg with "[%] [Hfsb Harm Hla Hep Hslback Hcnt Hfdisj' Hfrcp Hmr]");
        [done |].
      iExists ds. iSplitR; [done |]. iSplitR; [done |].
      iSplitL "Hfsb"; [iExact "Hfsb" |].
      iEval (rewrite -Hins).
      iApply ("Hslback" $! (ds !!! islot inum) with "[Harm Hla Hep Hcnt Hfdisj' Hfrcp Hmr]").
      rewrite Hkey.
      iApply (ireg_slot_intro γi (bv_unsigned inum) (ds !!! islot inum)
                wl wdu wdt gl cl rl' pl (Some (Excl ph')) m
                Hlok Hrt Hdir Hwl0 Hpar Hclm' Hfrz'
                with "Hla Hep Hdisj Hcnt Hfdisj' [Hfrcp Hmr] Harm").
      iApply (ireg_frzc_intro _ _ (frz_bit ph') Hmok' with "Hfrcp Hmr"). }
    iModIntro. iFrame "Hfz Hhalf Hmir".
  Qed.

  (* THE SAME OPEN, WITH A LICENCE IN HAND -- and this is the shape the
     UP-COUNTS take since RULING A (iclaim-ledger.md §3.1, A-custody +
     A-AUs).

     WHY THEY CANNOT TAKE THE TOKEN.  Increment II gave the three
     incrementers an [ifreeze_off] premise, on the theory that the unfrozen
     token rides under the itable lock beside the [icnt] half.  IIIb proved
     that false in both directions: a CACHED inum has no freeze token
     anywhere in the tree (Consequence 2), and the custody ruling then put
     the token in the PAYLOAD holder's hand -- which at an increment is the
     freezer's hand, not the incrementer's.  An [iget] cache-hit at an inum
     iput is freeing must be REFUTED, not served, so it cannot be asked to
     produce the very token that refutation would require.

     WHAT THEY TAKE INSTEAD is the licence [SpecIget] already demands: every
     iget in the tree presents one ([IgetLic.iname]), and §2.6's table --
     now [IgetLic.iname_not_frozen] -- turns any of the five into
     [f = FrzOff] with the region open.  Borrowed and handed straight back,
     like every other reading of a licence.  At [FrzOff] the pin is vacuous
     at ANY new count, so the continuation carries no obligation at all --
     which is why this accessor's wand, unlike the two above, takes nothing
     but the count. *)
  Lemma ireg_icnt_lic_acc (E : coPset) (γi : gname) (γfs : fs_names)
      (inodestart : Z) (nib : nat) (inum : bv 32) (l : ilic) (n : nat) :
    ↑iregN ⊆ E ->
    bv_unsigned inum < 16 * Z.of_nat nib ->
    ireg_inv γi γfs inodestart nib -∗
    iname γi γfs inodestart inum l -∗
    icnt_half (bv_unsigned inum) n
    ={E, E ∖ ↑iregN}=∗
      iname γi γfs inodestart inum l ∗
      (* THE MINT.  Both callers of this accessor are UP-counts by exactly
         one, and the unit they mint is FLAVOURED by the licence presented:
         ialloc's own [ClaimL] iget mints [runit_claim] into its own claim
         box, every other iget mints [runit_plain].  That is what keeps (R3)
         -- "no plainly-licenced reference to a claim box" -- true. *)
      (∀ m : nat, ⌜m = S n⌝ -∗
         |={E ∖ ↑iregN, E}=>
           icnt_half (bv_unsigned inum) m ∗
           runit (is_claim l) (bv_unsigned inum)).
  Proof.
    iIntros (HE Hin) "#Hinv Hl Hhalf".
    pose proof (islot_lt inum) as Hsl.
    assert (Hkey : (16 * Z.of_nat (ireg_bi inum) + Z.of_nat (islot inum))%Z
                   = bv_unsigned inum) by (symmetry; apply ireg_key_split).
    iMod (inv_acc E iregN with "Hinv") as "[Hbody Hclose]"; [exact HE |].
    iDestruct "Hbody" as (mrg) "(>Ha & Hblks & >Hreg)".
    pose proof (ireg_bi_lt inum nib Hin) as Hbi.
    iDestruct (ireg_blks_acc_upd γi γfs inodestart mrg nib (ireg_bi inum) Hbi
                with "Hblks") as "[Hblk Hback]".
    iDestruct "Hblk" as (ds) "(>%Hwf & >%Hcp & >Hfsb & >Hsls)".
    assert (Hlen16 : length ds = 16%nat) by (destruct Hwf as [Hl _]; exact Hl).
    iDestruct (ireg_slots_acc_upd γi (ireg_bi inum) ds (islot inum) Hsl Hlen16
                with "Hsls") as "[Hslot Hslback]".
    iEval (rewrite Hkey) in "Hslot".
    iDestruct "Hslot" as "[(%wl & %wdu & %wdt & %gl & %rl & %cl & %pl & %fz & %cn & Hla & %Hlok & %Hrt & %Hdir & %Hwl0 & %Hpar & #Hdisj & Hcnt & %Hclm & %Hfrz & Hfdisj & Hfrcp & Harm) Hep]".
    iDestruct (icnt_agree with "Hcnt Hhalf") as %->.
    (* the coupling names the region's record at this inum, which is what
       ties the licence's fragment-level facts to the slot's clauses *)
    pose proof (Hcp (islot inum) Hsl) as Hmd.
    rewrite -ireg_key_split in Hmd.
    (* §2.6's TABLE, at whichever licence the caller presented *)
    iDestruct (iname_not_frozen γi γfs inodestart inum l (ds !!! islot inum) mrg
                 wl wdu wdt gl rl cl pl fz n Hlok Hrt Hclm Hfrz Hmd
                 with "Ha Hla Hfdisj Hl") as %Hfz0.
    (* THE MINT's TABLE (§5', RULING R): the same five rows, read for the
       two side conditions [InodeRegion.ireg_ref_ok_mint] owes -- the box is
       ALLOCATED, and at any non-[ClaimL] licence it is UNCLAIMED.  The
       block half comes in because the [BufL] row transports a decoded type
       fact and this accessor already holds [↑iregN] open. *)
    iEval (rewrite -(ireg_bi_iblock inum inodestart)) in "Hfsb".
    iDestruct (iname_mint_ok γi γfs inodestart inum l ds mrg
                 wl wdu wdt gl rl cl pl fz n Hwf Hlok Hrt Hclm Hmd
                 with "Ha Hla Hfsb Hdisj Hl") as %[Hty0 Hcl0].
    iEval (rewrite (ireg_bi_iblock inum inodestart)) in "Hfsb".
    assert (Hins : <[islot inum := ds !!! islot inum]> ds = ds).
    { apply list_insert_id, list_lookup_lookup_total_lt. lia. }
    iModIntro. iFrame "Hl".
    iIntros (m) "->".
    iMod (ireg_rcol_mint (is_claim l) (bv_unsigned inum) wl wdu wdt gl cl rl pl
            fz n (ds !!! islot inum) Hty0 Hcl0 with "Hla") as "[(%rl' & Hla) Hu]".
    iMod (icnt_update (bv_unsigned inum) n (S n) with "Hcnt Hhalf")
      as "[Hcnt Hhalf]".
    iMod ("Hclose" with "[Ha Hreg Hfsb Harm Hla Hep Hslback Hback Hcnt Hfdisj Hfrcp]")
      as "_".
    { iNext. iExists mrg. iFrame "Ha Hreg".
      iApply ("Hback" $! mrg with "[%] [Hfsb Harm Hla Hep Hslback Hcnt Hfdisj Hfrcp]");
        [done |].
      iExists ds. iSplitR; [done |]. iSplitR; [done |].
      iSplitL "Hfsb"; [iExact "Hfsb" |].
      iEval (rewrite -Hins).
      iApply ("Hslback" $! (ds !!! islot inum) with "[Harm Hla Hep Hcnt Hfdisj Hfrcp]").
      rewrite Hkey.
      iApply (ireg_slot_intro γi (bv_unsigned inum) (ds !!! islot inum)
                wl wdu wdt gl cl rl' pl fz (S n)
                Hlok Hrt Hdir Hwl0 Hpar Hclm
                (ireg_frz_ok_of_off fz (S n) (ds !!! islot inum) Hfz0)
                with "Hla Hep Hdisj Hcnt Hfdisj Hfrcp Harm"). }
    iModIntro. iFrame "Hhalf Hu".
  Qed.

  (* B1's PIN READ, in one line (iclaim-ledger.md §3.16, the +0x82 seam).

     The reordered iput releases the itable lock at +0x66 and re-acquires it
     at +0x82, so the REF-1 fact its caller supplied is about the OLD map and
     [islot2]'s live arm hands back a count [cnt2] about the NEW one.  IVa
     recorded that nothing in the held resources forces [cnt2 = 1] -- and
     nothing did, until the MINT put a freeze on the column that spans the
     whole release/re-acquire.  With it standing, the region's own pin
     ([InodeRegion.ireg_frz_ok] at [FrzPre]) IS that fact, and the
     non-last-close arm at +0x8a is refuted rather than admitted.  This is
     what retires the first of [IputFreeLockedDev]'s two admits. *)
  Lemma icnt_freeze_forces_one (E : coPset) (γi : gname) (γfs : fs_names)
      (inodestart : Z) (nib : nat) (inum : bv 32) (n : nat) (rg : bool) :
    ↑iregN ⊆ E ->
    bv_unsigned inum < 16 * Z.of_nat nib ->
    ireg_inv γi γfs inodestart nib -∗
    ifreeze_pre rg (bv_unsigned inum) -∗
    icnt_half (bv_unsigned inum) n ={E}=∗
      ⌜n = 1%nat⌝ ∗ ifreeze_pre rg (bv_unsigned inum) ∗
      icnt_half (bv_unsigned inum) n.
  Proof.
    iIntros (HE Hin) "#Hinv Hpre Hcnt". rewrite /ifreeze_pre.
    iMod (ireg_frz_pin_read E γi γfs inodestart nib inum (FrzPre rg) n HE Hin
            with "Hinv Hpre Hcnt") as "((%d & %Hpin) & Hpre & Hcnt)".
    iModIntro. iFrame "Hpre Hcnt". iPureIntro.
    rewrite /ireg_frz_ok in Hpin. destruct Hpin as (_ & _ & Hn). exact Hn.
  Qed.

  (* THE +0x82 RECLAIM (S1b, iclaim-ledger.md §3.16 / ZZProbeFrz P3).  The
     freezer re-takes the itable lock and peels [islot2]'s live arm; the
     [ifreeze_pre] it has kept in hand since the mint fixes the column at the
     region ([InodeRegion.ireg_frzm_read]), so the arm's ORDINARY alternative
     -- the mirror bit DOWN -- is refuted outright, and what comes back is the
     mint's own two live slices: the dying reference's [q] and the escrow
     arm's [1/2].  Together with the invariant's retained [1/2 - q] they are
     the WHOLE unit the last close surrenders ([frz_evict_mass]). *)
  Lemma frz_park_pre_reclaim (E : coPset) (γi : gname) (γfs : fs_names)
      (inodestart : Z) (nib : nat) (inum : bv 32) (k : nat)
      (rg : bool) :
    ↑iregN ⊆ E ->
    bv_unsigned inum < 16 * Z.of_nat nib ->
    ireg_inv γi γfs inodestart nib -∗
    ifreeze_pre rg (bv_unsigned inum) -∗
    frz_park k (bv_unsigned inum) ={E}=∗
      ifreeze_pre rg (bv_unsigned inum) ∗ frzm_h (bv_unsigned inum) true ∗
      (* RULING R-e: the MASS never left [live_slot]'s frozen alternative, so
         what comes home here is the park's QUARTER of the selector -- to be
         joined with the escrow tail's at the +0x8a retirement. *)
      frzsel k ((1/2)/2)%Qp true.
  Proof.
    iIntros (HE Hin) "#Hinv Hpre Hpark". rewrite /frz_park.
    iDestruct "Hpark" as "[[Hbf _] | [Hbt Hs]]".
    - rewrite /ifreeze_pre.
      iMod (ireg_frzm_read E γi γfs inodestart nib inum (FrzPre rg) false HE Hin
              with "Hinv Hpre Hbf") as "(%Hiff & _ & _)".
      discriminate Hiff.
    - iModIntro. iFrame.
  Qed.

  (* THE PARK, DECIDED FROM A LICENCE (iclaim-ledger.md §3.16).  Two of the
     five count movers re-park [islot2]'s live arm across a count move, and
     the UP-COUNT cannot re-establish the arm on its own.  What pays there is
     the licence the up-count already
     carries: §2.6's table puts the column at [FrzOff] ([iname_not_frozen]),
     the region's mirror bit is therefore DOWN, and the arm's FROZEN
     alternative dies on [frzm_agree].  A standalone read -- nothing moves,
     no count is touched -- so not one mover's signature changes for it. *)
  Lemma frz_park_lic_off (E : coPset) (γi : gname) (γfs : fs_names)
      (inodestart : Z) (nib : nat) (inum : bv 32) (l : ilic)
      (k : nat) :
    ↑iregN ⊆ E ->
    bv_unsigned inum < 16 * Z.of_nat nib ->
    ireg_inv γi γfs inodestart nib -∗
    iname γi γfs inodestart inum l -∗
    frz_park k (bv_unsigned inum) ={E}=∗
      iname γi γfs inodestart inum l ∗ frzm_h (bv_unsigned inum) false ∗
      (* RULING R-e: the OFF arm's SELECTOR half comes out beside the mirror
         bit, and it is what [iref_incr_store_au] spends to refute
         [live_slot]'s frozen alternative. *)
      frzsel k (1/2)%Qp false.
  Proof.
    iIntros (HE Hin) "#Hinv Hl Hpark".
    pose proof (islot_lt inum) as Hsl.
    assert (Hkey : (16 * Z.of_nat (ireg_bi inum) + Z.of_nat (islot inum))%Z
                   = bv_unsigned inum) by (symmetry; apply ireg_key_split).
    iMod (inv_acc E iregN with "Hinv") as "[Hbody Hclose]"; [exact HE |].
    iDestruct "Hbody" as (mrg) "(>Ha & Hblks & >Hreg)".
    pose proof (ireg_bi_lt inum nib Hin) as Hbi.
    iDestruct (ireg_blks_acc_upd γi γfs inodestart mrg nib (ireg_bi inum) Hbi
                with "Hblks") as "[Hblk Hback]".
    iDestruct "Hblk" as (ds) "(>%Hwf & >%Hcp & >Hfsb & >Hsls)".
    assert (Hlen16 : length ds = 16%nat) by (destruct Hwf as [Hl _]; exact Hl).
    iDestruct (ireg_slots_acc_upd γi (ireg_bi inum) ds (islot inum) Hsl Hlen16
                with "Hsls") as "[Hslot Hslback]".
    iEval (rewrite Hkey) in "Hslot".
    iDestruct "Hslot" as "[(%wl & %wdu & %wdt & %gl & %rl & %cl & %pl & %fz & %cn & Hla & %Hlok & %Hrt & %Hdir & %Hwl0 & %Hpar & #Hdisj & Hcnt & %Hclm & %Hfrz & Hfdisj & Hfrcp & Harm) Hep]".
    pose proof (Hcp (islot inum) Hsl) as Hmd.
    rewrite -ireg_key_split in Hmd.
    iDestruct (iname_not_frozen γi γfs inodestart inum l (ds !!! islot inum) mrg
                 wl wdu wdt gl rl cl pl fz cn Hlok Hrt Hclm Hfrz Hmd
                 with "Ha Hla Hfdisj Hl") as %Hfz0.
    iDestruct "Hfrcp" as "[Hrc Hmr]".
    iDestruct "Hmr" as (b0) "[Hmr %Hmok]".
    assert (Hb0 : b0 = false).
    { rewrite /ireg_frzm_ok Hfz0 in Hmok. exact Hmok. }
    subst b0.
    iAssert (frzm_h (bv_unsigned inum) false ∗ frzm_h (bv_unsigned inum) false ∗
             frzsel k (1/2)%Qp false)%I
      with "[Hmr Hpark]" as "(Hmr & Hout & Hsel)".
    { rewrite /frz_park.
      iDestruct "Hpark" as "[[Ho Hs] | [Hbt _]]"; last first.
      { iDestruct (frzm_agree with "Hmr Hbt") as %Hbad. discriminate Hbad. }
      iFrame "Hmr Ho Hs". }
    assert (Hins : <[islot inum := ds !!! islot inum]> ds = ds).
    { apply list_insert_id, list_lookup_lookup_total_lt. lia. }
    iMod ("Hclose" with "[Ha Hreg Hfsb Harm Hla Hep Hslback Hback Hcnt Hfdisj Hrc Hmr]")
      as "_".
    { iNext. iExists mrg. iFrame "Ha Hreg".
      iApply ("Hback" $! mrg with "[%] [Hfsb Harm Hla Hep Hslback Hcnt Hfdisj Hrc Hmr]");
        [done |].
      iExists ds. iSplitR; [done |]. iSplitR; [done |].
      iSplitL "Hfsb"; [iExact "Hfsb" |].
      iEval (rewrite -Hins).
      iApply ("Hslback" $! (ds !!! islot inum) with "[Harm Hla Hep Hcnt Hfdisj Hrc Hmr]").
      rewrite Hkey.
      iApply (ireg_slot_intro γi (bv_unsigned inum) (ds !!! islot inum)
                wl wdu wdt gl cl rl pl fz cn
                Hlok Hrt Hdir Hwl0 Hpar Hclm Hfrz
                with "Hla Hep Hdisj Hcnt Hfdisj [Hrc Hmr] Harm").
      iApply (ireg_frzc_intro _ _ false Hmok with "Hrc Hmr"). }
    iModIntro. iFrame "Hl Hout Hsel".
  Qed.

  (* THE SAME OPEN, WITH THE MIRROR's [false] HALF IN HAND -- the
     LICENCE-FREE up-count RULING A⁗ buys (iclaim-ledger.md §3.16, closing
     §3.11's OPEN(2.6b)).

     §3.11's wall was that idup's two call sites are both [idup(p->cwd)] and
     a cwd holder can present no licence at any of the five constructors (xv6
     permits unlinking a process's cwd, so it is not even [nlink <> 0]), while
     the arithmetic route needs [2 <= n] and a cwd held by one process sits at
     exactly the count [FrzPre] admits.

     A⁗'s answer is neither: the mover presents the LOCK's own mirror half,
     which it peels out of [IcacheEscrow.islot2]'s live arm and which it can
     only have at [false] (the [true] alternative carries the freezer's parked
     live mass, and that is what collides with the mover's own share -- see
     [iref_upgrade_park_store_au], which does that half of the case split
     OUTSIDE this open).  At [false] the column is not [FrzPre]; the live
     arm's count is one or more, so [FrzPost]'s pin is refuted too; and
     [FrzOff]'s pin is vacuous at any new count, so the continuation carries
     no obligation -- exactly [ireg_icnt_lic_acc]'s shape, with the licence
     swapped for a resource a cwd holder actually has. *)
  Lemma ireg_icnt_mir_acc (E : coPset) (γi : gname) (γfs : fs_names)
      (inodestart : Z) (nib : nat) (inum : bv 32) (bfl : bool) (n : nat) :
    ↑iregN ⊆ E ->
    bv_unsigned inum < 16 * Z.of_nat nib ->
    (1 <= n)%nat ->
    ireg_inv γi γfs inodestart nib -∗
    frzm_h (bv_unsigned inum) false -∗
    icnt_half (bv_unsigned inum) n
    ={E, E ∖ ↑iregN}=∗
      frzm_h (bv_unsigned inum) false ∗
      (* RULING R, WIRED (§5''.3's step 4): idup's mint is SELF-PAYING.  The
         mover hands in the PARENT reference's own provenance unit, which
         gives allocatedness at either flavour ([ireg_rcol_alloc]) and, at
         the plain flavour, [c = None] ([ireg_rcol_unclaimed]); no licence,
         no table.  The copy is minted at the PARENT's flavour -- that is
         what "idup copies the flavour" means, and it is what keeps (R3)
         true: a dup of a claim reference is claim-flavoured, so no plain
         unit is ever created at a claim box. *)
      (∀ m : nat, ⌜m = S n⌝ -∗ runit bfl (bv_unsigned inum) -∗
         |={E ∖ ↑iregN, E}=>
           icnt_half (bv_unsigned inum) m ∗
           runit bfl (bv_unsigned inum) ∗ runit bfl (bv_unsigned inum)).
  Proof.
    iIntros (HE Hin Hn) "#Hinv Hmir Hhalf".
    pose proof (islot_lt inum) as Hsl.
    assert (Hkey : (16 * Z.of_nat (ireg_bi inum) + Z.of_nat (islot inum))%Z
                   = bv_unsigned inum) by (symmetry; apply ireg_key_split).
    iMod (inv_acc E iregN with "Hinv") as "[Hbody Hclose]"; [exact HE |].
    iDestruct "Hbody" as (mrg) "(>Ha & Hblks & >Hreg)".
    pose proof (ireg_bi_lt inum nib Hin) as Hbi.
    iDestruct (ireg_blks_acc_upd γi γfs inodestart mrg nib (ireg_bi inum) Hbi
                with "Hblks") as "[Hblk Hback]".
    iDestruct "Hblk" as (ds) "(>%Hwf & >%Hcp & >Hfsb & >Hsls)".
    assert (Hlen16 : length ds = 16%nat) by (destruct Hwf as [Hl _]; exact Hl).
    iDestruct (ireg_slots_acc_upd γi (ireg_bi inum) ds (islot inum) Hsl Hlen16
                with "Hsls") as "[Hslot Hslback]".
    iEval (rewrite Hkey) in "Hslot".
    iDestruct "Hslot" as "[(%wl & %wdu & %wdt & %gl & %rl & %cl & %pl & %fz & %cn & Hla & %Hlok & %Hrt & %Hdir & %Hwl0 & %Hpar & #Hdisj & Hcnt & %Hclm & %Hfrz & Hfdisj & Hfrcp & Harm) Hep]".
    iDestruct (icnt_agree with "Hcnt Hhalf") as %->.
    iDestruct "Hfrcp" as "[Hrc Hmr]".
    iDestruct "Hmr" as (b0) "[Hmr %Hmok]".
    iDestruct (frzm_agree with "Hmr Hmir") as %->.
    assert (Hnpre : frz_preb fz = false).
    { destruct (frz_preb fz) eqn:Hb; [| reflexivity].
      rewrite /ireg_frzm_ok Hb in Hmok. discriminate Hmok. }
    assert (Hfz0 : fz = Some (Excl FrzOff))
      by exact (ireg_frz_ok_not_pre fz n (ds !!! islot inum) Hn Hnpre Hfrz).
    assert (Hins : <[islot inum := ds !!! islot inum]> ds = ds).
    { apply list_insert_id, list_lookup_lookup_total_lt. lia. }
    iModIntro. iFrame "Hmir".
    iIntros (m) "-> Hu".
    (* the two side conditions, off the caller's OWN unit *)
    iDestruct (ireg_rcol_mint_ok bfl (bv_unsigned inum) wl wdu wdt gl cl rl pl
                 fz n (ds !!! islot inum) with "Hla Hu") as %[Hty0 Hcl0].
    iMod (ireg_rcol_mint bfl (bv_unsigned inum) wl wdu wdt gl cl rl pl fz n
            (ds !!! islot inum) Hty0 Hcl0 with "Hla") as "[(%rl' & Hla) Hu2]".
    iMod (icnt_update (bv_unsigned inum) n (S n) with "Hcnt Hhalf")
      as "[Hcnt Hhalf]".
    iMod ("Hclose" with "[Ha Hreg Hfsb Harm Hla Hep Hslback Hback Hcnt Hfdisj Hrc Hmr]")
      as "_".
    { iNext. iExists mrg. iFrame "Ha Hreg".
      iApply ("Hback" $! mrg with "[%] [Hfsb Harm Hla Hep Hslback Hcnt Hfdisj Hrc Hmr]");
        [done |].
      iExists ds. iSplitR; [done |]. iSplitR; [done |].
      iSplitL "Hfsb"; [iExact "Hfsb" |].
      iEval (rewrite -Hins).
      iApply ("Hslback" $! (ds !!! islot inum) with "[Harm Hla Hep Hcnt Hfdisj Hrc Hmr]").
      rewrite Hkey.
      iApply (ireg_slot_intro γi (bv_unsigned inum) (ds !!! islot inum)
                wl wdu wdt gl cl rl' pl fz (S n)
                Hlok Hrt Hdir Hwl0 Hpar Hclm
                (ireg_frz_ok_of_off fz (S n) (ds !!! islot inum) Hfz0)
                with "Hla Hep Hdisj Hcnt Hfdisj [Hrc Hmr] Harm").
      iApply (ireg_frzc_intro _ _ false Hmok with "Hrc Hmr"). }
    iModIntro. iFrame "Hhalf Hu Hu2".
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  THE FIVE COUNT MOVES                                               *)
  (* ------------------------------------------------------------------ *)

  (* THE WRITE.  The [sw] and the ghost step happen in the SAME invariant
     opening, which is the whole reason the read-modify-write is atomic in
     the proof: the lock's half stops any other thread moving [M], and the
     two halves meet only here, which is exactly the moment the physical
     word changes.  [Hno] -- that the incremented count is still an [int] --
     is what re-establishes [icM_wf]; it is NOT provable here and comes from
     the caller's [IrefSlots.iref_slots_no_overflow].

     SINCE §2.2 the LEDGER moves in the same breath: the slot's [icnt] half
     goes in at [Pos.to_nat n] and comes back at [Pos.to_nat (Pos.succ n)],
     and the region's half moves with it inside a nested [↑iregN] open.

     THE LICENCE, NOT THE TOKEN (iclaim-ledger.md §3.1, RULING A -- this
     SUPERSEDES increment II's [ifreeze_off] premise; see
     [ireg_icnt_lic_acc]'s header for why the token is unpresentable here).
     The mover borrows the caller's [IgetLic.iname], refutes both frozen
     phases inside the region open with §2.6's table, and hands the licence
     straight back. *)
  Lemma iref_dup_store_au (Eo : coPset)
      (γi : gname) (γfs : fs_names) (inodestart : Z) (nib : nat)
      (M : gmap nat (Qp * positive)) (k : nat) (inum : bv 32)
      (l : ilic) (q qt : Qp) (n : positive) :
    ↑icacheN ⊆ Eo -> ↑iregN ⊆ Eo ->
    bv_unsigned inum < 16 * Z.of_nat nib ->
    M !! k = Some (qt, n) ->
    (Z.pos (Pos.succ n) < 2 ^ 31)%Z ->
    (* THE SLOT'S SHARE AUTHORITY comes from the CALLER, not from the
       invariant: it lives in the itable LOCK's resource, and every step that
       moves it runs under that lock.  iput is why -- it has to hold the
       authoritative zero across a whole [acquiresleep] call, which no
       invariant can survive (claude-notes/projects/iput-acquiresleep.md).
       The [icnt] half rides there for the same reason. *)
    itable_inv -∗ ireg_inv γi γfs inodestart nib -∗
    itable_half M -∗ iref_tok k q -∗ isl_slot M k -∗
    iname γi γfs inodestart inum l -∗
    icnt_half (bv_unsigned inum) (Pos.to_nat n) -∗
    |={Eo, Eo ∖ ↑icacheN ∖ ↑iregN}=>
      i_ref (ientry k) ↦₄ iref_word M k ∗
      (i_ref (ientry k) ↦₄ (mword_of_int (Z.pos (Pos.succ n)) : mword 32)
         ={Eo ∖ ↑icacheN ∖ ↑iregN, Eo}=∗
         itable_half (<[k := (qt, Pos.succ n)]> M) ∗
         isl_slot (<[k := (qt, Pos.succ n)]> M) k ∗
         iref_tok k (q/2)%Qp ∗ iref_tok k (q/2)%Qp ∗
         iname γi γfs inodestart inum l ∗
         icnt_half (bv_unsigned inum) (Pos.to_nat (Pos.succ n)) ∗
         (* THE MINTED UNIT, flavoured by the licence presented *)
         runit (is_claim l) (bv_unsigned inum)).
  Proof.
    iIntros (HE HER Hin HMk Hno) "#Hinv #Hrinv Hhalf Htok Hislot Hoff Hcnt".
    iMod (inv_acc Eo icacheN with "Hinv") as "[Hbody Hclose]"; [exact HE|].
    iDestruct "Hbody" as (M') "(>Ha & >%Hwf & >Hcells & >Hpool)".
    iDestruct (itable_half_agree with "Ha Hhalf") as %->.
    assert (Hk : (k < NINODE)%nat) by (apply (proj1 Hwf); by eexists).
    iDestruct (iref_cells_acc_upd M k Hk with "Hcells") as "[Hcell Hback]".
    iDestruct (live_pool_acc_upd M k Hk with "Hpool") as "[Hslot Hpback]".
    (* ---- region: the SECOND open, nested inside the icache's hole ---- *)
    iMod (ireg_icnt_lic_acc (Eo ∖ ↑icacheN) γi γfs inodestart nib inum
            l (Pos.to_nat n) ltac:(solve_ndisj) Hin
            with "Hrinv Hoff Hcnt") as "[Hoff Hrback]".
    iModIntro. iFrame "Hcell". iIntros "Hcell".
    iDestruct (itable_half_join with "Ha Hhalf") as "Hauth".
    iMod (iref_dup_step M k q qt n HMk with "Hauth Htok Hislot")
      as "(Hauth & Hislot & Ht1 & Ht2)".
    iDestruct (itable_half_split with "Hauth") as "[Ha Hhalf]".
    iEval (rewrite (live_slot_recount M k qt n (Pos.succ n) HMk)) in "Hslot".
    (* ---- region: the ledger count moves in step with the word, and the
       region closes FIRST (inner mask first) ---- *)
    iMod ("Hrback" $! (Pos.to_nat (Pos.succ n)) with "[%]") as "[Hcnt Hu]";
      [by rewrite Pos2Nat.inj_succ |].
    iMod ("Hclose" with "[Ha Hcell Hback Hslot Hpback]") as "_".
    { iNext. iExists (<[k := (qt, Pos.succ n)]> M). iFrame "Ha".
      iSplitR.
      { iPureIntro. destruct Hwf as [Hdom Hcnt']. split.
        - intros j Hj. destruct (decide (j = k)) as [->|Hne]; [exact Hk|].
          rewrite lookup_insert_ne in Hj; [|by apply not_eq_sym]. by apply Hdom.
        - intros j qj nj Hj. destruct (decide (j = k)) as [->|Hne].
          + rewrite lookup_insert in Hj. apply Some_inj in Hj.
            injection Hj as _ Hn. subst nj. exact Hno.
          + rewrite lookup_insert_ne in Hj; [|by apply not_eq_sym].
            by apply (Hcnt' j qj). }
      iSplitL "Hcell Hback".
      { iApply ("Hback" $! (qt, Pos.succ n)).
        rewrite /iref_word lookup_insert. iExact "Hcell". }
      iApply ("Hpback" $! (<[k := (qt, Pos.succ n)]> M) with "[%] Hslot").
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
     [IrefSlots.iref_slots_no_overflow] exactly as in ProofIdup.

     THE LEDGER SIDE is [iref_dup_store_au]'s verbatim: half in, half out,
     the caller's LICENCE (not a freeze token -- RULING A) refuting both
     phases across the increment. *)
  Lemma iref_incr_store_au (Eo : coPset)
      (γi : gname) (γfs : fs_names) (inodestart : Z) (nib : nat)
      (M : gmap nat (Qp * positive)) (k : nat) (inum : bv 32)
      (l : ilic) (qt qn : Qp) (n : positive) :
    ↑icacheN ⊆ Eo -> ↑iregN ⊆ Eo ->
    bv_unsigned inum < 16 * Z.of_nat nib ->
    M !! k = Some (qt, n) ->
    (qt + qn < 1/2)%Qp ->
    (Z.pos (Pos.succ n) < 2 ^ 31)%Z ->
    itable_inv -∗ ireg_inv γi γfs inodestart nib -∗
    itable_half M -∗ isl_slot M k -∗
    (* RULING R-e: the ONE mover that holds no live slice of its own, so the
       ONE that has to spend the selector's OFF half to refute [live_slot]'s
       frozen alternative.  It comes from [frz_park]'s OFF arm, which the
       caller has just decided with the very [iname] it presents here
       ([frz_park_lic_off]), and it goes straight back out. *)
    frzsel k (1/2)%Qp false -∗
    iname γi γfs inodestart inum l -∗
    icnt_half (bv_unsigned inum) (Pos.to_nat n) -∗
    |={Eo, Eo ∖ ↑icacheN ∖ ↑iregN}=>
      i_ref (ientry k) ↦₄ iref_word M k ∗
      (i_ref (ientry k) ↦₄ (mword_of_int (Z.pos (Pos.succ n)) : mword 32)
         ={Eo ∖ ↑icacheN ∖ ↑iregN, Eo}=∗
         itable_half (<[k := ((qt + qn)%Qp, Pos.succ n)]> M) ∗
         isl_slot (<[k := ((qt + qn)%Qp, Pos.succ n)]> M) k ∗
         iref_tok k qn ∗ frzsel k (1/2)%Qp false ∗
         iname γi γfs inodestart inum l ∗
         icnt_half (bv_unsigned inum) (Pos.to_nat (Pos.succ n)) ∗
         runit (is_claim l) (bv_unsigned inum)).
  Proof.
    iIntros (HE HER Hin HMk Hq Hno) "#Hinv #Hrinv Hhalf Hislot Hsel Hoff Hcnt".
    iMod (inv_acc Eo icacheN with "Hinv") as "[Hbody Hclose]"; [exact HE|].
    iDestruct "Hbody" as (M') "(>Ha & >%Hwf & >Hcells & >Hpool)".
    iDestruct (itable_half_agree with "Ha Hhalf") as %->.
    assert (Hk : (k < NINODE)%nat) by (apply (proj1 Hwf); by eexists).
    iDestruct (iref_cells_acc_upd M k Hk with "Hcells") as "[Hcell Hback]".
    iDestruct (live_pool_acc_upd M k Hk with "Hpool") as "[Hslot Hpback]".
    iMod (ireg_icnt_lic_acc (Eo ∖ ↑icacheN) γi γfs inodestart nib inum
            l (Pos.to_nat n) ltac:(solve_ndisj) Hin
            with "Hrinv Hoff Hcnt") as "[Hoff Hrback]".
    iModIntro. iFrame "Hcell". iIntros "Hcell".
    iDestruct (itable_half_join with "Ha Hhalf") as "Hauth".
    iMod (iref_incr_step M k qt n qn HMk Hq with "Hauth Hsel Hslot Hislot")
      as "(Hauth & Hsel & Hslot & Hislot & Htok)".
    iDestruct (itable_half_split with "Hauth") as "[Ha Hhalf]".
    iMod ("Hrback" $! (Pos.to_nat (Pos.succ n)) with "[%]") as "[Hcnt Hu]";
      [by rewrite Pos2Nat.inj_succ |].
    iMod ("Hclose" with "[Ha Hcell Hback Hslot Hpback]") as "_".
    { iNext. iExists (<[k := ((qt + qn)%Qp, Pos.succ n)]> M). iFrame "Ha".
      iSplitR.
      { iPureIntro. destruct Hwf as [Hdom Hcnt']. split.
        - intros j Hj. destruct (decide (j = k)) as [->|Hne]; [exact Hk|].
          rewrite lookup_insert_ne in Hj; [|by apply not_eq_sym]. by apply Hdom.
        - intros j qj nj Hj. destruct (decide (j = k)) as [->|Hne].
          + rewrite lookup_insert in Hj. apply Some_inj in Hj.
            injection Hj as _ Hn. subst nj. exact Hno.
          + rewrite lookup_insert_ne in Hj; [|by apply not_eq_sym].
            by apply (Hcnt' j qj). }
      iSplitL "Hcell Hback".
      { iApply ("Hback" $! ((qt + qn)%Qp, Pos.succ n)).
        rewrite /iref_word lookup_insert. iExact "Hcell". }
      iApply ("Hpback" $! (<[k := ((qt + qn)%Qp, Pos.succ n)]> M) with "[%] Hslot").
      intros j Hj. rewrite lookup_insert_ne; [reflexivity | by apply not_eq_sym]. }
    iModIntro. iFrame.
  Qed.

  (* THE LICENCE-FREE UP-COUNT (iclaim-ledger.md §3.13's delivery, on A⁗'s
     mechanism): [iref_incr_store_au] verbatim with [ireg_icnt_lic_acc]
     swapped for [ireg_icnt_mir_acc], and the caller's SHARE carried through
     as in [iref_upgrade_store_au].

     What the mover presents in place of a licence is the LOCK's own mirror
     half at [false], which it peels out of [IcacheEscrow.islot2]'s live arm
     and decides with [frz_park_shr_off] -- its own share against the parked
     mass.  That is why this is idup's mover: [idup(p->cwd)] can produce no
     [iname] (xv6 permits unlinking a process's cwd, so not even
     [nlink <> 0]) and the arithmetic route wants [2 <= n], while a cwd held
     by one process sits at exactly the count [FrzPre] admits.

     ---- DELIVERY IS STILL BLOCKED, AND NOT WHERE §3.13 THOUGHT (IVd) ----

     §3.13's repair -- give [IcacheEscrow.itable_res2] a persistent
     [∃ ist, ireg_inv γi γfs ist nib] so that the handle comes DOWN out of
     the lock and [SpecIdup] stays byte-identical -- was executed and does
     not survive TYPE-CHECKING, for a reason its 11-edit costing could not
     see: [ireg_inv] is defined in [InodeRegion]'s section, whose Context is
     [!riscvGS, !diskGhostG, !fsLogG, !iregG, !icacheG, !logG], and
     [IcacheEscrow]'s main section has NO [!logG Σ].  Naming [ireg_inv] in
     [itable_res2] therefore puts [!logG Σ] on [itable_res2], hence on
     [is_itable2], hence on EVERY statement that takes it -- and
     [SpecIdup:203], [SpecKfork], [SpecSysFork] and [ProofKforkB4] all take
     [is_itable2] and none of the four carries [logG].  That is §3.11's wall
     again, one level below where §3.13 looked for it, and it breaks the
     byte-identity that was the whole point.

     The eleven edits themselves are right and were verified up to this
     point; what needs a RULING is the class hierarchy, and the cheapest
     shape is to make [logG] a FIELD of a class the cone already carries
     ([iregG], which [SpecIdup] and [SpecKfork] both have) rather than a
     separate Context entry -- at the price of removing the now-ambiguous
     [!logG Σ] from every section that also carries [!iregG Σ].  That is a
     design pass, not a convergence edit, so IVd stopped here with BOTH
     halves of the 2.6b mechanism proven and in the tree ([frz_park_shr_off]
     above and this lemma) and only their delivery to [ProofIdup] open. *)
  Lemma iref_upgrade_mir_store_au (Eo : coPset)
      (γi : gname) (γfs : fs_names) (inodestart : Z) (nib : nat)
      (M : gmap nat (Qp * positive)) (k : nat) (inum : bv 32)
      (bfl : bool) (qt qn s : Qp) (n : positive) :
    ↑icacheN ⊆ Eo -> ↑iregN ⊆ Eo ->
    bv_unsigned inum < 16 * Z.of_nat nib ->
    M !! k = Some (qt, n) ->
    (qt + qn < 1/2)%Qp ->
    (Z.pos (Pos.succ n) < 2 ^ 31)%Z ->
    itable_inv -∗ ireg_inv γi γfs inodestart nib -∗
    itable_half M -∗ live_frac k s -∗ isl_slot M k -∗
    frzm_h (bv_unsigned inum) false -∗
    (* RULING R, WIRED: idup's mint is SELF-PAYING -- the PARENT reference's
       own provenance unit is what buys the two side conditions, and the
       copy is minted at the parent's flavour. *)
    runit bfl (bv_unsigned inum) -∗
    icnt_half (bv_unsigned inum) (Pos.to_nat n) -∗
    |={Eo, Eo ∖ ↑icacheN ∖ ↑iregN}=>
      i_ref (ientry k) ↦₄ iref_word M k ∗
      (i_ref (ientry k) ↦₄ (mword_of_int (Z.pos (Pos.succ n)) : mword 32)
         ={Eo ∖ ↑icacheN ∖ ↑iregN, Eo}=∗
         itable_half (<[k := ((qt + qn)%Qp, Pos.succ n)]> M) ∗
         isl_slot (<[k := ((qt + qn)%Qp, Pos.succ n)]> M) k ∗
         iref_tok k qn ∗ live_frac k s ∗
         frzm_h (bv_unsigned inum) false ∗
         icnt_half (bv_unsigned inum) (Pos.to_nat (Pos.succ n)) ∗
         runit bfl (bv_unsigned inum) ∗ runit bfl (bv_unsigned inum)).
  Proof.
    iIntros (HE HER Hin HMk Hq Hno) "#Hinv #Hrinv Hhalf Hlv Hislot Hmir Hu Hcnt".
    iMod (inv_acc Eo icacheN with "Hinv") as "[Hbody Hclose]"; [exact HE|].
    iDestruct "Hbody" as (M') "(>Ha & >%Hwf & >Hcells & >Hpool)".
    iDestruct (itable_half_agree with "Ha Hhalf") as %->.
    assert (Hk : (k < NINODE)%nat) by (apply (proj1 Hwf); by eexists).
    iDestruct (iref_cells_acc_upd M k Hk with "Hcells") as "[Hcell Hback]".
    iDestruct (live_pool_acc_upd M k Hk with "Hpool") as "[Hslot Hpback]".
    iMod (ireg_icnt_mir_acc (Eo ∖ ↑icacheN) γi γfs inodestart nib inum
            bfl (Pos.to_nat n) ltac:(solve_ndisj) Hin (Pos2Nat.is_pos n)
            with "Hrinv Hmir Hcnt") as "[Hmir Hrback]".
    iModIntro. iFrame "Hcell". iIntros "Hcell".
    iDestruct (itable_half_join with "Ha Hhalf") as "Hauth".
    iMod (iref_incr_step_lv M k qt n qn s HMk Hq with "Hauth Hlv Hslot Hislot")
      as "(Hauth & Hlv & Hslot & Hislot & Htok)".
    iDestruct (itable_half_split with "Hauth") as "[Ha Hhalf]".
    iMod ("Hrback" $! (Pos.to_nat (Pos.succ n)) with "[%] Hu")
      as "(Hcnt & Hu & Hu2)"; [by rewrite Pos2Nat.inj_succ |].
    iMod ("Hclose" with "[Ha Hcell Hback Hslot Hpback]") as "_".
    { iNext. iExists (<[k := ((qt + qn)%Qp, Pos.succ n)]> M). iFrame "Ha".
      iSplitR.
      { iPureIntro. destruct Hwf as [Hdom Hcnt']. split.
        - intros j Hj. destruct (decide (j = k)) as [->|Hne]; [exact Hk|].
          rewrite lookup_insert_ne in Hj; [|by apply not_eq_sym]. by apply Hdom.
        - intros j qj nj Hj. destruct (decide (j = k)) as [->|Hne].
          + rewrite lookup_insert in Hj. apply Some_inj in Hj.
            injection Hj as _ Hn. subst nj. exact Hno.
          + rewrite lookup_insert_ne in Hj; [|by apply not_eq_sym].
            by apply (Hcnt' j qj). }
      iSplitL "Hcell Hback".
      { iApply ("Hback" $! ((qt + qn)%Qp, Pos.succ n)).
        rewrite /iref_word lookup_insert. iExact "Hcell". }
      iApply ("Hpback" $! (<[k := ((qt + qn)%Qp, Pos.succ n)]> M) with "[%] Hslot").
      intros j Hj. rewrite lookup_insert_ne; [reflexivity | by apply not_eq_sym]. }
    iModIntro. iFrame.
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
     asymmetry with the two increment wrappers is the whole difference.

     AND THERE IS NO FREEZE TOKEN EITHER, for a second asymmetry with them:
     this close comes in at [Pos.succ n >= 2], where BOTH phases of §2.3's
     pin are already refuted by arithmetic ([ireg_frz_ok_ge2]).  A slot at
     two or more references is not frozen and cannot become frozen under the
     lock the mover is holding, so the region clause re-establishes itself. *)
  Lemma iref_close_store_au (Eo : coPset)
      (γi : gname) (γfs : fs_names) (inodestart : Z) (nib : nat)
      (M : gmap nat (Qp * positive)) (k : nat) (inum : bv 32)
      (bfl : bool) (q qt qr : Qp) (n : positive) :
    ↑icacheN ⊆ Eo -> ↑iregN ⊆ Eo ->
    bv_unsigned inum < 16 * Z.of_nat nib ->
    M !! k = Some (qt, Pos.succ n) ->
    (qt - q)%Qp = Some qr ->
    itable_inv -∗ ireg_inv γi γfs inodestart nib -∗
    itable_half M -∗ iref_tok k q -∗ isl_slot M k -∗
    (* RULING R, WIRED: the closing reference surrenders its provenance
       unit, at whatever flavour the iget that minted it used. *)
    runit bfl (bv_unsigned inum) -∗
    icnt_half (bv_unsigned inum) (Pos.to_nat (Pos.succ n)) -∗
    |={Eo, Eo ∖ ↑icacheN ∖ ↑iregN}=>
      i_ref (ientry k) ↦₄ iref_word M k ∗
      (i_ref (ientry k) ↦₄ (mword_of_int (Z.pos n) : mword 32)
         ={Eo ∖ ↑icacheN ∖ ↑iregN, Eo}=∗
         itable_half (<[k := (qr, n)]> M) ∗ isl_slot (<[k := (qr, n)]> M) k ∗
         icnt_half (bv_unsigned inum) (Pos.to_nat n)).
  Proof.
    iIntros (HE HER Hin HMk Hsub) "#Hinv #Hrinv Hhalf Htok Hislot Hu Hcnt".
    assert (Hge2 : (2 <= Pos.to_nat (Pos.succ n))%nat).
    { rewrite Pos2Nat.inj_succ. pose proof (Pos2Nat.is_pos n). lia. }
    iMod (inv_acc Eo icacheN with "Hinv") as "[Hbody Hclose]"; [exact HE|].
    iDestruct "Hbody" as (M') "(>Ha & >%Hwf & >Hcells & >Hpool)".
    iDestruct (itable_half_agree with "Ha Hhalf") as %->.
    assert (Hk : (k < NINODE)%nat) by (apply (proj1 Hwf); by eexists).
    iDestruct (iref_cells_acc_upd M k Hk with "Hcells") as "[Hcell Hback]".
    iDestruct (live_pool_acc_upd M k Hk with "Hpool") as "[Hslot Hpback]".
    iMod (ireg_icnt_acc (Eo ∖ ↑icacheN) γi γfs inodestart nib inum
            (Pos.to_nat (Pos.succ n)) ltac:(solve_ndisj) Hin
            with "Hrinv Hcnt") as (fz dsl) "[%Hfrz Hrback]".
    iModIntro. iFrame "Hcell". iIntros "Hcell".
    iDestruct (itable_half_join with "Ha Hhalf") as "Hauth".
    iMod (iref_close_step M k q qt n qr HMk Hsub with "Hauth Htok Hslot Hislot")
      as "(Hauth & Hslot & Hislot)".
    iDestruct (itable_half_split with "Hauth") as "[Ha Hhalf]".
    iMod ("Hrback" $! (Pos.to_nat n) bfl with "[%] [%] Hu") as "Hcnt";
      [ exact (ireg_frz_ok_ge2_any fz _ _ dsl Hge2 Hfrz)
      | by rewrite Pos2Nat.inj_succ |].
    iMod ("Hclose" with "[Ha Hcell Hback Hslot Hpback]") as "_".
    { iNext. iExists (<[k := (qr, n)]> M). iFrame "Ha".
      iSplitR.
      { iPureIntro. destruct Hwf as [Hdom Hcnt']. split.
        - intros i Hi. destruct (decide (i = k)) as [->|Hne]; [exact Hk|].
          rewrite lookup_insert_ne in Hi; [|by apply not_eq_sym]. by apply Hdom.
        - intros i qi ni Hi. destruct (decide (i = k)) as [->|Hne].
          + rewrite lookup_insert in Hi. apply Some_inj in Hi.
            injection Hi as _ Hn. subst ni.
            pose proof (Hcnt' k qt (Pos.succ n) HMk) as Hb. lia.
          + rewrite lookup_insert_ne in Hi; [|by apply not_eq_sym].
            by apply (Hcnt' i qi). }
      iSplitL "Hcell Hback".
      { iApply ("Hback" $! (qr, n)).
        rewrite /iref_word lookup_insert. iExact "Hcell". }
      iApply ("Hpback" $! (<[k := (qr, n)]> M) with "[%] Hslot").
      intros j Hj. rewrite lookup_insert_ne; [reflexivity | by apply not_eq_sym]. }
    iModIntro. iFrame.
  Qed.

  (* iput's [ref--] WHEN IT IS THE LAST: the slot leaves [M] entirely and
     the word goes to zero, which is [iref_word]'s [None] branch -- i.e.
     the free-slot shape iget's scan looks for.  The closer must present
     the WHOLE outstanding share [qt]; REF-1 ([iref_lookup] at count one)
     is what tells it that its own [q] is that share.

     THE ONE COUNT MOVE THAT RUNS INSIDE A FREEZE WINDOW (§2.3, the probe's
     correction).  iput's free path mints the freeze in [ip_free_entry]'s
     span at +0x50 and retires it only at the +0xba deposit, so +0x8a's last
     close is strictly inside -- which is exactly why §2.3's original strict
     [icnt = 1] clause is FALSE, and why the phase is PHASED.  The token
     comes in at [ph] and goes out at [frz_close ph]: [FrzPre -> FrzPost]
     re-establishes the pin at zero, and [FrzOff] passes through, which is
     what lets the ORDINARY last close (an unfrozen slot at ref 1) use this
     same lemma with nothing new to find. *)
  Lemma iref_close_last_store_au (Eo : coPset)
      (γi : gname) (γfs : fs_names) (inodestart : Z) (nib : nat)
      (M : gmap nat (Qp * positive)) (k : nat) (inum : bv 32) (qt : Qp)
      (bfl : bool) (ph : frz) :
    ↑icacheN ⊆ Eo -> ↑iregN ⊆ Eo ->
    bv_unsigned inum < 16 * Z.of_nat nib ->
    M !! k = Some (qt, 1%positive) ->
    itable_inv -∗ ireg_inv γi γfs inodestart nib -∗
    itable_half M -∗ iref_tok k qt -∗ live_frac k (1/2)%Qp -∗
    frzsel k (1/2)%Qp false -∗
    isl_slot M k -∗
    (* RULING R, WIRED: the LAST close surrenders the dying reference's
       provenance unit, which is what (R1) needs to reach the all-zero
       clause the free then re-establishes. *)
    runit bfl (bv_unsigned inum) -∗
    ifreeze ph (bv_unsigned inum) -∗ icnt_half (bv_unsigned inum) 1%nat -∗
    (* THE FREEZE RECEIPT, AT THE PHASE THAT NEEDS IT (iclaim-ledger.md
       §3.14 as built).  [frz_close] never lands on [FrzPre], so the slot
       always owes a receipt on the way out; the open supplies it at every
       phase but [FrzPre], and at [FrzPre] this premise does -- which is
       exactly the free path handing back what [ireg_freeze_au] lent it.
       At the two other phases the premise is [emp]. *)
    frz_rcpt_pre ph (bv_unsigned inum) -∗
    (* ...AND THE MIRROR's LOCK HALF, at the same one phase (§3.16, A⁗).
       [emp] at [FrzOff]/[FrzPost]; at [FrzPre] it is the half the free path
       reclaims from [IcacheEscrow.islot2]'s FROZEN-PARK disjunct at the
       +0x82 re-acquire, and what comes back is the same half DOWN -- which
       is exactly what the evicted inum's pool bundle then owes. *)
    frz_mir ph (bv_unsigned inum) -∗
    |={Eo, Eo ∖ ↑icacheN ∖ ↑iregN}=>
      i_ref (ientry k) ↦₄ iref_word M k ∗
      (i_ref (ientry k) ↦₄ (mword_of_int 0 : mword 32)
         ={Eo ∖ ↑icacheN ∖ ↑iregN, Eo}=∗
         itable_half (delete k M) ∗ isl_slot (delete k M) k ∗
         ifreeze (frz_close ph) (bv_unsigned inum) ∗
         icnt_half (bv_unsigned inum) 0%nat ∗
         frz_mir_back ph (frz_close ph) (bv_unsigned inum)).
  Proof.
    iIntros (HE HER Hin HMk) "#Hinv #Hrinv Hhalf Htok Hh Hsel Hislot Hu Hfz Hcnt Hrpre Hmir".
    iMod (inv_acc Eo icacheN with "Hinv") as "[Hbody Hclose]"; [exact HE|].
    iDestruct "Hbody" as (M') "(>Ha & >%Hwf & >Hcells & >Hpool)".
    iDestruct (itable_half_agree with "Ha Hhalf") as %->.
    assert (Hk : (k < NINODE)%nat) by (apply (proj1 Hwf); by eexists).
    iDestruct (iref_cells_acc_del M k Hk with "Hcells") as "[Hcell Hback]".
    iDestruct (live_pool_acc_upd M k Hk with "Hpool") as "[Hslot Hpback]".
    iMod (ireg_icnt_frz_acc (Eo ∖ ↑icacheN) γi γfs inodestart nib inum
            ph 1%nat ltac:(solve_ndisj) Hin
            with "Hrinv Hfz Hcnt Hmir") as (dsl) "(%Hpin & Hrcpt & Hrback)".
    iDestruct (frz_rcpt_split ph (bv_unsigned inum) with "Hrcpt Hrpre") as "Hown".
    iModIntro. iFrame "Hcell". iIntros "Hcell".
    iDestruct (itable_half_join with "Ha Hhalf") as "Hauth".
    iMod (iref_close_last_step M k qt HMk with "Hauth Htok Hh Hsel Hslot Hislot")
      as "(Hauth & Hslot & Hislot)".
    iDestruct (itable_half_split with "Hauth") as "[Ha Hhalf]".
    (* THE PIN AT THE NEW PHASE, and RULING A made it a RECORD fact -- but
       the two record conjuncts are the same two at both phases, so the step
       carries them off the pin it came in with and supplies only the new
       count ([InodeRegion.ireg_frz_ok_phase]).  [FrzOff] stays [FrzOff],
       which is what keeps the ordinary last close from minting a freeze. *)
    assert (Hstep : ireg_frz_ok (Some (Excl (frz_close ph))) 0%nat dsl).
    { apply (ireg_frz_ok_phase ph (frz_close ph) 1%nat 0%nat dsl Hpin).
      - intros ->. reflexivity.
      - intros rg; destruct ph; cbn [frz_close]; intros Hc; discriminate Hc.
      - intros rg _. reflexivity. }
    iMod ("Hrback" $! (frz_close ph) 0%nat bfl with "[%] [%] [%] Hu [%] [Hown]")
      as "(Hfz & Hcnt & Hmir)";
      [ exact Hstep
      | right; exact (frz_close_reg ph)
      | reflexivity
      | destruct ph; cbn [frz_close frz_bit]; intros Hc; [discriminate Hc | reflexivity | discriminate Hc]
      | iApply (frz_rcpt_close ph (bv_unsigned inum) with "Hown") |].
    iMod ("Hclose" with "[Ha Hcell Hback Hslot Hpback]") as "_".
    { iNext. iExists (delete k M). iFrame "Ha".
      iSplitR.
      { iPureIntro. destruct Hwf as [Hdom Hcnt']. split.
        - intros i Hi. apply Hdom.
          destruct Hi as [e He]. exists e.
          rewrite lookup_delete_Some in He. apply He.
        - intros i qi ni Hi.
          rewrite lookup_delete_Some in Hi. destruct Hi as [_ Hi].
          by apply (Hcnt' i qi). }
      iSplitL "Hcell Hback"; [iApply ("Hback" with "Hcell") |].
      iApply ("Hpback" $! (delete k M) with "[%] Hslot").
      intros j Hj. rewrite lookup_delete_ne; [reflexivity | by apply not_eq_sym]. }
    iModIntro. iFrame.
  Qed.

  (* THE FREE PATH's INSTANCE, named as the probe named it: the phase steps
     [FrzPre -> FrzPost] at iput+0x8a and the freeze stays standing for the
     off-lock deposit to retire (§1.4). *)
  Lemma iref_close_last_freeze_store_au (Eo : coPset)
      (γi : gname) (γfs : fs_names) (inodestart : Z) (nib : nat)
      (M : gmap nat (Qp * positive)) (k : nat) (inum : bv 32) (qt : Qp)
      (bfl : bool) (rg : bool) :
    ↑icacheN ⊆ Eo -> ↑iregN ⊆ Eo ->
    bv_unsigned inum < 16 * Z.of_nat nib ->
    M !! k = Some (qt, 1%positive) ->
    itable_inv -∗ ireg_inv γi γfs inodestart nib -∗
    (* RULING R-e: NO live slice comes in.  The dying reference arrives as its
       COUNT FRAGMENT and its SLEEPLOCK SHARE alone -- its [q] and the escrow
       arm's ½ went into [live_slot]'s frozen alternative at the mint -- and
       what pays for the retirement is [frzsel k ½ true], the two quarters the
       +0x82 park-reclaim and the eviction hand back. *)
    itable_half M -∗ iref_frag k qt -∗ slh_tok (icfg_isl k) qt -∗
    frzsel k (1/2)%Qp true -∗
    isl_slot M k -∗
    (* RULING R, WIRED: the dying reference's provenance unit. *)
    runit bfl (bv_unsigned inum) -∗
    ifreeze_pre rg (bv_unsigned inum) -∗ icnt_half (bv_unsigned inum) 1%nat -∗
    (* THE RECEIPT GOES HOME HERE.  [ireg_freeze_au] handed it to the walk
       at the mint (iput+0x50) so that the +0x70 mid-free park could carry
       it in the payload's token slot while the walk kept [ifreeze_pre] in
       hand; this step is where the column stops reading [FrzPre] and the
       region takes it back. *)
    frzown (bv_unsigned inum) -∗
    (* ...AND THE MIRROR's LOCK HALF, UP (§3.16, A⁗).  It is what the walk
       reclaims at +0x82 from the FROZEN-PARK disjunct of [islot2]'s live arm
       -- the disjunct the mint built at +0x50 out of this very reference's
       live slice and the payload checkout's half -- and it comes back DOWN,
       for the evicted inum's pool bundle.  Reclaiming it is also what puts
       the two parked [live_frac]s back in the closer's hand, which is what
       the eviction's mass reconciliation needs (ZZProbeFrz P5). *)
    frzm_h (bv_unsigned inum) true -∗
    |={Eo, Eo ∖ ↑icacheN ∖ ↑iregN}=>
      i_ref (ientry k) ↦₄ iref_word M k ∗
      (i_ref (ientry k) ↦₄ (mword_of_int 0 : mword 32)
         ={Eo ∖ ↑icacheN ∖ ↑iregN, Eo}=∗
         itable_half (delete k M) ∗ isl_slot (delete k M) k ∗
         ifreeze_post rg (bv_unsigned inum) ∗
         icnt_half (bv_unsigned inum) 0%nat ∗
         frzm_h (bv_unsigned inum) false).
  Proof.
    iIntros (HE HER Hin HMk) "#Hinv #Hrinv Hhalf Hf Hsh Hsel Hislot Hu Hfz Hcnt Hrpre Hmir".
    iMod (inv_acc Eo icacheN with "Hinv") as "[Hbody Hclose]"; [exact HE|].
    iDestruct "Hbody" as (M') "(>Ha & >%Hwf & >Hcells & >Hpool)".
    iDestruct (itable_half_agree with "Ha Hhalf") as %->.
    assert (Hk : (k < NINODE)%nat) by (apply (proj1 Hwf); by eexists).
    iDestruct (iref_cells_acc_del M k Hk with "Hcells") as "[Hcell Hback]".
    iDestruct (live_pool_acc_upd M k Hk with "Hpool") as "[Hslot Hpback]".
    iMod (ireg_icnt_frz_acc (Eo ∖ ↑icacheN) γi γfs inodestart nib inum
            (FrzPre rg) 1%nat ltac:(solve_ndisj) Hin
            with "Hrinv Hfz Hcnt Hmir") as (dsl) "(%Hpin & Hrcpt & Hrback)".
    iDestruct (frz_rcpt_split (FrzPre rg) (bv_unsigned inum) with "Hrcpt Hrpre") as "Hown".
    iModIntro. iFrame "Hcell". iIntros "Hcell".
    iDestruct (itable_half_join with "Ha Hhalf") as "Hauth".
    iMod (iref_close_last_frz_step M k qt HMk with "Hauth Hf Hsh Hsel Hslot Hislot")
      as "(Hauth & Hslot & Hislot)".
    iDestruct (itable_half_split with "Hauth") as "[Ha Hhalf]".
    (* THE PIN AT THE NEW PHASE, and RULING A made it a RECORD fact -- but
       the two record conjuncts are the same two at both phases, so the step
       carries them off the pin it came in with and supplies only the new
       count ([InodeRegion.ireg_frz_ok_phase]).  [FrzOff] stays [FrzOff],
       which is what keeps the ordinary last close from minting a freeze. *)
    assert (Hstep : ireg_frz_ok (Some (Excl (frz_close (FrzPre rg)))) 0%nat dsl).
    { apply (ireg_frz_ok_phase (FrzPre rg) (frz_close (FrzPre rg))
               1%nat 0%nat dsl Hpin).
      - intros Hc; discriminate Hc.
      - intros rg' Hc; cbn [frz_close] in Hc; discriminate Hc.
      - intros rg' _. reflexivity. }
    iMod ("Hrback" $! (frz_close (FrzPre rg)) 0%nat bfl with "[%] [%] [%] Hu [%] [Hown]")
      as "(Hfz & Hcnt & Hmir)";
      [ exact Hstep
      | right; exact (frz_close_reg (FrzPre rg))
      | reflexivity
      | cbn [frz_close frz_bit]; intros Hc; reflexivity
      | iApply (frz_rcpt_close (FrzPre rg) (bv_unsigned inum) with "Hown") |].
    iMod ("Hclose" with "[Ha Hcell Hback Hslot Hpback]") as "_".
    { iNext. iExists (delete k M). iFrame "Ha".
      iSplitR.
      { iPureIntro. destruct Hwf as [Hdom Hcnt']. split.
        - intros i Hi. apply Hdom.
          destruct Hi as [e He]. exists e.
          rewrite lookup_delete_Some in He. apply He.
        - intros i qi ni Hi.
          rewrite lookup_delete_Some in Hi. destruct Hi as [_ Hi].
          by apply (Hcnt' i qi). }
      iSplitL "Hcell Hback"; [iApply ("Hback" with "Hcell") |].
      iApply ("Hpback" $! (delete k M) with "[%] Hslot").
      intros j Hj. rewrite lookup_delete_ne; [reflexivity | by apply not_eq_sym]. }
    iModIntro. iFrame.
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
      (γi : gname) (γfs : fs_names) (inodestart : Z) (nib : nat)
      (M : gmap nat (Qp * positive)) (k : nat) (inum : bv 32)
      (l : ilic) (qt qn s : Qp) (n : positive) :
    ↑icacheN ⊆ Eo -> ↑iregN ⊆ Eo ->
    bv_unsigned inum < 16 * Z.of_nat nib ->
    M !! k = Some (qt, n) ->
    (qt + qn < 1/2)%Qp ->
    (Z.pos (Pos.succ n) < 2 ^ 31)%Z ->
    itable_inv -∗ ireg_inv γi γfs inodestart nib -∗
    itable_half M -∗ live_frac k s -∗ isl_slot M k -∗
    frzsel k (1/2)%Qp false -∗
    iname γi γfs inodestart inum l -∗
    icnt_half (bv_unsigned inum) (Pos.to_nat n) -∗
    |={Eo, Eo ∖ ↑icacheN ∖ ↑iregN}=>
      i_ref (ientry k) ↦₄ iref_word M k ∗
      (i_ref (ientry k) ↦₄ (mword_of_int (Z.pos (Pos.succ n)) : mword 32)
         ={Eo ∖ ↑icacheN ∖ ↑iregN, Eo}=∗
         itable_half (<[k := ((qt + qn)%Qp, Pos.succ n)]> M) ∗
         isl_slot (<[k := ((qt + qn)%Qp, Pos.succ n)]> M) k ∗
         iref_tok k qn ∗ live_frac k s ∗ frzsel k (1/2)%Qp false ∗
         iname γi γfs inodestart inum l ∗
         icnt_half (bv_unsigned inum) (Pos.to_nat (Pos.succ n)) ∗
         runit (is_claim l) (bv_unsigned inum)).
  Proof.
    iIntros (HE HER Hin HMk Hq Hno) "#Hinv #Hrinv Hhalf Hlv Hislot Hsel Hoff Hcnt".
    iMod (iref_incr_store_au Eo γi γfs inodestart nib M k inum l qt qn n
            HE HER Hin HMk Hq Hno
            with "Hinv Hrinv Hhalf Hislot Hsel Hoff Hcnt")
      as "[Hcell Hback]".
    iModIntro. iFrame "Hcell". iIntros "Hcell".
    iMod ("Hback" with "Hcell") as "(Hhalf & Hislot & Htok & Hsel & Hoff & Hcnt & Hu)".
    iModIntro. iFrame.
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  THE SIXTH MOVE: THE RECYCLE's 0 -> 1 (iclaim-ledger.md §3.1, the    *)
  (*  brief's item 4; IIIb's Consequence 3)                               *)
  (* ------------------------------------------------------------------ *)

  (* Increment II shipped a region-aware wrapper for every count move BUT
     this one, because [iref_alloc_step] is region-blind and iget's +0x78
     did its own [itable_inv] opening inline.  Since §2.2 that is no longer
     enough: the peeled [icnt_half z 0] has to reach the slot at
     [icnt_half z 1], which is a move of the region's half and therefore a
     nested [↑iregN] open.

     THIS ONE DOES TAKE THE TOKEN, and it is the only up-count that can
     (A-custody): the recycle's inum is UNCACHED, so its [ifreeze_off] is
     exactly what the pool peel just handed the recycler, alongside the
     zero count half.  Both come back -- the token travels on into the
     entry's parked arm and the half into [islot2]'s live one.  No licence
     is needed and none would help: at an uncached inum there is no cached
     arm for the table's rows to talk about.

     The [ph] is a parameter for [iref_close_last_store_au]'s reason: the
     ORDINARY recycle threads [FrzOff] and the pin is vacuous both sides,
     while a recycle of a box whose freeze is still standing is refuted
     upstream, at the peel, and never reaches here. *)
  Lemma iref_alloc_store_au (Eo : coPset)
      (γi : gname) (γfs : fs_names) (inodestart : Z) (nib : nat)
      (M : gmap nat (Qp * positive)) (k : nat) (inum : bv 32) (l : ilic)
      (q : Qp) :
    ↑icacheN ⊆ Eo -> ↑iregN ⊆ Eo ->
    bv_unsigned inum < 16 * Z.of_nat nib ->
    (* the index bound is the CALLER's here and nowhere else in the family:
       a FREE slot is not in [M], so [icM_wf]'s domain clause cannot supply
       it (iget's scan has it, from [IcacheEscrow]'s pool geometry). *)
    (k < NINODE)%nat ->
    M !! k = None ->
    (q < 1/2)%Qp ->
    itable_inv -∗ ireg_inv γi γfs inodestart nib -∗
    itable_half M -∗ isl_slot M k -∗
    (* RULING R, WIRED: the recycle's 0 -> 1 MINTS, and the mint's two side
       conditions can only come from the licence iget already presents.  So
       this mover borrows it -- exactly as the other three up-counts do --
       and the [ifreeze_off] it also carries is now only threaded, not
       stepped (the phase does not move at a recycle). *)
    iname γi γfs inodestart inum l -∗
    ifreeze_off (bv_unsigned inum) -∗
    icnt_half (bv_unsigned inum) 0%nat -∗
    |={Eo, Eo ∖ ↑icacheN ∖ ↑iregN}=>
      i_ref (ientry k) ↦₄ iref_word M k ∗
      (i_ref (ientry k) ↦₄ (mword_of_int 1 : mword 32)
         ={Eo ∖ ↑icacheN ∖ ↑iregN, Eo}=∗
         itable_half (<[k := (q, 1%positive)]> M) ∗
         isl_slot (<[k := (q, 1%positive)]> M) k ∗
         iref_tok k q ∗
         (∃ g : gname, live_gen k (1/2)%Qp g ∗ ity_pending g) ∗
         (* RULING R-e: the recycled slot's selector splits, and THIS half is
            what [IcacheEscrow.islot2]'s live arm parks in [frz_park]'s OFF
            alternative -- the up-count's future weapon. *)
         frzsel k (1/2)%Qp false ∗
         iname γi γfs inodestart inum l ∗
         ifreeze_off (bv_unsigned inum) ∗
         icnt_half (bv_unsigned inum) 1%nat ∗
         runit (is_claim l) (bv_unsigned inum)).
  Proof.
    iIntros (HE HER Hin Hk HMk Hq) "#Hinv #Hrinv Hhalf Hislot Hl Hoff Hcnt".
    iMod (inv_acc Eo icacheN with "Hinv") as "[Hbody Hclose]"; [exact HE|].
    iDestruct "Hbody" as (M') "(>Ha & >%Hwf & >Hcells & >Hpool)".
    iDestruct (itable_half_agree with "Ha Hhalf") as %->.
    iDestruct (iref_cells_acc_upd M k Hk with "Hcells") as "[Hcell Hback]".
    iDestruct (live_pool_acc_upd M k Hk with "Hpool") as "[Hslot Hpback]".
    (* ---- region: the nested open, the token pinning the column ---- *)
    iMod (ireg_icnt_lic_acc (Eo ∖ ↑icacheN) γi γfs inodestart nib inum
            l 0%nat ltac:(solve_ndisj) Hin
            with "Hrinv Hl Hcnt") as "[Hl Hrback]".
    iModIntro. iFrame "Hcell". iIntros "Hcell".
    iDestruct (itable_half_join with "Ha Hhalf") as "Hauth".
    iMod (iref_alloc_step M k q HMk Hq with "Hauth Hslot Hislot")
      as (gnew) "(Hauth & Hslot & Hislot & Htok & Hlvh & Hpend & Hsel)".
    iDestruct (itable_half_split with "Hauth") as "[Ha Hhalf]".
    iMod ("Hrback" $! 1%nat with "[%]") as "[Hcnt Hu]"; [reflexivity |].
    iMod ("Hclose" with "[Ha Hcell Hback Hslot Hpback]") as "_".
    { iNext. iExists (<[k := (q, 1%positive)]> M). iFrame "Ha".
      iSplitR.
      { iPureIntro. destruct Hwf as [Hdom Hcnt']. split.
        - intros j Hj. destruct (decide (j = k)) as [->|Hne]; [exact Hk|].
          rewrite lookup_insert_ne in Hj; [|by apply not_eq_sym]. by apply Hdom.
        - intros j qj nj Hj. destruct (decide (j = k)) as [->|Hne].
          + rewrite lookup_insert in Hj. apply Some_inj in Hj.
            injection Hj as _ Hn. subst nj. vm_compute. reflexivity.
          + rewrite lookup_insert_ne in Hj; [|by apply not_eq_sym].
            by apply (Hcnt' j qj). }
      iSplitL "Hcell Hback".
      { iApply ("Hback" $! (q, 1%positive)).
        rewrite /iref_word lookup_insert. iExact "Hcell". }
      iApply ("Hpback" $! (<[k := (q, 1%positive)]> M) with "[%] Hslot").
      intros j Hj. rewrite lookup_insert_ne; [reflexivity | by apply not_eq_sym]. }
    iModIntro. iFrame "Hhalf Hislot Htok Hl Hoff Hcnt Hu Hsel".
    iExists gnew. iFrame "Hlvh Hpend".
  Qed.

End IcacheRefInvReg.

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
