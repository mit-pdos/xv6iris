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
From iris.base_logic.lib Require Import gen_heap invariants own.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvPtsto RiscvExtras.
Require Import WpLock.
Require Import LogInv.
Require Import FsCrash.
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

Definition NINODE : nat := 50%nat.

(* the spinlock is the first member, so its address IS the symbol *)
Definition itable_lock : mword 64 := mword_of_int KernelSyms.itable.

Definition ISLOTSZ : Z := 136.

Definition ientry (k : nat) : mword 64 :=
  mword_of_int (KernelSyms.itable + 24 + ISLOTSZ * Z.of_nat k).

(* the whole geometry as ONE arithmetic fact: every entry address in range
   is its literal offset, with no wrap.  Injectivity, the scan's step and
   the scan's sentinel are corollaries, which is why this is the only
   bitvector reasoning in the file. *)
Lemma ientry_unsigned (k : nat) :
  (k <= NINODE)%nat ->
  bv_unsigned (ientry k) = KernelSyms.itable + 24 + ISLOTSZ * Z.of_nat k.
Proof.
  intros Hk. rewrite /ientry. apply moi64_small.
  unfold NINODE in Hk. unfold ISLOTSZ, KernelSyms.itable. lia.
Qed.

Lemma ientry_inj (k1 k2 : nat) :
  (k1 <= NINODE)%nat -> (k2 <= NINODE)%nat -> ientry k1 = ientry k2 -> k1 = k2.
Proof.
  intros H1 H2 Heq.
  apply (f_equal bv_unsigned) in Heq.
  rewrite (ientry_unsigned k1 H1) (ientry_unsigned k2 H2) in Heq.
  unfold ISLOTSZ in Heq. lia.
Qed.

(* the scan's [addi s1,s1,136] *)
Lemma ientry_step (k : nat) :
  ientry (S k) = add_vec_int (ientry k) ISLOTSZ.
Proof.
  rewrite /ientry avi_mword.
  assert (Harith : KernelSyms.itable + 24 + ISLOTSZ * Z.of_nat (S k)
                 = KernelSyms.itable + 24 + ISLOTSZ * Z.of_nat k + ISLOTSZ)
    by (rewrite Nat2Z.inj_succ; unfold ISLOTSZ; lia).
  rewrite Harith. reflexivity.
Qed.

(* the scan's sentinel: one past the last entry is the NEXT SYMBOL.  If a
   future revision inserts a global between [itable] and [log] this lemma
   is what fails, which is the point of stating it. *)
Lemma ientry_sentinel : ientry NINODE = (mword_of_int KernelSyms.log : mword 64).
Proof. rewrite /ientry. apply bv_eq. vm_compute. reflexivity. Qed.

(* iinit's loop cursor walks the SLEEPLOCKS, not the entries *)
Lemma ientry_lock_0 :
  i_lock (ientry 0) = (mword_of_int (KernelSyms.itable + 40) : mword 64).
Proof. rewrite /i_lock /ientry. apply bv_eq. vm_compute. reflexivity. Qed.

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

(* [bfree] hands the freed block back to [BitmapInv.free_blk], whose
   [length bs = BSIZE] conjunct is the obligation; [inode_blocks] names a
   block's contents but says nothing about their length, so [SpecItrunc.v]
   takes that as a hypothesis too.

   Unlike the range premise this one is NOT derivable from anything the
   model holds today, because [FsBlocks.fsblock] is a bare ghost_map half
   with no length side condition anywhere above it.  It is an INDUCTIVE
   fact about the inode layer -- bmap deposits [replicate BSIZE 0], writei
   replaces a block's bytes with a list of the same length, itrunc empties
   to [replicate BSIZE 0] -- so it can be carried, and the place to carry
   it is beside [InodeLock.inode_ok], the pure record ilock mints and
   [inode_parked] holds.  That is what [inode_sized] is; the three laws
   below are what its producers need to re-establish it.

   Note the BOUND.  [SpecItrunc.v] states the premise for every [i : nat];
   no holder of ilock's bundle can supply that, because both
   [inode_blocks] and [blk_holes_zero] stop at MAXFILE.  The premise has to
   be narrowed to [i < MAXFILE] -- which is all itrunc's loops touch.

   The design note argues that the BETTER home is [fsblock] itself (the
   length is a block-layer truth, and [BitmapInv.free_blk] already pairs
   the two by hand); that change is recorded there and left unmade.        *)
Definition inode_sized (data : nat -> list (bv 8)) : Prop :=
  forall i : nat, (i < MAXFILE)%nat -> length (data i) = BSIZE.

(* itrunc's own output, and ialloc's fresh inode *)
Lemma inode_sized_zero : inode_sized (fun _ => replicate BSIZE (bv_0 8)).
Proof. intros i _. apply length_replicate. Qed.

(* bmap's deposit and writei's block update are both this *)
Lemma inode_sized_insert (data : nat -> list (bv 8)) (i : nat) (bs : list (bv 8)) :
  inode_sized data -> length bs = BSIZE ->
  inode_sized (<[i := bs]> data).
Proof.
  intros Hs Hbs j Hj.
  destruct (decide (j = i)) as [->|Hne].
  - rewrite fn_lookup_insert. exact Hbs.
  - rewrite fn_lookup_insert_ne; [|exact (not_eq_sym Hne)]. exact (Hs j Hj).
Qed.

(* a HOLE is sized for free, so a producer only ever has to think about the
   ALLOCATED indices ([blk_holes_zero] is already an [inode_ok] conjunct) *)
Lemma inode_sized_of_alloc (bm : blkmap) (data : nat -> list (bv 8)) :
  blk_holes_zero bm data ->
  (forall i : nat, (i < MAXFILE)%nat -> bv_unsigned (blkmap_get bm i) <> 0 ->
     length (data i) = BSIZE) ->
  inode_sized data.
Proof.
  intros Hholes Halloc i Hi.
  destruct (decide (bv_unsigned (blkmap_get bm i) = 0)) as [Hz|Hnz].
  - rewrite (Hholes i Hi Hz). apply length_replicate.
  - exact (Halloc i Hi Hnz).
Qed.

(* ===================================================================== *)
(*  4.  THE REFERENCE-COUNT ALGEBRA                                       *)
(* ===================================================================== *)

(* RustBelt's Arc algebra, exactly as [FileInv.frefUR] uses it for
   [struct file]: [M !! k = Some (q, n)] means "itable slot [k] is live,
   with [n] outstanding references holding [q] of its identity fields
   between them"; [k ∉ dom M] means the slot is FREE.

   The frac x count pairing is the whole trick and it is what the design
   note calls REF-1 EXCLUSIVITY: [fracR] has no unit, so [Some (q,c) ≼
   Some (qt,n)] forces [q = qt -> c = n].  A thread that holds the WHOLE
   outstanding share and reads [ip->ref == 1] therefore knows there is no
   other reference in the system.  That is [iref_lookup], and it is the
   algebraic half of the theorem xv6's comment above iput asserts.

   ---- WHY THE COUNT IS [natR] AND NOT [positiveR] ---------------------

   Because a reference must be SHAREABLE without being DUPLICATED.  A
   [struct file] holds ONE inode reference and shares it among every fd
   that has a reference to that file: [filedup] bumps [f->ref] and does
   NOT bump [ip->ref].  At [positiveR] that is inexpressible -- the count
   component's [⋅] is addition and the smallest element is 1, so any split
   of a fragment duplicates its count and three fds sharing a file would
   compose to [ip->ref == 3], which nothing ever wrote.

   [natR] has a zero, so a fragment's count component says how many
   LOGICAL REFERENCES the fragment carries, and the two shapes are:

     [iref_tok γ k q]    = [(q, 1)]   ONE reference, plus [q] of the
                                      identity fields
     [iref_share γ k q]  = [(q, 0)]   [q] of the identity fields and NO
                                      reference of its own -- a share of
                                      somebody else's

   [iref_tok γ k (q1 + q2) ⊣⊢ iref_tok γ k q1 ∗ iref_share γ k q2], and
   shares split and rejoin freely ([iref_share_split]).  A share is what
   travels to each fd and to each [ilock] caller; only the indivisible [1]
   is parked in the ftable slot or in [p->cwd].  It is enough for a reader:
   a positive [q] proves the slot is in [dom M], hence live, hence
   [ip->ref > 0] -- which is what kills ilock's panic.

   What [natR] costs is that "this slot is live" is no longer free from the
   type: [icM_wf] must SAY [1 <= n], or a slot whose fragments are all
   shares would be legal and [iref_word_live] would be false.             *)
Definition icacheUR : ucmra := authUR (gmapUR nat (prodR fracR natR)).

Class icacheG (Σ : gFunctors) := IcacheG { icache_inG :: inG Σ icacheUR }.
Definition icacheΣ : gFunctors := #[GFunctor icacheUR].
Global Instance subG_icacheΣ {Σ} : subG icacheΣ Σ -> icacheG Σ.
Proof. solve_inG. Qed.

(* the word in [ip->ref]: zero exactly on a free slot.  [FileInv]'s
   [fref_word_zero] / [fref_word_nonzero] / [fref_word_spos] read the two
   branch tests off this shape and are reusable verbatim -- they are about
   a count in an [int] field, not about struct file. *)
Definition iref_word (M : gmap nat (Qp * nat)) (k : nat) : mword 32 :=
  match M !! k with
  | None => mword_of_int 0
  | Some (_, n) => mword_of_int (Z.of_nat n)
  end.

(* the three things the authority's map may never do.  The count bound is
   not bookkeeping: it is what makes the [lw]/[sext.w] the code performs
   mean the count.  The LOWER bound is what kills ilock's and iunlock's
   [ref < 1] panic, and unlike at [positiveR] it has to be stated -- see
   the algebra's header. *)
Definition icM_wf (M : gmap nat (Qp * nat)) : Prop :=
  (forall k : nat, is_Some (M !! k) -> (k < NINODE)%nat)
  /\ (forall (k : nat) (q : Qp) (n : nat),
        M !! k = Some (q, n) -> Z.of_nat n < 2 ^ 31)
  /\ (forall (k : nat) (q : Qp) (n : nat),
        M !! k = Some (q, n) -> (1 <= n)%nat).

Lemma icM_wf_count (M : gmap nat (Qp * nat)) (k : nat) (q : Qp) (n : nat) :
  icM_wf M -> M !! k = Some (q, n) -> Z.of_nat n < 2 ^ 31.
Proof. intros (_ & H & _). apply H. Qed.

Lemma icM_wf_live (M : gmap nat (Qp * nat)) (k : nat) (q : Qp) (n : nat) :
  icM_wf M -> M !! k = Some (q, n) -> (1 <= n)%nat.
Proof. intros (_ & _ & H). apply H. Qed.

(* the two ways the map ever moves.  Every [ref++] / [ref--] / recycle
   re-establishes [icM_wf] through one of these, so the three conjuncts are
   discharged in one place rather than at each opening. *)
Lemma icM_wf_insert (M : gmap nat (Qp * nat)) (k : nat) (q : Qp) (n : nat) :
  icM_wf M -> (k < NINODE)%nat -> (Z.of_nat n < 2 ^ 31)%Z -> (1 <= n)%nat ->
  icM_wf (<[k := (q, n)]> M).
Proof.
  intros (Hdom & Hcnt & Hlive) Hk Hn Hl.
  split; [|split].
  - intros j Hj. destruct (decide (j = k)) as [->|Hne]; [exact Hk|].
    rewrite lookup_insert_ne in Hj; [|by apply not_eq_sym]. by apply Hdom.
  - intros j qj nj Hj. destruct (decide (j = k)) as [->|Hne].
    + rewrite lookup_insert in Hj. apply Some_inj in Hj.
      injection Hj as _ Hj. by subst nj.
    + rewrite lookup_insert_ne in Hj; [|by apply not_eq_sym].
      by apply (Hcnt j qj).
  - intros j qj nj Hj. destruct (decide (j = k)) as [->|Hne].
    + rewrite lookup_insert in Hj. apply Some_inj in Hj.
      injection Hj as _ Hj. by subst nj.
    + rewrite lookup_insert_ne in Hj; [|by apply not_eq_sym].
      by apply (Hlive j qj).
Qed.

Lemma icM_wf_delete (M : gmap nat (Qp * nat)) (k : nat) :
  icM_wf M -> icM_wf (delete k M).
Proof.
  intros (Hdom & Hcnt & Hlive). split; [|split].
  - intros j [x Hj]. rewrite lookup_delete_Some in Hj.
    apply Hdom. exists x. apply Hj.
  - intros j qj nj Hj. rewrite lookup_delete_Some in Hj.
    by apply (Hcnt j qj), Hj.
  - intros j qj nj Hj. rewrite lookup_delete_Some in Hj.
    by apply (Hlive j qj), Hj.
Qed.

(* the count component's [⋅] IS [Nat.add]; naming it lets [lia] see the
   arithmetic in the local-update side conditions *)
Lemma ic_nat_op_add (a b : nat) : (a ⋅ b) = (a + b)%nat.
Proof. reflexivity. Qed.

(* ---- the cache-HIT increment, as pure algebra (BioInv.bio_incr_lu) ----

   iget's hit arm runs [ref++] holding NO reference of its own, so unlike
   [iref_dup_step] (idup's shape) nothing can come out of a caller's
   fragment: the entry GROWS by exactly the minted [(qn,1)], taken from the
   share the table retained.  That makes the update an allocation keyed
   pointwise rather than a [singleton_local_update].

   Stated OUTSIDE the Iris section so the [own_update] below is handed a
   CLOSED update -- BioInv.v's header explains why an evar-headed target
   makes [apply auth_update_alloc] search forever. *)
Local Lemma ic_incr_lu (M : gmap nat (Qp * nat)) (k : nat)
    (qt qn : Qp) (n : nat) :
  M !! k = Some (qt, n) ->
  ✓ (qt + qn)%Qp ->
  @local_update _ (gmapUR nat (prodR fracR natR))
    (M, ∅) (<[k := ((qt + qn)%Qp, S n)]> M, {[ k := (qn, 1%nat) ]}).
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
  rewrite -Some_op -pair_op frac_op ic_nat_op_add.
  by rewrite (Qp.add_comm qn qt) Nat.add_1_l.
Qed.

Local Lemma ic_incr_upd (M : gmap nat (Qp * nat)) (k : nat)
    (qt qn : Qp) (n : nat) :
  M !! k = Some (qt, n) ->
  ✓ (qt + qn)%Qp ->
  (● M : icacheUR) ~~>
  ● (<[k := ((qt + qn)%Qp, S n)]> M) ⋅ ◯ {[ k := (qn, 1%nat) ]}.
Proof. intros HM Hq. apply auth_update_alloc. by apply ic_incr_lu. Qed.

(* the first reference's allocation, likewise closed (§13.1b's budget makes
   the minted fraction a parameter, so the caller's [1/2 - q] side of the
   split is what fixes it) *)
Local Lemma ic_alloc_upd (M : gmap nat (Qp * nat)) (k : nat) (q : Qp) :
  M !! k = None ->
  ✓ q ->
  (● M : icacheUR) ~~>
  ● (<[k := (q, 1%nat)]> M) ⋅ ◯ {[ k := (q, 1%nat) ]}.
Proof.
  intros HM Hq. apply auth_update_alloc.
  apply (alloc_singleton_local_update _ k (q, 1%nat)); [done|].
  split; [exact Hq | done].
Qed.

(* the ref word of a LIVE slot is positive and in range: precisely the two
   bounds [InodeLock.inode_ref_spos] turns into "the panic is dead".  The
   LOWER bound is [icM_wf]'s third conjunct -- at [natR] the type no longer
   supplies it. *)
Lemma iref_word_live (M : gmap nat (Qp * nat)) (k : nat) (q : Qp) (n : nat) :
  icM_wf M -> M !! k = Some (q, n) ->
  0 < bv_unsigned (iref_word M k) < 2 ^ 31.
Proof.
  intros Hwf HM.
  pose proof (icM_wf_count M k q n Hwf HM) as Hn.
  pose proof (icM_wf_live M k q n Hwf HM) as Hlo.
  assert (E31 : (2 ^ 31 = 2147483648)%Z) by (vm_compute; reflexivity).
  assert (E32 : (2 ^ 32 = 4294967296)%Z) by (vm_compute; reflexivity).
  rewrite E31 in Hn.
  rewrite /iref_word HM moi32_small; [|rewrite E32; lia].
  rewrite E31. split; lia.
Qed.

Section IcacheGhost.
  Context `{!icacheG Σ}.

  (* HALF the authority.  The other half is the other one: the itable
     lock's resource and the [ref]-word invariant hold one each, so neither
     can move [M] alone, and the lock holder's half PINS every count across
     the [lw; addiw; sw] the code performs. *)
  Definition itable_half (γ : gname) (M : gmap nat (Qp * nat)) : iProp Σ :=
    own γ (●{#(1/2)} M).

  (* A fragment at slot [k]: [q] of the identity fields, carrying [c]
     logical references.  Only [c = 1] and [c = 0] are ever used, and they
     have names; the general form exists so the lookup lemma below is one
     lemma rather than a cross-product. *)
  Definition iref_frag (γ : gname) (k : nat) (q : Qp) (c : nat) : iProp Σ :=
    own γ (◯ {[ k := (q, c) ]}).

  (* ONE reference to slot [k], holding fraction [q] of its identity. *)
  Definition iref_tok (γ : gname) (k : nat) (q : Qp) : iProp Σ :=
    iref_frag γ k q 1.

  (* [q] OF SOMEBODY ELSE'S reference: enough to read [ip->dev]/[ip->inum]
     and to know the slot is live, but it is not a reference and closing it
     is not an [iput].  This is what every fd sharing a [struct file] holds,
     and what an [ilock] caller needs (see the algebra's header). *)
  Definition iref_share (γ : gname) (k : nat) (q : Qp) : iProp Σ :=
    iref_frag γ k q 0.

  Global Instance itable_half_timeless γ M : Timeless (itable_half γ M).
  Proof. apply _. Qed.
  Global Instance iref_frag_timeless γ k q c : Timeless (iref_frag γ k q c).
  Proof. apply _. Qed.
  Global Instance iref_tok_timeless γ k q : Timeless (iref_tok γ k q).
  Proof. apply _. Qed.
  Global Instance iref_share_timeless γ k q : Timeless (iref_share γ k q).
  Proof. apply _. Qed.

  (* THE SPLIT THE FILE TABLE NEEDS, and the whole reason for [natR]: the
     fraction divides, the reference does not. *)
  Lemma iref_frag_op γ k q1 c1 q2 c2 :
    iref_frag γ k (q1 + q2) (c1 + c2) ⊣⊢
    iref_frag γ k q1 c1 ∗ iref_frag γ k q2 c2.
  Proof.
    rewrite /iref_frag -own_op -auth_frag_op singleton_op -pair_op frac_op.
    by rewrite ic_nat_op_add.
  Qed.

  Lemma iref_share_split γ k q1 q2 :
    iref_share γ k (q1 + q2) ⊣⊢ iref_share γ k q1 ∗ iref_share γ k q2.
  Proof. rewrite /iref_share -(iref_frag_op γ k q1 0 q2 0). done. Qed.

  Lemma iref_tok_split_share γ k q1 q2 :
    iref_tok γ k (q1 + q2) ⊣⊢ iref_tok γ k q1 ∗ iref_share γ k q2.
  Proof. rewrite /iref_tok /iref_share -(iref_frag_op γ k q1 1 q2 0). done. Qed.

  Lemma itable_half_agree γ M1 M2 :
    itable_half γ M1 -∗ itable_half γ M2 -∗ ⌜M1 = M2⌝.
  Proof.
    rewrite /itable_half. iIntros "H1 H2".
    iDestruct (own_valid_2 with "H1 H2") as %Hv.
    iPureIntro.
    apply auth_auth_dfrac_op_valid in Hv as (_ & Heq & _).
    by apply leibniz_equiv.
  Qed.

  (* the two halves ARE the authority: this is how a lock holder that has
     opened the [ref]-word invariant gets the right to update. *)
  Lemma itable_half_op γ M :
    itable_half γ M ∗ itable_half γ M ⊣⊢ own γ (● M).
  Proof.
    rewrite /itable_half -own_op -auth_auth_dfrac_op dfrac_op_own Qp.half_half.
    done.
  Qed.

  Lemma itable_half_join γ M :
    itable_half γ M -∗ itable_half γ M -∗ own γ (● M).
  Proof.
    iIntros "H1 H2". iApply itable_half_op. iFrame.
  Qed.

  Lemma itable_half_split γ M :
    own γ (● M) -∗ itable_half γ M ∗ itable_half γ M.
  Proof. iIntros "H". by iApply itable_half_op. Qed.

  (* ------------------------------------------------------------------ *)
  (*  REF-1 EXCLUSIVITY -- the algebraic half of iput's theorem           *)
  (* ------------------------------------------------------------------ *)

  (* ANY fragment read against EITHER half of the authority.  The last
     conjunct is the one the whole design turns on, and at [natR] it is the
     ONLY surviving direction: a fragment holding the ENTIRE outstanding
     share of the identity carries every reference there is.  Its converse
     -- "count one implies the whole share" -- was true at [positiveR] and
     is FALSE here, because a count-1 fragment may now sit beside shares.
     That is the right way round for the consumer: iput's last closer
     rejoins all the shares to [qt] FIRST, and only then learns it is
     alone.

     The [q ≤ qt] / [c ≤ n] conjuncts are the ordinary monotonicity a
     reader needs to know its slot is live. *)
  Lemma iref_frag_lookup γ M k q c :
    itable_half γ M -∗ iref_frag γ k q c -∗
    ⌜∃ (qt : Qp) (n : nat), M !! k = Some (qt, n) /\ (qt ≤ 1)%Qp /\
       (q ≤ qt)%Qp /\ (c <= n)%nat /\ (q = qt -> n = c)⌝.
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
      assert (Hq' : q = qt) by exact Hq. assert (Hn' : c = n) by exact Hn.
      subst. split; [reflexivity | split; [lia | by intros _]].
    - apply pair_included in Hlt as [Hq Hn]; cbn in Hq, Hn.
      apply frac_included in Hq. apply nat_included in Hn.
      split; [by apply Qp.lt_le_incl | split; [exact Hn|]].
      intros Hc. exfalso. rewrite Hc in Hq. by apply (irreflexivity Qp.lt qt).
  Qed.

  (* the two named instances *)
  Lemma iref_lookup γ M k q :
    itable_half γ M -∗ iref_tok γ k q -∗
    ⌜∃ (qt : Qp) (n : nat), M !! k = Some (qt, n) /\ (qt ≤ 1)%Qp /\
       (q ≤ qt)%Qp /\ (1 <= n)%nat /\ (q = qt -> n = 1%nat)⌝.
  Proof. iIntros "Ha Hf". iApply (iref_frag_lookup with "Ha Hf"). Qed.

  Lemma iref_share_lookup γ M k q :
    itable_half γ M -∗ iref_share γ k q -∗
    ⌜∃ (qt : Qp) (n : nat), M !! k = Some (qt, n) /\ (qt ≤ 1)%Qp /\
       (q ≤ qt)%Qp⌝.
  Proof.
    iIntros "Ha Hf".
    iDestruct (iref_frag_lookup with "Ha Hf") as %(qt & n & ? & ? & ? & _).
    iPureIntro. by exists qt, n.
  Qed.

  (* A reference fragment against an authority showing NO reference at all:
     the refutation every AUTHORITY-SIDE opener uses (design §10.3 -- iget's
     recycle holds [itable.lock] at [M !! k = None] and refutes the escrow's
     checked-out arm with this, holding no checkout token of its own).
     BioInv.bref_tok_free_absurd's mirror, against the HALF authority --
     [singleton_included_l] reads through any dfrac, exactly as in
     [iref_lookup] above. *)
  Lemma iref_frag_free_absurd γ M k q c :
    M !! k = None ->
    itable_half γ M -∗ iref_frag γ k q c -∗ False.
  Proof.
    rewrite /itable_half /iref_frag. iIntros (HM) "Ha Hf".
    iDestruct (own_valid_2 with "Ha Hf")
      as %[_ [Hincl _]]%auth_both_dfrac_valid_discrete.
    iPureIntro.
    apply singleton_included_l in Hincl as [y [Hy _]].
    rewrite HM in Hy. inversion Hy.
  Qed.

  Lemma iref_tok_free_absurd γ M k q :
    M !! k = None ->
    itable_half γ M -∗ iref_tok γ k q -∗ False.
  Proof. apply iref_frag_free_absurd. Qed.

  Lemma iref_share_free_absurd γ M k q :
    M !! k = None ->
    itable_half γ M -∗ iref_share γ k q -∗ False.
  Proof. apply iref_frag_free_absurd. Qed.

  (* TWO reference fragments at one slot force the count to be at least two.
     This is REF-1 EXCLUSIVITY used as a refutation rather than as a
     conclusion: a thread that has read [ip->ref == 1] (so [n = 1]) and
     holds one reference can rule out the existence of any second one --
     which is how iput's authority-side opening of the escrow kills the
     checked-out arm.  The count component's inclusion is the whole content:
     [(q1,1) ⋅ (q2,1) = (q1+q2, 2)], and note that a SHARE beside a
     reference proves nothing of the kind -- [(q,0)] adds nothing to the
     count, which is exactly what makes shares safe to hand out. *)
  Lemma iref_tok_two_lookup γ M k q1 q2 :
    itable_half γ M -∗ iref_tok γ k q1 -∗ iref_tok γ k q2 -∗
    ⌜∃ (qt : Qp) (n : nat), M !! k = Some (qt, n) /\ (2 <= n)%nat⌝.
  Proof.
    iIntros "Ha H1 H2".
    iAssert (iref_frag γ k (q1 + q2)%Qp (1 + 1)) with "[H1 H2]" as "Hf".
    { rewrite (iref_frag_op γ k q1 1 q2 1). iFrame. }
    iDestruct (iref_frag_lookup with "Ha Hf") as %(qt & n & HM & _ & _ & Hn & _).
    iPureIntro. exists qt, n. split; [exact HM | exact Hn].
  Qed.

  (* a fragment's slot is in range -- what the scan's index bound needs *)
  Lemma iref_frag_in_range γ M k q c :
    icM_wf M -> itable_half γ M -∗ iref_frag γ k q c -∗ ⌜(k < NINODE)%nat⌝.
  Proof.
    intros [Hdom _]. iIntros "Ha Hf".
    iDestruct (iref_frag_lookup with "Ha Hf") as %(qt & n & HM & _).
    iPureIntro. apply Hdom. by eexists.
  Qed.

  Lemma iref_tok_in_range γ M k q :
    icM_wf M -> itable_half γ M -∗ iref_tok γ k q -∗ ⌜(k < NINODE)%nat⌝.
  Proof. apply iref_frag_in_range. Qed.

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
  Lemma iref_alloc_step γ M k (q : Qp) :
    M !! k = None ->
    (q ≤ 1/2)%Qp ->
    own γ (● M) ==∗
    own γ (● (<[k := (q, 1%nat)]> M)) ∗ iref_tok γ k q.
  Proof.
    iIntros (HM Hq) "Ha".
    assert (Hv : ✓ q).
    { apply frac_valid. etrans; [exact Hq | compute_done]. }
    iMod (own_update _ _ _ (ic_alloc_upd M k q HM Hv) with "Ha") as "H".
    rewrite own_op. iDestruct "H" as "[$ $]". done.
  Qed.

  (* iget's cache-HIT arm: [ref++] on a live entry, minting a fresh
     reference at fraction [qn] taken from the table's RETAINED share.  The
     incrementer holds no reference of its own, so the entry grows by exactly
     the minted amount -- BioInv.bio_incr_step verbatim. *)
  Lemma iref_incr_step γ M k qt (n : nat) (qn : Qp) :
    M !! k = Some (qt, n) ->
    ✓ (qt + qn)%Qp ->
    own γ (● M) ==∗
    own γ (● (<[k := ((qt + qn)%Qp, S n)]> M)) ∗ iref_tok γ k qn.
  Proof.
    iIntros (HM Hq) "Ha". rewrite /iref_tok /iref_frag.
    iMod (own_update _ _ _ (ic_incr_upd M k qt qn n HM Hq) with "Ha") as "H".
    rewrite own_op. iDestruct "H" as "[$ $]". done.
  Qed.

  (* idup, and iget's cache-hit arm: [ref++].  The new reference's fraction
     comes out of the CALLER's own -- nothing is conjured, which is why the
     invariant's leftover share is untouched. *)
  Lemma iref_dup_step γ M k q qt (n : nat) :
    M !! k = Some (qt, n) ->
    own γ (● M) -∗ iref_tok γ k q ==∗
    own γ (● (<[k := (qt, S n)]> M)) ∗
    iref_tok γ k (q/2)%Qp ∗ iref_tok γ k (q/2)%Qp.
  Proof.
    iIntros (HM) "Ha Hf".
    iMod (own_update_2 _ _ _ (● (<[k := (qt, S n)]> M)
                              ⋅ ◯ {[k := (q, 2%nat)]}) with "Ha Hf") as "H".
    { apply auth_update.
      apply (singleton_local_update _ k (qt, n) (q, 1%nat)
                                      (qt, S n) (q, 2%nat) HM).
      apply local_update_discrete. intros mz Hv Hz.
      destruct Hv as [Hvq Hvn]. split; [by split|].
      destruct mz as [[qf nf]|]; destruct Hz as [Hq Hn]; simpl in Hq, Hn.
      - split; simpl; [exact Hq|].
        assert (Hn' : n = (1 + nf)%nat) by exact Hn.
        assert (Hg : S n = (2 + nf)%nat) by lia.
        rewrite ic_nat_op_add. exact Hg.
      - split; simpl; [exact Hq|]. by rewrite Hn. }
    rewrite own_op. iDestruct "H" as "[$ Hfrag]".
    rewrite /iref_tok /iref_frag.
    assert (Hsp : ({[k := (q, 2%nat)]} : gmap nat (Qp * nat))
                  = {[k := ((q/2)%Qp, 1%nat)]} ⋅ {[k := ((q/2)%Qp, 1%nat)]}).
    { rewrite singleton_op. f_equal. rewrite -pair_op.
      by rewrite frac_op Qp.div_2. }
    rewrite Hsp auth_frag_op own_op. iDestruct "Hfrag" as "[$ $]". done.
  Qed.

  (* iput, [--ref > 0]: the departing reference's fraction has to go
     SOMEWHERE, and it goes back into the outstanding total.  That is why
     the frac component tracks OUTSTANDING share rather than being pinned
     at 1. *)
  Lemma iref_close_step γ M k q qt (n : nat) (qr : Qp) :
    M !! k = Some (qt, S n) ->
    (qt - q)%Qp = Some qr ->
    own γ (● M) -∗ iref_tok γ k q ==∗ own γ (● (<[k := (qr, n)]> M)).
  Proof.
    iIntros (HM Hsub) "Ha Hf".
    apply Qp.sub_Some in Hsub.       (* qt = q + qr *)
    iApply (own_update_2 _ _ _ (● (<[k := (qr, n)]> M)) with "Ha Hf").
    apply auth_update_dealloc, gmap_local_update. intros i.
    destruct (decide (i = k)) as [->|Hne]; last first.
    { assert (Hki : k <> i) by auto.
      pose proof (lookup_singleton_ne (M:=gmap nat) k i (q, 1%nat) Hki) as Hs.
      pose proof (lookup_insert_ne M k i (qr, n) Hki) as Hm.
      apply local_update_discrete. intros mz Hv Hz.
      rewrite Hs in Hz. rewrite Hm. split; [exact Hv | exact Hz]. }
    pose proof (lookup_singleton (M:=gmap nat) k (q, 1%nat)) as Hs.
    pose proof (lookup_insert M k (qr, n)) as Hm.
    apply local_update_discrete. intros mz Hv Hz.
    rewrite HM in Hz, Hv. rewrite Hs in Hz. rewrite Hm.
    (* the two frame-free cases are killed by the FRACTION, not by the
       count: at [natR] "the count was 1" is no contradiction, but
       [qt = q + qr] is one -- [Qp] has no zero. *)
    destruct mz as [[[qf nf]|]|]; simpl in Hz.
    - apply Some_equiv_inj in Hz. destruct Hz as [Hq Hn]; simpl in Hq, Hn.
      rewrite ic_nat_op_add in Hn.
      assert (Hn' : S n = (1 + nf)%nat) by exact Hn.
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
      destruct Hz as [Hq _]; simpl in Hq.
      assert (Hq' : qt = q) by exact Hq.
      rewrite Hsub in Hq'. by apply (Qp.add_id_free q qr).
    - exfalso. apply Some_equiv_inj in Hz.
      destruct Hz as [Hq _]; simpl in Hq.
      assert (Hq' : qt = q) by exact Hq.
      rewrite Hsub in Hq'. by apply (Qp.add_id_free q qr).
  Qed.

  (* iput, [--ref == 0]: the entry is DELETED.  Stated at an arbitrary [qt]
     -- the [qt = 1] version is unusable, because after any earlier close
     the outstanding total has already shrunk.  What makes this closer the
     last one is the FRACTION: it holds [qt], the entry's WHOLE outstanding
     share, and [Qp] has no zero, so no frame can sit beside it.  At
     [positiveR] the count could have carried this argument too; at [natR]
     it cannot, because a count-0 frame -- a share held by somebody else --
     is exactly the thing that must be ruled out, and only the fraction
     rules it out.  That is why the caller must REJOIN every share first:
     [iref_lookup]'s surviving direction, [q = qt -> n = 1]. *)
  Lemma iref_close_last_step γ M k (qt : Qp) (n : nat) :
    M !! k = Some (qt, n) ->
    own γ (● M) -∗ iref_tok γ k qt ==∗ own γ (● (delete k M)).
  Proof.
    iIntros (HM) "Ha Hf".
    iApply (own_update_2 _ _ _ (● (delete k M)) with "Ha Hf").
    apply auth_update_dealloc, gmap_local_update. intros i.
    destruct (decide (i = k)) as [->|Hne]; last first.
    { assert (Hki : k <> i) by auto.
      pose proof (lookup_singleton_ne (M:=gmap nat) k i (qt, 1%nat) Hki) as Hs.
      pose proof (lookup_delete_ne M k i Hki) as Hm.
      apply local_update_discrete. intros mz Hv Hz.
      rewrite Hs in Hz. rewrite Hm. split; [exact Hv | exact Hz]. }
    pose proof (lookup_singleton (M:=gmap nat) k (qt, 1%nat)) as Hs.
    pose proof (lookup_delete M k) as Hm.
    apply local_update_discrete. intros mz Hv Hz.
    rewrite HM in Hz. rewrite Hs in Hz. rewrite Hm.
    destruct mz as [[[qf nf]|]|]; simpl in Hz.
    - exfalso. apply Some_equiv_inj in Hz. destruct Hz as [Hq _]; simpl in Hq.
      rewrite frac_op in Hq.
      assert (Hq' : qt = (qt + qf)%Qp) by exact Hq.
      apply (Qp.add_id_free qt qf). by rewrite -Hq'.
    - split; done.
    - split; done.
  Qed.

End IcacheGhost.

(* ===================================================================== *)
(*  5.  THE [ref] WORDS: A SHARED INVARIANT, NOT THE LOCK'S RESOURCE      *)
(* ===================================================================== *)

Section IcacheRefInv.
  Context `{!riscvGS Σ, !icacheG Σ}.
  Context `{GEN : GenId}.

  Definition icacheN : namespace := nroot .@ "icache".

  Definition iref_cells (M : gmap nat (Qp * nat)) : iProp Σ :=
    ([∗ list] k ∈ seq 0 NINODE, i_ref (ientry k) ↦₄ iref_word M k)%I.

  (* The invariant's half of the authority sits BESIDE the cells, so the
     cells and the counts can never disagree, and a thread holding the
     other half (the itable lock's) is the only one that can move either. *)
  Definition itable_body (γ : gname) : iProp Σ :=
    (∃ M : gmap nat (Qp * nat),
       itable_half γ M ∗ ⌜icM_wf M⌝ ∗ iref_cells M)%I.

  Definition itable_inv (γ : gname) : iProp Σ := inv icacheN (itable_body γ).

  Global Instance itable_inv_persistent γ : Persistent (itable_inv γ).
  Proof. apply _. Qed.

  Local Lemma seq_ninode_lookup (k : nat) :
    (k < NINODE)%nat -> seq 0 NINODE !! k = Some k.
  Proof. intros Hk. apply lookup_seq. split; [lia|exact Hk]. Qed.

  Lemma iref_cells_acc (M : gmap nat (Qp * nat)) (k : nat) :
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
  Lemma iref_cells_acc_upd (M : gmap nat (Qp * nat)) (k : nat) :
    (k < NINODE)%nat ->
    iref_cells M -∗
      i_ref (ientry k) ↦₄ iref_word M k ∗
      (∀ e : Qp * nat,
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
     [Ψ v := ⌜0 < bv_unsigned v < 2^31⌝ ∗ iref_tok γ k q].

     The two bounds are exactly what [InodeLock.inode_ref_spos] turns into
     "[bge x0,a5] falls through", i.e. into "the panic is dead" -- so this
     lemma REPLACES [SpecIlock.v]'s [i_ref ip ↦₄{dqr} refv] premise, which
     no icache can supply (see the file header and the design note).       *)
  Lemma iref_load_au (Eo : coPset) (γ : gname) (k : nat) (q : Qp) :
    ↑icacheN ⊆ Eo ->
    itable_inv γ -∗ iref_tok γ k q -∗
    |={Eo, Eo ∖ ↑icacheN}=> ∃ v : mword 32,
      i_ref (ientry k) ↦₄ v ∗
      (i_ref (ientry k) ↦₄ v ={Eo ∖ ↑icacheN, Eo}=∗
         ⌜0 < bv_unsigned v < 2 ^ 31⌝ ∗ iref_tok γ k q).
  Proof.
    iIntros (HE) "#Hinv Htok".
    iMod (inv_acc Eo icacheN with "Hinv") as "[Hbody Hclose]"; [exact HE|].
    iDestruct "Hbody" as (M) "(>Ha & >%Hwf & >Hcells)".
    iDestruct (iref_lookup with "Ha Htok") as %(qt & n & HMk & _ & _ & _ & _).
    assert (Hk : (k < NINODE)%nat) by (apply (proj1 Hwf); by eexists).
    iDestruct (iref_cells_acc M k Hk with "Hcells") as "[Hcell Hback]".
    iModIntro. iExists (iref_word M k). iFrame "Hcell".
    iIntros "Hcell".
    iMod ("Hclose" with "[Ha Hcell Hback]") as "_".
    { iNext. iExists M. iFrame "Ha". iSplitR; [iPureIntro; exact Hwf|].
      iApply ("Hback" with "Hcell"). }
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
  Lemma iref_load_locked_au (Eo : coPset) (γ : gname)
      (M : gmap nat (Qp * nat)) (k : nat) :
    ↑icacheN ⊆ Eo -> (k < NINODE)%nat ->
    itable_inv γ -∗ itable_half γ M -∗
    |={Eo, Eo ∖ ↑icacheN}=>
      i_ref (ientry k) ↦₄ iref_word M k ∗
      (i_ref (ientry k) ↦₄ iref_word M k ={Eo ∖ ↑icacheN, Eo}=∗ itable_half γ M).
  Proof.
    iIntros (HE Hk) "#Hinv Hhalf".
    iMod (inv_acc Eo icacheN with "Hinv") as "[Hbody Hclose]"; [exact HE|].
    iDestruct "Hbody" as (M') "(>Ha & >%Hwf & >Hcells)".
    iDestruct (itable_half_agree with "Ha Hhalf") as %->.
    iDestruct (iref_cells_acc M k Hk with "Hcells") as "[Hcell Hback]".
    iModIntro. iFrame "Hcell". iIntros "Hcell".
    iMod ("Hclose" with "[Ha Hcell Hback]") as "_".
    { iNext. iExists M. iFrame "Ha". iSplitR; [iPureIntro; exact Hwf|].
      iApply ("Hback" with "Hcell"). }
    iModIntro. iFrame.
  Qed.

  (* THE WRITE.  The [sw] and the ghost step happen in the SAME invariant
     opening, which is the whole reason the read-modify-write is atomic in
     the proof: the lock's half stops any other thread moving [M], and the
     two halves meet only here, which is exactly the moment the physical
     word changes.  [Hno] -- that the incremented count is still an [int] --
     is what re-establishes [icM_wf]; it is NOT provable here and comes from
     the caller's [IrefSlots.iref_slots_no_overflow]. *)
  Lemma iref_dup_store_au (Eo : coPset) (γ : gname)
      (M : gmap nat (Qp * nat)) (k : nat) (q qt : Qp) (n : nat) :
    ↑icacheN ⊆ Eo ->
    M !! k = Some (qt, n) ->
    (Z.of_nat (S n) < 2 ^ 31)%Z ->
    itable_inv γ -∗ itable_half γ M -∗ iref_tok γ k q -∗
    |={Eo, Eo ∖ ↑icacheN}=>
      i_ref (ientry k) ↦₄ iref_word M k ∗
      (i_ref (ientry k) ↦₄ (mword_of_int (Z.of_nat (S n)) : mword 32)
         ={Eo ∖ ↑icacheN, Eo}=∗
         itable_half γ (<[k := (qt, S n)]> M) ∗
         iref_tok γ k (q/2)%Qp ∗ iref_tok γ k (q/2)%Qp).
  Proof.
    iIntros (HE HMk Hno) "#Hinv Hhalf Htok".
    iMod (inv_acc Eo icacheN with "Hinv") as "[Hbody Hclose]"; [exact HE|].
    iDestruct "Hbody" as (M') "(>Ha & >%Hwf & >Hcells)".
    iDestruct (itable_half_agree with "Ha Hhalf") as %->.
    assert (Hk : (k < NINODE)%nat) by (apply (proj1 Hwf); by eexists).
    iDestruct (iref_cells_acc_upd M k Hk with "Hcells") as "[Hcell Hback]".
    iModIntro. iFrame "Hcell". iIntros "Hcell".
    iDestruct (itable_half_join with "Ha Hhalf") as "Hauth".
    iMod (iref_dup_step γ M k q qt n HMk with "Hauth Htok") as "(Hauth & Ht1 & Ht2)".
    iDestruct (itable_half_split with "Hauth") as "[Ha Hhalf]".
    iMod ("Hclose" with "[Ha Hcell Hback]") as "_".
    { iNext. iExists (<[k := (qt, S n)]> M). iFrame "Ha".
      iSplitR.
      { iPureIntro. apply (icM_wf_insert M k qt (S n) Hwf Hk Hno). lia. }
      iApply ("Hback" $! (qt, S n)).
      rewrite /iref_word lookup_insert. iExact "Hcell". }
    iModIntro. iFrame.
  Qed.

End IcacheRefInv.

(* ===================================================================== *)
(*  6.  THE itable LOCK'S RESOURCE: dev / inum, AND WHAT A REFERENCE IS   *)
(* ===================================================================== *)

Section IcacheTable.
  Context `{!riscvGS Σ, !lockG Σ, !icacheG Σ, !irefslotG Σ}.
  Context `{GEN : GenId}.

  (* An entry's IDENTITY -- the two cells iget writes into a recycled slot
     and nobody writes again while the slot is live.  Fractional, so a
     reference holder reads [ip->dev] / [ip->inum] with no lock at all,
     which is what ilock's contract already assumes of them. *)
  Definition inode_ident (k : nat) (dq : dfrac) (dev inum : mword 32) : iProp Σ :=
    (i_dev (ientry k) ↦₄{dq} dev ∗ i_inum (ientry k) ↦₄{dq} inum)%I.

  Lemma inode_ident_agree k dq1 d1 n1 dq2 d2 n2 :
    inode_ident k dq1 d1 n1 -∗ inode_ident k dq2 d2 n2 -∗ ⌜d1 = d2 /\ n1 = n2⌝.
  Proof.
    iIntros "[Hd1 Hn1] [Hd2 Hn2]".
    iDestruct (word4_pointsto_agree with "Hd1 Hd2") as %->.
    iDestruct (word4_pointsto_agree with "Hn1 Hn2") as %->.
    done.
  Qed.

  (* the fraction JOIN for one cell, as a wand.  A bare
     [rewrite word4_pointsto_frac_split] at a call site rewrites the whole
     [envs_entails] -- hypotheses included -- and silently re-splits the very
     fragments being joined (durable-notes' proofmode rule); inside this
     lemma the two hypotheses' dfracs are bare variables, so the pattern
     matches the goal only. *)
  Local Lemma word4_frac_join (a : Arch.pa) (q1 q2 : Qp) (w : bv 32) :
    a ↦₄{DfracOwn q1} w -∗ a ↦₄{DfracOwn q2} w -∗ a ↦₄{DfracOwn (q1 + q2)} w.
  Proof. iIntros "H1 H2". rewrite word4_pointsto_frac_split. iFrame. Qed.

  Lemma inode_ident_split k q1 q2 dev inum :
    inode_ident k (DfracOwn (q1 + q2)) dev inum ⊣⊢
    inode_ident k (DfracOwn q1) dev inum ∗ inode_ident k (DfracOwn q2) dev inum.
  Proof.
    rewrite /inode_ident !word4_pointsto_frac_split.
    iSplit; [iIntros "[[$ $] [$ $]]" | iIntros "[[$ $] [$ $]]"].
  Qed.

  (* HOLDING ONE REFERENCE to itable slot [k].  This is the predicate
     [FileInv.inode_ref] is today a [emp] placeholder for -- note it needs
     no inode POINTER argument beyond the slot, because [ientry] determines
     the address and [ientry_inj] determines the slot. *)
  Definition inode_ref (γ : gname) (k : nat) (q : Qp)
      (dev inum : mword 32) : iProp Σ :=
    (iref_tok γ k q ∗ inode_ident k (DfracOwn q) dev inum)%I.

  (* [q] OF SOMEBODY ELSE'S REFERENCE, at the points-to level: the identity
     cells at [q] and a count-0 fragment.  This is what an fd holds of its
     [struct file]'s inode, and what [ilock] takes -- see the algebra's
     header for why taking an [inode_ref] there is a mis-specification. *)
  Definition inode_shr (γ : gname) (k : nat) (q : Qp)
      (dev inum : mword 32) : iProp Σ :=
    (iref_share γ k q ∗ inode_ident k (DfracOwn q) dev inum)%I.

  (* two holders of one entry see the same inode -- for free, from the
     fractional cells; no [agree] ghost is needed *)
  Lemma inode_ident_of_ref γ k q d i :
    inode_ref γ k q d i -∗ inode_ident k (DfracOwn q) d i.
  Proof. by iIntros "[_ $]". Qed.

  Lemma inode_ident_of_shr γ k q d i :
    inode_shr γ k q d i -∗ inode_ident k (DfracOwn q) d i.
  Proof. by iIntros "[_ $]". Qed.

  Lemma inode_ref_agree γ k q1 d1 n1 q2 d2 n2 :
    inode_ref γ k q1 d1 n1 -∗ inode_ref γ k q2 d2 n2 -∗ ⌜d1 = d2 /\ n1 = n2⌝.
  Proof.
    iIntros "[_ H1] [_ H2]". iApply (inode_ident_agree with "H1 H2").
  Qed.

  Lemma inode_shr_agree γ k q1 d1 n1 q2 d2 n2 :
    inode_shr γ k q1 d1 n1 -∗ inode_shr γ k q2 d2 n2 -∗ ⌜d1 = d2 /\ n1 = n2⌝.
  Proof.
    iIntros "[_ H1] [_ H2]". iApply (inode_ident_agree with "H1 H2").
  Qed.

  Lemma inode_ref_shr_agree γ k q1 d1 n1 q2 d2 n2 :
    inode_ref γ k q1 d1 n1 -∗ inode_shr γ k q2 d2 n2 -∗ ⌜d1 = d2 /\ n1 = n2⌝.
  Proof.
    iIntros "[_ H1] [_ H2]". iApply (inode_ident_agree with "H1 H2").
  Qed.

  (* ---- SHARING A REFERENCE, at the points-to level -------------------

     THIS is what [FileInv.file_payload]'s FD_INODE arm needs and what the
     [positiveR] count made impossible: the identity fraction splits, the
     reference itself does not move.  Rejoining is the last closer's step
     and is what restores an [inode_ref] fit for [iput]. *)
  Lemma inode_shr_split γ k q1 q2 dev inum :
    inode_shr γ k (q1 + q2) dev inum ⊣⊢
    inode_shr γ k q1 dev inum ∗ inode_shr γ k q2 dev inum.
  Proof.
    rewrite /inode_shr iref_share_split inode_ident_split.
    iSplit; [iIntros "[[$ $] [$ $]]" | iIntros "[[$ $] [$ $]]"].
  Qed.

  Lemma inode_ref_split_shr γ k q1 q2 dev inum :
    inode_ref γ k (q1 + q2) dev inum ⊣⊢
    inode_ref γ k q1 dev inum ∗ inode_shr γ k q2 dev inum.
  Proof.
    rewrite /inode_ref /inode_shr iref_tok_split_share inode_ident_split.
    iSplit; [iIntros "[[$ $] [$ $]]" | iIntros "[[$ $] [$ $]]"].
  Qed.

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

     and a reference's fraction therefore ranges in (0, ½].  The table's
     retained share is now an [inode_ident] like every other share.

     [islot_rest_at] pins the two values (the pool's slot->inum map wants
     them pinned, §13.2); [islot_rest] is the ∃-bound form the plain
     [itable_res] uses.  The [Qp.sub] shape is unchanged: [None] is the
     [q = ½] case, where the whole shared half is out and the table keeps
     nothing of either cell. *)
  Definition islot_rest_at (k : nat) (q : Qp) (dev inum : mword 32) : iProp Σ :=
    match (1/2 - q)%Qp with
    | Some q' => inode_ident k (DfracOwn q') dev inum
    | None => emp%I
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
  Definition islot (M : gmap nat (Qp * nat)) (k : nat) : iProp Σ :=
    match M !! k with
    | None => islot_free k
    | Some (q, n) => (islot_rest k q ∗ iref_slots n)%I
    end.

  Definition itable_res (γ : gname) : iProp Σ :=
    (∃ M : gmap nat (Qp * nat),
       itable_half γ M ∗ ⌜icM_wf M⌝ ∗ iref_slots_auth ∗
       [∗ list] k ∈ seq 0 NINODE, islot M k)%I.

  Definition is_itable (γl γ : gname) : iProp Σ :=
    is_lock γl itable_lock "itable"%string (itable_res γ).

  Global Instance is_itable_persistent γl γ : Persistent (is_itable γl γ).
  Proof. apply _. Qed.

  (* The lock resource's slot accessor, in the form a WRITER needs: the map
     may come back CHANGED, provided it changed only at [k].  Same shape and
     same proof as [iref_cells_acc_upd] one section up -- [big_sepL_delete]
     splits index [k] off, and the element of [seq 0 NINODE] at index [j]
     being [j] is what turns "index ≠ k" into "this slot did not move". *)
  Lemma islots_acc_upd (M : gmap nat (Qp * nat)) (k : nat) :
    (k < NINODE)%nat ->
    ([∗ list] j ∈ seq 0 NINODE, islot M j) -∗
      islot M k ∗
      (∀ M' : gmap nat (Qp * nat),
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
     the points-to level.  The closer arrives holding [qt] -- it has
     rejoined every share -- and [iref_lookup] then says its count is one,
     so the closer's share plus whatever the table kept is
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
    - apply Qp.sub_None in Et.
      assert (qt = (1/2)%Qp) as -> by
        (apply (anti_symm (≤)%Qp); [exact Hle | exact Et]).
      iIntros "[Hd Hn] _". iFrame.
  Qed.

End IcacheTable.
