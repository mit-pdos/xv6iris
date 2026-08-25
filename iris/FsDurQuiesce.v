(* ====================================================================== *)
(*  FsDurQuiesce.v -- WHY THE COMMIT CANNOT COLLECT THE FILE SYSTEM        *)
(*  YET: the two STRUCTURAL walls in front of                             *)
(*  claude-notes/design/durable-fs-plan.md section 4 ("collection at      *)
(*  quiescence"), found by lane C.                                        *)
(*                                                                        *)
(*  Neither is a proof difficulty.  Both are properties of WHERE the era's *)
(*  inode bundles are parked, and both have to be fixed in                *)
(*  [IcacheEscrow.v] before the collection lemma is statable at all.      *)
(*                                                                        *)
(*  WHAT THE COLLECTION NEEDS.  [FsDurSnap.fs_snap_alloc] takes            *)
(*  [snap_ok S L], whose byte half carries the cross-inode clauses         *)
(*  [sk_disj] ("no two nodes share a block") and [sk_own_used] ("a node's  *)
(*  blocks are marked in use, and none is a metadata block").  Neither is  *)
(*  maintained anywhere -- that is the ruling of plan section 8 -- so both *)
(*  are read off the SEPARATING CONJUNCTION at the commit: two full byte   *)
(*  elements at one address are [False] ([FsStateDefs.phi_excl], which     *)
(*  [FsStateDefs.blk_owned_ne] and [FsStateBitmap.free_pool_used] are the  *)
(*  two readings of).  That is a statement about TWO inodes' resources IN  *)
(*  ONE HAND, so the commit must hold every inode's bundle simultaneously: *)
(*  it must collect [FsState.fs_state (FsBytesGamma.fs_gamma_L γfs) S].    *)
(*                                                                        *)
(*  WALL 1 -- THE FIFTY CACHE ESCROWS SHARE ONE NAMESPACE.                 *)
(*  [IcacheEscrow.ic_escrow cn γfs γi cov ls k] is                         *)
(*  [inv icEscN (ic_escrow_body … k)] for EVERY slot [k], and              *)
(*  [ic_escrows] is the [big_sepL] of those fifty over one and the same    *)
(*  [icEscN].  An [inv N P] offers exactly one accessor, at NAMESPACE      *)
(*  granularity: it opens at [E] and leaves [E ∖ ↑N].  Opening a second    *)
(*  invariant of the same namespace inside that would need                 *)
(*  [↑N ⊆ E ∖ ↑N], and [ns_not_reopenable] below is that side condition    *)
(*  refuted -- for EVERY namespace, at every mask.  So no fupd can hold    *)
(*  two cached inodes' bundles at once while the escrows are allocated at  *)
(*  one namespace.  THE FIX is per-slot namespaces ([icEscN .@ k]), after  *)
(*  which the fifty openings are an ordinary induction over               *)
(*  [seq 0 NINODE] accumulating disjoint masks.                            *)
(*                                                                        *)
(*  WALL 2 -- THE UNCACHED INODES' BUNDLES ARE BEHIND THE itable SPINLOCK. *)
(*  Plan section 4 says an unlocked inode's bundle "sits in the cache      *)
(*  escrow ([ic_loaded], [inv icEscN]) or the pool ([live_pool] inside     *)
(*  [inv icacheN])".  The second half does not hold in the tree, and the   *)
(*  two pools it conflates are different objects:                          *)
(*                                                                        *)
(*    - [IcacheInv.live_pool] (inside [IcacheInv.itable_inv], an [inv] at  *)
(*      [icacheN]) is the REFERENCE-COUNT fraction pool.  It holds no      *)
(*      inode bundle at all.                                               *)
(*    - [IcacheEscrow.ipool], which DOES hold the uncached inums'          *)
(*      [inode_owned_era] bundles, is a conjunct of                        *)
(*      [IcacheEscrow.itable_res2] -- the resource of the itable SPINLOCK  *)
(*      ([IcacheEscrow.is_itable2] = [is_lock … itable_lock "itable"]).    *)
(*                                                                        *)
(*  A spinlock's resource is reachable only by ACQUIRING it, which is a    *)
(*  program step; the commit's ghost step is inside [write_head]'s disk    *)
(*  write permit, where no code runs and no lock can be taken -- and       *)
(*  [end_op] never takes [itable.lock] in xv6's C in any case.  So the     *)
(*  uncached inodes' bundles are provably out of the commit's reach.  THE  *)
(*  FIX is to move [ipool] out of [itable_res2] into its own invariant     *)
(*  (per-inum namespaces, for wall 1's reason); the comment inside         *)
(*  [itable_res2] that forbids this move is about [isl_pool] (iput holds a *)
(*  slot's authoritative zero across an [acquiresleep]), not about         *)
(*  [ipool].                                                               *)
(*                                                                        *)
(*  Until both are fixed, lane C's items 1-3 are unstatable and the        *)
(*  WAL-side change that landed with this file -- the deletion of the      *)
(*  parked payload -- is as far as the commit can go.                      *)
(* ====================================================================== *)

Require Import stdpp.base stdpp.namespaces stdpp.sets stdpp.coPset.

(* THE SIDE CONDITION A SECOND OPENING WOULD OWE, REFUTED.  [inv_acc] at
   [E] concludes at [E ∖ ↑N]; a second [inv N _] there needs
   [↑N ⊆ E ∖ ↑N].  A namespace's closure is infinite ([nclose_infinite]),
   hence inhabited, and no inhabited set is contained in a set it has been
   removed from.  Stated at an arbitrary [E] so that it covers the nested
   openings the collection would need, not just the outermost one. *)
Lemma ns_not_reopenable (N : namespace) (E : coPset) :
  ↑N ⊆ E -> ~ (↑N ⊆ E ∖ ↑N).
Proof.
  intros HE Hsub.
  pose proof (coPpick_elem_of (↑N) (nclose_infinite N)) as Hx.
  apply (Hsub _) in Hx as Hx'.
  apply elem_of_difference in Hx' as [_ Hnot].
  exact (Hnot Hx).
Qed.

(* ...and the same fact in the form the fix is stated at: two DISTINCT
   namespaces of one family are disjoint, so the two openings compose.
   This is what [icEscN .@ j] / [icEscN .@ k] buys, and it is why the fix
   is a change of allocation rather than of the proof. *)
Lemma esc_ns_disjoint (N : namespace) (j k : nat) :
  j <> k -> (↑N.@j : coPset) ## ↑N.@k.
Proof. intros Hne. apply ndot_ne_disjoint. exact Hne. Qed.

(* the mask a k-th opening leaves still contains every LATER slot's
   namespace, which is the induction step the fifty-fold collection runs *)
Lemma esc_ns_still_open (N : namespace) (E : coPset) (j k : nat) :
  j <> k -> ↑N.@k ⊆ E -> ↑N.@k ⊆ E ∖ ↑N.@j.
Proof.
  intros Hne HE x Hx.
  apply elem_of_difference. split; [exact (HE x Hx)|].
  intros Hxj. exact (esc_ns_disjoint N k j (fun H => Hne (eq_sym H)) x Hx Hxj).
Qed.
