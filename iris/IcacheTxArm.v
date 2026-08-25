(* IcacheTxArm.v -- THE SECOND WALL AT THE ESCROW'S "OUT FOR WRITING" ARM,
   machine-checked.  Documentation, like [IcacheTxRefute.v] (whose finding
   this one continues), [FsDurRefute.v], [FsDurDefer.v], [FsDurTrunc.v] and
   [FsDurQuiesce.v]; nothing consumes it.

   ---- WHERE THIS PICKS UP --------------------------------------------

   [IcacheTxRefute.v] refuted parking a share of [LogInv.log_tx] in the
   escrow's checked-out arm AS THE PLAN STATES IT -- the id is closed
   existentially, so the arm's [t] and the holder's [t] never re-identify --
   and recommended the fix: an additive write-checkout constructor
   [Xv6Cameras.DepTx (s : Qp) (dev inum : mword 32) (g : gname) (t : nat)
   (q : Qp)], whose [ic_deposit] ghost_var pins [(t, q)] between the arm and
   the holder for free.  THAT FIX IS SOUND AND IT DOES CLOSE THE
   RE-IDENTIFICATION: with the descriptor naming [t], [iunlock] recovers
   exactly the share [ilock] parked, and a transaction that write-locks k
   inodes parks k shares and gets each back.

   It does NOT close the mechanism, because of something one layer up.

   ---- THE WALL: ARMING NEEDS THE WHOLE TOKEN, AND create HOLDS TWO -----

   Lane A's locked registry ([InodeRegion.ftop_body]) is keyed by
   TRANSACTION and parks the arming transaction's WHOLE element:

     [ftop_body] holds  [[∗ map] t ↦ _ ∈ A, t ↪[ln_tx icfg_log] tt]

   and [InodeRegion.ireg_arm] takes [LogInv.log_tx icfg_log] -- a WHOLE
   element -- for two reasons that are both load-bearing there: the insert
   needs [A !! t = None], and the ONLY proof of that freeness is that a
   parked entry would hold this very element ([ghost_map_elem_ne] on two
   whole elements, [InodeRegion.v]'s own note).

   xv6's ONE arming walk is [create], and it arms at the [ip->nlink = 1]
   flush ([ProofCreate.v], the [ireg_arm] at ~:5000) -- at which point it
   holds the write lock on its parent [dp] AND on its fresh child [ip].
   Under the write arm each of those two [ilock]s has parked a share, so
   what create holds at the arm is a RESIDUE, and

     A RESIDUE AT ANY POSITIVE FRACTION REFUTES THE WHOLE ELEMENT

   -- which is exactly the property that makes the arm work for the commit,
   and exactly what makes [ireg_arm] undischargeable.  [arm_needs_whole]
   below is that fact positively: from the authority at the singleton
   [{[t := ()]}] (the state in which create's own transaction is the only
   open one) plus any share of [t], NO whole element exists at ANY id, so
   [ireg_arm]'s premise cannot be supplied by any walk that has parked one.

   The two mechanisms are therefore mutually exclusive as they stand: the
   escrow's write arm and lane A's armed registry both want a share of the
   same one-element-per-transaction ghost, and lane A's freeness argument
   needs its share to be the whole thing.

   ---- WHAT WOULD CLOSE IT (for whoever takes this next) ---------------

   Exactly one of:

     (a) RE-KEY THE REGISTRY SO FRESHNESS IS NOT NEEDED.  [ireg_arm]'s only
         use of the whole element is [A !! t = None] for [ghost_map_insert].
         If the registry entry parked a SHARE and the arm were an "insert or
         extend" -- or if [icfg_lk] became an [auth (gmap nat (gsetUR Z))]
         whose fragments compose by union -- then the parked share would
         still refute a non-empty registry at an EMPTY [ln_tx] authority
         (which is all [IregClean.ireg_snap_local_acc] reads off it), and
         create could arm from its residue.  This is a change to
         [InodeRegion.v] and [ProofCreate.v] -- lane A's landed files.

     (b) HAVE [ilock] PARK SOMETHING THAT IS NOT A SHARE OF [log_tx].  The
         collection at quiescence needs the write arm to be refutable
         against an EMPTY [ln_tx] authority, and the only resources with
         that property are elements of [ln_tx] itself.  A second per-
         transaction ghost minted by [begin_op] and consumed by [end_op]
         would do -- and that is a change to [LogInv.v] / [ProofBeginOp.v] /
         [ProofEndOp.v], i.e. lane C's files.

   ---- AND THE ABI THE WRITE ARM COSTS, MEASURED --------------------

   Independently of the above, the holder's residue must be NAMED across the
   ilock/iunlock pair (that is what the [DepTx t q] receipt gives), so every
   contract that spans a HELD inode lock and today threads
   [LogInv.log_op = log_opb ∗ log_tx] must carry the fractional form
   instead.  Measured on the tree at this lane: that bill is much smaller
   than plan section 6 feared, because the interior contracts already take
   the tx-free forms -- [SpecWritei]/[SpecIupdate]/[SpecItrunc]/
   [SpecDirlink]/[SpecBmap]/[SpecBalloc]/[SpecBfree]/[SpecIunlockput] all
   have [log_opS] / [log_opSe] GEN contracts, and [ProofCreate] calls the
   GEN forms throughout, framing [log_tx] itself.  What moves is (i) the
   [_sconf] corollaries' callers that hold a lock, and (ii) the five files
   that name [log_tx] ([SpecCreate], [ProofCreate], [ProofSysOpen],
   [ProofSysUnlink], [ProofSysLinkTails]).  The wall above is what stops
   the mechanism, not this bill.                                          *)

From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap.
From iris.algebra Require Import dfrac.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_map.

Section TxArm.
  Context `{!ghost_mapG Σ nat unit}.

  (* THE ARM'S SHARE AND THE REGISTRY'S WHOLE ELEMENT CANNOT COEXIST.

     [T] is the reachable state in which create's transaction [t] is the
     only open one; [t ↪{#q} ()] is what create still holds after an
     [ilock] parked a share of its token in the escrow's write arm.  The
     conclusion is [InodeRegion.ireg_arm]'s premise, refuted: no whole
     element of [ln_tx] exists at any id at all, so a walk that has parked
     a share can never arm. *)
  Lemma arm_needs_whole (γ : gname) (t : nat) (q : Qp) :
    ghost_map_auth γ 1 ({[t := ()]} : gmap nat unit) -∗
    t ↪[γ]{#q} () -∗
    ∀ t' : nat, t' ↪[γ] () -∗ False.
  Proof.
    iIntros "Ha Hres" (t') "Hw".
    destruct (decide (t' = t)) as [-> | Hne].
    - (* the same id: a whole element beside any share is invalid *)
      iDestruct (ghost_map_elem_valid_2 with "Hw Hres") as %[Hv _].
      iPureIntro. exact (exclusive_l (DfracOwn 1) (DfracOwn q) Hv).
    - (* any other id: the authority has no row for it *)
      iDestruct (ghost_map_lookup with "Ha Hw") as %Ht.
      rewrite lookup_singleton_ne in Ht; [| by apply not_eq_sym].
      discriminate Ht.
  Qed.

  (* ...and the state IS reachable: one open transaction with a share
     parked, which is precisely where create stands at its [ip->nlink = 1]
     flush with both [dp] and [ip] write-locked. *)
  Lemma arm_state_reachable (γ : gname) (t : nat) :
    ghost_map_auth γ 1 (∅ : gmap nat unit) ==∗
      ghost_map_auth γ 1 ({[t := ()]} : gmap nat unit) ∗
      t ↪[γ]{#(1/2)} () ∗ t ↪[γ]{#(1/2)} ().
  Proof.
    iIntros "Ha".
    iMod (ghost_map_insert t () (lookup_empty t) with "Ha") as "[Ha H]".
    rewrite insert_empty. iDestruct "H" as "[H1 H2]".
    iModIntro. iFrame.
  Qed.

End TxArm.
