(* IcacheEscrow.v -- THE INODE ENTRY'S ESCROW, AND THE UNCACHED POOL.
   Design: claude-notes/design/fs-icache.md §13 (which supersedes §10 and
   §12.5 where they disagree).  Modelled line-by-line on BioInv.v's buffer
   escrow; every shape below has a named counterpart there.

   ---- WHY AN ESCROW AT ALL --------------------------------------------

   Same two facts as bio's, transposed to inodes:

   (1) A releasing holder's content must be reachable from the sleeplock
       side BY THE END of [iunlock] -- a blocked waiter's [acquiresleep] can
       return before the releaser has done anything else.
   (2) [iget]'s recycle rewrites dev / inum / ref / valid under only
       [itable.lock], and its scan reads every entry's dev/inum there -- so
       those cells sit fully inside neither the sleeplock chain nor the
       table's resource.

   ---- THE FIVE ARMS (§13.1c, §13.8/13.9, §13.13) -----------------------

     PARKED : the traveling content, waiting for whoever wins the sleeplock.
              [i_valid] FULL, keyed by a bool that selects the payload's
              shape (loaded / unloaded); BOTH identity cells at HALF
              (§13.1e).  The [i_inum] half is what ties the payload's
              [dinode_at] to the inum the identity cells name (§13.1b); the
              [i_dev] half exists because a checked-out thread has deposited
              its WHOLE reference and would otherwise have no way to read
              [ip->dev] (ilock's own bread, at ilock+0x48) or to get its
              reference back AT ITS OWN DEVICE (iunlock's postcondition).
              [BioInv.buf_parked] holds [b_dev ↦₄{½}] for the same two
              reasons.  Plus the recycle token.
     EMPTY  : the arm of a slot that is NOT live (§13.8/§13.9) -- the boot
              state of all fifty entries, and what iput's last close leaves
              behind.  NO payload: no bundle and no [dinode_at], the record
              having gone back to the pool.  The DEV cell is FULL here, and
              that is the discriminator every reference-holding opener uses;
              the inum cell stays at ½ so that FULL-inum remains MID's
              signature alone.
     OUT    : checked out by a sleeplock chain -- the chain's DEPOSIT, half of
              the checkout descriptor and the recycle token wait here until the
              parker brings the content back.  The deposit is a REFERENCE
              (iput's authority-side window exit) or a SHARE (ilock's checkout
              under SpecIlock v3), and WHICH is what the descriptor says: with
              two shapes in one arm the two parkers are otherwise
              resource-indistinguishable, so each holds the descriptor's other
              half and selects its own arm by [ghost_var_agree] (§14.8).
     MID    : iget's recycle window [+0x72, +0x7c): the inum cell already
              names the NEW inode and the payload is already the incoming
              unloaded bundle, but the valid word is still STALE, so the
              arm's valid<->shape coupling cannot be stated.  The inum cell
              is FULL here (the recycler joined the table's half in at the
              store and keeps it across the window) and the recycle token is
              OUT, in the recycler's hand.  The DEV cell stays at HALF here
              exactly as in PARKED: the inum cell remains the sole
              parked/mid discriminator, and the dev store at +0x6e is its
              own open/close pair over the PARKED arm
              ([ic_open_empty_dev]), not part of this window --
              nothing couples the arm's dev to its payload, so a parked arm
              whose dev already names the incoming inode is well formed.
     HELD   : iput's AUTHORITY-SIDE window [+0x3c, the post-acquiresleep
              checkout) -- design §13.13.  Same idea as MID, for the other
              function and in the other direction: the CELLS stay in the arm
              (dev ½ as always, inum FULL -- the same discriminator MID uses
              -- and HALF the valid word, the holder keeping the other half
              so the polarity stays pinned by agreement) while the PAYLOAD
              LEAVES WITH THE HOLDER, at the concrete polarity the holder
              observed.  That is the whole content of the arm: iput reads
              [ip->valid] at +0x3c and cannot use the answer twenty bytes
              later, because [ic_open_auth_ref] re-seals the parked arm with
              its [v] existentially bound and NOTHING an itable-lock holder
              owns can pin it ([valid]'s writer, ilock, holds no itable
              credential, so a table-anchored ghost half would have no
              partner).  Taking the payload out of the invariant removes the
              question: a resource in the holder's own context is not
              re-bound by anything.

   Refutations, and which opener uses which (§10.3, §13.1c, §13.13):

     * the sleeplock winner (post-[acquiresleep]) refutes OUT with its own
       [ic_tok], and MID with its reference's inum-cell FRACTION against
       MID's FULL inum cell;
     * the parker ([iunlock]) refutes PARKED and MID with the FULL valid
       cell it is carrying (both arms hold that cell full);
     * iget's recycle, which arrives at a slot the table shows NOT LIVE,
       refutes all three of PARKED / OUT / MID with the table's [false] half
       of the identification ghost -- it has no cell fraction to reason with,
       because the empty arm owns the whole dev cell (§13.8/§13.9);
     * an authority-side opener at REF-1 (iput) refutes OUT by
       [IcacheInv.iref_tok_two_lookup] -- its own reference plus the arm's
       would make the count at least two -- and MID by its own inum
       fraction;
     * the recycler re-opening its own window refutes PARKED and OUT with
       [ic_mid], which both of them hold and it is carrying;
     * HELD is refuted by every one of the above with the line it already
       uses: the sleeplock winner and the REF-1 opener by their inum
       FRACTION against HELD's FULL cell (the MID line, verbatim), the
       parker and [ic_open_out] by their FULL valid cell, the recycler by
       [ic_mid] (HELD parks it, exactly as PARKED does), and iget's arrival
       at a not-live slot by the identification ghost;
     * ...and HELD's own re-opener -- iput -- needs NO NEW TOKEN, which is
       why none was added (§13.13 wrote one down as an option; the compile
       settles it, and it is not needed).  Its credential is REF-1 PLUS THE
       PAYLOAD, and each part kills one arm: the authority half at count one
       against its own [iref_tok] kills OUT ([iref_tok_two_lookup], the line
       [ic_open_auth_ref] already uses) and is what makes the credential
       exclusive -- no second thread holds a reference to this slot at all;
       the PAYLOAD it is carrying kills PARKED and MID, because every payload
       owns this ENTRY's metadata cells and those are exclusive
       ([ic_payload_excl]; before §16.4 this went through the payload's
       [dinode_at], which the slimmed free arm no longer has -- and the cells
       are slot-keyed, so no [ic_id_agree] is needed to pin the inums first);
       and the table's [ic_id] half at [true] kills EMPTY.  REF-1
       rather than [ic_tok] is FORCED, not chosen: iput must also be able to
       UNDO the window at +0x44, when [ip->nlink] is nonzero and no
       [acquiresleep] has run.  Putting a
       fresh token in the four other arms instead would have forced
       [ic_mid_arm] to carry it, which is [ProofIget]'s inline arm
       construction at +0x72 and its destructuring at +0x7c -- i.e. it would
       have broken the "no proof file moves" requirement for the sake of a
       refutation that is already available.

   The ½-versus-FULL split of the inum cell IS the parked/mid
   discriminator, which is why §13.1b's identity re-budget in
   [IcacheInv.islot_rest] is not bookkeeping.  HELD shares that signature
   deliberately -- no opener has to tell HELD from MID except iput, which
   does it with the payload, and MID/HELD are told apart by [ic_mid]
   (HELD parks it, MID does not).

   ---- ONE DEVIATION FROM THE C3a BRIEF, RECORDED HERE ------------------

   The brief described [ic_swap_checkout] as splitting the winner's
   reference in half -- q/2 deposited into OUT, q/2 kept.  THAT IS NOT AN
   ENTAILMENT: [iref_tok k q] is [own icfg_iref (◯ {[k := (q,1)]})] and two
   half-fraction tokens compose to [{[k := (q,2)]}], a different element, so
   splitting a reference's FRACTION also splits its COUNT and needs the
   authority (that is exactly [iref_dup_step], which is idup's shape and
   needs a lock the winner does not hold).  §13.1c's arm table is what is
   transcribed instead, verbatim: OUT holds a WHOLE [inode_ref], the winner
   deposits its reference on checkout and gets it back at the park --
   BioInv's [escrow_swap_checkout] / [escrow_swap_park] exactly.  A winner
   that needs a reference fragment MID-CRITICAL-SECTION (iunlock's lock-free
   [ip->ref] read at its panic guard) borrows it from the arm through
   [ic_open_out], which is what that lemma is for.

   ---- WHAT IS DELIBERATELY NOT HERE ------------------------------------

   No function contract and no instruction step: iget / ilock / iunlock /
   iput are stated over this file, not in it.  The recycler's payload
   juggling (turning an evicted entry's parked payload back into a pool
   entry) is iget's obligation and is NOT baked into a swap lemma here --
   see the [ic_open_parked_free] / [ic_close_mid] comment.               *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list functions bitvector.definitions.
From iris.algebra Require Import auth gmap frac numbers.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap invariants own ghost_map ghost_var mono_nat.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvPtsto RiscvExtras.
Require Import WpLock.
Require Import TsoCtx.   (* the lock payload's context axis; [<{ }>] *)

Require Import FsBlocks.
Require Import DinodeEnc.
Require Import DirView.
Require Import FsTree.        (* [dir_uniq] -- the name-uniqueness payload clause *)
(* THE TWO CONTENTS HOLDS ARE GONE (fs-syscall-specs, THE DVIEW RETIREMENT,
   2026-08-30).  [ipool_alloc], [ic_loaded], [ic_rd_arm] and the byte-less
   arms each carried [dv_ride]/[fv_ride] beside the era leg, and this file
   [Require Export]ed [DirViewG]/[DirViewLend] so the ~forty sites that
   destruct those payloads could name them.  The abstract contents are a
   reading of the era fragment the same arms already carry
   ([FsStateEra.dir_entries_era_node], [fn_file_bytes]), so the column and
   both leaves are deleted. *)
Require Import InodeInv.
Require Import InodeLock.
Require Import SleepLock.  (* [is_sleeplock_gen] / [slh_tok] -- see [ic_sleeplocks] below *)
Require Import InodeRegion.
(* durable-disk 2b-inode-3: the payload's OWNERSHIP is the era bundle.
   [FsState] for [top_frag], [FsBytesGamma] for [fs_gamma_L], [FsStateEra]
   for [inode_owned_era] and the payload dictionary ([era_node],
   [node_shape_ok], [inode_rec_local] and the three [_era_node_*] bridges).
   Placed here, after [InodeRegion], because this file spells none of the
   four names the [FsState*] stack shadows ([fs_view], [byte_range],
   [link_auth], [free_pool]) -- checked. *)
Require Import FsState.
Require Import FsBytesGamma.
Require Import LogDefs.       (* [fs_home_set] -- [ic_loaded_open]'s row *)
(* THE TRANSACTION PIN (rank 5).  Every park below that keeps a share of an
   open transaction's [ln_tx] element -- [ic_dep_own]'s write arm and its
   reading [ic_dep_side], [ic_out_frz]'s freeze window, the slot pin
   [ic_pin_tx], and section 5c's two pool ledgers -- spells it with this one
   vocabulary, and every refutation the commit reads off them is an instance
   of [TxPin.tx_pin_no_ops]. *)
Require Import TxPin.
Require Import FsStateEra.
Require Import EscrowDefs.
Require Import EscrowInode.   (* OPTION A: pool_pending, reg_full *)
Require Import IrefSlots.
(* §3.1's A-refuter: the pool peel refutes its AWAIT arm with the caller's
   LICENCE ([IgetLic.iname_freeze_off]) rather than with a wand into False *)
Require Import IgetLic.
Require Import IcacheInv.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
(* R3.3 (endgame §4.2): the box instance lives here -- its kit *)
From Stdlib Require Import QArith Qcanon.
From iris.algebra Require Import ufrac.
Require Import TsoMemPa TsoGhost.
Require Import CtxBox.
Require Import SepThread.   (* the boot threads own_context through the slots *)

Local Open Scope Z_scope.
Require Import TsoCtx.

(* ===================================================================== *)
(*  0.  GHOST NAMES                                                       *)
(* ===================================================================== *)

(* [ic_names] -- the three per-slot gname families this layer's arms are
   stated over -- is in [IcacheRef], beside [icfg] and [icfg_isl]: it is a
   record of gnames and nothing more, and [FsCfg] has to name it to carry
   [fsc_ic].  [IcacheInv] re-exports [IcacheRef], so every reading of it
   through this file is unchanged. *)

Section IcacheEscrow.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !irefslotG Σ}.
  Context `{GEN : GenId}.
  Context `{ICFG : icfg}.
  Context `{XI : CurCtx}.

  (* THE STRUCTURAL Timeless PEELER, and it lives HERE -- at the top of the
     section -- on purpose.  It used to sit ~700 lines down, so every instance
     above it could not see it and closed with a bare [apply _] instead: one
     search backtracking across a whole [∃/∗/∨] tower, 8.1 s over the 18 sites
     that preceded the old definition ([inode_meta_timeless] 3.2 s and
     [ic_loaded_timeless] 2.9 s between them).  Peeling one connective per step
     and calling [apply _] only at the LEAVES is optimization.md's rule; keeping
     the tactic in scope for the whole section is what lets every instance obey
     it.  Dispatch is SYNTACTIC ([lazymatch] on the connective), so it never
     descends into a leaf that typeclass search should have. *)
  Local Ltac tl_struct :=
    lazymatch goal with
    | |- Timeless (bi_exist _) => apply bi.exist_timeless; intro; tl_struct
    | |- Timeless (bi_sep _ _) => apply bi.sep_timeless; [tl_struct | tl_struct]
    | |- Timeless (bi_or _ _) => apply bi.or_timeless; [tl_struct | tl_struct]
    | |- _ => apply _
    end.

  (* ------------------------------------------------------------------ *)
  (*  Timeless instances the arms are built out of                       *)
  (* ------------------------------------------------------------------ *)

  (* Every opener below is inside a store's or a load's atomic update, with
     no step left to absorb a ▷, so the WHOLE body must be timeless (bio's
     [bv_clean_tl]/[bv_dirty_tl] exist for exactly this reason).  The
     components are points-tos, ghost_map elements and pure facts -- all
     timeless -- but several are guarded by a [decide], so the instances
     have to be discharged by hand rather than found. *)

  Global Instance word2_pointsto_timeless (ktr : CurKtier) (a : Arch.pa) (dq : dfrac) (w : bv 16) :
    Timeless (word2_pointsto (KTR := ktr) a dq w).
  Proof. rewrite /word2_pointsto. tl_struct. Qed.

  Global Instance word2_pointsto_timeless' (ktr : ktier) (a : Arch.pa) (dq : dfrac) (w : bv 16) :
    Timeless (word2_pointsto (KTR := ktr) a dq w).
  Proof. exact (word2_pointsto_timeless ktr a dq w). Qed.

  Global Instance inode_meta_timeless (ip : mword 64) (d : dinode) :
    Timeless (inode_meta ip d).
  Proof. rewrite /inode_meta. tl_struct. Qed.

  Global Instance inode_addrs_timeless (ip : mword 64) (l : list (bv 32)) :
    Timeless (inode_addrs ip l).
  Proof. rewrite /inode_addrs. tl_struct. Qed.

  Global Instance inode_raw_timeless (ip : mword 64) : Timeless (inode_raw ip).
  Proof. rewrite /inode_raw. tl_struct. Qed.

  Global Instance ind_blk_timeless γfs bm : Timeless (ind_blk γfs bm).
  Proof. rewrite /ind_blk. case_decide; apply _. Qed.


  Global Instance ind_res_timeless γfs bm : Timeless (ind_res γfs bm).
  Proof. rewrite /ind_res. tl_struct. Qed.

  Global Instance blk_res_timeless γfs w bs : Timeless (blk_res γfs w bs).
  Proof. rewrite /blk_res. case_decide; apply _. Qed.

  Global Instance inode_blocks_timeless γfs bm data :
    Timeless (inode_blocks γfs bm data).
  Proof. rewrite /inode_blocks. tl_struct. Qed.

  (* full ownership of a 4-byte cell is exclusive AGAINST ANY FRACTION --
     which is what makes the FULL-versus-½ inum cell a discriminator.
     (BioInv and FileOff each carry a private copy; the real home is
     RiscvPtsto's [word4_pointsto] section, and moving it there is a
     whole-tree rebuild this additive file does not take.) *)
  Lemma ic_word4_excl (a : Arch.pa) (w1 w2 : bv 32) (dq : dfrac) :
    a ↦₄ w1 -∗ a ↦₄{dq} w2 -∗ False.
  Proof.
    iIntros "H1 H2".
    rewrite !ctx_word4_pointsto_unfold.
    iDestruct "H1" as "[_ H1]". iDestruct "H2" as "[_ H2]".
    change (seq 0 4) with ([0; 1; 2; 3]%nat).
    iDestruct "H1" as "[Hb1 _]". iDestruct "H2" as "[Hb2 _]".
    iDestruct (ctx_pointsto_ne with "Hb1 Hb2") as %Hne.
    iPureIntro. exact (Hne eq_refl).
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  1.  THE TWO TOKENS                                                 *)
  (* ------------------------------------------------------------------ *)

  (* THE ENTRY SLEEPLOCK'S WHOLE RESOURCE (BioInv.bown), AND THE CHECKOUT
     DEPOSIT'S DESCRIPTOR, IN ONE GHOST (design §14.8).

     Holding [ic_tok] is what lets a winner refute the checked-out arm; the
     checkout then splits it so that the arm records "somebody is inside the
     critical section" AND WHAT THEY LEFT.  It is a [ghost_var] over
     [Xv6Cameras.ic_dep] rather than a [WpLock.lock_tok_excl] for exactly one
     reason (§14.8, "the two-parkers problem"): with the OUT arm able to hold
     EITHER a reference (iput's window exit) or a share (ilock's checkout), the
     two parkers are otherwise resource-indistinguishable, so neither could
     select its own arm.  Here each parker holds the OTHER half of this
     variable, and [ghost_var_agree] pins the kind, the fraction AND the
     identity in one line.

     [ic_tok] keeps its old meaning verbatim -- it is the variable WHOLE, at
     the neutral descriptor -- so it is still exclusive, [is_sleeplock ...
     (ic_tok cn k)] is unchanged, and IcacheBoot's allocation is unchanged in
     character. *)
  Definition ic_tok (cn : ic_names) (k : nat) : iProp Σ :=
    ghost_var (icn_esc cn k) 1 DepNone.
  Lemma ic_tok_exclusive cn k : ic_tok cn k -∗ ic_tok cn k -∗ False.
  Proof.
    rewrite /ic_tok. iIntros "H1 H2".
    iDestruct (ghost_var_valid_2 with "H1 H2") as %[Hv _].
    iPureIntro. by apply (Qp.not_add_le_l 1 1).
  Qed.

  (* HALF the variable, at a concrete descriptor: one of these sits in the OUT
     arm and the other travels with the checked-out thread, from the checkout
     to the park. *)
  Definition ic_deposit (cn : ic_names) (k : nat) (d : ic_dep) : iProp Σ :=
    ghost_var (icn_dep cn k) (1/2) d.
  (* ...and the variable WHOLE at the neutral descriptor: what the L2 payload
     row carries between a park and the next checkout (the stitch: the box's
     token [ic_tok] stays whole inside the box during OUT_L2, so main's
     descriptor halves live on their own gname, [icn_dep]). *)
  Definition ic_dep_neutral (cn : ic_names) (k : nat) : iProp Σ :=
    ghost_var (icn_dep cn k) 1 DepNone.

  (* THE CHECKOUT'S GHOST STEP: the winner turns the sleeplock's variable into
     the descriptor of what it is about to deposit, and splits.  One half goes
     into the arm, the other travels with it. *)
  Lemma ic_dep_checkout cn k (d : ic_dep) :
    ic_dep_neutral cn k ==∗ ic_deposit cn k d ∗ ic_deposit cn k d.
  Proof.
    rewrite /ic_dep_neutral /ic_deposit. iIntros "H".
    iMod (ghost_var_update d with "H") as "H".
    iModIntro. iDestruct "H" as "[H1 H2]". iFrame.
  Qed.

  (* ...AND THE PARK'S: the two halves meet, AGREE (which is what selects the
     arm), rejoin and go back to the neutral descriptor, ready for
     releasesleep. *)
  Lemma ic_dep_park cn k (d1 d2 : ic_dep) :
    ic_deposit cn k d1 -∗ ic_deposit cn k d2 ==∗ ⌜d1 = d2⌝ ∗ ic_dep_neutral cn k.
  Proof.
    rewrite /ic_deposit /ic_dep_neutral. iIntros "H1 H2".
    iDestruct (ghost_var_agree with "H1 H2") as %<-.
    iMod (ghost_var_update_halves DepNone with "H1 H2") as "[H1 H2]".
    iModIntro. iSplitR; [done |].
    iCombine "H1 H2" as "H". iExact "H".
  Qed.

  Lemma ic_deposit_agree cn k d1 d2 :
    ic_deposit cn k d1 -∗ ic_deposit cn k d2 -∗ ⌜d1 = d2⌝.
  Proof. rewrite /ic_deposit. iIntros "H1 H2". by iApply (ghost_var_agree with "H1 H2"). Qed.

  Global Instance ic_tok_timeless cn k : Timeless (ic_tok cn k).
  Proof. rewrite /ic_tok. tl_struct. Qed.
  Global Instance ic_deposit_timeless cn k d : Timeless (ic_deposit cn k d).
  Proof. rewrite /ic_deposit. tl_struct. Qed.

  (* ---- ...AND THE IDENTIFICATION AGREEMENT (§13.8) ------------------- *)

  (* Is entry [k] LIVE -- equivalently, does its escrow arm hold a payload?
     A two-state ghost with one half on each side of the seam: the ESCROW's
     half rides its arms (the empty arm carries [false], the other three
     carry [true]) and the TABLE's half rides [islot2] (the not-live
     (None, None) arm carries [false], the live arm carries [true]).

     It is NOT monotone (§13.9): iget's recycle flips it false->true and
     iput's LAST CLOSE flips it back, because a non-live slot's bundle goes
     home to the pool rather than staying cached.

     It exists for exactly one opener.  Every other refutation in this file
     is a cell fraction or an exclusive token that the opener already holds:
     a reference holder kills the empty arm with its DEV fraction against
     that arm's full cell, the parker kills it with its full valid cell, the
     recycler re-opening its window kills it with [ic_mid].  But the recycler
     ARRIVING at a non-live slot holds no dev fraction at all -- the empty
     arm owns the whole cell, which is the point -- and so cannot tell that
     arm from an ordinary parked one.  This is what it reads instead.

     It is not a lock: both halves live in resources their holders already
     own, and the two flips happen at the one opening where both are in one
     hand -- iget's recycle and iput's last close.  Not
     [lock_tok_excl] (FsCrash.v's route out of the same problem): BOTH sides
     must be able to READ the state, and an exclusive token can be held by
     only one of them. *)
  Definition ic_id (cn : ic_names) (k : nat) (q : Qp)
      (v : bool) (dev inum : mword 32) : iProp Σ :=
    ghost_var (icn_id cn k) q (v, dev, inum).

  Global Instance ic_id_timeless cn k q v dev inum :
    Timeless (ic_id cn k q v dev inum).
  Proof. rewrite /ic_id. tl_struct. Qed.

  Lemma ic_id_agree cn k q1 q2 v1 d1 n1 v2 d2 n2 :
    ic_id cn k q1 v1 d1 n1 -∗ ic_id cn k q2 v2 d2 n2 -∗
    ⌜v1 = v2 /\ d1 = d2 /\ n1 = n2⌝.
  Proof.
    rewrite /ic_id. iIntros "H1 H2".
    iDestruct (ghost_var_agree with "H1 H2") as %Heq.
    iPureIntro. by injection Heq.
  Qed.

  (* the two halves in one hand -- iget's recycle (twice: the dev store's
     re-tag at +0x6e and the identification flip at +0x72) and iput's last
     close.  §13.10: this is a VALUE update, not just a state flip, and the
     values are what a recycler cannot otherwise recover from a cell its arm
     owns whole. *)
  Lemma ic_id_flip cn k (v v' : bool) (d n d' n' : mword 32) :
    ic_id cn k (1/2) v d n -∗ ic_id cn k (1/2) v d n ==∗
    ic_id cn k (1/2) v' d' n' ∗ ic_id cn k (1/2) v' d' n'.
  Proof.
    rewrite /ic_id. iIntros "H1 H2".
    iApply (ghost_var_update_halves (v', d', n') with "H1 H2").
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  2.  THE PAYLOADS                                                   *)
  (* ------------------------------------------------------------------ *)

  (* ONE UNCACHED INUM'S POOL BUNDLE (§13.3, slimmed by §16.4).  Two shapes,
     because free inodes exist: [inode_ok] demands a nonzero type, and a
     type-0 inode owns no blocks (itrunc returned them).

     THE FREE ARM IS NOW A BARE MARKER (§16.3/§16.4).  It used to carry the
     inum's [dinode_at]; ialloc cannot reach it there, because the pool is
     behind the itable spinlock and the claim is serialised by the BUFFER
     instead (§16.1/§16.2).  So a free inum's record fragment lives in
     [InodeRegion]'s invariant and what the pool holds is
     [InodeRegion.imark] -- the per-inum token whose other home is that same
     invariant's OUT arm.  It is not decoration: it is exactly what makes
     ilock's fill able to conclude that a nonzero type at a marker-parked
     entry means the fragment is still in the region
     ([InodeRegion.ireg_withdraw]).

     THE DIRECTORY-WF CONJUNCT (§15(a)).  The allocated arm also carries
     [DirView.dir_ok icfg_nib] -- if this inode is a DIRECTORY then every
     live record in it names an inum the inode region covers.  It rides
     beside [inode_ok] rather than inside it because [inode_ok]'s signature
     has no [nib] and its users are legion; [icfg_nib] is the ambient
     region size, capacity and not resource.  The FREE arm needs no such
     conjunct: it carries no data at all, and its type is 0.

     ...AND ITS RESOURCE TWIN (§20.3, stage B; since G6 the TYPE REGISTER).
     [dlinks] rides BESIDE [dir_ok], not inside it: one type-register
     fragment per live non-self record (fs-state.md §6½).  [dir_ok] says the
     named inum is IN RANGE; the twin says it is ALLOCATED and reveals its
     TYPE, which is a fact about another inum's REGION record and therefore
     cannot be a [Prop] over [data] (§20.1, §20.9(a)).  It is timeless, so
     the [Timeless] instance below survives verbatim.  (Through G5 the
     conjunct was the one the old flavoured link ledger carried
     beside it; G6 deleted the ledger.)

     ...AND THE ".." INDEX CLAUSE (fs-icache §20.17.4, fs-fragments R9).
     [DirView.dir_dots_ix]: a LIVE directory ([T_DIR] and [nlink <> 0]) has
     at least two records and its record 1 is the live [".."].  It is what
     lets S7 name the one entry unit at [dp] it must convert -- an entry's
     unit is keyed by record INDEX and is name-blind, so without it nothing
     says WHICH unit in a child's [dlinks] is the parent's.  It rides HERE,
     beside [dir_ok], for [dir_ok]'s own reason: it is a fact about this
     payload's bytes that no contract in the tree wants to carry, and the
     [Timeless] instances below are unaffected because it is pure.

     ...AND ITS COMPLEMENT, [DirView.dir_orphan_clean] (the STRONG isdirempty
     invariant, fs-fragments F1.5d's plank).  [dir_dots_ix] speaks only above
     [nlink <> 0]; this one speaks only at [nlink = 0], and between them the
     directory case is partitioned with no overlap and no gap: an ORPHANED
     directory's live records are exactly ["."] and [".."].  It is true of
     THIS binary because sys_link's orphan guard (xv6 f60ff58, ARM E2)
     refuses to [dirlink] into a directory whose count has already fallen to
     zero, and it carries three loads at once -- fs-icache §20.6's itrunc
     row, §20.17.5's residue, and [sys_unlink]'s own input premise, since a
     live NON-dot record under it forces the home's count nonzero, which is
     what [FsStateEra.ent_toks_era_unlink] needs of the home. *)
  (* ...AND ITS OWNERSHIP IS THE ERA BUNDLE (durable-disk 2b-inode-3).
     The three RESOURCE conjuncts [dinode_at] / [ind_res] / [inode_blocks]
     are gone; what stands in their place is
     [FsStateEra.inode_owned_era] at this arm's own node, which CONTAINS all
     three and carries the era's abstract value ([FsState.top_frag]) beside
     them.  [IcacheBoot.ipool_shape_alloc] assembles it and
     [FsStateEra.inode_owned_era_era_node_to] takes it apart, both off
     [inode_ok]'s own representational half ([FsStateEra.node_shape_ok]).

     [inode_ok] STAYS A PURE CONJUNCT, and that is a deliberate deviation
     from 2b-inode-2's plan (which had it derived on demand by
     [FsStateEra.inode_owned_era_era_node_ok], a fupd at [logN]).  It costs
     nothing -- every producer proved it before the flip and still does --
     and it is what keeps the flip from moving a single consumer's MASK:
     with it, [ic_loaded_open] is an ordinary entailment, so no walk has to
     find a [logN]-open window at the point where it unpacks its payload,
     and no arm that unpacks inside an [iInv] becomes unprovable.  The
     derivation is landed and is what an arm that would rather NOT maintain
     the coverage sweep or the injectivity uses. *)
  (* ---- THE LINKS CONJUNCT (durable-disk G6: THE OLD LEDGER IS GONE) --

     The payload's links half is the TYPE REGISTER's fragments
     ([FsStateInode.ent_toks] at this payload's own node; fs-state.md
     §6½): one per entry of this directory that names another inum, drawn
     out of that inum's region-side authority at the [iupdate] that raised
     its count.  Through 2b-inode-5..G5 it rode BESIDE the old flavoured
     flavoured link ledger, so that the ~forty payload sites which
     only pass the conjunct through never moved; G6 deleted that first
     conjunct and the payloads keep their arity again.

     The form is the DEPOSIT-TIME [FsStateInode.ent_toks_x]: the marker set
     is existential and the per-directory count is EXACT, which is where
     [ProofSysUnlink]'s (D2) reads "a directory holding a live subdirectory
     record has at least two links".  A checked-out walk OPENS it --
     [dlinks_open] names the marker set -- moves entries and counts freely,
     and re-seals at [dlinks_intro] with the equation restored.  create's
     mkdir arm is exactly the window that needs the freedom: it appends
     [dp]'s record for the child and raises [dp->nlink] at two different
     instructions. *)
  Definition dlinks (γfs : fs_names) (self : Z) (dn : dinode) (bm : blkmap)
      (data : nat -> list (bv 8)) : iProp Σ :=
    (FsStateInode.ent_toks_x (fs_gamma_L γfs) self
       (era_node dn bm data))%I.

  Global Instance dlinks_timeless γfs self dn bm data :
    Timeless (dlinks γfs self dn bm data).
  Proof. rewrite /dlinks. tl_struct. Qed.

  Lemma dlinks_open γfs self dn bm data :
    dlinks γfs self dn bm data -∗
      ∃ D, ⌜FsStateInode.ent_dset_ok (era_node dn bm data) D
            /\ FsStateInode.node_exact (era_node dn bm data) D⌝
           ∗ FsStateInode.ent_toks (fs_gamma_L γfs) self
               (era_node dn bm data) D.
  Proof.
    iIntros "(%D & %Hd & %Hx & Ht)". iExists D.
    iSplitR; [iPureIntro; split; [exact Hd | exact Hx] |]. iExact "Ht".
  Qed.

  Lemma dlinks_intro γfs self dn bm data D :
    FsStateInode.ent_dset_ok (era_node dn bm data) D ->
    FsStateInode.node_exact (era_node dn bm data) D ->
    FsStateInode.ent_toks (fs_gamma_L γfs) self (era_node dn bm data) D -∗
    dlinks γfs self dn bm data.
  Proof.
    intros Hd Hx. iIntros "H2". iExists D.
    iSplitR; [by iPureIntro |]. iSplitR; [by iPureIntro |]. iExact "H2".
  Qed.

  (* the two free discharges: a NON-directory owns no links at all, and
     neither does a record whose size is zero (a claim box, a corpse) *)
  Lemma dlinks_not_dir γfs self dn bm data :
    bv_unsigned (di_type dn) <> T_DIR_z -> ⊢ dlinks γfs self dn bm data.
  Proof.
    intros Hne. rewrite /dlinks.
    iApply (FsStateEra.ent_toks_x_era_not_dir _ self dn bm data Hne).
  Qed.

  Lemma dlinks_size_zero γfs self dn bm data :
    bv_unsigned (di_size dn) = 0 ->
    bv_unsigned (di_nlink dn) <= 1 -> ⊢ dlinks γfs self dn bm data.
  Proof.
    intros Hsz Hnl. rewrite /dlinks.
    iApply (FsStateEra.ent_toks_x_era_nrec0 _ self dn bm data
              ltac:(rewrite Hsz /dir_nrec //)).
    intros _. pose proof (di_nlink_nonneg dn). lia.
  Qed.

  (* ==================================================================== *)
  (*  THE PER-INODE ESCROWED LEG                                          *)
  (*  (durable-disk EV, the era-vocabulary unification, stage 4)          *)
  (* ==================================================================== *)

  (* EVERYTHING A SLOT HOLDS OF ONE INODE, AT A SHARE -- AND IT IS EXACTLY
     THE PIECE THE COMMIT'S COLLECTION ASSEMBLES.  [FsState]'s per-inum
     conjunct is [FsStateInode.inode_owned] = [inode_phi] beside
     [inode_ghost], and 2b-inode-1/4's rulings (fs-state.md section 7) put
     its four parts in three hands:

       - the RECORD's bytes and this inum's link AUTHORITY are region-side
         ([InodeRegion.ireg_recs] at [FsStateInode.rec_owned_at],
         [InodeRegion.ireg_lnk_at] around [FsStateLink.link_auth]) and never
         travel;
       - the DATA LEG -- [FsStateInode.inode_dat_q], which is [inode_phi]
         MINUS its record -- and this inode's entry TOKENS
         ([FsStateInode.ent_toks_x], the Φ-free half's other piece) are
         HERE, in whichever escrow arm or pool row owns the inum;
       - the era's own two, the record PROXY [dinode_at] and the abstract
         fragment [FsState.top_frag], ride with the leg and are RESIDUE to
         the collection, which consumes neither.

     So the pair is what every arm carries and what [ic_slot_cover]'s third
     alternative lends, and naming it ONCE is what lets the collection take
     it off a slot without re-associating anything.  The three readings
     below -- [ic_inode_leg_phi_at], [ic_inode_leg_ghost] and their join
     [ic_inode_leg_owned] -- are the whole of the translation into the
     collection's own vocabulary; each one is the leg beside what the REGION
     kept.

     IT SITS IN [dlinks]' CONJUNCT POSITION in all three arms (durable-notes,
     "replacing one conjunct of a big payload: bundle the pair in the old
     one's position"), and [dlinks γfs (bv_unsigned inum) dn bm data] IS
     [ent_toks_x _ (bv_unsigned inum) (era_node dn bm data)] -- one unfold --
     so no arm's textual order moved and the arity dropped by one.
     [ic_inode_leg_era_open]/[_era_intro] are the two directions at the
     era's own [(dn, bm, data)] triple. *)
  Definition ic_inode_leg (γfs : fs_names) (dq : dfrac) (γi : gname)
      (inum : mword 32) (n : fs_node) : iProp Σ :=
    (FsStateInode.ent_toks_x (fs_gamma_L γfs) (bv_unsigned inum) n
     ∗ inode_owned_era_q γfs dq γi inum n)%I.

  (* NAMED, NOT SEARCHED, and the difference is 19 seconds -- measured, on
     this one sentence.  Both leaves have declared instances, but a bare
     [apply _] (which is what [tl_struct] falls through to at a leaf) has
     to REACH them past every other [Timeless] instance in scope, with the
     node a VARIABLE so nothing in [ent_toks_x]'s body reduces to cut the
     search short.  Naming the two instances makes the sentence free. *)
  Global Instance ic_inode_leg_timeless γfs dq γi inum n :
    Timeless (ic_inode_leg γfs dq γi inum n).
  Proof.
    rewrite /ic_inode_leg.
    apply bi.sep_timeless;
      [apply FsStateInode.ent_toks_x_timeless
      | apply inode_owned_era_q_timeless].
  Qed.

  (* SEALED THE DAY IT IS WRITTEN (durable-notes, the [iFrame]-up-to-delta
     rule): it rides inside [ic_loaded] and [ipool_alloc], whose framing
     searches this file runs constantly, and unsealed it would cost each of
     them the era bundle's four conjuncts on top of what they already walk.
     [rewrite /ic_inode_leg] and the declared [Timeless] instance still
     work, and the four openers below are what the proofs use.

     GLOBAL SINCE STAGE 5, because the seal has a second consumer now:
     [FsCollect.col_side] IS this predicate, and a seal does not travel
     (durable-notes, "a [Typeclasses Opaque] seal does not travel").  An
     unsealed leg there would let a framing search walk into the era
     bundle's four conjuncts at every one of the collection's inums. *)
  Global Typeclasses Opaque ic_inode_leg.

  Lemma ic_inode_leg_open γfs dq γi (inum : mword 32) n :
    ic_inode_leg γfs dq γi inum n -∗
      FsStateInode.ent_toks_x (fs_gamma_L γfs) (bv_unsigned inum) n
      ∗ inode_owned_era_q γfs dq γi inum n.
  Proof. rewrite /ic_inode_leg. iIntros "[H1 H2]". iFrame. Qed.

  Lemma ic_inode_leg_intro γfs dq γi (inum : mword 32) n :
    FsStateInode.ent_toks_x (fs_gamma_L γfs) (bv_unsigned inum) n -∗
    inode_owned_era_q γfs dq γi inum n -∗
    ic_inode_leg γfs dq γi inum n.
  Proof.
    rewrite /ic_inode_leg. iIntros "H1 H2".
    iSplitL "H1"; [iExact "H1" | iExact "H2"].
  Qed.

  Lemma ic_inode_leg_era_open γfs dq γi (inum : mword 32) dn bm data :
    ic_inode_leg γfs dq γi inum (era_node dn bm data) -∗
      dlinks γfs (bv_unsigned inum) dn bm data
      ∗ inode_owned_era_q γfs dq γi inum (era_node dn bm data).
  Proof. rewrite /ic_inode_leg /dlinks. iIntros "[H1 H2]". iFrame. Qed.

  Lemma ic_inode_leg_era_intro γfs dq γi (inum : mword 32) dn bm data :
    dlinks γfs (bv_unsigned inum) dn bm data -∗
    inode_owned_era_q γfs dq γi inum (era_node dn bm data) -∗
    ic_inode_leg γfs dq γi inum (era_node dn bm data).
  Proof.
    rewrite /ic_inode_leg /dlinks. iIntros "H1 H2".
    iSplitL "H1"; [iExact "H1" | iExact "H2"].
  Qed.

  (* the leg's own pure reading: [inode_local] is the era bundle's last
     conjunct and a consumer that only wants it should not have to open the
     pair. *)
  Lemma ic_inode_leg_local γfs dq γi (inum : mword 32) n :
    ic_inode_leg γfs dq γi inum n -∗ ⌜inode_local (bv_unsigned inum) n⌝.
  Proof.
    rewrite /ic_inode_leg /inode_owned_era_q.
    iIntros "(_ & _ & _ & _ & $)".
  Qed.

  (* THE READER'S QUARTER, AT THE LEG.  [FsStateEra.inode_owned_era_shed_to]
     is about the era bundle alone; the entry TOKENS do not split (they are
     the Φ-free half and stay whole on the arm), so the leg's shed is the
     bundle's beside an untouched token conjunct.  [ic_loaded_shed] and
     [ic_rd_join] are these two and the cells. *)
  Lemma ic_inode_leg_shed_to γfs γi (inum : mword 32) n :
    ic_inode_leg γfs (DfracOwn 1) γi inum n -∗
    ic_inode_leg γfs (DfracOwn (3/4)) γi inum n
    ∗ inode_rd_era γfs (DfracOwn (1/4)) inum n.
  Proof.
    rewrite /ic_inode_leg. iIntros "[Hte Hn]".
    iDestruct (inode_owned_era_shed_to with "Hn") as "[Hn34 Hn14]".
    iSplitR "Hn14"; [| iExact "Hn14"].
    iSplitL "Hte"; [iExact "Hte" | iExact "Hn34"].
  Qed.

  (* the read arm's re-identification, at the leg: the era's abstract
     fragment is inside the bundle, so the pin travels with the leg and
     [ic_rd_join] never opens it. *)
  Lemma ic_inode_leg_rd_agree γfs dq1 dq2 γi (inum : mword 32) n1 n2 :
    ic_inode_leg γfs dq1 γi inum n1 -∗
    inode_rd_era γfs dq2 inum n2 -∗ ⌜n1 = n2⌝.
  Proof.
    rewrite /ic_inode_leg. iIntros "[_ Hn] Hrd".
    iApply (inode_rd_era_agree with "Hn Hrd").
  Qed.

  Lemma ic_inode_leg_shed_of γfs γi (inum : mword 32) n :
    ic_inode_leg γfs (DfracOwn (3/4)) γi inum n -∗
    inode_rd_era γfs (DfracOwn (1/4)) inum n -∗
    ic_inode_leg γfs (DfracOwn 1) γi inum n.
  Proof.
    rewrite /ic_inode_leg. iIntros "[Hte Hn34] Hn14".
    iSplitL "Hte"; [iExact "Hte" |].
    iApply (inode_owned_era_shed_of with "Hn34 Hn14").
  Qed.

  (* ---- WHAT THE COLLECTION TAKES OFF A LEG ---------------------------- *)

  (* (i) THE Φ HALF.  The leg's data leg beside the REGION's own record run
     at this inum IS [FsStateInode.inode_phi_at] -- the geometry-free
     reading, which is what [FsCollectAll.col_recs_by_inum] hands in (the
     inode region has no superblock, only [icfg_ist] and a plain [Z]).  The
     era's two residue pieces come out beside it and the collection consumes
     neither; the tokens come out because they are the OTHER half's input,
     [ic_inode_leg_ghost]'s. *)
  Lemma ic_inode_leg_phi_at γfs γi (inum : mword 32) (n : fs_node)
      (istart : Z) :
    ic_inode_leg γfs (DfracOwn 1) γi inum n -∗
    FsStateInode.rec_owned_at (fs_gamma_L γfs) istart (bv_unsigned inum)
      (fn_rec n) -∗
    FsStateInode.inode_phi_at (fs_gamma_L γfs) istart (bv_unsigned inum) n
    ∗ FsStateInode.ent_toks_x (fs_gamma_L γfs) (bv_unsigned inum) n
    ∗ ⌜inode_local (bv_unsigned inum) n⌝
    ∗ dinode_at γi inum (fn_rec n)
    ∗ top_frag (fs_gamma_L γfs) (bv_unsigned inum) n.
  Proof.
    rewrite /ic_inode_leg /inode_owned_era_q /FsStateInode.inode_phi_at.
    rewrite -(FsStateInode.inode_dat_1 (fs_gamma_L γfs) n).
    iIntros "(Hte & Hd & Hb & Ht & %Hloc) Hrec".
    iSplitL "Hrec Hb"; [iSplitL "Hrec"; [iExact "Hrec" | iExact "Hb"] |].
    iSplitL "Hte"; [iExact "Hte" |].
    iSplitR; [by iPureIntro |].
    iSplitL "Hd"; [iExact "Hd" | iExact "Ht"].
  Qed.

  (* (ii) THE Φ-FREE HALF, and it is [FsStateInode.inode_ghost_of] with the
     leg supplying both of that lemma's inputs it can supply: the entry
     TOKENS and [inode_local].  What it cannot supply is the region's
     per-inum AUTHORITY and the type agreement [fn_ity_ok] -- the collection
     reads the second off [InodeRegion.ireg_reg_ok] when it peels
     [ireg_lnk_at], which is where the first comes from too. *)
  Lemma ic_inode_leg_ghost γfs γi (inum : mword 32) (n : fs_node) v :
    fn_ity_ok n v ->
    ic_inode_leg γfs (DfracOwn 1) γi inum n -∗
    FsStateLink.link_auth (fs_gamma_L γfs) (bv_unsigned inum) (fn_mult n) v -∗
    FsStateInode.inode_ghost (fs_gamma_L γfs) (bv_unsigned inum) n
    ∗ FsStateInode.inode_dat (fs_gamma_L γfs) n
    ∗ dinode_at γi inum (fn_rec n)
    ∗ top_frag (fs_gamma_L γfs) (bv_unsigned inum) n.
  Proof.
    intros Hv.
    rewrite /ic_inode_leg /inode_owned_era_q.
    rewrite -(FsStateInode.inode_dat_1 (fs_gamma_L γfs) n).
    iIntros "(Hte & Hd & Hb & Ht & %Hloc) Hla".
    iSplitR "Hb Hd Ht".
    { iApply (FsStateInode.inode_ghost_of _ (bv_unsigned inum) n v Hv Hloc
                with "Hla Hte"). }
    iSplitL "Hb"; [iExact "Hb" |].
    iSplitL "Hd"; [iExact "Hd" | iExact "Ht"].
  Qed.

  (* (iii) THE TWO TOGETHER, at the superblock the state is stated over: a
     slot's whole leg, the region's record run and the region's link
     authority ADD UP TO [FsState]'s own per-inum conjunct, with the era's
     residue left over.  [FsStateInode.inode_phi_sb]'s range premise is free
     here -- [bv_unsigned] of a [mword 32] is in [0, 2^32) by construction --
     which is the honest reading of "an inum is a 32-bit word". *)
  Lemma ic_inode_leg_owned γfs γi (inum : mword 32) (n : fs_node)
      (sb : FsImg.fs_sb) v :
    fn_ity_ok n v ->
    ic_inode_leg γfs (DfracOwn 1) γi inum n -∗
    FsStateInode.rec_owned_at (fs_gamma_L γfs) (FsImg.sb_inodestart sb)
      (bv_unsigned inum) (fn_rec n) -∗
    FsStateLink.link_auth (fs_gamma_L γfs) (bv_unsigned inum) (fn_mult n) v -∗
    FsStateInode.inode_owned (fs_gamma_L γfs) sb (bv_unsigned inum) n
    ∗ dinode_at γi inum (fn_rec n)
    ∗ top_frag (fs_gamma_L γfs) (bv_unsigned inum) n.
  Proof.
    intros Hv.
    (* the range premise, proved with the proofmode context still EMPTY --
       [lia] in a nine-conjunct Iris context is the hygiene rule's case *)
    assert (Hrng : 0 <= bv_unsigned inum < 2 ^ 32).
    { pose proof (bv_unsigned_in_range 32 inum) as H.
      unfold bv_modulus in H. exact H. }
    iIntros "Hleg Hrec Hla".
    iDestruct (ic_inode_leg_phi_at with "Hleg Hrec")
      as "(Hphi & Hte & %Hloc & Hd & Ht)".
    rewrite /FsStateInode.inode_owned.
    rewrite -(FsStateInode.inode_phi_sb (fs_gamma_L γfs) sb
                (bv_unsigned inum) n Hrng).
    iSplitR "Hd Ht".
    { iSplitL "Hphi"; [iExact "Hphi" |].
      iApply (FsStateInode.inode_ghost_of _ (bv_unsigned inum) n v Hv Hloc
                with "Hla Hte"). }
    iSplitL "Hd"; [iExact "Hd" | iExact "Ht"].
  Qed.

  Definition ipool_alloc (γfs : fs_names) (γi : gname) (cov : gset Z)
      (logstart : Z) (inum : mword 32) : iProp Σ :=
    (∃ (dn0 : dinode) (bm0 : blkmap) (data0 : nat -> list (bv 8)),
       ⌜inode_ok cov logstart dn0 bm0 data0⌝ ∗
       ⌜dir_ok icfg_nib dn0 data0⌝ ∗
       ⌜dir_dots_ix (bv_unsigned inum) dn0 data0⌝ ∗
       ⌜dir_orphan_clean dn0 data0⌝ ∗
       ⌜dir_uniq dn0 data0⌝ ∗
       (* THE PER-INODE ESCROWED LEG (durable-disk EV stage 4), in [dlinks]'
          own conjunct position and absorbing the era bundle beside it: the
          entry TOKENS and [FsStateEra.inode_owned_era_q] at fraction 1, i.e.
          exactly what the commit's collection takes off this inum.
          [ic_inode_leg_era_open]/[_era_intro] are the two directions. *)
       (* THE TWO CONTENTS HOLDS THAT USED TO RIDE HERE ARE RETIRED (THE
          DVIEW RETIREMENT).  What they said -- the abstract entry map and
          the byte list of this inum -- is a READING of the era fragment
          inside the leg above, at the same [(dn0, bm0, data0)]. *)
       ic_inode_leg γfs (DfracOwn 1) γi inum (era_node dn0 bm0 data0))%I.

  (* OPTION A: the NON-PENDING (Timeless) pool shape -- the ORIGINAL two-arm
     shape, unchanged.  It is what the escrow's parked bundle [ic_unloaded]
     carries, so the escrow (and the whole loaded/unloaded/evict/fill/recycle
     lifecycle) is untouched.  [reg_full] does NOT ride here: the region's own
     [InodeRegion.ireg_slot] arm carries each inum's [reg_full]/[reg_half]
     fragment, coupled to pending-ness, so "non-pending => reg_full" is
     structural and [ireg_claim_au] refutes the pending arm from the open it
     already does. *)
  (* THE ERA'S ABSTRACT VALUE IS NOT ON THE MARKER ARM ANY MORE (durable-disk
     C-3c).  It used to ride here UNTIED, which is exactly what left the
     commit's collection unable to prove [FsDurSnap.sk_rec] or [sk_links] at a
     free inum (FsCollect's supplier (D)).  It now parks WITH the record, in
     [InodeRegion.ireg_top_park] -- tied at a type-0 record, untied at a claim
     box -- and reaches the fill through [InodeRegion.ireg_withdraw]. *)
  Definition ipool_shape_np (γfs : fs_names) (γi : gname) (cov : gset Z)
      (logstart : Z) (inum : mword 32) : iProp Σ :=
    (ipool_alloc γfs γi cov logstart inum
     ∨ imark γi (bv_unsigned inum))%I.
  (* THE MARKER ARM'S TWO UNTIED HOLDS ARE RETIRED with the column (THE DVIEW
     RETIREMENT): a byte-less arm used to carry the two elements at a
     forgotten value, so that the fill which re-tied them had a hold to set.
     There is nothing to re-tie now -- the fill retags the era fragment and
     that IS the contents reading. *)

  (* THE AWAIT ARM (iclaim-ledger.md §1.2/§1.3): the entry a FREER has parked
     on its way to the off-lock deposit.  It is the whole point of B2's
     resolution that it does NOT contain [dinode_at] -- the freer keeps the
     record, with its identity intact and no existential, all the way to
     [OFF.ip_free_offlock]'s entry.  What it carries instead is the escrow the
     freer minted ([EscrowInode.escA_alloc], mask-only) and that escrow's
     exclusive redemption ticket, i.e. exactly [pool_pending] MINUS the
     [committedA] the deposit has not yet produced.

     ...AND THE FREEZE, which §1.2 does not name and which is here for §1.3's
     sake.  §1.3 requires a pre-deposit consumer -- a fill or a recycle of
     THIS inum -- to be refutable, and the refutation the design gives is
     §2.6's exclusivity, not an arithmetic one.  Parking the freer's
     [ifreeze_post] here is what makes it a two-line refutation
     ([IcacheRef.ifreeze_excl]) against the "right to freeze" [ifreeze_off]
     that the consumer must present: one exclusive cell, two holders.  The
     cost is that §1.4's retire (f Some -> None) reads the token back out of
     the POOL at the await-redeem rather than out of the depositor's hand; the
     pin it carries ([FrzPost => icnt = 0], InodeRegion.ireg_frz_ok) is
     undisturbed across the wider window, because the inum is uncached
     throughout it.

     WHERE IT SITS, AND WHY THAT IS A DEVIATION FROM §1.2 (recorded).  §1.2
     puts the arm inside [ipool_shape_np].  It cannot go there: [escA_inv] is
     an [inv] and therefore not Timeless, [ipool_shape_np] is what
     [ic_unloaded] wraps, and [ic_unloaded_timeless] is what
     [ic_escrow_body_timeless] -- hence every [iInv "Hesc" as ">"] in the tree
     -- is built out of.  This is EscrowDefs' own trade, made there for the
     region and quoted at [region_pending]: "[esc_inv] (not Timeless) rides
     the POOL side, so this stays Timeless".  So the await arm rides the pool
     side too, beside [pool_pending], and §1.2's park at iput+0x70 needs a
     Timeless stand-in of its own (the A-walk's item, not this increment's). *)
  (* A⁗ (iclaim-ledger.md §3.16) DROPPED THE [ifreeze_post] CONJUNCT, and
     IIIa's DEVIATION 3 is superseded.  §1.3's original design put the
     refutation of a pre-deposit consumer on the CALLER's licence
     ([iname_not_frozen], landed IIIc) rather than on a token parked here,
     and that is now buildable -- while the token is NOT parkable any more:
     the phase fragment has to stay in the FREER's hand from the mint at
     +0x50 to the off-lock deposit at +0xba, because it is what decides the
     escrow arm's tail at +0x70 and +0x8a ([ic_payload_arm_decide_frz]) and
     what [IcacheInv.iref_close_last_freeze_store_au] consumes in between.
     One exclusive ledger cell cannot be in two places. *)
  (* ...AND ITS TWO UNTIED CONTENTS HOLDS ARE RETIRED (THE DVIEW RETIREMENT),
     for [ipool_shape_np]'s marker arm's reason verbatim. *)
  Definition pool_await (γfs : fs_names) (z : Z) : iProp Σ :=
    (∃ ge gr gd (rg : frzidx),
       escA_inv γfs ge gr gd z rg ∗ redeem_ticketA gr)%I.

  (* the PENDING-capable pool shape -- lives ONLY at the itable free pool,
     which is LOCK-HELD (never [iInv .. as ">"], verified), so the non-Timeless
     [pool_pending] (an [esc_inv]) is fine here.  A pending entry has disk
     type=0 and is provably never filled ([ireg_withdraw] needs type<>0), hence
     never enters the escrow's [ipool_shape_np] side.  Since §1.2 the AWAIT arm
     rides here for the same reason and with the same consequence.

     ---- THE UNCACHED LEDGER RESOURCES (increment IIIa) ------------------

     THE COUNT HALF, at the bundle level and above the arms.  §2.2 puts one
     [icnt] half in [InodeRegion.ireg_slot] and the other wherever the inum's
     identity is parked; increment II proved the "not-cached arms" reading of
     that ruling FALSE at [islot_empty] (fifty slots, one key: fraction 25)
     and deferred the true home to here.  This IS the true home: the pool's
     domain is [region_inums nib ∖ ci_inums ci], i.e. exactly the complement
     of the live arms' inums, so one half per POOL ENTRY is one half per
     UNCACHED inum, which is what the fraction discipline demands.  The value
     is the literal 0: an inum in the free pool is, by the pool's own
     definition, in no [ci] entry, so its in-core count is zero.  It rides
     ABOVE the disjunction because all three arms are uncached and agree on
     it -- and because that keeps the two movers' peel one line long.

     THE FREEZE TOKEN, per ARM and NOT above them.  [ifreeze] is one
     exclusive ledger cell ([ifreeze_excl] refutes ANY two fragments at one
     inum, equal phases included), so a bundle-level copy beside
     [pool_await]'s [ifreeze_post] would make the await arm unreachable --
     which is exactly the arm §1.3 needs.  So: the two ORDINARY arms carry
     the unfrozen token [ifreeze_off], the "right to freeze" that
     [IcacheInv.iref_upgrade_store_au] demands of a recycler and that
     [InodeRegion.ireg_freeze_au] swaps for [ifreeze_pre]; the AWAIT arm
     carries the freer's [ifreeze_post] inside [pool_await], where increment
     II already filed it.  One token per inum on every arm, never two. *)
  (* THE FREEZE MIRROR's UNCACHED HALF (iclaim-ledger.md §3.16) rides both
     rows beside the count half, and for its reason verbatim: the pool's
     domain is the complement of the live arms' inums, so one half per pool
     entry is one half per uncached inum.  The value is the literal [false]
     on all three arms: [FrzOff] on the two ordinary ones and [FrzPost] on
     the await arm, and [ireg_frzm_ok] is down at both.

     THE PENDING ARM's TOKEN IS IN ITS ESCROW (A⁗, §3.16): the off-lock
     deposit hands the retired [ifreeze_off] to
     [EscrowInode.escA_deposit_acc], which parks it in the escrow's FILLED
     state, and [escA_redeem] gives it to whoever converts this entry to an
     [imark].  Two copies of one exclusive ledger cell is not a choice --
     and the placement is what lets the AWAIT arm carry the STANDING freeze
     in the same escrow, which is the refuter §1.3 always wanted.

     THE ERA'S ABSTRACT VALUE IS NOT ON EITHER ROW (durable-disk C-3c).
     A freed inum's fragment travels from iput's payload to the region
     through the ESCROW's own EMPTY arm ([EscrowInode.escA_body]), which is
     the one place both the +0x94 park and the +0xba deposit reach -- so
     neither in-transition arm carries it and the deposit parks it
     region-side ([InodeRegion.ireg_top_park]) at the corpse's bare
     record. *)

  (* the ORDINARY row: the count half, the mirror half, the two-arm
     (allocated / marker) Timeless shape and the unfrozen token. *)
  Definition ipool_ord (γfs : fs_names) (γi : gname) (cov : gset Z)
      (logstart : Z) (inum : mword 32) : iProp Σ :=
    (icnt_half (bv_unsigned inum) 0%nat ∗
     frzm_h (bv_unsigned inum) false ∗
     ipool_shape_np γfs γi cov logstart inum ∗
     ifreeze_off (bv_unsigned inum))%I.

  (* ...and the IN-TRANSITION row: the same two ledger halves beside the
     pending or the await arm.  NOT Timeless ([escA_inv] is an [inv]),
     which is the whole reason for the split. *)
  Definition ipool_ext (γfs : fs_names) (γi : gname) (cov : gset Z)
      (logstart : Z) (inum : mword 32) : iProp Σ :=
    (icnt_half (bv_unsigned inum) 0%nat ∗
     frzm_h (bv_unsigned inum) false ∗
     (pool_pending γfs (bv_unsigned inum)
      ∨ pool_await γfs (bv_unsigned inum)))%I.

  Global Instance ipool_ord_timeless γfs γi cov logstart inum :
    Timeless (ipool_ord γfs γi cov logstart inum).
  Proof. rewrite /ipool_ord. tl_struct. Qed.


  Global Instance ipool_alloc_timeless γfs γi cov logstart inum :
    Timeless (ipool_alloc γfs γi cov logstart inum).
  Proof. rewrite /ipool_alloc. tl_struct. Qed.

  Global Instance ipool_shape_np_timeless γfs γi cov logstart inum :
    Timeless (ipool_shape_np γfs γi cov logstart inum).
  Proof. rewrite /ipool_shape_np. tl_struct. Qed.

  (* A LOADED entry's parked content: the in-memory record [dn] in the five
     metadata cells and the block map in the thirteen addrs cells, with the
     file's blocks and the indirect block alongside.  The inum is a
     parameter, not existential: the arm's inum-cell half pins it (§13.1b).

     PARKED-MEANS-FLUSHED: the loaded arm's region record IS the
     in-memory record ([dinode_at] at [dn], no separate [dn0]).  Every
     writer in this kernel ends with iupdate (writei's tail, itrunc's
     tail), so a holder can always re-establish it at iunlock -- and
     WITHOUT it, iget's eviction could never conclude the pool's
     allocated shape (whose [inode_ok] is about the ON-DISK record)
     from the loaded arm's (which is about the in-memory one).  The
     stale-record freedom exists only INSIDE a critical section: the
     checked-out bundle's dinode_at may lag until the holder's iupdate
     retags it.  Design: fs-icache.md §13 (parked-clean).

     THE DIRECTORY-WF CONJUNCT (§15(a)), the twin of the pool row's: a
     parked DIRECTORY's live records all name inums the inode region
     covers.  This is what namex destructs out of ilock's postcondition,
     and it is the reason dirlookup's [dir_inums_ok] premise is
     dischargeable at a directory nobody named in advance.

     ...AND ITS RESOURCE TWIN (§20.3, stage B), the twin of [ipool_alloc]'s:
     [dlinks] over this record's own [data].  It is what dirlookup will hand
     [iget] as licence (a)/(b) in stage C, borrowed out of this payload at
     the matched index and returned before the holder's iunlock.  Every
     re-park in the landed tree carries it unchanged because none of them
     changes a DIRECTORY's bytes.

     ...AND THE ".." INDEX CLAUSE, the twin of [ipool_alloc]'s: see there.
     create is its sole PRODUCER (at [dirlink(ip, "..", dp->inum)]); every
     other re-park in the tree transfers it, and the ones that move the
     record discharge it from [DirView]'s five ways -- most often
     [dir_dots_ix_orphan], since a walk that zeroes [nlink] before parking
     is parking a directory the clause says nothing about.

     ...AND ITS COMPLEMENT [DirView.dir_orphan_clean], the twin of
     [ipool_alloc]'s: see there.  Where [dir_dots_ix] is transferred by the
     peels and discharged by [_orphan] at the walks that zero a count, this
     one is exactly the other way round -- [_live] at every live directory,
     [_not_dir] at every file, [_size_zero] at a claim box and a truncated
     corpse -- and its one PRODUCING site is create's [fail:] twin, which
     parks a child it has just orphaned. *)
  Definition ic_loaded (γfs : fs_names) (γi : gname) (cov : gset Z)
      (logstart : Z) (k : nat) (inum : mword 32)
      (dn : dinode) (bm : blkmap) : iProp Σ :=
    (∃ (data : nat -> list (bv 8)),
       ⌜inode_ok cov logstart dn bm data⌝ ∗
       ⌜dir_ok icfg_nib dn data⌝ ∗
       ⌜dir_dots_ix (bv_unsigned inum) dn data⌝ ∗
       ⌜dir_orphan_clean dn data⌝ ∗
       ⌜dir_uniq dn data⌝ ∗
       (* THE OWNERSHIP IS THE PER-INODE ESCROWED LEG (durable-disk EV
          stage 4), which is [dlinks] and the era bundle (durable-disk
          2b-inode-3) as ONE conjunct at this payload's own node.  The
          bundle CONTAINS what three conjuncts used to say separately --
          [dinode_at], [ind_res] and [inode_blocks] -- and adds the era's
          abstract value [top_frag], which is what a holder retags at its
          writes ([InodeRegion.ireg_top_retag]).  A consumer that wants the
          old shape back applies [ic_loaded_open], an ordinary entailment;
          see [ipool_alloc]'s note for why [inode_ok] stays a conjunct
          rather than being derived. *)
       (* THE TWO CONTENTS HOLDS ARE RETIRED, [ipool_alloc]'s note verbatim:
          a checked-out holder owns the era fragment inside the leg, and the
          abstract contents are its reading. *)
       ic_inode_leg γfs (DfracOwn 1) γi inum (era_node dn bm data) ∗
       inode_meta (ientry k) dn ∗
       inode_addrs (ientry k) (bm_cells bm))%I.

  (* An UNLOADED entry's parked content: the cells at no particular value
     (iget minted the entry and nobody has read the dinode yet) plus the
     inum's pool bundle, parked here on its way past the recycler so that
     WHOEVER wins the sleeplock race finds what the fill needs. *)
  Definition ic_unloaded (γfs : fs_names) (γi : gname) (cov : gset Z)
      (logstart : Z) (k : nat) (inum : mword 32) : iProp Σ :=
    (inode_raw (ientry k) ∗ ipool_shape_np γfs γi cov logstart inum)%I.

  Global Instance ic_loaded_timeless γfs γi cov logstart k inum dn bm :
    Timeless (ic_loaded γfs γi cov logstart k inum dn bm).
  Proof. rewrite /ic_loaded. tl_struct. Qed.

  Global Instance ic_unloaded_timeless γfs γi cov logstart k inum :
    Timeless (ic_unloaded γfs γi cov logstart k inum).
  Proof. rewrite /ic_unloaded. tl_struct. Qed.

  (* ==================================================================== *)
  (*  THE READ ARM (durable-fs-plan.md section 3, [ilock] without a        *)
  (*  transaction; sections 4's second bullet; durable-disk B''-join)      *)
  (* ==================================================================== *)

  (* PLAN SECTION 4 NEEDS EVERY INODE'S VALIDITY PREDICATE TO BE INSIDE THE
     INVARIANTS AT A COMMIT, and a read-locker -- [fileread] and [filestat],
     the only two callers of [ilock] that hold no transaction -- can never
     park a transaction share, because it has none.  So its withdrawal is a
     SHARE: it takes a quarter of the byte legs and of the abstract fragment
     and leaves the rest here, and the collection reads the residue off the
     open escrow exactly as it reads an unlocked inode's whole bundle.  The
     quarter (and not a half) is what makes 3/4 + 3/4 invalid, i.e. what
     keeps cross-inode block disjointness pure separation logic
     ([FsStateDefs.blk_owned_ne_34]).

     WHAT STAYS: the record proxy [dinode_at] -- so a read-locker cannot move
     a record, [InodeRegion.ireg_write_au] taking it -- three quarters of the
     byte legs and of [top_frag], the link ledger and the two contents holds,
     and every pure clause.  WHAT LEAVES is [ic_rd_held] below: the in-memory
     CELLS (which the design keeps at fraction 1 -- [filestat] reads them,
     [readi] reads [ip->addrs]) and the reader's quarter.

     THE ARM'S [(dn, bm, data)] IS EXISTENTIAL, and nothing pins it but the
     quarter of [top_frag] the holder carries: [FsStateEra.inode_rd_era_agree]
     gives the two nodes equal and [FsStateEra.era_node_pair_inj] turns that
     into the PAIR equal.  [data] is never compared -- the join re-forms the
     payload at the arm's own, which is existentially bound in [ic_loaded]
     anyway.  That is why this arm needs no per-slot pin ghost, where the
     WRITE arm needed the descriptor's [(t, q)] fields. *)
  Definition ic_rd_arm (γfs : fs_names) (γi : gname) (cov : gset Z)
      (logstart : Z) (inum : mword 32) : iProp Σ :=
    (∃ (dn : dinode) (bm : blkmap) (data : nat -> list (bv 8)),
       ⌜inode_ok cov logstart dn bm data⌝ ∗
       ⌜dir_ok icfg_nib dn data⌝ ∗
       ⌜dir_dots_ix (bv_unsigned inum) dn data⌝ ∗
       ⌜dir_orphan_clean dn data⌝ ∗
       ⌜dir_uniq dn data⌝ ∗
       (* the leg at THREE QUARTERS -- the same conjunct [ic_loaded] carries
          at 1, which is what makes [ic_loaded_shed]/[ic_rd_join] a fraction
          move and nothing else *)
       ic_inode_leg γfs (DfracOwn (3/4)) γi inum (era_node dn bm data))%I.

  (* ...and what the READ-LOCKING HOLDER carries in its place.  [inode_ok] is
     restated here (it is pure, so both sides keep it) because the holder
     needs it to call [readi]; [inode_local] of the node is what
     [FsStateEra.inode_dat_era_to] takes to turn the quarter into
     [readi]'s [inode_map_q] / [inode_blocks_q] pair. *)
  Definition ic_rd_held (γfs : fs_names) (cov : gset Z) (logstart : Z)
      (k : nat) (inum : mword 32) (dn : dinode) (bm : blkmap) : iProp Σ :=
    (∃ (data : nat -> list (bv 8)),
       ⌜inode_ok cov logstart dn bm data⌝ ∗
       ⌜inode_local (bv_unsigned inum) (era_node dn bm data)⌝ ∗
       inode_meta (ientry k) dn ∗
       inode_addrs (ientry k) (bm_cells bm) ∗
       inode_rd_era γfs (DfracOwn (1/4)) inum (era_node dn bm data))%I.

  (* THE STRUCTURAL [Timeless] TACTIC.  Defined HERE, above the read arm's
     two bundles, because a bare [apply _] on a nine-conjunct payload
     backtracks through every definition in it; the arms below use it too. *)

  Global Instance ic_rd_arm_timeless γfs γi cov logstart inum :
    Timeless (ic_rd_arm γfs γi cov logstart inum).
  Proof. rewrite /ic_rd_arm. tl_struct. Qed.

  Global Instance ic_rd_held_timeless γfs cov logstart k inum dn bm :
    Timeless (ic_rd_held γfs cov logstart k inum dn bm).
  Proof. rewrite /ic_rd_held. tl_struct. Qed.

  (* SEALED THE DAY THEY ARE WRITTEN (durable-notes, the [iFrame]-up-to-delta
     rule): both bodies are separating conjunctions over [dlinks] and the era
     bundle, [ic_rd_arm] rides inside [ic_out] -- i.e. inside [ic_escrow_body],
     which every framing search in this file walks -- and an unsealed one costs
     each of those searches the whole payload.  [rewrite /ic_rd_arm] and the
     declared [Timeless] instances still work. *)
  Local Typeclasses Opaque ic_rd_arm ic_rd_held.

  (* THE SHED: a holder of the whole payload gives three quarters back. *)
  Lemma ic_loaded_shed γfs γi cov logstart k (inum : mword 32)
      (dn : dinode) (bm : blkmap) :
    ic_loaded γfs γi cov logstart k inum dn bm -∗
    ic_rd_arm γfs γi cov logstart inum
    ∗ ic_rd_held γfs cov logstart k inum dn bm.
  Proof.
    rewrite /ic_loaded /ic_rd_arm /ic_rd_held. iIntros "H".
    iDestruct "H" as (data)
      "(%Hok & %Hdok & %Hddix & %Hdoc & %Hduq & Hleg & Hm & Ha)".
    iDestruct (ic_inode_leg_local with "Hleg") as %Hloc.
    iDestruct (ic_inode_leg_shed_to with "Hleg") as "[Hleg34 Hn14]".
    iSplitR "Hm Ha Hn14".
    - iExists dn, bm, data. iFrame "Hleg34".
      iSplitR; [iPureIntro; exact Hok |].
      iSplitR; [iPureIntro; exact Hdok |].
      iSplitR; [iPureIntro; exact Hddix |].
      iSplitR; [iPureIntro; exact Hdoc |].
      iPureIntro; exact Hduq.
    - iExists data. iFrame "Hm Ha Hn14".
      iSplitR; [iPureIntro; exact Hok |].
      iPureIntro; exact Hloc.
  Qed.

  (* ...AND THE PARK, which is the whole re-identification argument in five
     lines.  The result is at the HOLDER'S [(dn, bm)] -- the arm's pair is
     proven equal to it -- so [iunlock] and every consumer of [ic_loaded]
     meet exactly what they met before. *)
  Lemma ic_rd_join γfs γi cov logstart k (inum : mword 32)
      (dn : dinode) (bm : blkmap) :
    ic_rd_arm γfs γi cov logstart inum -∗
    ic_rd_held γfs cov logstart k inum dn bm -∗
    ic_loaded γfs γi cov logstart k inum dn bm.
  Proof.
    rewrite /ic_rd_arm /ic_rd_held /ic_loaded.
    iIntros "Harm Hheld".
    iDestruct "Harm" as (dn' bm' data')
      "(%Hok' & %Hdok & %Hddix & %Hdoc & %Hduq & Hleg)".
    iDestruct "Hheld" as (data) "(%Hok & %Hloc & Hm & Ha & Hn14)".
    iDestruct (ic_inode_leg_rd_agree with "Hleg Hn14") as %Hnode.
    destruct (era_node_pair_inj cov logstart dn' dn bm' bm data' data
                Hok' Hok Hnode) as [<- <-].
    (* the HELD quarter is at the holder's [data], the arm's residue at its
       own; the node equation moves the quarter onto the ARM's, which is the
       one [ic_loaded] is re-formed at.  Rewriting the other way would leave
       the two sides at different [data]s and send [iApply]'s unifier into a
       function unification it never comes back from. *)
    rewrite -Hnode.
    iExists data'.
    iSplitR; [iPureIntro; exact Hok' |].
    iSplitR; [iPureIntro; exact Hdok |].
    iSplitR; [iPureIntro; exact Hddix |].
    iSplitR; [iPureIntro; exact Hdoc |].
    iSplitR; [iPureIntro; exact Hduq |].
    iSplitL "Hleg Hn14";
      [iApply (ic_inode_leg_shed_of with "Hleg Hn14") |].
    iFrame "Hm Ha".
  Qed.

  (* the arm's own reading of the residue, which is what plan section 4's
     collection takes off an open escrow: the record proxy, the byte legs at
     three quarters and the node's well-formedness. *)

  (* THE PAYLOAD THE VALID WORD KEYS, AT THE SLOT'S GENERATION, AND THE
     GENERATION'S TYPE ONE-SHOT ON ITS TWO POLARITIES (design §17.3 (A) /
     §17.6, ratified §17.4 / §17.7).

     [ic_loaded] DOES NOT MOVE -- it is named in nineteen files and this is
     why none of them changed; the generation rides HERE, where three files
     name it, and so does the witness: [ity_shot g (di_type dn)] on the
     LOADED polarity, [ity_pending g] on the UNLOADED one.

     WHY THE PENDING RIDES HERE AND NOT ONE LEVEL DOWN.  §17.3 (B) put it
     with [ipool_shape_np]'s ALLOCATED disjunct, on the argument that "ilock's
     fill MUST take the allocated branch -- it is where [dinode_at] lives".
     §16.4's CLAIM BOX refutes that: [ProofIlock]'s fill also completes on
     the MARKER branch, through [InodeRegion.ireg_withdraw], whenever ialloc
     has retagged the inum to a [fresh_shape] record.  Putting it on BOTH
     pool disjuncts is what §17.3 (B) refuted from the other side.  And it
     may NOT go into [ic_unloaded] either: [ic_mid_arm] holds [ic_unloaded]
     DIRECTLY and is sealed at iget's +0x72 ([ic_mk_unloaded],
     [ProofIget.v:1167]), six instructions before the slot enters [M] and any
     unit is split -- there is no pending in existence to put there.

     On this polarity the obligation lands exactly at iget's +0x7c
     ([ic_close_mid_to_parked]), where the recycler is already carrying the
     token by hand.  Both conjuncts are TIMELESS, so [ic_payload_timeless]
     survives verbatim (§17.1 (iv), respected).

     A GENERATION THEREFORE SEES AT MOST ONE FILL, which is the invariant
     §17.5 proved necessary: the recycle mints a generation and its pending
     ([IcacheInv.live_slot_alloc]); the fill spends it; and iput's free path
     -- the second filler, via §17.6.1's reachable claim-and-hit sequence --
     RETIRES the generation at +0x54 ([IcacheInv.live_slot_regen]) before it
     re-parks UNLOADED with a fresh pending.  The pool row, [imark],
     [InodeRegion] and [ProofIalloc] are untouched, which is §16's standing
     constraint respected by construction. *)
  Definition ic_payload_np (γfs : fs_names) (γi : gname) (cov : gset Z)
      (logstart : Z) (k : nat) (inum : mword 32) (g : gname)
      (v : bool) : iProp Σ :=
    (if v
     then ∃ (dn : dinode) (bm : blkmap),
            ic_loaded γfs γi cov logstart k inum dn bm ∗
            ity_shot g (di_type dn)
     else ic_unloaded γfs γi cov logstart k inum ∗ ity_pending g)%I.

  Global Instance ic_payload_np_timeless γfs γi cov logstart k inum g v :
    Timeless (ic_payload_np γfs γi cov logstart k inum g v).
  Proof. rewrite /ic_payload_np. destruct v; tl_struct. Qed.

  (* ==================================================================== *)
  (*  THE FREEZE TOKEN RIDES THE PAYLOAD (iclaim-ledger.md §3.1 A-custody, *)
  (*  §3.9 RULING A-prime)                                                 *)
  (* ==================================================================== *)

  (*  A-custody's words are "the freeze token RIDES THE PAYLOAD ... exactly
      like [dinode_at]", and this is where that lands.  [ic_payload] is the
      payload as an ARM holds it; [ic_payload_np] is the same bundle MINUS
      the token, which is what the eviction lemmas below and iput's free
      path speak at.  The split costs no arity anywhere and no other file
      names [ic_payload_np].

      WHY HERE AND NOT IN [ic_loaded].  [ic_loaded] is named in forty-five
      files and destructured in a dozen; [ic_payload] is named in eight.
      Both would put the token on the same custody path -- pool bundle ->
      parked arm -> holder -> parked arm -> pool -- because [ic_parked]'s
      payload conjunct is exactly this predicate.  The cheaper one wins, and
      the expensive one would also have poisoned the FREE path's eviction,
      whose payload is the FREEZER's (its token is standing at [FrzPost],
      not [FrzOff]); with the split, those lemmas keep their exact
      signatures by speaking at [_np].

      WHY [FrzOff] AND NOT [(ifreeze_off ∨ ifreeze_pre)].  A-custody's
      PARKED row offers the disjunction so that the freezer's +0x70 mid-free
      park has somewhere to put its [FrzPre].  That park is [ProofIput]'s and
      [EscrowDeposit]'s -- both red by design in this increment -- and every
      LANDED path through the arms is [FrzOff]-only: the recycle peels
      [FrzOff] out of the pool ([ipool_shape_to_np]), the fill carries it
      [ic_unloaded] -> [ic_loaded], the checkout hands it to the holder, the
      park takes it back and the eviction returns it to the pool's
      [ifreeze_off] arm.  Stating the disjunction now would cost every one of
      those a refutation it cannot yet perform (TRIPWIRE t2's obligation) and
      would buy nothing green.  The widening is the iput integration's, at
      the same one line.

      WHAT IT BUYS, which is the whole point of RULING A-prime: [SpecIlock]'s
      post now hands the holder [ifreeze_off z] beside the payload, so
      create's fresh child (ProofCreate) and sys_link's [ip->nlink++]
      (ProofSysLink) can pay [wp_iupdate_link]'s freeze-pin premise with the
      token arm, where the pure arm [di_nlink dn0 <> 0] is FALSE at the one
      and unavailable at the other. *)
  Definition ic_payload (γfs : fs_names) (γi : gname) (cov : gset Z)
      (logstart : Z) (k : nat) (inum : mword 32) (g : gname)
      (v : bool) : iProp Σ :=
    (ic_payload_np γfs γi cov logstart k inum g v ∗
     ifreeze_off (bv_unsigned inum))%I.

  Global Instance ic_payload_timeless γfs γi cov logstart k inum g v :
    Timeless (ic_payload γfs γi cov logstart k inum g v).
  Proof. rewrite /ic_payload. tl_struct. Qed.

  Lemma ic_payload_split γfs γi cov logstart k inum g v :
    ic_payload γfs γi cov logstart k inum g v -∗
    ic_payload_np γfs γi cov logstart k inum g v ∗
    ifreeze_off (bv_unsigned inum).
  Proof. rewrite /ic_payload. iIntros "H". iExact "H". Qed.

  Lemma ic_payload_join γfs γi cov logstart k inum g v :
    ic_payload_np γfs γi cov logstart k inum g v -∗
    ifreeze_off (bv_unsigned inum) -∗
    ic_payload γfs γi cov logstart k inum g v.
  Proof.
    rewrite /ic_payload. iIntros "H Ht".
    iSplitL "H"; [iExact "H" | iExact "Ht"].
  Qed.

  (* ---- THE PARKED ARM's TAIL, WIDENED BY A⁗ (iclaim-ledger.md §3.16) ----

     DEVIATION 1 (§3.10/§3.14) made the parked arm's TOKEN slot a
     disjunction so that iput's +0x70 mid-free park -- which runs INSIDE the
     freeze window -- had somewhere to put the phase the mint left standing.
     A⁗ widens the same disjunction from the token to the WHOLE tail, and
     that is what dissolves B2 and the ½-parking problem at once:

       LEFT  (the ordinary parked arm) -- the payload, the inum's unfrozen
             token, and the arm's own liveness half at the payload's
             generation.  Byte-for-byte what the arm has always held; the
             [live_gen] conjunct simply moved INSIDE, so that the frozen
             alternative can omit it.
       RIGHT (THE FROZEN PARK, iput +0x5e..+0x8a) -- the freeze RECEIPT and
             NOTHING ELSE.  The freer keeps the payload in its own hand from
             the +0x5e window exit to the +0xa8 deposit ([inode_raw], the
             block resources and, crucially, [dinode_at] with its identity
             intact -- which is exactly B2's "one bundle, two consumers"
             dissolved: there is no bundle to share), and the arm's liveness
             half is parked in [IcacheInv.frz_park], inside [islot2]'s live
             arm, where a foreign [idup] collides with it (OPEN(2.6b)).

     THE DISJUNCTION IS DECIDABLE AT EVERY READER, and by ONE line:
       * at iput+0x70 and +0x8a the freer holds [ifreeze_pre] (kept in hand
         since the mint) and the LEFT arm's [ifreeze_off] dies on
         [IcacheRef.ifreeze_excl];
       * at a CHECKOUT ([ic_swap_checkout]) the holder owes the refutation of
         the RIGHT arm, and RULING R-e pays it from the INVARIANT: the arm
         carries a QUARTER of the slot's freeze selector, [live_slot]'s
         frozen alternative holds the slot's whole liveness unit beside the
         other half, and the deposit the checkout hands straight back carries
         the caller's own positive slice -- [IcacheInv.frz_slot_kill] in one
         line, with no licence and no region open (recorded at ProofIlock).
     Every LEFT-only consumer ([ic_payload], [ic_mk_parked], [ic_swap_park],
     the eviction family) keeps its exact signature. *)
  (* ---- THE LOCK-WINDOW PIN, PER ARM (durable-disk B''-tx5) ----

     [ic_slot_cover]'s alternative (d) was inhabited by iput's three windows,
     and what it cost the commit was a slot at which the escrow holds no
     bundle and says nothing.  Two of the three -- [ic_held] (+0x3c..+0x5e,
     which spans [acquiresleep]) and [ic_payload_arm]'s frozen alternative
     (the +0x70 mid-free park) -- carry no descriptor at all, so a share of
     the freeing transaction's token parked in them would come back at an
     EXISTENTIAL [(t, q)] and could not be rejoined with the residue iput's
     caller must get back.  [IcacheRef.hpn_h] is the pin that fixes it: the
     arm holds one half BESIDE the share and the walk the other, and
     [hpn_agree] re-identifies the pair at the exit.

     THE PIN SITS INSIDE THE ARMS, NOT BESIDE THE DISJUNCTION.  A body-level
     [ic_pin_rest k ∨ ic_pin_tx k] is refutable at an empty [ln_tx]
     authority too, but it says nothing about WHICH arm is standing, so it
     does not refute [ic_held].  Per-arm, LAST conjunct each, it does:
     [ic_pin_rest] in [ic_out] / [ic_mid_arm] / [ic_empty_arm] /
     [ic_payload_arm]'s LEFT, [ic_pin_tx] in [ic_held] and in
     [ic_payload_arm]'s FROZEN alternative.  [DepFrz] needs no pin at all --
     the DESCRIPTOR is in iput's hand across that window, so its [(t, qt)]
     are two more fields of the constructor and the share rides in
     [ic_out_frz], exactly as [DepTx]'s does in [ic_dep_own]. *)
  Definition ic_pin_rest (k : nat) : iProp Σ := hpn_full k None.

  Definition ic_pin_tx (k : nat) : iProp Σ :=
    (∃ (t : nat) (q : Qp),
       hpn_h k (Some (t, q)) ∗ tx_pin icfg_log t q)%I.

  Global Instance ic_pin_rest_timeless k : Timeless (ic_pin_rest k).
  Proof. rewrite /ic_pin_rest. tl_struct. Qed.
  Global Instance ic_pin_tx_timeless k : Timeless (ic_pin_tx k).
  Proof. rewrite /ic_pin_tx. tl_struct. Qed.

  (* THE REFUTATION THE COMMIT READS, and the whole reason the pin exists:
     an arm inside one of iput's two windows holds a POSITIVE share of some
     transaction's [ln_tx] element, so at a commit -- where the WAL's
     authority for that map is EMPTY -- neither window can be standing.
     NO NAMED LEMMA: the two consumers ([ic_escrow_body_cover]'s mid-free
     park and its held arm) open the pin's existential and call the generic
     [TxPin.tx_pin_no_ops] on the share inside. *)

  (* THE PIN'S OWN MOVERS, as the two windows use them.  ENTER: the arm at
     rest hands out the WHOLE cell, the walk names its transaction and its
     share, and the pair splits -- half into the window's arm beside the
     share, half into the walk's hand.  EXIT: the two halves agree, so the
     share comes back AT THE NAMED [(t, q)], and the cell goes back to
     [None] whole. *)
  Lemma ic_pin_enter k (t : nat) (q : Qp) :
    ic_pin_rest k -∗ t ↪[ln_tx icfg_log]{#q} tt ==∗
    ic_pin_tx k ∗ hpn_h k (Some (t, q)).
  Proof.
    iIntros "Hp Htx". rewrite /ic_pin_rest /ic_pin_tx /tx_pin.
    iMod (hpn_full_update _ _ (Some (t, q)) with "Hp") as "Hp".
    rewrite hpn_split. iDestruct "Hp" as "[Hp1 Hp2]".
    iModIntro. iSplitR "Hp2"; [| iExact "Hp2"].
    iExists t, q. iFrame "Hp1 Htx".
  Qed.

  Lemma ic_pin_exit k (t : nat) (q : Qp) :
    hpn_h k (Some (t, q)) -∗ ic_pin_tx k ==∗
    ic_pin_rest k ∗ t ↪[ln_tx icfg_log]{#q} tt.
  Proof.
    iIntros "Hh Hpin". rewrite /ic_pin_tx /ic_pin_rest /tx_pin.
    iDestruct "Hpin" as (t' q') "[Hh' Htx]".
    iDestruct (hpn_agree with "Hh Hh'") as %Heq.
    inversion Heq as [Heq']. subst t' q'.
    iDestruct (hpn_join with "Hh Hh'") as "Hf".
    iMod (hpn_full_update _ _ None with "Hf") as "Hf".
    iModIntro. iFrame.
  Qed.

  Definition ic_payload_arm (γfs : fs_names) (γi : gname) (cov : gset Z)
      (logstart : Z) (k : nat) (inum : mword 32) (g : gname)
      (v : bool) : iProp Σ :=
    ((ic_payload_np γfs γi cov logstart k inum g v
      ∗ ifreeze_off (bv_unsigned inum)
      ∗ live_gen k (1/2) g
      (* the slot is in NEITHER of iput's two windows (durable-disk
         B''-tx5), LAST so no destructuring pattern above moved *)
      ∗ ic_pin_rest k)
     (* RULING R-e (iclaim-ledger.md §5⁗⁗): the frozen alternative IS the
        SELECTOR's quarter.  That quarter is what turns
        ProofIlock:2422 from an unpayable obligation into one line: with it
        and the live slice inside the deposit [ic_swap_checkout] hands back,
        [IcacheInv.frz_slot_kill] closes -- no lock, no licence, no region
        open, no index. *)
     ∨ (frzsel k ((1/2)/2)%Qp true
        (* THE MID-FREE PARK IS A WINDOW (durable-disk B''-tx5): it names the
           freeing transaction and the share it parked, so the +0x8a
           eviction gets that very share back. *)
        ∗ ic_pin_tx k))%I.

  Global Instance ic_payload_arm_timeless γfs γi cov logstart k inum g v :
    Timeless (ic_payload_arm γfs γi cov logstart k inum g v).
  Proof. rewrite /ic_payload_arm. tl_struct. Qed.

  (* the ordinary holder's bundle + the arm's liveness half IS an arm's tail,
     on its LEFT alternative *)
  Lemma ic_payload_to_arm γfs γi cov logstart k inum g v :
    ic_payload γfs γi cov logstart k inum g v -∗
    live_gen k (1/2) g -∗
    ic_pin_rest k -∗
    ic_payload_arm γfs γi cov logstart k inum g v.
  Proof.
    rewrite /ic_payload /ic_payload_arm.
    iIntros "[H Ht] Hl Hpin". iLeft. iFrame.
  Qed.

  (* ...and the FROZEN alternative, which is the selector's quarter and the
     window's own pin *)
  Lemma ic_payload_arm_frz γfs γi cov logstart k inum g v :
    frzsel k ((1/2)/2)%Qp true -∗
    ic_pin_tx k -∗
    ic_payload_arm γfs γi cov logstart k inum g v.
  Proof. rewrite /ic_payload_arm. iIntros "Hs Hpin". iRight. iFrame. Qed.

  (* THE DECIDER at the free path's two readers (+0x70, +0x8a): the
     [ifreeze_pre] the walk has kept in hand since the mint kills the LEFT
     alternative outright ([ifreeze_excl] -- one exclusive ledger cell, two
     fragments), so what comes back is the frozen tail. *)
  Lemma ic_payload_arm_decide_frz γfs γi cov logstart k inum g v (rg : frzidx) :
    ifreeze_pre rg (bv_unsigned inum) -∗
    ic_payload_arm γfs γi cov logstart k inum g v -∗
    ifreeze_pre rg (bv_unsigned inum) ∗
    frzsel k ((1/2)/2)%Qp true ∗
    (* ...AND THE WINDOW'S PIN (durable-disk B''-tx5), which is what the
       +0x8a eviction rejoins with the half it has held since the +0x70
       park: the share comes back at the [(t, q)] the arm NAMES. *)
    ic_pin_tx k.
  Proof.
    rewrite /ic_payload_arm. iIntros "Hpre [(_ & Hoff & _) | Hrc]".
    - iExFalso. rewrite /ifreeze_pre /ifreeze_off.
      iApply (ifreeze_excl with "Hpre Hoff").
    - iFrame.
  Qed.

  (* THE LOADED POLARITY AT A NAMED RECORD (design §20.13/§20.14's (R1)).

     [ic_payload]'s [true] branch binds the record EXISTENTIALLY, which is
     right for the arms -- an arm says "this slot is loaded", not "it is
     loaded at THIS record" -- and wrong for a thread that carries the
     bundle across a window it is going to re-enter.  [ProofIput] is that
     thread: it reads [ip->nlink] at +0x40 off the record it is holding,
     hands the bundle back into the escrow across [acquiresleep], and takes
     it out again at +0x54.  Through an existential the record that comes
     back is a FRESH one and [nlink == 0] does not travel with it -- which
     is precisely the fact the region's (L3) needs at the free (fs-sysfile
     S5f's knot; the missing fact is [di_nlink dn2 = 0]).

     So the window opener below is stated at THIS predicate: the same [dn]
     and [bm] go in and come out.  It is exactly xv6's own REF-1 argument
     -- the sole reference holder's record cannot move under it -- made
     available to the proof, and it costs no arity anywhere: [ic_payload]
     is unchanged, and every arm still binds the record existentially.

     Carrying [⌜di_nlink dn = 0⌝] in the PAYLOAD instead is dead for
     §17.5's reason: the payload is re-parked and the conjunct would have
     to be re-established by whoever picks it up. *)
  Definition ic_payload_at (γfs : fs_names) (γi : gname) (cov : gset Z)
      (logstart : Z) (k : nat) (inum : mword 32) (g : gname)
      (dn : dinode) (bm : blkmap) : iProp Σ :=
    (ic_loaded γfs γi cov logstart k inum dn bm ∗ ity_shot g (di_type dn))%I.

  Global Instance ic_payload_at_timeless γfs γi cov logstart k inum g dn bm :
    Timeless (ic_payload_at γfs γi cov logstart k inum g dn bm).
  Proof. rewrite /ic_payload_at. tl_struct. Qed.

  Lemma ic_payload_at_pack_np γfs γi cov logstart k inum g dn bm :
    ic_payload_at γfs γi cov logstart k inum g dn bm -∗
    ic_payload_np γfs γi cov logstart k inum g true.
  Proof.
    rewrite /ic_payload_np /ic_payload_at. iIntros "H". iExists dn, bm.
    iExact "H".
  Qed.

  (* ...and the arm-level pack, which is the [_np] one plus the token the
     arm owes (§3.9).  The holder that re-parks a named record presents
     both. *)

  Definition ic_dep_own (k : nat) (d : ic_dep) (dev inum : mword 32) : iProp Σ :=
    match d with
    | DepNone => False%I
    (* the FROZEN window (IVd) holds no ordinary deposit at all -- see
       [ic_out_frz], which is what its arm holds instead *)
    | DepFrz _ _ _ _ _ => False%I
    (* THE WRITE ARM (durable-fs-plan.md section 3): the caller's
       generation-named credential plus the PARKED TRANSACTION SHARE.  That share is the whole point --
       [end_op] consumes the WHOLE [ln_tx] element, so it cannot run while
       any inode of the transaction is checked out for writing, and at a
       commit (where the authority is empty) this arm is refuted outright
       ([TxPin.tx_pin_no_ops] at the share).  The descriptor names [(t, q)],
       so the park gives back exactly the share the checkout took. *)
    | DepTx s dv nu g lo t q =>
        (⌜dv = dev /\ nu = inum⌝ ∗ inode_shr_genlo_bare k s dev inum g lo ∗
         tx_pin icfg_log t q)%I
    (* THE READ ARM (durable-fs-plan.md section 3): the write arm's
       credential VERBATIM.  What distinguishes the arm is not it but what
       the escrow KEEPS beside it -- [ic_rd_arm], the bundle's three
       quarters -- which is a conjunct of [ic_out] and not of the deposit,
       because it is indexed by the file system's names and the deposit is
       not. *)
    | DepRd s dv nu g lo =>
        (⌜dv = dev /\ nu = inum⌝ ∗ inode_shr_genlo_bare k s dev inum g lo)%I
    end.

  (* ...and the ARM's OWN 1/2, which the checkout takes out of PARKED and the
     park puts back (design §17.3 (A)).  [ic_out]'s text does not move
     because the slice rides here. *)
  Definition ic_dep_half (k : nat) (d : ic_dep) : iProp Σ :=
    match d with
    | DepNone => False%I
    | DepFrz _ _ _ _ _ => False%I
    | DepTx _ _ _ g _ _ _ => live_gen k (1/2) g
    | DepRd _ _ _ g _ => live_gen k (1/2) g
    end.

  Definition ic_dep_res (k : nat) (d : ic_dep) (dev inum : mword 32) : iProp Σ :=
    (ic_dep_own k d dev inum ∗ ic_dep_half k d)%I.

  Global Instance ic_dep_own_timeless k d dev inum :
    Timeless (ic_dep_own k d dev inum).
  Proof. rewrite /ic_dep_own. destruct d; tl_struct. Qed.

  Global Instance ic_dep_half_timeless k d :
    Timeless (ic_dep_half k d).
  Proof. rewrite /ic_dep_half. destruct d; tl_struct. Qed.

  Global Instance ic_dep_res_timeless k d dev inum :
    Timeless (ic_dep_res k d dev inum).
  Proof. rewrite /ic_dep_res. tl_struct. Qed.

  (* the descriptor's generation is the one its slice names -- the bridge
     between the pure [IcacheRef.ic_dep_gname] side condition every swap
     lemma carries and the resource. *)
  Lemma ic_dep_half_gname k d :
    ic_dep_half k d -∗
    ∃ g : gname, ⌜ic_dep_gname d = Some g⌝ ∗ live_gen k (1/2) g.
  Proof.
    rewrite /ic_dep_half /ic_dep_gname.
    destruct d as [| qf dv nu | s dv nu g lo t q | s dv nu g lo];
      [iIntros "[]" | iIntros "[]" | |];
      iIntros "H"; iExists g; by iFrame.
  Qed.

  (* BOTH SHAPES CARRY AN IDENTITY FRACTION, which is every checkout-side
     refutation's ammunition (EMPTY's full dev cell, MID's and HELD's full inum
     cell).  An accessor rather than a projection, so a refuting opener pays
     nothing and a succeeding one gets the resource back. *)
  Lemma ic_dep_own_ident k d dev inum :
    ic_dep_own k d dev inum -∗
    ∃ f : Qp,
      inode_ident k (DfracOwn f) dev inum ∗
      (inode_ident k (DfracOwn f) dev inum -∗ ic_dep_own k d dev inum).
  Proof.
    rewrite /ic_dep_own.
    destruct d as [| qf dv nu | s dv nu g lo t q | s dv nu g lo];
      [iIntros "[]" | iIntros "[]" | |].
    - iIntros "[%Heq [[Hid Hlv] Htx]]". iExists s. iFrame "Hid".
      iIntros "Hid". iSplitR; [iPureIntro; exact Heq |].
      rewrite /inode_shr_gen_bare. iFrame.
    - iIntros "[%Heq [Hid Hlv]]". iExists s. iFrame "Hid".
      iIntros "Hid". iSplitR; [iPureIntro; exact Heq |].
      rewrite /inode_shr_gen. iFrame.
  Qed.


  (* ...AND BOTH CARRY A LIVENESS SLICE, which is what a lock-free reader
     INSIDE the critical section borrows for its [ip->ref] guard
     ([IcacheInv.iref_live_load_au]).  Under v2 that read borrowed the arm's
     whole reference; under the descriptor there may not BE one, and the slice
     is all the guard ever needed. *)
  Lemma ic_dep_res_live k d dev inum :
    ic_dep_res k d dev inum -∗
    ∃ s : Qp, live_frac k s ∗ (live_frac k s -∗ ic_dep_res k d dev inum).
  Proof.
    rewrite /ic_dep_res /ic_dep_half /live_frac.
    destruct d as [| qf dv nu | s dv nu g lo t q | s dv nu g lo];
      [iIntros "[[] _]" | iIntros "[[] _]" | |].
    - iIntros "[Hown Hhalf]". iExists (1/2)%Qp.
      iSplitL "Hhalf"; [iExists g; iExact "Hhalf" |].
      iIntros "[%g2 Hhalf]".
      iDestruct "Hown" as "[%Heq [[Hid Hlv] Htx]]".
      iDestruct "Hhalf" as (lo2) "Hhalf".
      iDestruct (IcacheRef.live_genlo_agree with "Hlv Hhalf") as %[<- <-].
      iSplitR "Hhalf"; [| iExists lo; iExact "Hhalf"].
      iSplitR; [iPureIntro; exact Heq |].
      rewrite /inode_shr_genlo_bare. iFrame.
    - iIntros "[Hown Hhalf]". iExists (1/2)%Qp.
      iSplitL "Hhalf"; [iExists g; iExact "Hhalf" |].
      iIntros "[%g2 Hhalf]".
      iDestruct "Hown" as "[%Heq [Hid Hlv]]".
      iDestruct "Hhalf" as (lo2) "Hhalf".
      iDestruct (IcacheRef.live_genlo_agree with "Hlv Hhalf") as %[<- <-].
      iSplitR "Hhalf"; [| iExists lo; iExact "Hhalf"].
      iSplitR; [iPureIntro; exact Heq |].
      rewrite /inode_shr_genlo_bare. iFrame.
  Qed.

  (* the depositor's OWN slice, named -- what the checkout agrees against *)
  (* the slice comes out at the descriptor's own EPOCH (the stitch: main's
     [live_gen] form cannot be handed back, an ∃-bound epoch would not
     re-tie the credential's floor) *)
  Lemma ic_dep_own_live k d dev inum :
    ic_dep_own k d dev inum -∗
    ∃ (s : Qp) (g : gname) (lo : nat),
      ⌜ic_dep_gname d = Some g⌝ ∗ ⌜ic_dep_lo d = Some lo⌝ ∗
      IcacheRef.live_genlo k s g lo ∗
      (IcacheRef.live_genlo k s g lo -∗ ic_dep_own k d dev inum).
  Proof.
    rewrite /ic_dep_own /ic_dep_gname /ic_dep_lo.
    destruct d as [| qf dv nu | s dv nu g lo t q | s dv nu g lo];
      [iIntros "[]" | iIntros "[]" | |].
    - iIntros "[%Heq [[Hid Hlv] Htx]]". iExists s, g, lo.
      iSplitR; [done |]. iSplitR; [done |].
      iFrame "Hlv". iIntros "Hlv". iSplitR; [iPureIntro; exact Heq |].
      rewrite /inode_shr_genlo_bare. iFrame.
    - iIntros "[%Heq [Hid Hlv]]". iExists s, g, lo.
      iSplitR; [done |]. iSplitR; [done |].
      iFrame "Hlv". iIntros "Hlv". iSplitR; [iPureIntro; exact Heq |].
      rewrite /inode_shr_genlo_bare. iFrame.
  Qed.

  Lemma ic_dep_half_intro k d g :
    ic_dep_gname d = Some g -> live_gen k (1/2) g -∗ ic_dep_half k d.
  Proof.
    rewrite /ic_dep_gname /ic_dep_half.
    destruct d as [| qf dv nu | s dv nu g2 lo t q | s dv nu g2 lo];
      intros H;
      [discriminate | discriminate | |];
      injection H as <-; iIntros "$".
  Qed.


  (* ---- WHAT A DESCRIPTOR ASKS OF THE WITHDRAWING CALLER ---------------
     (durable-fs-plan.md section 3, [ilock]; durable-disk B''-tx3)

     [ilock]'s two descriptors -- [DepTx] and [DepRd] -- carry the SAME
     credential, the caller's generation-named share, and differ only in what
     rides beside it: a parked transaction share at [DepTx], nothing at the
     read arm.  [ic_dep_shr] reads the common part off the descriptor and
     [ic_dep_side] names the extra, so ONE proof of ilock's code serves both:
     it takes [inode_shr_gen] as it always did plus [ic_dep_side d], and
     hands the checkout [ic_dep_own k d dev inum]. *)
  Definition ic_dep_shr (d : ic_dep) : option (Qp * mword 32 * mword 32 * gname * nat) :=
    match d with
    | DepTx s dv nu g lo _ _ => Some (s, dv, nu, g, lo)
    | DepRd s dv nu g lo => Some (s, dv, nu, g, lo)
    | _ => None
    end.

  (* WHICH TRANSACTION THE DESCRIPTOR PINS, as a PURE reading of it -- the
     [option] shape [TxPin.tx_pin_o] is stated at, and hence what makes
     [ic_dep_side] one instance of the vocabulary rather than a match of its
     own.  It lived in [SpecIunlockput] (the walk that needed to NAME the
     [(t, q)] without destructing a descriptor); its home is here, beside
     [ic_dep_shr], which reads the descriptor's OTHER half. *)
  Definition ic_dep_side_tx (d : ic_dep) : option (nat * Qp) :=
    match d with
    | DepTx _ _ _ _ _ t q => Some (t, q)
    | _ => None
    end.

  Definition ic_dep_side (d : ic_dep) : iProp Σ :=
    tx_pin_o icfg_log (ic_dep_side_tx d).

  (* the equation the two generic [iunlockput] bodies take as a pure premise:
     with the descriptor's pin NAMED, the side condition IS the pin.  It is a
     LEIBNIZ equality between propositions, discharged by [reflexivity] --
     which is what [tx_pin]'s transparency buys ([TxPin]'s header). *)
  Lemma ic_dep_side_of_tx (d : ic_dep) (t : nat) (q : Qp) :
    ic_dep_side_tx d = Some (t, q) ->
    ic_dep_side d = tx_pin icfg_log t q.
  Proof. rewrite /ic_dep_side. intros ->. reflexivity. Qed.

  Global Instance ic_dep_side_timeless d : Timeless (ic_dep_side d).
  Proof. rewrite /ic_dep_side. apply _. Qed.

  Lemma ic_dep_gname_of_shr d (s : Qp) (dev inum : mword 32) (g : gname) (lo : nat) :
    ic_dep_shr d = Some (s, dev, inum, g, lo) -> ic_dep_gname d = Some g.
  Proof.
    rewrite /ic_dep_shr /ic_dep_gname.
    destruct d; try discriminate; intros H; injection H as _ _ _ <- _; reflexivity.
  Qed.

  Lemma ic_dep_lo_of_shr d (s : Qp) (dev inum : mword 32) (g : gname) (lo : nat) :
    ic_dep_shr d = Some (s, dev, inum, g, lo) -> ic_dep_lo d = Some lo.
  Proof.
    rewrite /ic_dep_shr /ic_dep_lo.
    destruct d; try discriminate; intros H; injection H as _ _ _ _ <-; reflexivity.
  Qed.

  Lemma ic_dep_rd_shr d (s : Qp) (dev inum : mword 32) (g : gname) (lo : nat) :
    ic_dep_shr d = Some (s, dev, inum, g, lo) ->
    ic_dep_rd d = true ->
    d = DepRd s dev inum g lo.
  Proof.
    rewrite /ic_dep_shr /ic_dep_rd.
    destruct d; try discriminate; intros H _;
      injection H as <- <- <- <- <-; reflexivity.
  Qed.

  Lemma ic_dep_own_of_shr k d (s : Qp) (dev inum : mword 32) (g : gname) (lo : nat) :
    ic_dep_shr d = Some (s, dev, inum, g, lo) ->
    inode_shr_genlo_bare k s dev inum g lo -∗ ic_dep_side d -∗
    ic_dep_own k d dev inum.
  Proof.
    rewrite /ic_dep_shr /ic_dep_own /ic_dep_side.
    destruct d; try discriminate; intros H; injection H as <- <- <- <- <-;
      iIntros "Hshr Hpark".
    - iSplitR; [iPureIntro; split; reflexivity |].
      iSplitL "Hshr"; [iExact "Hshr" | iExact "Hpark"].
    - iSplitR; [iPureIntro; split; reflexivity | iExact "Hshr"].
  Qed.

  (* ---- THE OUT ARM AND ITS SECOND ALTERNATIVE (IVd, §3.16's item 7) ----

     iput's window exit at +0x5e must deposit NO live mass -- the mint at
     +0x50 has already parked its reference's live slice and the escrow arm's
     half in [islot2]'s frozen park ([IcacheInv.frz_park]), where they must
     stay for the whole lock-free span, because that is where a foreign [idup]
     collides with them.  So the tail is a DISJUNCTION:

       LEFT  (every ordinary checkout) -- [ic_dep_res], the descriptor's own
             credential and the arm's liveness half, byte-for-byte what OUT
             has always held;
       RIGHT (THE FROZEN WINDOW, iput +0x5e..+0x70) -- the reference's COUNT
             FRAGMENT, its IDENTITY fraction, and the freeze RECEIPT: exactly
             [ic_dep_own] MINUS the two live slices, which are in the frozen
             park instead.

     THE COUNT FRAGMENT IS NOT DECORATION: it is exactly what keeps
     [ic_open_auth_ref]'s and [ic_open_held]'s REF-1 refutations of this arm
     alive ([iref_frag_two_lookup] -- two fragments at a count of one).  With
     the live slices parked, the LEFT arm's own live-mass refutation is not
     available and the count is all there is.

     THE IDENTITY FRACTION IS NOT DECORATION EITHER: the +0x70 park has to
     pin the arm's existentially-bound [dev]/[inum] to the cells it is putting
     back, and on the LEFT that pin is [ic_dep_own_ident]'s.  Here it is this
     conjunct, read with [ctx_word4_pointsto_agree] exactly as there.  It is a
     FRACTION, not the ½ discriminator halves: itrunc keeps those.

     AND IT IS STATED AT THE DESCRIPTOR, exactly as [ic_dep_own] is.  The
     window deposits [Xv6Cameras.DepFrz q dev inum], and that buys two things
     at once:

       * every ORDINARY consumer refutes this alternative in ONE LINE.  A
         parker ([ic_swap_park_arm]) and a borrower ([ic_open_out]) both name
         a descriptor WITH a generation, [ic_deposit_agree] / [ic_dep_park]
         pins the arm's to it, and [ic_dep_gname (DepFrz …) = None] closes it
         by [discriminate].  ([ic_dep_res] is [False] at [DepFrz], so the LEFT
         alternative collapses for them at the same stroke.)
       * THE FRACTIONS ARE NAMED.  The +0x70 park takes the count fragment and
         the identity slice back and needs them at exactly the [q] it put in
         -- the eviction rebuilds [iref_tok k q] beside a sleeplock share
         releasesleep returned at [q], and [iref_frag] does not split.  An
         existential fraction in the arm can be pinned by no resource; the
         descriptor pins it.

     WHY THE ARM AND NOT [ic_parked]: this span is the one in which the FREER
     still holds the identity cells (itrunc reads [ip->dev]/[ip->inum] and
     writes [ip->addrs]/[ip->size]), and OUT is the only arm that keeps no
     cells at all.  [ic_parked]'s frozen alternative -- see [ic_payload_arm]
     -- is the +0x70..+0x8a park, where the cells go back, and the freer moves
     from this arm to that one with [ic_swap_park_frz]. *)
  Definition ic_out_frz (k : nat) (d : ic_dep) (dev inum : mword 32) : iProp Σ :=
    match d with
    | DepFrz qf dv nu t qt =>
        (⌜dv = dev /\ nu = inum⌝ ∗
         iref_frag k qf ∗
         inode_ident k (DfracOwn qf) dev inum ∗
         (* RULING R-e: the selector's quarter rides the DepFrz window too --
            it is the same quarter, moving from the mint through the OUT arm
            to [ic_parked]'s frozen tail at the +0x70 park. *)
         frzsel k ((1/2)/2)%Qp true ∗
         (* THE PARKED TRANSACTION SHARE (durable-disk B''-tx5), [DepTx]'s
            conjunct at the window that carries no ordinary deposit: it is
            what makes the commit refute this arm ([TxPin.tx_pin_no_ops]) and
            the descriptor is what pins it to the share the freer must get
            back.  LAST, so no destructuring pattern above moved. *)
         tx_pin icfg_log t qt)%I
    | _ => False%I
    end.

  Global Instance ic_out_frz_timeless k d dev inum :
    Timeless (ic_out_frz k d dev inum).
  Proof. rewrite /ic_out_frz /inode_ident. destruct d; tl_struct. Qed.

  (* ...and the refutation the commit reads off it, at the freeze window: a
     [DepFrz] arm holds a positive share of an open transaction's element, so
     at an empty authority it cannot stand.  NO NAMED LEMMA -- the one
     consumer ([ic_escrow_body_cover]'s frozen alternative) takes the share
     out of the arm and calls [TxPin.tx_pin_no_ops]. *)

  (* WHAT THE ARM KEEPS BESIDE THE CREDENTIAL, keyed by the descriptor: the
     READ arm's three quarters at [DepRd], and nothing at all at every other
     descriptor -- a write-locked inode's bundle is wholly in its holder's
     hand (that is what [DepTx]'s parked transaction share pays for), and
     iput's two windows carry no bundle either. *)
  Definition ic_out_rd (γfs : fs_names) (γi : gname) (cov : gset Z)
      (logstart : Z) (d : ic_dep) (inum : mword 32) : iProp Σ :=
    match d with
    | DepRd _ _ _ _ _ => ic_rd_arm γfs γi cov logstart inum
    | _ => emp%I
    end.

  Lemma ic_out_rd_none γfs γi cov logstart d inum :
    ic_dep_rd d = false ->
    ic_out_rd γfs γi cov logstart d inum = emp%I.
  Proof. destruct d; cbn; try reflexivity. discriminate. Qed.

  Global Instance ic_out_rd_timeless γfs γi cov logstart d inum :
    Timeless (ic_out_rd γfs γi cov logstart d inum).
  Proof. rewrite /ic_out_rd. destruct d; tl_struct. Qed.

  Local Typeclasses Opaque ic_out_rd.

  (* ...AND WHAT THE HOLDER CARRIES OUT, the complement of [ic_out_rd] and
     keyed by the same boolean (durable-disk B''-tx3).  A checkout at a
     bundleless descriptor hands over the WHOLE loaded bundle; a checkout at
     [DepRd] leaves three quarters in the arm and what leaves is the reader's
     [ic_rd_held].  [SpecIlock]'s ONE generic contract posts this, so the
     plain form and the read form are one statement. *)
  Definition ic_dep_held (γfs : fs_names) (γi : gname) (cov : gset Z)
      (logstart : Z) (d : ic_dep) (k : nat) (inum : mword 32)
      (dn : dinode) (bm : blkmap) : iProp Σ :=
    (if ic_dep_rd d
     then ic_rd_held γfs cov logstart k inum dn bm
     else ic_loaded γfs γi cov logstart k inum dn bm)%I.


  (* THE ARM GAINED THE FILE SYSTEM'S NAMES, and nothing outside this file
     names [ic_out] at all. *)
  Lemma ic_mk_unloaded γfs γi cov logstart k (inum : mword 32) :
    inode_raw (ientry k) -∗
    ipool_shape_np γfs γi cov logstart inum -∗
    ic_unloaded γfs γi cov logstart k inum.
  Proof.
    iIntros "Hr Hp". rewrite /ic_unloaded.
    iSplitL "Hr"; [iExact "Hr" | iExact "Hp"].
  Qed.

  (* [ic_loaded]'s own tail is the same 268-element [inode_blocks] big-op
     ([InodeInv.MAXFILE] = 268) that motivates the arms' constructors above,
     and it is reached far more often -- every [create]/[iput]/[dirlink] site
     that re-parks a loaded slot rebuilds it.  Measured at ProofCreate's
     eight construction sites: 90-172 s per bare-[iFrame] close, free by
     name here. *)
  (* THE CLOSE, AS IT STANDS SINCE durable-disk 2b-inode-3: the SAME
     argument list as before plus the era's abstract value [top_frag] and
     the three record-only facts [inode_ok] does not carry
     ([FsStateEra.inode_rec_local] -- the type enumeration, the nlink bound
     and a directory's 16-divisible size).  Both are the walk's own
     evidence: the fragment is what it retagged at its writes
     ([InodeRegion.ireg_top_retag]) and the three facts are what its record
     delta preserved.  [inode_ok] stays a PREMISE here rather than a
     conjunct of the payload -- every producer already had it, and it is
     what [FsStateEra.inode_local_of_ok_rec] needs. *)
  Lemma ic_mk_loaded γfs γi cov logstart k (inum : mword 32)
      (dn : dinode) (bm : blkmap) (data : nat -> list (bv 8)) :
    inode_ok cov logstart dn bm data ->
    inode_rec_local dn ->
    dir_ok icfg_nib dn data ->
    dir_dots_ix (bv_unsigned inum) dn data ->
    dir_orphan_clean dn data ->
    dir_uniq dn data ->
    dlinks γfs (bv_unsigned inum) dn bm data -∗
    dinode_at γi inum dn -∗
    inode_meta (ientry k) dn -∗
    inode_addrs (ientry k) (bm_cells bm) -∗
    ind_res γfs bm -∗
    inode_blocks γfs bm data -∗
    top_frag (fs_gamma_L γfs) (bv_unsigned inum) (era_node dn bm data) -∗
    ic_loaded γfs γi cov logstart k inum dn bm.
  Proof.
    intros Hok Hrl Hdok Hddix Hdoc Hduq.
    iIntros "Hl Hd Hm Ha Hr Hb Ht".
    pose proof (node_shape_ok_of_inode_ok cov logstart dn bm data Hok) as Hsh.
    pose proof (inode_local_of_ok_rec (bv_unsigned inum) cov logstart dn bm
                  data Hok Hrl Hduq Hddix) as Hloc.
    pose proof Hok as Hok'. destruct Hok' as (_ & _ & _ & Hty & _ & _ & _).
    rewrite /ic_loaded.
    iExists data. iSplitR; [done |]. iSplitR; [done |]. iSplitR; [done |].
    iSplitR; [done |]. iSplitR; [done |].
    iSplitR "Hm Ha".
    { iApply (ic_inode_leg_era_intro with "Hl").
      iApply (inode_owned_era_era_node_of γfs γi inum dn bm data Hsh Hloc
                with "Hd Hr Hb Ht"). }
    iSplitL "Hm"; [iExact "Hm" | iExact "Ha"].
  Qed.

  (* THE OPEN, the other half of the same seam, and it is an ORDINARY
     ENTAILMENT.  It hands back EXACTLY the conjunct list [ic_loaded] used
     to have, in the same order, plus the two things the era bundle knows
     and the old payload did not: the era's abstract value [top_frag]
     (which a re-park retags, [InodeRegion.ireg_top_retag]) and
     [FsStateEra.inode_rec_local] of the record, which a re-park owes of
     its NEW record and gets here for its old one.  So a consumer's whole
     cost is one line -- this lemma in place of the [rewrite /ic_loaded] it
     used to do -- and two extra names in its destructuring pattern.  No
     mask moves; see [ipool_alloc]'s note. *)
  (* THE FLAT SHAPE: [ic_loaded]'s OLD conjunct list, in the OLD order, with
     the two things the era bundle knows and the old payload did not --
     [FsStateEra.inode_rec_local] of the record (second, so that a producer
     that had [inode_ok] proves the two together) and the era's abstract
     value [FsState.top_frag] (just before the two contents holds, which it
     rides beside everywhere else).  It is what the ~forty consumer sites
     open and close through, so the flip costs each of them one lemma name,
     one pure conjunct and one framed hypothesis instead of a rewritten
     re-pack.  [ic_loaded_flat] and [ic_loaded_open] are the two directions;
     [ic_mk_loaded] is the same close with the pieces as separate wands. *)
  Definition ic_loaded_flat_body (γfs : fs_names) (γi : gname) (cov : gset Z)
      (logstart : Z) (k : nat) (inum : mword 32)
      (dn : dinode) (bm : blkmap) : iProp Σ :=
    (∃ (data : nat -> list (bv 8)),
       ⌜inode_ok cov logstart dn bm data⌝ ∗
       ⌜inode_rec_local dn⌝ ∗
       ⌜dir_ok icfg_nib dn data⌝ ∗
       ⌜dir_dots_ix (bv_unsigned inum) dn data⌝ ∗
       ⌜dir_orphan_clean dn data⌝ ∗
       ⌜dir_uniq dn data⌝ ∗
       dlinks γfs (bv_unsigned inum) dn bm data ∗
       dinode_at γi inum dn ∗
       inode_meta (ientry k) dn ∗
       inode_addrs (ientry k) (bm_cells bm) ∗
       ind_res γfs bm ∗
       inode_blocks γfs bm data ∗
       (* THE TWO CONTENTS HOLDS THAT USED TO SIT HERE, between the blocks
          and the era fragment, are retired (THE DVIEW RETIREMENT): every
          consumer's spatial pattern loses two names and every re-pack two
          [iSplitL]s, and the era fragment below is the reading they were. *)
       top_frag (fs_gamma_L γfs) (bv_unsigned inum) (era_node dn bm data))%I.

  (* R3 (F24): the loaded bundle's 13 addrs cells, off [inode_ok]'s
     [blkmap_wf] -- what the box's rest row states and the park re-forms *)
  Lemma ic_loaded_bm_len γfs γi cov logstart k (inum : mword 32)
      (dn : dinode) (bm : blkmap) :
    ic_loaded γfs γi cov logstart k inum dn bm -∗ ⌜length (bm_cells bm) = 13%nat⌝.
  Proof.
    iIntros "H". rewrite /ic_loaded. iDestruct "H" as (data) "(%Hok & _)".
    iPureIntro. destruct Hok as (Hwf & _).
    rewrite /bm_cells length_app (blkmap_wf_dir_len _ _ _ Hwf). reflexivity.
  Qed.

  Lemma ic_loaded_open γfs γi cov logstart k (inum : mword 32)
      (dn : dinode) (bm : blkmap) :
    ic_loaded γfs γi cov logstart k inum dn bm -∗
    ic_loaded_flat_body γfs γi cov logstart k inum dn bm.
  Proof.
    iIntros "H". rewrite /ic_loaded /ic_loaded_flat_body.
    iDestruct "H" as (data)
      "(%Hok & %Hdok & %Hddix & %Hdoc & %Hduq & Hleg & Hm & Ha)".
    iDestruct (ic_inode_leg_era_open with "Hleg") as "[Hl Hn]".
    pose proof (node_shape_ok_of_inode_ok cov logstart dn bm data Hok) as Hsh.
    iDestruct (inode_owned_era_local with "Hn") as %Hloc.
    iDestruct (inode_owned_era_era_node_to γfs γi inum dn bm data Hsh with "Hn")
      as "(Hd & Hr & Hb & Ht)".
    iExists data.
    iSplitR; [iPureIntro; exact Hok |].
    iSplitR; [iPureIntro;
              exact (inode_rec_local_of (bv_unsigned inum)
                       (era_node dn bm data) Hloc) |].
    iSplitR; [done |]. iSplitR; [done |]. iSplitR; [done |]. iSplitR; [done |].
    iSplitL "Hl"; [iExact "Hl" |].
    iSplitL "Hd"; [iExact "Hd" |].
    iSplitL "Hm"; [iExact "Hm" |].
    iSplitL "Ha"; [iExact "Ha" |].
    iSplitL "Hr"; [iExact "Hr" |].
    iSplitL "Hb"; [iExact "Hb" | iExact "Ht"].
  Qed.

  Lemma ic_loaded_flat γfs γi cov logstart k (inum : mword 32)
      (dn : dinode) (bm : blkmap) :
    ic_loaded_flat_body γfs γi cov logstart k inum dn bm -∗
    ic_loaded γfs γi cov logstart k inum dn bm.
  Proof.
    rewrite /ic_loaded_flat_body. iIntros "H".
    iDestruct "H" as (data)
      "(%Hok & %Hrl & %Hdok & %Hddix & %Hdoc & %Hduq & Hl & Hd & Hm & Ha & Hr & Hb
        & Ht)".
    iApply (ic_mk_loaded γfs γi cov logstart k inum dn bm data
              Hok Hrl Hdok Hddix Hdoc Hduq
              with "Hl Hd Hm Ha Hr Hb Ht").
  Qed.

  (* the pool entry the free path parks at iput+0x94, on its AWAIT arm: the
     uncached ledger row the last close produced, and the escrow the freer
     minted around the [FrzPost] token it left standing. *)
  Lemma ipool_shape_await γfs γi cov logstart (inum : mword 32)
      (ge gr gd : gname) (rg : frzidx) :
    icnt_half (bv_unsigned inum) 0%nat -∗
    frzm_h (bv_unsigned inum) false -∗
    escA_inv γfs ge gr gd (bv_unsigned inum) rg -∗
    redeem_ticketA gr -∗
    (* THE ERA'S ABSTRACT VALUE DOES NOT COME HERE (durable-disk C-3c): the
       freer hands it to [EscrowInode.escA_alloc] at the mint instead, and
       the off-lock deposit parks it region-side. *)
    (* AN IN-TRANSITION ROW, NAMED (durable-disk C-7): what the free path
       parks is the lock's half of a corpse -- [ipool_put_corpse] is what
       takes it, and the corpse ledger's row in [ipool_body] is the other
       half. *)
    ipool_ext γfs γi cov logstart inum.
  Proof.
    iIntros "Hcnt Hmir #Hesc Htk". rewrite /ipool_ext.
    iSplitL "Hcnt"; [iExact "Hcnt" |].
    iSplitL "Hmir"; [iExact "Hmir" |].
    iRight.
    rewrite /pool_await. iExists ge, gr, gd, rg.
    iSplitR; [iExact "Hesc" | iExact "Htk"].
  Qed.


  (* THE SHRINK, on the body: the OUT arm is already at [DepTx] and its
     share drops from [q1 + q2] to [q1], the difference coming home to the
     holder.  It is [ic_arm_tx_body]'s [ghost_var_update_2] verbatim, with
     the descriptor moving between two [DepTx]s. *)


  (* ------------------------------------------------------------------ *)
  (*  5.  THE POOL (§13.2 / §13.3)                                       *)
  (* ------------------------------------------------------------------ *)

  (* THE CACHED SET, speakable.  [M] is slot-keyed and value-blind and the
     inums live in identity CELLS, so [itable_res2] carries a pure
     slot -> (dev, inum) map [ci] alongside; the pool then covers the
     region's inums MINUS the cached ones. *)
  Definition ci_inums (ci : gmap nat (mword 32 * mword 32)) : gset Z :=
    list_to_set ((fun p => bv_unsigned (snd (snd p))) <$> map_to_list ci).

  Lemma ci_inums_spec (ci : gmap nat (mword 32 * mword 32)) (z : Z) :
    z ∈ ci_inums ci <->
    ∃ (k : nat) (p : mword 32 * mword 32), ci !! k = Some p /\ z = bv_unsigned (snd p).
  Proof.
    rewrite /ci_inums elem_of_list_to_set elem_of_list_fmap.
    split.
    - intros ([k p] & -> & Hin). exists k, p.
      split; [| reflexivity]. by apply elem_of_map_to_list in Hin.
    - intros (k & p & Hk & ->). exists (k, p).
      split; [reflexivity |]. by apply elem_of_map_to_list.
  Qed.

  (* THE REGION'S INUMS: sixteen per dinode block. *)
  Definition region_inums (nib : nat) : gset Z :=
    list_to_set (Z.of_nat <$> seq 0 (16 * nib)).

  Lemma region_inums_spec (nib : nat) (z : Z) :
    z ∈ region_inums nib <-> 0 <= z < 16 * Z.of_nat nib.
  Proof.
    rewrite /region_inums elem_of_list_to_set elem_of_list_fmap.
    split.
    - intros (j & -> & Hj). apply elem_of_seq in Hj. lia.
    - intros [Hlo Hhi]. exists (Z.to_nat z).
      split; [lia |]. apply elem_of_seq. lia.
  Qed.

  (* THE FOUR WF CLAUSES (§13.2, §13.9 on why the first one is an
     EQUALITY after all, §13.11 for the fourth): [ci] records exactly the
     LIVE slots, at ONE device.

     §13.7 weakened this to [dom M ⊆ dom ci] so that iput's last close could
     leave a ref-0 entry CACHED, and §13.9 undid that: xv6's scan hit-test
     requires [ref > 0] and its recycle takes the FIRST ref-0 slot without
     ever consulting a ref-0 slot's identity, so a cached ref-0 entry for
     inum B does not stop a later [iget(B)] recycling a DIFFERENT slot for B
     -- ci-injectivity is then false, and two escrow arms hold B's bundle
     against [InodeRegion.dinode_at_excl].  Under the equality a non-live
     slot holds no payload at all (its arm is [ic_empty_arm]) and the
     bundle went back to the pool at iput's last close, where the flush
     semantics that justify the eviction actually hold.  §13.8's empty arm is
     what makes the equality satisfiable at boot, which is what §13.7 thought
     it was fixing.

     [ci] is INJECTIVE on inums (xv6's own guarantee -- iget recycles only
     after a full scan misses, and the scan's LIVE-slot loop invariant is
     exactly what proves it, now that live is all [ci] records); and every
     cached inum is inside the inode region, which is what makes
     [mword_of_int] faithful on the pool's keys.

     AND THE TABLE IS SINGLE-DEVICE (§13.11).  The region and the pool are
     inum-keyed -- [InodeRegion]'s map is one file system's, [dinode_at γi
     inum dn] names an inum and nothing else -- so "this inum is not
     cached" has to be decidable from the inums alone.  But xv6's scan
     hit-test is on the PAIR (`ip->dev == dev && ip->inum == inum`, and the
     dev compare at iget+0x4c short-circuits BEFORE the inum is ever
     loaded), so a scan that misses proves only that no live slot carries
     (dev, inum) -- and a live slot at (dev', inum) would leave iget's
     recycle with no bundle to withdraw, a second [dinode_at] for one inum
     against [InodeRegion.dinode_at_excl], and [ci]-injectivity broken.
     The two coincide exactly when every cached entry has the SAME device,
     which is what this clause says and what [BioInv]'s [bv_dev V] already
     says for the buffer cache.  [dv] is the table's device; iget and idup
     instantiate it at their own [dev] argument, so the clause is
     re-established by construction at the one place [ci] grows. *)
  Definition ic_ci_wf (M : gmap nat (Qp * positive))
      (ci : gmap nat (mword 32 * mword 32)) (nib : nat) (dv : mword 32) : Prop :=
    dom ci = dom M
    /\ (forall (k1 k2 : nat) (p1 p2 : mword 32 * mword 32),
          ci !! k1 = Some p1 -> ci !! k2 = Some p2 ->
          bv_unsigned (snd p1) = bv_unsigned (snd p2) -> k1 = k2)
    /\ (forall (k : nat) (p : mword 32 * mword 32),
          ci !! k = Some p -> bv_unsigned (snd p) < 16 * Z.of_nat nib)
    /\ (forall (k : nat) (p : mword 32 * mword 32),
          ci !! k = Some p -> fst p = dv).

  (* the pool's keys are region inums, so [mword_of_int] round-trips *)
  Lemma region_inum_faithful (nib : nat) (z : Z) :
    (16 * Z.of_nat nib <= 2 ^ 32) ->
    z ∈ region_inums nib ->
    bv_unsigned (mword_of_int z : mword 32) = z.
  Proof.
    intros Hnib Hz. apply region_inums_spec in Hz.
    apply moi32_small. lia.
  Qed.

  (* ==================================================================== *)
  (*  5b.  THE POOL, SPLIT BY ARM (durable-disk lane B''-esc;              *)
  (*       durable-fs-plan.md section 4, the commit's collection)          *)
  (* ==================================================================== *)

  (* ---- WHY THE POOL CANNOT SIMPLY MOVE INTO AN INVARIANT --------------
     (durable-fs-plan.md section 4: the commit has to collect the UNCACHED
     inodes' bundles too, and it cannot take the itable spinlock.)

     [inv N P] hands its opener [|> P].  Both of this pool's consumers --
     iget's miss (ProofIget, the withdraw at the +0x72 store) and iput's
     evictions (ProofIput's two deposits) -- spend the bundle inside a
     store's ATOMIC UPDATE, where there is no step left to absorb a later
     (this file's own note at the head of section 0), and this tree has no
     later credits ([RiscvPtsto.num_laters_per_step _ := 0]).  So an
     invariant-resident pool would have to be TIMELESS, and the full
     the pool row is not: its pending and await alternatives hold
     [EscrowInode.escA_inv], an [inv].  [ipool_no_timeless_check] below is
     that obstruction, checked.

     SO THE POOL SPLITS BY ARM.  [ipool_ord] -- the ORDINARY alternative,
     which is the only one carrying an [FsStateEra.inode_owned_era] at all,
     i.e. the only one the commit's collection wants -- IS timeless, and it
     goes into an Iris invariant at [ipoolN] ([iInv .. as ">"] keeps working
     at both consumers).  [ipool_ext] -- pending and await, the two
     in-transition arms a FREER parks -- stays under the itable lock, and
     the lock keeps the invariant's index set as the RESIDENCY KEY, one
     conjunct in [ipool]'s own position.  So neither [itable_res2]'s arity
     nor iget's scan-loop hypothesis list moves, and no consumer outside
     this file's two movers ([ipool_take], [ipool_put]) changes shape.

     A consumer that lands on a pending/await inum refutes or redeems it
     exactly where it does today -- [ipool_shape_to_np], the caller's
     licence and [IcacheRef.ifreeze_excl] -- because both movers hand out
     and take back the FULL pool row. *)

  (* THE ORDINARY ROWS, as one big-op -- what boot stocks and what the
     invariant is allocated from. *)
  Definition ipool_rows (γfs : fs_names) (γi : gname) (cov : gset Z)
      (logstart : Z) (P : gset Z) : iProp Σ :=
    ([∗ set] z ∈ P, ipool_ord γfs γi cov logstart (mword_of_int z))%I.

  Global Instance ipool_rows_timeless γfs γi cov logstart P :
    Timeless (ipool_rows γfs γi cov logstart P).
  Proof. rewrite /ipool_rows. tl_struct. Qed.

  (* THE RESIDENCY KEY.  Two halves at [icfg_pool] (ambient, see
     [IcacheRef]): one inside the invariant, one under the itable lock, so
     that only a lock holder moves the index and the commit -- which never
     takes the lock -- can still read every row. *)
  Definition ipool_key (P : gset Z) : iProp Σ :=
    ghost_var icfg_pool (1/2) P.

  (* ==================================================================== *)
  (*  5c.  THE PARTITION (durable-disk lane C-3b; durable-fs-plan.md       *)
  (*       section 4, the commit's collection)                             *)
  (*                                                                      *)
  (*  THE COMMIT HAS TO KNOW THAT IT HAS SEEN EVERY INUM.  It opens the    *)
  (*  pool invariant (one bundle per index entry) and the fifty escrows    *)
  (*  (one bundle per LIVE slot), and what it needs is that between them   *)
  (*  they exhaust [region_inums nib].  Neither side knows that today:     *)
  (*  the fact is [ic_ci_wf]'s [dom ci = dom M] plus [ipool]'s domain, and *)
  (*  BOTH are under the itable spinlock, which the commit's ghost step    *)
  (*  cannot take.                                                        *)
  (*                                                                      *)
  (*  SO THE POOL'S INVARIANT CARRIES THE PARTITION, and a QUARTER of      *)
  (*  every slot's [ic_id] beside it is what makes it speak about the      *)
  (*  escrows: the escrow arm holds a HALF of the same cell, so a reader   *)
  (*  with both open reads one identity, not two.  Every mover of a        *)
  (*  slot's identity (iget's recycle, iput's two evictions) therefore     *)
  (*  opens this invariant too, and it is exactly there that the partition *)
  (*  changes.  [islot2] keeps the remaining quarter.                      *)
  (*                                                                      *)
  (*  IT IS A THREE-WAY PARTITION AND NOT THE TWO-WAY ONE B''-join         *)
  (*  IMAGINED, AND THAT IS A FINDING, not a convenience.  "[O] together   *)
  (*  with the live slots' identities exhausts the region" is FALSE in     *)
  (*  this kernel, for two reasons that are one reason:                    *)
  (*                                                                      *)
  (*   - iput's FREE path deposits an AWAIT row ([ipool_ext]), which by    *)
  (*     construction cannot live in an invariant ([EscrowInode.escA_inv]  *)
  (*     is an [inv], hence not Timeless -- section 5b's whole reason for  *)
  (*     the split), so it sits under the lock in [ipool]'s own [P ∖ O]    *)
  (*     and the invariant's index never sees it.  That row holds NO       *)
  (*     [FsStateEra.inode_owned_era] at all, so no partition could have   *)
  (*     handed the commit a bundle for it anyway.                         *)
  (*   - an eviction's identity flip and its deposit are TWO ghost steps   *)
  (*     (the deposited bundle's three ledger columns do not exist until   *)
  (*     the refcount store has fired), so the evicted inum is in neither  *)
  (*     part in between.                                                 *)
  (*                                                                      *)
  (*  Both are the same thing -- an inum a WALK is carrying -- so both go  *)
  (*  into one third part [X], the IN-TRANSITION index.  It is pinned, not *)
  (*  free: [icfg_pext]'s other half is a conjunct of [ipool], so a lock   *)
  (*  holder is the only one who can grow it and the partition cannot go   *)
  (*  vacuous by taking [X] to be the whole region.  At boot [X] is empty  *)
  (*  and the partition IS B''-join's two-way one ([ipool_alloc_inv]).     *)
  (*                                                                      *)
  (*  WHAT IT LEAVES THE COLLECTION is one residue, the pool-side twin of  *)
  (*  [ic_escrow_body_cover]'s alternative (d): an inum in [X] has no      *)
  (*  bundle anywhere.  It is refutable at a commit for the same reason    *)
  (*  (d) is -- a walk inside iput's free window holds an open             *)
  (*  transaction's token and the commit runs at [outstanding = 0] -- and  *)
  (*  closing it is the same ABI sweep, so it belongs with (d).            *)
  (* ==================================================================== *)

  (* THE PARTITION'S TWO SET MOVES.  [set_solver] does not close either --
     both need the decidable split on [y = z], which [naive_solver] will not
     take -- so they are stated once here and cited at the movers. *)


  (* THE IN-TRANSITION KEY, the twin of [ipool_key] and in the same two
     places: one half inside the invariant, one inside [ipool]. *)
  Definition ipool_xkey (X : gset Z) : iProp Σ :=
    ghost_var icfg_pext (1/2) X.

  (* ==================================================================== *)
  (*  5c'.  THE TRANSIT LEDGER (durable-disk lane C-4, plan section 4)     *)
  (*                                                                      *)
  (*  C-3b's third part [X] IS TWO THINGS, AND THEY ARE UNLIKE -- that is  *)
  (*  B''-tx4's finding, and it is what forced this split.  An [ipool_ext] *)
  (*  row (iput's free path's pending/await deposit) stands until a LATER  *)
  (*  [iget] of that inum redeems it, arbitrarily many transactions on, so *)
  (*  no share of the depositing transaction can ever be parked for it and *)
  (*  "[X] is empty at a commit" is FALSE as stated.  The inum a walk is   *)
  (*  CARRYING between an eviction's identity flip and its deposit is the  *)
  (*  opposite: that window is INSIDE one transaction (iput holds a share  *)
  (*  of its caller's token, durable-disk B''-tx5), so the row can park    *)
  (*  one and the commit refutes it exactly as it refutes iput's three     *)
  (*  windows, at [TxPin.tx_pin_no_ops]'s line.                            *)
  (*                                                                      *)
  (*  SO THE TRANSIT PART GETS ITS OWN KEY, and the share must sit in      *)
  (*  [ipool_body] -- not under the itable lock -- because the commit's    *)
  (*  ghost step takes no lock.                                           *)
  (*                                                                      *)
  (*  [(t, q)] ARE FIELDS OF THE LEDGER and not existentials inside the    *)
  (*  parked share, for [Xv6Cameras.ic_dep]'s reason verbatim              *)
  (*  -- two halves are not the whole: [ipool_put] has to hand             *)
  (*  the walk back EXACTLY the element it parked, and an existentially    *)
  (*  keyed share cannot be re-identified.  The ledger is a [ghost_var]    *)
  (*  whose other half the walk carries inside [ipool], so the two agree.  *)
  (* ==================================================================== *)

  Definition ipool_tkey (T : gmap Z (nat * Qp)) : iProp Σ :=
    ghost_var icfg_ptrn (1/2) T.

  (* one parked share per inum in transit, at the ledger's own [(t, q)] --
     [TxPin.tx_pins] at the pool's key, which is exactly the shape *)
  Definition ipool_transit (T : gmap Z (nat * Qp)) : iProp Σ :=
    tx_pins icfg_log T.

  Global Instance ipool_transit_timeless T : Timeless (ipool_transit T).
  Proof. rewrite /ipool_transit. tl_struct. Qed.

  (* THE REFUTATION THE COMMIT READS, and the whole reason the ledger exists:
     every inum in transit has a POSITIVE share of some transaction's [ln_tx]
     element parked for it, so at a commit -- where the WAL's authority for
     that map is EMPTY -- nothing is in transit.  NO NAMED LEMMA: the ledger
     IS a [TxPin.tx_pins], so its one consumer ([ipool_quiesce_acc]) calls
     [TxPin.tx_pins_no_ops] on it directly. *)

  (* ==================================================================== *)
  (*  5c''.  THE CORPSE LEDGER (durable-disk lane C-7, plan section 4)     *)
  (*                                                                      *)
  (*  WHAT [X] LEFT THE COLLECTION, AND WHY IT NEEDED A LEDGER OF ITS      *)
  (*  OWN.  Section 5c's third part is the pending/await rows, and those   *)
  (*  live under the itable SPINLOCK ([EscrowInode.escA_inv] is an [inv],  *)
  (*  so [ipool_ext] is not Timeless and cannot enter this body).  A       *)
  (*  commit's ghost step takes no lock, so at an [X] inum it saw NOTHING  *)
  (*  -- and the region slot there is on its MARKED sub-arm from the free  *)
  (*  path's eviction until the OFF-LOCK deposit, which carries            *)
  (*  [InodeRegion.imark] and no record, so the region had nothing to give *)
  (*  either.  That was residue (G) ([FsCollect]'s section 5d).            *)
  (*                                                                      *)
  (*  SO THE MARKER MOVES HERE.  One row per [X] inum, in THIS body, at    *)
  (*  the value [Xv6Cameras.icorpse] gives it:                             *)
  (*                                                                      *)
  (*    [CrpPre t q] -- the deposit has not run, and the row parks the     *)
  (*      freeing transaction's share, so a commit refutes the state       *)
  (*      outright ([ipool_corpse_no_ops], whose row is a                  *)
  (*      [TxPin.tx_pin_no_ops]).  The share is the very one the transit   *)
  (*      ledger returns at [ipool_put_corpse]: iput parks it and the      *)
  (*      deposit hands it back.                                          *)
  (*    [CrpDep] -- the deposit HAS run, and the row parks                 *)
  (*      [InodeRegion.imark], which is what [FsCollect.col_free_slot_acc] *)
  (*      reads as the free bundle.                                       *)
  (*                                                                      *)
  (*  THE KEY IS A [ghost_map] AND NOT [ipool_tkey]'s PAIRED [ghost_var],  *)
  (*  and that is forced: the deposit runs twenty instructions after iput  *)
  (*  released the itable lock, so it holds neither half of [icfg_pext]    *)
  (*  and cannot tell that its own inum is in [X].  Its ELEMENT locates    *)
  (*  the row instead ([EscrowDefs.crp_elem]) -- carried from              *)
  (*  [ipool_put_corpse] to [EscrowDeposit.ireg_free_deposit_au], where it *)
  (*  is updated to [CrpDep] and handed to the escrow's FILLED arm.        *)
  (*                                                                      *)
  (*  THAT LAST HOP IS THE TIE BETWEEN THE TWO ONE-SHOTS, and without it   *)
  (*  the recycle is unprovable: the escrow and the ledger both record     *)
  (*  "has the deposit run", and [ipool_take_lend] must conclude the       *)
  (*  ledger's state from the escrow's peel.  It does, by                  *)
  (*  [ghost_map_lookup] against the element the peel returns.             *)
  (* ==================================================================== *)

  (* the ledger's AUTHORITY, whole and in this body alone *)
  Definition ipool_ckey (K : gmap Z icorpse) : iProp Σ :=
    ghost_map_auth icfg_pcrp 1 K.

  (* what one row parks, by its value *)
  Definition crp_row (γi : gname) (z : Z) (v : icorpse) : iProp Σ :=
    match v with
    | CrpPre t q => tx_pin icfg_log t q
    | CrpDep => imark γi z
    end.

  Definition ipool_corpse (γi : gname) (K : gmap Z icorpse) : iProp Σ :=
    ([∗ map] z ↦ v ∈ K, crp_row γi z v)%I.

  Global Instance crp_row_timeless γi z v : Timeless (crp_row γi z v).
  Proof. destruct v; rewrite /crp_row; apply _. Qed.

  Global Instance ipool_corpse_timeless γi K : Timeless (ipool_corpse γi K).
  Proof. rewrite /ipool_corpse. tl_struct. Qed.

  Global Instance ipool_ckey_timeless K : Timeless (ipool_ckey K).
  Proof. rewrite /ipool_ckey. tl_struct. Qed.

  (* THE WHOLE LEDGER, REFUTED ROW BY ROW: a corpse whose deposit has not
     run parks a POSITIVE share of the freeing transaction's element, and at
     a commit the WAL's authority for that map is empty -- so every row is an
     [imark] and the collection reaches every [X] inum.  The ledger the
     pending/await rows needed and the transit set could not supply
     (durable-disk C-4's second finding).  The row's own refutation is
     [TxPin.tx_pin_no_ops] and gets no name of its own; the induction stays
     because the conclusion is a [map_Forall], not [K = ∅]. *)
  Lemma ipool_corpse_no_ops γi (K : gmap Z icorpse) :
    ghost_map_auth (ln_tx icfg_log) 1 (∅ : gmap nat unit) -∗
    ipool_corpse γi K -∗ ⌜map_Forall (fun _ v => v = CrpDep) K⌝.
  Proof.
    rewrite /ipool_corpse.
    iInduction K as [| z v K Hz] "IH" using map_ind.
    { iIntros "_ _". iPureIntro. apply map_Forall_empty. }
    iIntros "Ha HK". rewrite big_sepM_insert; [| exact Hz].
    iDestruct "HK" as "[Hrow HK]".
    destruct v as [t q |].
    { rewrite /crp_row. iDestruct (tx_pin_no_ops with "Ha Hrow") as %[]. }
    iDestruct ("IH" with "Ha HK") as %HF.
    iPureIntro. by apply map_Forall_insert_2.
  Qed.

  (* ...and the reading the collection takes off that: the rows ARE the
     markers, one per [X] inum. *)
  Lemma ipool_corpse_marks γi (K : gmap Z icorpse) :
    map_Forall (fun _ v => v = CrpDep) K ->
    ipool_corpse γi K ⊣⊢ ([∗ set] z ∈ dom K, imark γi z).
  Proof.
    intros HF. rewrite /ipool_corpse -big_sepM_dom.
    apply big_sepM_proper. intros z v Hzv.
    rewrite (HF z v Hzv). done.
  Qed.

  (* the row index this file hands out is at [mword_of_int z]; a mover that
     names the inum as a word wants it back. *)
  Lemma ipl_moi_inum (w : mword 32) :
    (mword_of_int (bv_unsigned w) : mword 32) = w.
  Proof.
    apply bv_eq. rewrite moi32_unsigned.
    apply bv_wrap_small. apply bv_unsigned_in_range.
  Qed.

  (* THE FOUR-PART PARTITION'S TWO SET MOVES, [gset_move_out]/[gset_move_mid]
     at the row's own shape.  [set_solver] closes neither -- both need the
     decidable split on [y = z]. *)
  Lemma gset_move4_out (A B C D : gset Z) (z : Z) :
    z ∈ A -> A ∪ B ∪ C ∪ D = (A ∖ {[z]}) ∪ B ∪ C ∪ (D ∪ {[z]}).
  Proof.
    intros Hz. apply set_eq. intros y.
    rewrite !elem_of_union elem_of_difference elem_of_singleton.
    destruct (decide (y = z)) as [->|Hne]; naive_solver.
  Qed.

  Lemma gset_move4_mid (A B C D : gset Z) (z : Z) :
    z ∈ B -> A ∪ B ∪ C ∪ D = A ∪ (B ∖ {[z]}) ∪ C ∪ (D ∪ {[z]}).
  Proof.
    intros Hz. apply set_eq. intros y.
    rewrite !elem_of_union elem_of_difference elem_of_singleton.
    destruct (decide (y = z)) as [->|Hne]; naive_solver.
  Qed.

  (* THE FIFTY IDENTITIES, as the POOL holds them: a quarter each, in slot
     order. *)
  Definition ic_ids (cn : ic_names)
      (ids : list (bool * mword 32 * mword 32)) : iProp Σ :=
    ([∗ list] k ↦ p ∈ ids, ic_id cn k (1/4) p.1.1 p.1.2 p.2)%I.

  Global Instance ic_ids_timeless cn ids : Timeless (ic_ids cn ids).
  Proof. rewrite /ic_ids. tl_struct. Qed.

  (* one slot's contribution to the cached set: its inum when it is live,
     nothing when it is not *)
  Definition ic_id_inum (p : bool * mword 32 * mword 32) : gset Z :=
    if p.1.1 then {[ bv_unsigned p.2 ]} else ∅.

  Lemma ic_id_inum_spec (p : bool * mword 32 * mword 32) (z : Z) :
    z ∈ ic_id_inum p <-> (p.1.1 = true /\ z = bv_unsigned p.2).
  Proof.
    rewrite /ic_id_inum. destruct (p.1.1) eqn:Hv.
    - rewrite elem_of_singleton. split; [by intros -> | by intros [_ ->]].
    - split; [by intros ?%elem_of_empty | by intros [Hc _]].
  Qed.

  Definition ic_live_inums (ids : list (bool * mword 32 * mword 32)) : gset Z :=
    list_to_set
      (omap (fun p : bool * mword 32 * mword 32 =>
               if p.1.1 then Some (bv_unsigned p.2) else None) ids).

  Lemma ic_live_inums_lookup (ids : list (bool * mword 32 * mword 32)) (z : Z) :
    z ∈ ic_live_inums ids <->
    ∃ (k : nat) (p : bool * mword 32 * mword 32),
      ids !! k = Some p /\ p.1.1 = true /\ z = bv_unsigned p.2.
  Proof.
    rewrite /ic_live_inums elem_of_list_to_set elem_of_list_omap.
    split.
    - intros (p & Hp & Hf). apply elem_of_list_lookup in Hp as [k Hk].
      exists k, p. destruct (p.1.1) eqn:Hv; [| discriminate].
      split; [exact Hk |]. split; [reflexivity |]. by injection Hf.
    - intros (k & p & Hk & Hv & ->). exists p.
      split; [apply elem_of_list_lookup; by exists k |]. by rewrite Hv.
  Qed.

  (* THE ONE MOVE, as a set equation: replacing slot [k]'s identity trades
     its old contribution for its new one, and nothing else changes. *)
  Lemma ic_live_inums_insert (ids : list (bool * mword 32 * mword 32))
      (k : nat) (q p : bool * mword 32 * mword 32) :
    ids !! k = Some q ->
    ic_live_inums (<[k := p]> ids) ∪ ic_id_inum q
    = ic_live_inums ids ∪ ic_id_inum p.
  Proof.
    intros Hk.
    assert (Hlen : (k < length ids)%nat)
      by (apply lookup_lt_is_Some; by eexists).
    apply set_eq. intros z.
    rewrite !elem_of_union !ic_live_inums_lookup !ic_id_inum_spec.
    split.
    - intros [(j & r & Hj & Hv & ->) | Hq].
      + destruct (decide (j = k)) as [->|Hne].
        * rewrite list_lookup_insert in Hj; [| exact Hlen].
          injection Hj as <-. by right.
        * rewrite list_lookup_insert_ne in Hj; [| exact (not_eq_sym Hne)].
          left. by exists j, r.
      + left. exists k, q. destruct Hq as [Hv ->]. done.
    - intros [(j & r & Hj & Hv & ->) | Hp].
      + destruct (decide (j = k)) as [->|Hne].
        * rewrite Hk in Hj. injection Hj as <-. by right.
        * left. exists j, r. rewrite list_lookup_insert_ne; [| exact (not_eq_sym Hne)].
          done.
      + left. exists k, p. rewrite list_lookup_insert; [| exact Hlen].
        destruct Hp as [Hv ->]. done.
  Qed.

  (* the pool's quarter of one slot, out and back *)
  Lemma ic_ids_acc (cn : ic_names) (ids : list (bool * mword 32 * mword 32))
      (k : nat) (v : bool) (d n : mword 32) :
    ids !! k = Some (v, d, n) ->
    ic_ids cn ids -∗
      ic_id cn k (1/4) v d n ∗
      (∀ (v' : bool) (d' n' : mword 32),
         ic_id cn k (1/4) v' d' n' -∗ ic_ids cn (<[k := (v', d', n')]> ids)).
  Proof.
    intros Hk. rewrite /ic_ids.
    iIntros "H".
    iDestruct (big_sepL_insert_acc _ _ k (v, d, n) Hk with "H") as "[Hq Hback]".
    iSplitL "Hq"; [iExact "Hq" |].
    iIntros (v' d' n') "Hq". iApply ("Hback" $! (v', d', n') with "Hq").
  Qed.

  Lemma ic_live_inums_none (ids : list (bool * mword 32 * mword 32)) :
    (forall (k : nat) (p : bool * mword 32 * mword 32),
       ids !! k = Some p -> p.1.1 = false) ->
    ic_live_inums ids = ∅.
  Proof.
    intros H. apply set_eq. intros z. rewrite ic_live_inums_lookup.
    split; [| by intros ?%elem_of_empty].
    intros (k & p & Hk & Hv & _). rewrite (H k p Hk) in Hv. discriminate.
  Qed.

  (* THE BOOT LIST: fifty dead slots at whatever the entry cells say. *)
  Definition ic_ids_of (dvs : nat -> mword 32 * mword 32)
    : list (bool * mword 32 * mword 32) :=
    (fun k => (false, (dvs k).1, (dvs k).2)) <$> seq 0 NINODE.

  Lemma ic_ids_of_length dvs : length (ic_ids_of dvs) = NINODE.
  Proof. rewrite /ic_ids_of length_fmap length_seq //. Qed.


  Lemma ic_ids_of_live dvs : ic_live_inums (ic_ids_of dvs) = ∅.
  Proof.
    apply ic_live_inums_none. intros k p Hk.
    rewrite /ic_ids_of list_lookup_fmap in Hk.
    destruct (seq 0 NINODE !! k) as [x |] eqn:Hx; [| discriminate].
    cbn in Hk. injection Hk as <-. reflexivity.
  Qed.

  Lemma ic_ids_of_intro cn dvs :
    ([∗ list] k ∈ seq 0 NINODE, ic_id cn k (1/4) false (dvs k).1 (dvs k).2)
    ⊢ ic_ids cn (ic_ids_of dvs).
  Proof.
    rewrite /ic_ids /ic_ids_of big_sepL_fmap.
    iIntros "H". iApply (big_sepL_impl with "H").
    iIntros "!>" (j x Hjx) "Hq".
    apply lookup_seq in Hjx as [-> _]. iExact "Hq".
  Qed.

  (* THE BODY.  [O] is the ordinary index (one bundle each, in here), [X]
     the in-transition index (under the lock), [ids] the fifty identities. *)
  Definition ipool_body (cn : ic_names) (γfs : fs_names) (γi : gname)
      (cov : gset Z) (logstart : Z) (nib : nat) : iProp Σ :=
    (∃ (O X : gset Z) (T : gmap Z (nat * Qp))
       (ids : list (bool * mword 32 * mword 32)) (K : gmap Z icorpse),
       ⌜length ids = NINODE⌝ ∗
       ⌜region_inums nib = O ∪ X ∪ dom T ∪ ic_live_inums ids⌝ ∗
       (* THE CORPSE LEDGER'S DOMAIN IS THE IN-TRANSITION INDEX (C-7): one
          row per pending/await inum, and the row is where that inum's
          [InodeRegion.imark] lives once its deposit has run.  This is what
          makes the commit's reading at an [X] inum EXHAUSTIVE. *)
       ⌜dom K = X⌝ ∗
       ipool_key O ∗ ipool_xkey X ∗ ipool_tkey T ∗ ipool_transit T ∗
       ic_ids cn ids ∗
       ipool_rows γfs γi cov logstart O ∗
       ipool_ckey K ∗ ipool_corpse γi K)%I.

  Global Instance ipool_body_timeless cn γfs γi cov logstart nib :
    Timeless (ipool_body cn γfs γi cov logstart nib).
  Proof.
    rewrite /ipool_body /ipool_key /ipool_xkey /ipool_tkey. tl_struct.
  Qed.

  (* distinct from every namespace an opener may already hold: the escrow
     family [icEscN], the ref words [IcacheInv.icacheN], the region
     [InodeRegion.iregN] and [ftopN], the per-inum [EscrowDefs.escAN] and
     the log's [logN]. *)
  Definition ipoolN : namespace := nroot .@ "ipool".

  Definition ipool_inv (cn : ic_names) (γfs : fs_names) (γi : gname)
      (cov : gset Z) (logstart : Z) (nib : nat) : iProp Σ :=
    inv ipoolN (ipool_body cn γfs γi cov logstart nib).

  Global Instance ipool_inv_persistent cn γfs γi cov logstart nib :
    Persistent (ipool_inv cn γfs γi cov logstart nib).
  Proof. apply _. Qed.

  (* WHAT THE LOCK KEEPS, in [ipool]'s own position: the residency key for
     the invariant's index set, the in-transition key at the ext rows plus
     whatever this walk is CARRYING ([T], empty outside an eviction's
     window), and the in-transition rows the invariant may not hold. *)
  Definition ipool (γfs : fs_names) (γi : gname) (cov : gset Z)
      (logstart : Z) (P : gset Z) (T : gmap Z (nat * Qp)) : iProp Σ :=
    (∃ O : gset Z,
       ⌜O ⊆ P⌝ ∗ ipool_key O ∗ ipool_xkey (P ∖ O) ∗ ipool_tkey T ∗
       [∗ set] z ∈ P ∖ O, ipool_ext γfs γi cov logstart (mword_of_int z))%I.

  (* the pool at its BOOT state: every row ordinary, no slot live, nothing
     in transit -- so the partition is the two-way one and the lock's side
     is the two keys alone.  This is what [IcacheBoot.icache_boot_at]
     builds. *)
  Lemma ipool_alloc_inv (E : coPset) (cn : ic_names) (γfs : fs_names)
      (γi : gname) (cov : gset Z) (logstart : Z) (nib : nat)
      (ids : list (bool * mword 32 * mword 32)) :
    length ids = NINODE ->
    ic_live_inums ids = ∅ ->
    ghost_var icfg_pool 1 (∅ : gset Z) -∗
    ghost_var icfg_pext 1 (∅ : gset Z) -∗
    ghost_var icfg_ptrn 1 (∅ : gmap Z (nat * Qp)) -∗
    (* ...AND THE CORPSE LEDGER (durable-disk C-7), EMPTY: the image has no
       corpses -- every free inum's record is bare and its marker is on the
       pool's own ordinary row, not in transit -- so [X] and the ledger are
       empty together and the partition is the two-way one. *)
    ghost_map_auth icfg_pcrp 1 (∅ : gmap Z icorpse) -∗
    ic_ids cn ids -∗
    ipool_rows γfs γi cov logstart (region_inums nib) ={E}=∗
      ipool_inv cn γfs γi cov logstart nib ∗
      ipool γfs γi cov logstart (region_inums nib) ∅.
  Proof.
    intros Hlen Hlive. iIntros "Hkey Hxkey Htkey Hckey Hids Hrows".
    iMod (ghost_var_update (region_inums nib) with "Hkey") as "Hkey".
    iAssert (ipool_key (region_inums nib) ∗ ipool_key (region_inums nib))%I
      with "[Hkey]" as "[Hk1 Hk2]".
    { rewrite /ipool_key.
      iApply (ghost_var_split icfg_pool (region_inums nib) (1/2) (1/2)).
      rewrite Qp.half_half. iExact "Hkey". }
    iAssert (ipool_xkey ∅ ∗ ipool_xkey ∅)%I with "[Hxkey]" as "[Hx1 Hx2]".
    { rewrite /ipool_xkey.
      iApply (ghost_var_split icfg_pext (∅ : gset Z) (1/2) (1/2)).
      rewrite Qp.half_half. iExact "Hxkey". }
    iAssert (ipool_tkey ∅ ∗ ipool_tkey ∅)%I with "[Htkey]" as "[Ht1 Ht2]".
    { rewrite /ipool_tkey.
      iApply (ghost_var_split icfg_ptrn (∅ : gmap Z (nat * Qp)) (1/2) (1/2)).
      rewrite Qp.half_half. iExact "Htkey". }
    iMod (inv_alloc ipoolN E (ipool_body cn γfs γi cov logstart nib)
            with "[Hk1 Hx1 Ht1 Hckey Hids Hrows]") as "#Hinv".
    { iApply bi.later_intro. rewrite /ipool_body. iExists (region_inums nib), ∅, ∅, ids, ∅.
      iSplitR; [iPureIntro; exact Hlen |].
      iSplitR; [iPureIntro; rewrite Hlive dom_empty_L; set_solver |].
      iSplitR; [iPureIntro; exact dom_empty_L |].
      rewrite /ipool_ckey /ipool_transit /tx_pins /ipool_corpse !big_sepM_empty.
      iFrame "Hk1 Hx1 Ht1 Hids Hrows Hckey". }
    iModIntro. iFrame "Hinv". rewrite /ipool.
    iExists (region_inums nib). iSplitR; [iPureIntro; set_solver |].
    iFrame "Hk2".
    rewrite difference_diag_L.
    iFrame "Hx2 Ht2". rewrite big_sepS_empty. done.
  Qed.

  (* ---- THE THREE MOVERS ----------------------------------------------
     [ipool_take_lend] and [ipool_evict_lend] are ACCESSORS and not plain
     fupds, and that shape is the whole of C-3b: the pool's quarter has to
     be in the caller's hand at the same ghost step as the escrow arm's
     half, because the flip needs the whole cell and the partition moves
     with it.  They hand out a HALF -- the pool's quarter joined to the
     table's -- so [ic_open_empty_free] and the eviction family are called
     UNCHANGED, and the wand takes the flipped half back and
     returns the table its quarter.

     [ipool_put] needs no identity at all: it moves an inum out of the
     in-transition index into the ordinary one (or leaves it there, if the
     row is a pending/await arm), and the fifty identities do not move. *)

  Lemma ic_id_join cn k (q1 q2 : Qp) v d n :
    ic_id cn k q1 v d n -∗ ic_id cn k q2 v d n -∗ ic_id cn k (q1 + q2) v d n.
  Proof.
    rewrite /ic_id. iIntros "H1 H2". iCombine "H1 H2" as "H". iExact "H".
  Qed.

  Lemma ic_id_split_q cn k (q1 q2 : Qp) v d n :
    ic_id cn k (q1 + q2) v d n -∗ ic_id cn k q1 v d n ∗ ic_id cn k q2 v d n.
  Proof. rewrite /ic_id. iApply ghost_var_split. Qed.

  Lemma ic_id_quarters_join cn k v d n :
    ic_id cn k (1/4) v d n -∗ ic_id cn k (1/4) v d n -∗ ic_id cn k (1/2) v d n.
  Proof.
    iIntros "H1 H2".
    iDestruct (ic_id_join cn k (1/4) (1/4) with "H1 H2") as "H".
    by rewrite Qp.quarter_quarter.
  Qed.

  Lemma ic_id_quarters_split cn k v d n :
    ic_id cn k (1/2) v d n -∗ ic_id cn k (1/4) v d n ∗ ic_id cn k (1/4) v d n.
  Proof.
    iIntros "H". rewrite -Qp.quarter_quarter.
    iApply (ic_id_split_q cn k (1/4) (1/4) with "H").
  Qed.

  (* THE RECYCLE, AND IT PEELS THE ROW ITSELF (durable-disk C-3b, C-7).
     iget's +0x72: the row goes out, the inum leaves [O] or leaves [X], the
     pool lends its quarter of the slot's identity so the flip below has a
     whole unit, and the wand records the new identity.

     SINCE C-7 IT ALSO DOES [ipool_shape_to_np]'s WORK, and the merge is
     FORCED rather than tidy.  An [X] inum's [InodeRegion.imark] is in the
     CORPSE LEDGER, whose row can only be deleted with the ledger ELEMENT --
     and the only place that element can be found is the escrow's FILLED arm,
     which the peel is what opens.  Since the ledger's domain IS [X], the
     peel and the index move have to be the same ghost step.  What comes out
     is therefore an ORDINARY row's four pieces, on both branches.

     THE AWAIT ARM IS A REFUTATION, NOT A CONVERSION (iclaim-ledger.md 1.3,
     and 3.1's reshaping of its premise): before the deposit the escrow holds
     the STANDING freeze, and the caller's LICENCE refutes it at the region
     ([IgetLic.iname_freeze_off] -- 2.6's table, at whichever of the five
     licences the caller presented).  The licence is borrowed and comes back.
     After the deposit the escrow hands back the ledger element and the
     re-armed [ifreeze_off], which is exactly the ordinary arm's token. *)
  Lemma ipool_take_lend (E : coPset) (cn : ic_names) (gfs : fs_names)
      (gi : gname) (inodestart : Z) (cov : gset Z) (logstart : Z) (nib : nat)
      (P : gset Z) (k : nat) (inum : mword 32) (dv0 nu0 : mword 32)
      (l : ilic) :
    ↑ipoolN ⊆ E ->
    ↑escAN (bv_unsigned inum) ⊆ E ∖ ↑ipoolN ->
    ↑iregN ⊆ E ∖ ↑ipoolN ->
    (* ...AND STILL INSIDE the escrow's own opening: the await arm's
       refutation runs at the region while [escAN inum] is held. *)
    ↑iregN ⊆ E ∖ ↑ipoolN ∖ ↑escAN (bv_unsigned inum) ->
    (k < NINODE)%nat ->
    bv_unsigned inum ∈ P ->
    (bv_unsigned inum < 16 * Z.of_nat nib)%Z ->
    ireg_reg gi gfs inodestart nib -∗
    ipool_inv cn gfs gi cov logstart nib -∗
    ipool gfs gi cov logstart P ∅ -∗
    ic_id cn k (1/4) false dv0 nu0 -∗
    iname gi gfs inodestart inum l -∗
    |={E, E ∖ ↑ipoolN}=>
      iname gi gfs inodestart inum l ∗
      ipool_shape_np gfs gi cov logstart inum ∗
      icnt_half (bv_unsigned inum) 0%nat ∗
      frzm_h (bv_unsigned inum) false ∗
      ifreeze_off (bv_unsigned inum) ∗
      ipool gfs gi cov logstart (P ∖ {[bv_unsigned inum]}) ∅ ∗
      ic_id cn k (1/2) false dv0 nu0 ∗
      (∀ dv1 nu1 : mword 32, ⌜bv_unsigned nu1 = bv_unsigned inum⌝ -∗
         ic_id cn k (1/2) true dv1 nu1 ={E ∖ ↑ipoolN, E}=∗
         ic_id cn k (1/4) true dv1 nu1).
  Proof.
    iIntros (HE HEesc HEreg HEreg2 Hk Hz Hin) "#Hrinv #Hinv H Hq Hl".
    rewrite {1}/ipool.
    iDestruct "H" as (O) "(%Hsub & Hkey & Hxkey & Htkey & Hext)".
    iMod (inv_acc E ipoolN with "Hinv") as "[Hb Hclose]"; [exact HE |].
    iDestruct "Hb" as ">Hb".
    iDestruct "Hb" as (O' X T ids K)
      "(%Hlen & %Hrow & %Hdk & Hk1 & Hx1 & Ht1 & Htr & Hids & Hrows & Hck & Hcrp)".
    iDestruct (ghost_var_agree with "Hk1 Hkey") as %->.
    iDestruct (ghost_var_agree with "Hx1 Hxkey") as %->.
    iDestruct (ghost_var_agree with "Ht1 Htkey") as %->.
    rewrite dom_empty_L in Hrow.
    assert (Hik : is_Some (ids !! k))
      by (apply lookup_lt_is_Some_2; rewrite Hlen; exact Hk).
    destruct Hik as [[[pv pd] pn] Hp].
    iDestruct (ic_ids_acc cn ids k pv pd pn Hp with "Hids") as "[Hqp Hidsback]".
    iDestruct (ic_id_agree with "Hq Hqp") as %(Hv & Hd & Hn).
    subst pv pd pn.
    destruct (decide (bv_unsigned inum ∈ O)) as [Hzo | Hzo].
    - (* AN ORDINARY ROW: no corpse, no escrow, nothing to peel. *)
      rewrite /ipool_rows (big_sepS_delete _ O (bv_unsigned inum) Hzo).
      iDestruct "Hrows" as "[Hrow0 Hrows]".
      iEval (rewrite ipl_moi_inum) in "Hrow0".
      iDestruct "Hrow0" as "(Hcnt & Hmir & Hnp & Hoff)".
      iMod (ghost_var_update_halves (O ∖ {[bv_unsigned inum]}) with "Hk1 Hkey")
        as "[Hk1 Hkey]".
      iDestruct (ic_id_quarters_join with "Hq Hqp") as "Hhalf".
      iModIntro. iFrame "Hl Hnp Hcnt Hmir Hoff".
      iSplitL "Hkey Hxkey Htkey Hext".
      { rewrite /ipool. iExists (O ∖ {[bv_unsigned inum]}).
        iSplitR; [iPureIntro; set_solver |]. iFrame "Hkey Htkey".
        assert (Hset2 : (P ∖ {[bv_unsigned inum]}) ∖ (O ∖ {[bv_unsigned inum]})
                        = P ∖ O) by set_solver.
        rewrite Hset2. iFrame "Hxkey". iExact "Hext". }
      iFrame "Hhalf".
      iIntros (dv1 nu1 Hnu1) "Hhalf".
      iDestruct (ic_id_quarters_split with "Hhalf") as "[Hq1 Hq2]".
      iDestruct ("Hidsback" $! true dv1 nu1 with "Hq2") as "Hids".
      iMod ("Hclose" with "[Hk1 Hx1 Ht1 Htr Hids Hrows Hck Hcrp]") as "_".
      { iApply bi.later_intro. rewrite /ipool_body.
        iExists (O ∖ {[bv_unsigned inum]}), (P ∖ O), ∅,
          (<[k := (true, dv1, nu1)]> ids), K.
        iSplitR; [iPureIntro; rewrite length_insert; exact Hlen |].
        iSplitR.
        { iPureIntro. rewrite dom_empty_L.
          pose proof (ic_live_inums_insert ids k (false, dv0, nu0)
                        (true, dv1, nu1) Hp) as Heq.
          assert (Hpe : ic_id_inum (false, dv0, nu0) = ∅) by reflexivity.
          assert (Hne : ic_id_inum (true, dv1, nu1) = {[bv_unsigned inum]})
            by (rewrite /ic_id_inum /=; by rewrite Hnu1).
          rewrite Hpe Hne union_empty_r_L in Heq.
          rewrite Hrow Heq.
          exact (gset_move4_out O (P ∖ O) ∅ _ (bv_unsigned inum) Hzo). }
        iSplitR; [iPureIntro; exact Hdk |].
        iFrame "Hk1 Hx1 Ht1 Htr Hids Hrows Hck Hcrp". }
      iModIntro. iExact "Hq1".
    - (* AN IN-TRANSITION ROW: peel the escrow, spend the corpse row. *)
      assert (Hzd : bv_unsigned inum ∈ P ∖ O) by set_solver.
      rewrite (big_sepS_delete _ (P ∖ O) (bv_unsigned inum) Hzd).
      iDestruct "Hext" as "[Hrow0 Hext]".
      iEval (rewrite ipl_moi_inum) in "Hrow0".
      iDestruct "Hrow0" as "(Hcnt & Hmir & Harm)".
      (* the peel: a deposited entry hands back the ledger element and the
         re-armed token; an undeposited one is refuted by the licence. *)
      iAssert (|={E ∖ ↑ipoolN}=>
                 iname gi gfs inodestart inum l ∗
                 crp_elem (bv_unsigned inum) CrpDep ∗
                 ifreeze_off (bv_unsigned inum))%I
        with "[Harm Hl]" as ">(Hl & Hel & Hoff)".
      { iDestruct "Harm" as "[Hpp | Haw]".
        - iDestruct "Hpp" as (ge gr gd rg) "(#Hesc & #Hcom & Htk)".
          iMod (escA_redeem (E ∖ ↑ipoolN) gfs ge gr gd (bv_unsigned inum) rg
                  HEesc with "Hesc Htk Hcom") as "[Hel Hoff]".
          iModIntro. iFrame "Hl Hel Hoff".
        - iDestruct "Haw" as (ge gr gd rg) "(#Hesc & Htk)".
          iMod (escA_await_peel (E ∖ ↑ipoolN) gfs ge gr gd (bv_unsigned inum) rg
                  (iname gi gfs inodestart inum l) HEesc
                  with "Hesc Htk Hl []") as "(Hl & Hel & Hoff)".
          { iIntros "Hl Hpost". rewrite /ifreeze_post.
            iMod (iname_freeze_off (E ∖ ↑ipoolN ∖ ↑escAN (bv_unsigned inum))
                    gi gfs inodestart nib inum l (FrzPost rg) HEreg2 Hin
                    with "Hrinv Hl Hpost") as "(%Hc & _ & _)".
            discriminate Hc. }
          iModIntro. iFrame "Hl Hel Hoff". }
      (* the corpse row: the element the peel returned locates it, and its
         value is [CrpDep] by [ghost_map_lookup] -- which is the tie between
         the escrow's one-shot and the ledger's. *)
      iDestruct (ghost_map_lookup with "Hck Hel") as %HKz.
      rewrite /ipool_corpse (big_sepM_delete _ K (bv_unsigned inum) CrpDep HKz).
      iDestruct "Hcrp" as "[Hmk Hcrp]".
      iEval (rewrite /crp_row) in "Hmk".
      iMod (ghost_map_delete with "Hck Hel") as "Hck".
      iMod (ghost_var_update_halves ((P ∖ O) ∖ {[bv_unsigned inum]})
              with "Hx1 Hxkey") as "[Hx1 Hxkey]".
      iDestruct (ic_id_quarters_join with "Hq Hqp") as "Hhalf".
      iModIntro. iFrame "Hl Hcnt Hmir Hoff".
      iSplitL "Hmk".
      { rewrite /ipool_shape_np. iRight. iExact "Hmk". }
      iSplitL "Hkey Hxkey Htkey Hext".
      { rewrite /ipool. iExists O.
        iSplitR; [iPureIntro; set_solver |]. iFrame "Hkey Htkey".
        assert (Hset2 : (P ∖ {[bv_unsigned inum]}) ∖ O
                        = (P ∖ O) ∖ {[bv_unsigned inum]}) by set_solver.
        rewrite Hset2. iFrame "Hxkey". iExact "Hext". }
      iFrame "Hhalf".
      iIntros (dv1 nu1 Hnu1) "Hhalf".
      iDestruct (ic_id_quarters_split with "Hhalf") as "[Hq1 Hq2]".
      iDestruct ("Hidsback" $! true dv1 nu1 with "Hq2") as "Hids".
      iMod ("Hclose" with "[Hk1 Hx1 Ht1 Htr Hids Hrows Hck Hcrp]") as "_".
      { iApply bi.later_intro. rewrite /ipool_body.
        iExists O, ((P ∖ O) ∖ {[bv_unsigned inum]}), ∅,
          (<[k := (true, dv1, nu1)]> ids), (delete (bv_unsigned inum) K).
        iSplitR; [iPureIntro; rewrite length_insert; exact Hlen |].
        iSplitR.
        { iPureIntro. rewrite dom_empty_L.
          pose proof (ic_live_inums_insert ids k (false, dv0, nu0)
                        (true, dv1, nu1) Hp) as Heq.
          assert (Hpe : ic_id_inum (false, dv0, nu0) = ∅) by reflexivity.
          assert (Hne : ic_id_inum (true, dv1, nu1) = {[bv_unsigned inum]})
            by (rewrite /ic_id_inum /=; by rewrite Hnu1).
          rewrite Hpe Hne union_empty_r_L in Heq.
          rewrite Hrow Heq.
          exact (gset_move4_mid O (P ∖ O) ∅ _ (bv_unsigned inum) Hzd). }
        iSplitR; [iPureIntro; rewrite dom_delete_L Hdk; reflexivity |].
        iFrame "Hk1 Hx1 Ht1 Htr Hids Hrows Hck Hcrp". }
      iModIntro. iExact "Hq1".
  Qed.

  Lemma ipool_evict_lend (E : coPset) (cn : ic_names) (γfs : fs_names)
      (γi : gname) (cov : gset Z) (logstart : Z) (nib : nat)
      (P : gset Z) (k : nat) (z : Z) (dv0 nu0 : mword 32)
      (t : nat) (q : Qp) :
    ↑ipoolN ⊆ E ->
    (k < NINODE)%nat ->
    bv_unsigned nu0 = z ->
    ipool_inv cn γfs γi cov logstart nib -∗
    ipool γfs γi cov logstart P ∅ -∗
    ic_id cn k (1/4) true dv0 nu0 -∗
    |={E, E ∖ ↑ipoolN}=>
      ipool γfs γi cov logstart P {[z := (t, q)]} ∗
      ic_id cn k (1/2) true dv0 nu0 ∗
      (* THE TRANSIT ROW'S SHARE (durable-disk C-4) IS PAID AT THE CLOSING
         STEP, and that position is forced: the free path's evicting walk has
         its transaction share parked in the escrow's FROZEN arm at the
         opening and gets it back ([ic_pin_exit]) only inside the very window
         this accessor holds [ipoolN] open for.  The ledger's VALUE moves at
         the opening (both halves are in hand there); the share itself is
         only needed when the body is put back together.  It comes home at
         [ipool_put], AT THE SAME [(t, q)]: the ledger's other half rides in
         [ipool], so the walk knows what it parked. *)
      (∀ dv1 nu1 : mword 32,
         ic_id cn k (1/2) false dv1 nu1 -∗ t ↪[ln_tx icfg_log]{#q} tt
         ={E ∖ ↑ipoolN, E}=∗ ic_id cn k (1/4) false dv1 nu1).
  Proof.
    iIntros (HE Hk Hnu0) "#Hinv H Hq". rewrite {1}/ipool.
    iDestruct "H" as (O) "(%Hsub & Hkey & Hxkey & Htkey & Hext)".
    iMod (inv_acc E ipoolN with "Hinv") as "[Hb Hclose]"; [exact HE |].
    iDestruct "Hb" as ">Hb".
    iDestruct "Hb" as (O' X T ids K)
      "(%Hlen & %Hrow & %Hdk & Hk1 & Hx1 & Ht1 & Htr & Hids & Hrows & Hck & Hcrp)".
    iDestruct (ghost_var_agree with "Hk1 Hkey") as %->.
    iDestruct (ghost_var_agree with "Hx1 Hxkey") as %->.
    iDestruct (ghost_var_agree with "Ht1 Htkey") as %->.
    rewrite dom_empty_L in Hrow.
    assert (Hik : is_Some (ids !! k))
      by (apply lookup_lt_is_Some_2; rewrite Hlen; exact Hk).
    destruct Hik as [[[pv pd] pn] Hp].
    iDestruct (ic_ids_acc cn ids k pv pd pn Hp with "Hids") as "[Hqp Hidsback]".
    iDestruct (ic_id_agree with "Hq Hqp") as %(Hv & Hd & Hn).
    subst pv pd pn.
    iMod (ghost_var_update_halves {[z := (t, q)]} with "Ht1 Htkey")
      as "[Ht1 Htkey]".
    iDestruct (ic_id_quarters_join with "Hq Hqp") as "Hhalf".
    iModIntro. iSplitL "Hkey Hxkey Htkey Hext".
    { rewrite /ipool. iExists O. iSplitR; [iPureIntro; exact Hsub |].
      iFrame "Hkey Hxkey Htkey Hext". }
    iFrame "Hhalf".
    iIntros (dv1 nu1) "Hhalf Htx".
    iDestruct (ic_id_quarters_split with "Hhalf") as "[Hq1 Hq2]".
    iDestruct ("Hidsback" $! false dv1 nu1 with "Hq2") as "Hids".
    iMod ("Hclose" with "[Hk1 Hx1 Ht1 Htr Htx Hids Hrows Hck Hcrp]") as "_".
    { iApply bi.later_intro. rewrite /ipool_body.
      iExists O, (P ∖ O), {[z := (t, q)]}, (<[k := (false, dv1, nu1)]> ids), K.
      iSplitR; [iPureIntro; rewrite length_insert; exact Hlen |].
      iSplitR.
      { iPureIntro. rewrite dom_singleton_L.
        pose proof (ic_live_inums_insert ids k (true, dv0, nu0)
                      (false, dv1, nu1) Hp) as Heq.
        assert (Hpe : ic_id_inum (true, dv0, nu0) = {[z]}).
        { rewrite /ic_id_inum /=. by rewrite Hnu0. }
        assert (Hne : ic_id_inum (false, dv1, nu1) = ∅) by reflexivity.
        rewrite Hpe Hne union_empty_r_L in Heq.
        rewrite Hrow -Heq. clear Hrow. set_solver. }
      iSplitR; [iPureIntro; exact Hdk |].
      iDestruct "Htr" as "_".
      iFrame "Hk1 Hx1 Ht1 Hids Hrows Hck Hcrp".
      rewrite /ipool_transit /tx_pins big_sepM_singleton /=. iExact "Htx". }
    iModIntro. iExact "Hq1".
  Qed.

  (* A DEAD SLOT'S RE-TAG (iget's dev store at +0x6e): the recorded words
     move while the slot stays NOT LIVE, so the partition does not move at
     all -- a dead slot contributes nothing to it -- but the pool holds a
     quarter of the cell and so has to be in the same ghost step. *)
  Lemma ipool_id_lend (E : coPset) (cn : ic_names) (γfs : fs_names)
      (γi : gname) (cov : gset Z) (logstart : Z) (nib : nat)
      (k : nat) (dv0 nu0 : mword 32) :
    ↑ipoolN ⊆ E ->
    (k < NINODE)%nat ->
    ipool_inv cn γfs γi cov logstart nib -∗
    ic_id cn k (1/4) false dv0 nu0 -∗
    |={E, E ∖ ↑ipoolN}=>
      ic_id cn k (1/2) false dv0 nu0 ∗
      (∀ dv1 nu1 : mword 32,
         ic_id cn k (1/2) false dv1 nu1 ={E ∖ ↑ipoolN, E}=∗
         ic_id cn k (1/4) false dv1 nu1).
  Proof.
    iIntros (HE Hk) "#Hinv Hq".
    iMod (inv_acc E ipoolN with "Hinv") as "[Hb Hclose]"; [exact HE |].
    iDestruct "Hb" as ">Hb".
    iDestruct "Hb" as (O X T ids K)
      "(%Hlen & %Hrow & %Hdk & Hk1 & Hx1 & Ht1 & Htr & Hids & Hrows & Hck & Hcrp)".
    assert (Hik : is_Some (ids !! k))
      by (apply lookup_lt_is_Some_2; rewrite Hlen; exact Hk).
    destruct Hik as [[[pv pd] pn] Hp].
    iDestruct (ic_ids_acc cn ids k pv pd pn Hp with "Hids") as "[Hqp Hidsback]".
    iDestruct (ic_id_agree with "Hq Hqp") as %(Hv & Hd & Hn).
    subst pv pd pn.
    iDestruct (ic_id_quarters_join with "Hq Hqp") as "Hhalf".
    iModIntro. iFrame "Hhalf".
    iIntros (dv1 nu1) "Hhalf".
    iDestruct (ic_id_quarters_split with "Hhalf") as "[Hq1 Hq2]".
    iDestruct ("Hidsback" $! false dv1 nu1 with "Hq2") as "Hids".
    iMod ("Hclose" with "[Hk1 Hx1 Ht1 Htr Hids Hrows Hck Hcrp]") as "_".
    { iApply bi.later_intro. rewrite /ipool_body.
      iExists O, X, T, (<[k := (false, dv1, nu1)]> ids), K.
      iSplitR; [iPureIntro; rewrite length_insert; exact Hlen |].
      iSplitR;
        [| iSplitR; [iPureIntro; exact Hdk |];
           iFrame "Hk1 Hx1 Ht1 Htr Hids Hrows Hck Hcrp"].
      iPureIntro.
      pose proof (ic_live_inums_insert ids k (false, dv0, nu0)
                    (false, dv1, nu1) Hp) as Heq.
      assert (Hpe : ic_id_inum (false, dv0, nu0) = ∅) by reflexivity.
      assert (Hne : ic_id_inum (false, dv1, nu1) = ∅) by reflexivity.
      rewrite Hpe Hne !union_empty_r_L in Heq.
      rewrite Hrow Heq. reflexivity. }
    iModIntro. iExact "Hq1".
  Qed.

  (* THE DEPOSIT, ORDINARY.  The evicted row goes back into the pool's own
     invariant and the inum stops being in transit; the fifty identities do
     not move, and the share the eviction parked comes home at the ledger's
     own [(t, q)].  Since durable-disk C-7 the ARM IS NAMED rather than
     re-hidden behind the pool row: which side the row lands on decides what
     the walk gets back, so the two sides are two lemmas. *)
  Lemma ipool_put_ord (E : coPset) (cn : ic_names) (gfs : fs_names) (gi : gname)
      (cov : gset Z) (logstart : Z) (nib : nat) (P : gset Z) (z : Z)
      (t : nat) (q : Qp) :
    ↑ipoolN ⊆ E ->
    z ∉ P ->
    ipool_inv cn gfs gi cov logstart nib -∗
    ipool_ord gfs gi cov logstart (mword_of_int z) -∗
    ipool gfs gi cov logstart P {[z := (t, q)]} ={E}=∗
      ipool gfs gi cov logstart ({[z]} ∪ P) ∅ ∗
      (* the share the eviction parked, back at the ledger's own [(t, q)] *)
      t ↪[ln_tx icfg_log]{#q} tt.
  Proof.
    iIntros (HE Hz) "#Hinv Hrow H". rewrite {1}/ipool.
    iDestruct "H" as (O) "(%Hsub & Hkey & Hxkey & Htkey & Hext)".
    assert (Hzo : z ∉ O) by set_solver.
    iInv "Hinv" as ">Hb" "Hclose".
    iDestruct "Hb" as (O' X T ids K)
      "(%Hlen & %Hrow & %Hdk & Hk1 & Hx1 & Ht1 & Htr & Hids & Hrows & Hck & Hcrp)".
    iDestruct (ghost_var_agree with "Hk1 Hkey") as %->.
    iDestruct (ghost_var_agree with "Hx1 Hxkey") as %->.
    iDestruct (ghost_var_agree with "Ht1 Htkey") as %->.
    rewrite dom_singleton_L in Hrow.
    rewrite /ipool_transit /tx_pins big_sepM_singleton /=.
    iMod (ghost_var_update_halves (∅ : gmap Z (nat * Qp)) with "Ht1 Htkey")
      as "[Ht1 Htkey]".
    iMod (ghost_var_update_halves ({[z]} ∪ O) with "Hk1 Hkey")
      as "[Hk1 Hkey]".
    iMod ("Hclose" with "[Hk1 Hx1 Ht1 Hids Hrows Hrow Hck Hcrp]") as "_".
    { iApply bi.later_intro. rewrite /ipool_body. iExists ({[z]} ∪ O), (P ∖ O), ∅, ids, K.
      iSplitR; [iPureIntro; exact Hlen |].
      iSplitR;
        [iPureIntro; rewrite dom_empty_L Hrow; clear Hrow; set_solver |].
      iSplitR; [iPureIntro; exact Hdk |].
      iFrame "Hk1 Hx1 Ht1 Hids Hck Hcrp".
      iSplitR; [rewrite /ipool_transit /tx_pins big_sepM_empty; done |].
      rewrite /ipool_rows big_sepS_union; [| set_solver].
      iSplitL "Hrow"; [| iExact "Hrows"].
      rewrite big_sepS_singleton. iExact "Hrow". }
    iModIntro. iFrame "Htr". rewrite /ipool. iExists ({[z]} ∪ O).
    iSplitR; [iPureIntro; set_solver |]. iFrame "Hkey Htkey".
    assert (Hset2 : ({[z]} ∪ P) ∖ ({[z]} ∪ O) = P ∖ O) by set_solver.
    rewrite Hset2. iFrame "Hxkey". iExact "Hext".
  Qed.

  (* ...AND THE DEPOSIT OF A CORPSE (durable-disk C-7).  iput's free path
     parks its AWAIT row at +0x94, and the row is half of a corpse: the
     lock's half is [ipool_ext], the invariant's half is a CORPSE LEDGER row.
     So the share the eviction parked does NOT come home here -- it moves
     into that row, where a commit refutes it -- and what comes out instead
     is the row's ELEMENT, which the walk carries off-lock to
     [EscrowDeposit.ireg_free_deposit_au].  The deposit swaps the share for
     [InodeRegion.imark] and hands the freer its share back there.

     WHICH SHARE IT IS: exactly the one [ipool_evict_lend] took, i.e. the
     half iput split off at the +0x3a checkout window (durable-disk C-6's
     fraction plan).  The other half is the freeze index's, and it comes home
     at the same deposit. *)
  Lemma ipool_put_corpse (E : coPset) (cn : ic_names) (gfs : fs_names)
      (gi : gname) (cov : gset Z) (logstart : Z) (nib : nat) (P : gset Z)
      (z : Z) (t : nat) (q : Qp) :
    ↑ipoolN ⊆ E ->
    z ∉ P ->
    ipool_inv cn gfs gi cov logstart nib -∗
    ipool_ext gfs gi cov logstart (mword_of_int z) -∗
    ipool gfs gi cov logstart P {[z := (t, q)]} ={E}=∗
      ipool gfs gi cov logstart ({[z]} ∪ P) ∅ ∗
      crp_elem z (CrpPre t q).
  Proof.
    iIntros (HE Hz) "#Hinv Hrow H". rewrite {1}/ipool.
    iDestruct "H" as (O) "(%Hsub & Hkey & Hxkey & Htkey & Hext)".
    assert (Hzo : z ∉ O) by set_solver.
    iInv "Hinv" as ">Hb" "Hclose".
    iDestruct "Hb" as (O' X T ids K)
      "(%Hlen & %Hrow & %Hdk & Hk1 & Hx1 & Ht1 & Htr & Hids & Hrows & Hck & Hcrp)".
    iDestruct (ghost_var_agree with "Hk1 Hkey") as %->.
    iDestruct (ghost_var_agree with "Hx1 Hxkey") as %->.
    iDestruct (ghost_var_agree with "Ht1 Htkey") as %->.
    rewrite dom_singleton_L in Hrow.
    rewrite /ipool_transit /tx_pins big_sepM_singleton /=.
    iMod (ghost_var_update_halves (∅ : gmap Z (nat * Qp)) with "Ht1 Htkey")
      as "[Ht1 Htkey]".
    iMod (ghost_var_update_halves ({[z]} ∪ (P ∖ O)) with "Hx1 Hxkey")
      as "[Hx1 Hxkey]".
    (* the ledger row is FRESH: its domain is the in-transition index, and
       [z] was not in the pool at all. *)
    assert (HKz : K !! z = None).
    { apply not_elem_of_dom. rewrite Hdk. set_solver. }
    iMod (ghost_map_insert z (CrpPre t q) HKz with "Hck") as "[Hck Hel]".
    iMod ("Hclose" with "[Hk1 Hx1 Ht1 Hids Hrows Hck Hcrp Htr]") as "_".
    { iApply bi.later_intro. rewrite /ipool_body.
      iExists O, ({[z]} ∪ (P ∖ O)), ∅, ids, (<[z := CrpPre t q]> K).
      iSplitR; [iPureIntro; exact Hlen |].
      iSplitR;
        [iPureIntro; rewrite dom_empty_L Hrow; clear Hrow; set_solver |].
      iSplitR; [iPureIntro; rewrite dom_insert_L Hdk; reflexivity |].
      iFrame "Hk1 Hx1 Ht1 Hids Hrows Hck".
      iSplitR; [rewrite /ipool_transit /tx_pins big_sepM_empty; done |].
      rewrite /ipool_corpse big_sepM_insert; [| exact HKz].
      iSplitL "Htr"; [iExact "Htr" | iExact "Hcrp"]. }
    iModIntro. iFrame "Hel". rewrite /ipool. iExists O.
    iSplitR; [iPureIntro; set_solver |]. iFrame "Hkey Htkey".
    assert (Hset2 : ({[z]} ∪ P) ∖ O = {[z]} ∪ (P ∖ O)) by set_solver.
    rewrite Hset2. iFrame "Hxkey".
    rewrite big_sepS_union; [| set_solver].
    iSplitL "Hrow"; [| iExact "Hext"].
    rewrite big_sepS_singleton. iExact "Hrow".
  Qed.

  (* THE OFF-LOCK DEPOSIT'S OWN GHOST STEP (durable-disk C-7), and the ONE
     thing the corpse ledger exists for: iput's deposit runs twenty
     instructions after the itable lock went, so it holds neither half of
     [icfg_pext] and cannot tell that its inum is in [X].  Its ELEMENT is
     what locates the row -- [ghost_map_lookup] against the authority in
     [ipool_body] -- and the swap is the whole transition: the freeing
     transaction's parked share comes OUT (iput gets it back, and with it its
     caller's whole [ln_tx] share) and this inum's [InodeRegion.imark] goes
     IN, where a commit reads it as the free bundle.

     The element comes back at [CrpDep], and [EscrowInode.escA_body]'s FILLED
     arm is where it is parked -- which is what lets a later recycle conclude
     the ledger's state from the escrow's peel. *)
  Lemma ipool_deposit_corpse (E : coPset) (cn : ic_names) (gfs : fs_names)
      (gi : gname) (cov : gset Z) (logstart : Z) (nib : nat) (z : Z)
      (t : nat) (q : Qp) :
    ↑ipoolN ⊆ E ->
    ipool_inv cn gfs gi cov logstart nib -∗
    crp_elem z (CrpPre t q) -∗
    imark gi z ={E}=∗
      crp_elem z CrpDep ∗ t ↪[ln_tx icfg_log]{#q} tt.
  Proof.
    iIntros (HE) "#Hinv Hel Hmk".
    iInv "Hinv" as ">Hb" "Hclose".
    iDestruct "Hb" as (O X T ids K)
      "(%Hlen & %Hrow & %Hdk & Hk1 & Hx1 & Ht1 & Htr & Hids & Hrows & Hck & Hcrp)".
    iDestruct (ghost_map_lookup with "Hck Hel") as %HKz.
    rewrite {1}/ipool_corpse (big_sepM_delete _ K z (CrpPre t q) HKz).
    iDestruct "Hcrp" as "[Hshare Hcrp]".
    iEval (rewrite /crp_row /tx_pin) in "Hshare".
    iMod (ghost_map_update CrpDep with "Hck Hel") as "[Hck Hel]".
    iMod ("Hclose" with "[Hk1 Hx1 Ht1 Htr Hids Hrows Hck Hcrp Hmk]") as "_".
    { iApply bi.later_intro. rewrite /ipool_body.
      iExists O, X, T, ids, (<[z := CrpDep]> K).
      iSplitR; [iPureIntro; exact Hlen |].
      iSplitR; [iPureIntro; exact Hrow |].
      iSplitR.
      { iPureIntro. rewrite dom_insert_L -Hdk.
        assert (Hzin : z ∈ dom K) by (apply elem_of_dom; by eexists).
        set_solver. }
      iFrame "Hk1 Hx1 Ht1 Htr Hids Hrows Hck".
      rewrite /ipool_corpse big_sepM_insert_delete.
      iSplitL "Hmk"; [iExact "Hmk" | iExact "Hcrp"]. }
    iModIntro. iFrame "Hel Hshare".
  Qed.

  (* [ic_escrow_body_ident] (main: the escrow's half of the identification
     ghost read off any arm) is GONE with the arms: the box's register carries
     the identity ([sr_ident], agreed between the box and the L1 row), and
     where the escrow-side [ic_id] half rides under the stitch is settled at
     the site map (tso-cutover-endgame.md §3.4.2). *)

  (* THE COMMIT'S DOOR (durable-fs-plan.md section 4): every ordinary
     uncached inum's bundle, at ONE ghost step and with no lock taken.
     Read-only -- the rows go straight back -- so it disturbs nothing a
     concurrent lock holder owns. *)
  Lemma ipool_inv_acc (E : coPset) (cn : ic_names) (γfs : fs_names)
      (γi : gname) (cov : gset Z) (logstart : Z) (nib : nat) :
    ↑ipoolN ⊆ E ->
    ipool_inv cn γfs γi cov logstart nib ={E, E ∖ ↑ipoolN}=∗
      ∃ (O X : gset Z) (T : gmap Z (nat * Qp))
        (ids : list (bool * mword 32 * mword 32)) (K : gmap Z icorpse),
        ⌜length ids = NINODE⌝ ∗
        (* THE PARTITION (durable-disk C-3b, split by C-4), which is what
           makes the rows below EXHAUSTIVE: see sections 5c and 5c' on why
           there are four parts and not two. *)
        ⌜region_inums nib = O ∪ X ∪ dom T ∪ ic_live_inums ids⌝ ∗
        (* ...AND THE CORPSE LEDGER'S DOMAIN (durable-disk C-7): the [X] part
           is not bundleless any more -- every one of its inums has a row
           here, and at a commit every row is that inum's marker. *)
        ⌜dom K = X⌝ ∗
        ipool_rows γfs γi cov logstart O ∗ ic_ids cn ids ∗
        ipool_transit T ∗ ipool_corpse γi K ∗
        ((ipool_rows γfs γi cov logstart O ∗ ic_ids cn ids ∗
          ipool_transit T ∗ ipool_corpse γi K) ={E ∖ ↑ipoolN, E}=∗ True).
  Proof.
    iIntros (HE) "#Hinv".
    iMod (inv_acc E ipoolN with "Hinv") as "[Hb Hclose]"; [exact HE |].
    iDestruct "Hb" as ">Hb".
    iDestruct "Hb" as (O X T ids K)
      "(%Hlen & %Hrow & %Hdk & Hk & Hx & Ht & Htr & Hids & Hrows & Hck & Hcrp)".
    iModIntro. iExists O, X, T, ids, K.
    iSplitR; [iPureIntro; exact Hlen |].
    iSplitR; [iPureIntro; exact Hrow |].
    iSplitR; [iPureIntro; exact Hdk |].
    iFrame "Hrows Hids Htr Hcrp".
    iIntros "(Hrows & Hids & Htr & Hcrp)". iApply "Hclose". iApply bi.later_intro.
    rewrite /ipool_body. iExists O, X, T, ids, K.
    iSplitR; [iPureIntro; exact Hlen |].
    iSplitR; [iPureIntro; exact Hrow |].
    iSplitR; [iPureIntro; exact Hdk |].
    iFrame "Hk Hx Ht Htr Hids Hrows Hck Hcrp".
  Qed.

  (* ---- THE POOL-SIDE TWIN OF [ic_escrow_body_cover] (durable-disk C-4) --
     (durable-fs-plan.md section 4; the shape B''-tx5's REMAINS forced)

     THE COMMIT'S DOOR AT QUIESCENCE, and the ONE thing it adds to
     [ipool_inv_acc] is that NOTHING IS IN TRANSIT.  The escrow's per-slot
     cover ([ic_escrow_body_cover_all]) says what each of the fifty slots is
     holding; this says what the POOL is, and together they exhaust
     [region_inums nib] -- which is the whole point of C-3b's partition.

     [T = ∅] is read off the parked shares ([TxPin.tx_pins_no_ops] at the
     transit ledger, which IS a [tx_pins]): a walk
     between an eviction's identity flip and its deposit is inside iput,
     hence inside its caller's transaction, and at a commit the WAL's
     [ln_tx] authority is empty.  So the row comes out in B''-join's own
     three-part shape, and the residue the collection still has to place is
     [X] alone -- the pending/await rows, whose region slot carries C-3c's
     [InodeRegion.ireg_top_park] on [ireg_slot]'s PENDING arm and whose
     bundle the collection therefore reads REGION-side through
     [FsCollect.col_free_slot_acc], owing the pool nothing.

     The [ln_tx] authority is BORROWED and comes straight back: the
     committer holds it inside [LogInv.log_res] and needs it there. *)
  Lemma ipool_quiesce_acc (E : coPset) (cn : ic_names) (γfs : fs_names)
      (γi : gname) (cov : gset Z) (logstart : Z) (nib : nat) :
    ↑ipoolN ⊆ E ->
    ipool_inv cn γfs γi cov logstart nib -∗
    ghost_map_auth (ln_tx icfg_log) 1 (∅ : gmap nat unit) ={E, E ∖ ↑ipoolN}=∗
      ∃ (O X : gset Z) (ids : list (bool * mword 32 * mword 32)),
        ⌜length ids = NINODE⌝ ∗
        ⌜region_inums nib = O ∪ X ∪ ic_live_inums ids⌝ ∗
        ghost_map_auth (ln_tx icfg_log) 1 (∅ : gmap nat unit) ∗
        ipool_rows γfs γi cov logstart O ∗ ic_ids cn ids ∗
        (* THE [X] PART'S MARKERS (durable-disk C-7): every corpse has been
           deposited (a pre-deposit row parks a share of the freeing
           transaction, and no transaction is open), so what the ledger holds
           is one [InodeRegion.imark] per in-transition inum -- which is
           exactly what [FsCollect.col_free_slot_acc] reads as that inum's
           free bundle.  Residue (G) of [FsCollect]'s header, closed. *)
        ([∗ set] z ∈ X, imark γi z) ∗
        ((ipool_rows γfs γi cov logstart O ∗ ic_ids cn ids ∗
          ([∗ set] z ∈ X, imark γi z)) ={E ∖ ↑ipoolN, E}=∗ True).
  Proof.
    iIntros (HE) "#Hinv Htxa".
    iMod (ipool_inv_acc E cn γfs γi cov logstart nib HE with "Hinv")
      as (O X T ids K) "(%Hlen & %Hrow & %Hdk & Hrows & Hids & Htr & Hcrp & Hback)".
    iDestruct (tx_pins_no_ops _ T with "Htxa Htr") as %->.
    iDestruct (ipool_corpse_no_ops γi K with "Htxa Hcrp") as %HF.
    iEval (rewrite (ipool_corpse_marks γi K HF) Hdk) in "Hcrp".
    iModIntro. iExists O, X, ids.
    iSplitR; [iPureIntro; exact Hlen |].
    iSplitR.
    { iPureIntro. rewrite dom_empty_L in Hrow. rewrite Hrow. set_solver. }
    iFrame "Htxa Hrows Hids Hcrp".
    iIntros "(Hrows & Hids & Hcrp)". iApply "Hback". iFrame "Hrows Hids".
    iSplitR; [rewrite /ipool_transit /tx_pins big_sepM_empty; done |].
    iEval (rewrite (ipool_corpse_marks γi K HF) Hdk). iExact "Hcrp".
  Qed.

  (* WHAT THE COLLECTION READS OFF THE PARTITION: every region inum is
     either in the ordinary index (a pool row, hence a bundle), or in
     transit (the residue -- see section 5c), or the inum of a LIVE slot,
     whose escrow is where its bundle then is. *)
  Lemma ipool_cover_inum (O X : gset Z)
      (ids : list (bool * mword 32 * mword 32)) (nib : nat) (z : Z) :
    region_inums nib = O ∪ X ∪ ic_live_inums ids ->
    z ∈ region_inums nib ->
    z ∈ O \/ z ∈ X \/
    ∃ (k : nat) (p : bool * mword 32 * mword 32),
      ids !! k = Some p /\ p.1.1 = true /\ bv_unsigned p.2 = z.
  Proof.
    intros Hrow Hz. rewrite Hrow in Hz.
    apply elem_of_union in Hz as [Hz | Hz].
    - apply elem_of_union in Hz as [Hz | Hz]; [by left | by right; left].
    - right; right. apply ic_live_inums_lookup in Hz as (k & p & Hk & Hv & ->).
      by exists k, p.
  Qed.

  (* THE BRIDGE the collection walks (durable-disk C-3b, accessor 2): the
     identity the PARTITION records for slot [k] is the one the escrow's arm
     carries -- one cell, two shares.  Pure, so nothing is consumed and the
     caller hands every escrow back untouched. *)
  Lemma ic_ids_pin (cn : ic_names) (ids : list (bool * mword 32 * mword 32))
      (k : nat) (v : bool) (d n : mword 32)
      (q : Qp) (v' : bool) (d' n' : mword 32) :
    ids !! k = Some (v, d, n) ->
    ic_ids cn ids -∗ ic_id cn k q v' d' n' -∗ ⌜v' = v /\ d' = d /\ n' = n⌝.
  Proof.
    intros Hk. iIntros "Hids Hq".
    iDestruct (ic_ids_acc cn ids k v d n Hk with "Hids") as "[Hqp _]".
    iApply (ic_id_agree with "Hq Hqp").
  Qed.

  (* THE PARTITION, EXERCISED AT THE REAL SHAPE (durable-disk C-3b): an inum
     the pool does not hold as an ordinary row and that is not in transit is
     CACHED, and this is how the collection reaches the slot that caches it
     -- it names the slot, reads the escrow's own identity half off the open
     body, and PINS it to that inum against the pool's quarter.  What the
     collection does next is [ic_escrow_body_cover] at that slot, whose four
     alternatives are all stated at this very [dev]/[inum] pair. *)

  (* the obstruction the split is FOR, checked: the in-transition row is not
     Timeless, so a pool shape carrying it could never have moved into an
     invariant whole. *)

End IcacheEscrow.

(* THE ICACHE INSTANCE OF THE TRANSIT BOX (endgame §4.2, R3; formerly
   IcacheBox.v, merged here at R3.3 so the instance and the escrow it
   replaces live in one module).  STATUS: PROVEN (no [Admitted]).  The
   second instantiation of CtxBox.v (the "rule of two"); bcache's is
   BioInv v6.

   WHAT THIS FILE PINS, so R3 does not re-derive it in prose:

   M-1' THE DEAD SLOT IS AN IDENTITY, NOT A SHAPE.  id := option (dev × inum);
        None is "never identified or evicted".  P_hdr None x forces x = IcRaw
        (a fixed raw header: cells at any value, no payload ghost), so the
        recycler's (a) at c = 0 KNOWS the shape from the register's identity
        -- no refutation of Unloaded/Loaded is needed.  The vetted M-1
        discharge ("the pool owns sr_ident's inum after eviction") does not
        hold once the evicted inum has been re-cached in another slot k' --
        k' 's box owns the inum's pool resource then, and the recycler of k
        cannot see it.  Encoding deadness in the identity avoids the
        discharge entirely, and the L1 row's tie ⌜sr_ident r = ci !! k⌝
        mirrors the table's identification map exactly (ic_id retires).

   M-3  X := IcRaw | IcUnloaded g | IcLoaded g dn bm.  The generation rides
        the shape (the vetting's addition).  P_hdr = i_valid (full) ∗ the
        identity halves ∗ i_nlink ∗ the payload GHOST at (inum, x) -- the
        loaded/unloaded ghost with its frozen alternative, exactly today's
        ic_payload_arm minus its two cell conjuncts; P_rest = the other four
        meta cells + addrs at x.  Regrouping lemma: ic_payload_regroup.

   M-4  The holder's handle row: ic_deposit at DepShr redefined as
        l2_hold at the SHARE SINGLETON {[(Some (dev,inum), t) := s]} (keys and
        mass pinned, R-1) ∗ the share's identity cells ∗ its liveness slice.

   M-5  THE STAMPS MASS: a whole reference carries mass 1; a share of
        identity fraction s carries mass s; a parent that has lent identity
        (qt − qi) carries mass 1 − (qt − qi).  Σ mass over a slot's
        references = the count, as CtxBox's row (Σ) requires.  The doc's
        "mass q / s" (identity fractions) would break (Σ): a whole reference
        holds identity q ≤ 1/2 but must weigh 1.

   M-6  L2 payload := CtxBox.l2_row at tok := ic_tok; L1 row := ic_slot_row.

   Names (F19): the four box gnames per slot become a FIELD of ic_names
   (icn_box : nat → box_names; six MkIcNames sites, the smaller sweep, and
   what lets [ic_deposit cn k d] keep its name and arity).  In this
   skeleton the record [ic_boxes] stands in for that field so the file is
   self-contained; every [b] below is [cn] at R3.

   AFTER REVIEWER 1's RULE-0 AUDIT (F14–F20, applied here):
   F14  the recycle and the eviction CHANGE the shape at (b): CtxBox gains
        box_deposit_L1_shape (target x1, client entailment P_rest x0 ⊢
        P_rest x1); ic_rest_raw_unloaded / ic_rest_to_raw are the icache's
        two entailments.
   F15  the holder has the share MINUS slh_tok (acquiresleep deposited it):
        (e)/(f) take and return [ic_body k d], the descriptor's cells and
        slice; the client re-forms inode_shr2 after releasesleep.
   F16  (tso-flip) iput's own (e)/(f) at mass 1 with the WHOLE unit and a
        [DepRef] descriptor: NOT on this branch (endgame F39) -- iput's free
        path is main's guard (a) at count 1 plus the (g) exchange to
        [DepFrz]; [DepRef] is deleted from [ic_dep].
   F17  ic_slot_row carries the cnt half (tied to M !! k's count, 0 at
        None); the table's dead row keeps [islot_free_at] as the
        complement of the dead header's identity halves.
   F18  ic_decr over any identity (the eviction's (d) is at None).
   F20  boot deposits ic_rest k IcRaw. *)

(* the identity, the shape and the cameras live in Xv6Cameras §15; the
   per-slot box names are [icfg_box k] (IcacheRef.icfg, canonical) *)
Definition ic_x_loaded (x : ic_x) : bool :=
  match x with IcLoaded _ _ _ => true | _ => false end.
Definition ic_x_gen (x : ic_x) : option gname :=
  match x with IcRaw => None | IcUnloaded g => Some g | IcLoaded g _ _ => Some g end.

Definition icBoxN : namespace := nroot .@ "xv6icbox".

(* ====================================================================== *)
(*  The bundle, at the AMBIENT context (the box λs instantiate XI := ξ)    *)
(* ====================================================================== *)
Section IcacheBoxAmb.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !irefslotG Σ}.
  Context `{GEN : GenId} `{ICFG : icfg}.
  Context `{XI : CurCtx}.
  Implicit Types (cn : ic_names).

  (* the payload's GHOST side: [ic_loaded] minus its two cell conjuncts
     ([inode_meta], [inode_addrs]), verbatim otherwise *)
  (* THE STITCH: main's [ic_loaded] minus its two cell conjuncts -- the
     five pure rows and the per-inode LEG (entry tokens + the era bundle at
     fraction 1, durable-disk EV stage 4); main's dview/fview retirement
     stands, so no [dv_ride]/[fv_ride] here. *)
  Definition ic_loaded_ghost (γfs : fs_names) (γi : gname) (cov : gset Z)
      (logstart : Z) (inum : mword 32) (dn : dinode) (bm : blkmap) : iProp Σ :=
    (∃ (data : nat -> list (bv 8)),
       ⌜inode_ok cov logstart dn bm data⌝ ∗
       ⌜dir_ok icfg_nib dn data⌝ ∗
       ⌜dir_dots_ix (bv_unsigned inum) dn data⌝ ∗
       ⌜dir_orphan_clean dn data⌝ ∗
       ⌜dir_uniq dn data⌝ ∗
       ic_inode_leg γfs (DfracOwn 1) γi inum (era_node dn bm data))%I.

  (* the identity-keyed payload at a shape: today's [ic_payload_arm] with
     the cells removed.  An IDENTIFIED slot is never raw. *)
  Definition ic_pay (γfs : fs_names) (γi : gname) (cov : gset Z) (logstart : Z)
      (k : nat) (inum : mword 32) (x : ic_x) : iProp Σ :=
    match x with
    | IcRaw => False%I
    (* the two alternatives are main's [ic_payload_arm]'s (durable-disk
       B''-tx5).  F42 (endgame §6¹²): the window pin AT REST ([ic_pin_rest])
       does NOT ride the ordinary arm any more -- it rides the TABLE ROW
       ([IcacheInv.frz_park]'s OFF arm, F42′), where iput's guard can update
       it BEFORE its (a) produces the OUT_L1 residue [ic_pin_tx].  The FROZEN
       alternative -- iput's mid-free park -- carries the selector's quarter
       and the window's pin [ic_pin_tx] (main's; the freeze receipt [frzown]
       is retired). *)
    | IcUnloaded g =>
        ((ipool_shape_np γfs γi cov logstart inum ∗ ity_pending g ∗
          ifreeze_off (bv_unsigned inum) ∗ live_gen k (1/2) g)
         ∨ (frzsel k ((1/2)/2)%Qp true ∗ ic_pin_tx k))%I
    | IcLoaded g dn bm =>
        ((ic_loaded_ghost γfs γi cov logstart inum dn bm ∗ ity_shot g (di_type dn) ∗
          ifreeze_off (bv_unsigned inum) ∗ live_gen k (1/2) g)
         ∨ (frzsel k ((1/2)/2)%Qp true ∗ ic_pin_tx k))%I
    end.

  (* the four meta cells P_rest keeps (nlink is L1-side: iput's guard) *)
  Definition ic_meta_rest (ip : mword 64) (d : dinode) : iProp Σ :=
    (i_type  ip ↦₂ di_type  d ∗
     i_major ip ↦₂ di_major d ∗
     i_minor ip ↦₂ di_minor d ∗
     i_size  ip ↦₄ di_size  d)%I.

  (* P_rest at a shape: cells at the record's values when loaded, at any
     values otherwise; the addrs likewise.  [i_size] is the FULL cell
     P_rest_excl runs on. *)
  Definition ic_rest_amb (k : nat) (x : ic_x) : iProp Σ :=
    match x with
    | IcLoaded _ dn bm =>
        (⌜length (bm_cells bm) = 13%nat⌝ ∗
         ic_meta_rest (ientry k) dn ∗ inode_addrs (ientry k) (bm_cells bm))%I
    | _ =>
        ((∃ d : dinode, ic_meta_rest (ientry k) d) ∗
         (∃ l : list (bv 32), ⌜length l = 13%nat⌝ ∗ inode_addrs (ientry k) l))%I
    end.

  (* P_hdr at an identity and a shape.  DEAD (None): the raw header, shape
     forced to IcRaw.  IDENTIFIED: valid at the shape's polarity, the two
     identity halves, nlink (at the record's value when loaded), the payload
     ghost.  [i_valid] is the FULL cell P_hdr_excl runs on. *)
  (* THE STITCH (endgame plan §6″ P3, §6⁸ Q1/Q3): the header carries the
     BOX'S QUARTER of main's identification ghost [ic_id] -- true at the
     identity when identified, false (∃-bound values) when dead -- so the
     register's [sr_ident] and [ic_id] agree by this definition, and the
     commit's collection agrees against the pool's quarter exactly where
     main did; the table keeps a half under itable.lock.  Main's window
     pin AT REST ([ic_pin_rest]) rides the TABLE ROW, not the header (F42,
     §6¹²: the guard must produce the OUT_L1 residue from the row it holds
     before (a) opens the box). *)
  Definition ic_hdr_amb cn (γfs : fs_names) (γi : gname) (cov : gset Z) (logstart : Z)
      (k : nat) (i : ic_bid) (x : ic_x) : iProp Σ :=
    match i with
    | None =>
        (⌜x = IcRaw⌝ ∗
         (∃ v : mword 32, i_valid (ientry k) ↦₄ v) ∗
         (∃ dev inum : mword 32, inode_ident k (DfracOwn (1/2)) dev inum) ∗
         (∃ n : bv 16, i_nlink (ientry k) ↦₂ n) ∗
         (∃ dev inum : mword 32, ic_id cn k (1/4) false dev inum))%I
    | Some (dev, inum) =>
        (i_valid (ientry k) ↦₄ valid_word (ic_x_loaded x) ∗
         inode_ident k (DfracOwn (1/2)) dev inum ∗
         (match x with
          | IcLoaded _ dn _ => i_nlink (ientry k) ↦₂ di_nlink dn
          | _ => ∃ n : bv 16, i_nlink (ientry k) ↦₂ n
          end) ∗
         ic_pay γfs γi cov logstart k inum x ∗
         ic_id cn k (1/4) true dev inum)%I
    end.

  (* M-1': the dead header's shape is known *)
  Lemma ic_hdr_dead_raw cn γfs γi cov logstart k x :
    ic_hdr_amb cn γfs γi cov logstart k None x -∗ ⌜x = IcRaw⌝.
  Proof. iIntros "(% & _)". by iPureIntro. Qed.

  (* F14: the two P_rest entailments the shape-changing (b) needs *)
  Lemma ic_rest_raw_unloaded k g :
    ic_rest_amb k IcRaw ⊣⊢ ic_rest_amb k (IcUnloaded g).
  Proof. reflexivity. Qed.
  Lemma ic_rest_to_raw k x :
    ic_rest_amb k x ⊢ ic_rest_amb k IcRaw.
  Proof.
    destruct x as [|g|g dn bm]; simpl; [iIntros "H"; iExact "H" | iIntros "H"; iExact "H" |].
    iIntros "(%Hlen & Hm & Ha)". iSplitL "Hm". { iExists dn. iExact "Hm". }
    iExists (bm_cells bm). iFrame "Ha". by iPureIntro.
  Qed.

  (* THE REGROUPING (F2's icache twin), PER SHAPE.  Today's rows for a loaded
     / unloaded entry ⇄ the box bundle at IcLoaded g dn bm / IcUnloaded g.
     The frozen alternative has no cell side of its own: the freer deposits
     it with the raw P_rest it holds, so no iff over today's arm is stated. *)
  (* PEEL ONE CONNECTIVE PER STEP (optimization.md / BioInv's tl_struct): a
     single [apply _] over these ∃/∗/∨ towers backtracks across the whole
     instance space and takes minutes. *)
  Local Ltac tl_struct :=
    lazymatch goal with
    | |- Timeless (bi_exist _) => apply bi.exist_timeless; intro; tl_struct
    | |- Timeless (bi_sep _ _) => apply bi.sep_timeless; [tl_struct | tl_struct]
    | |- Timeless (bi_or _ _)  => apply bi.or_timeless;  [tl_struct | tl_struct]
    | |- Timeless (bi_pure _)  => apply bi.pure_timeless
    | |- _ => apply _
    end.
  Global Instance ic_loaded_ghost_timeless γfs γi cov logstart inum dn bm :
    Timeless (ic_loaded_ghost γfs γi cov logstart inum dn bm).
  Proof. rewrite /ic_loaded_ghost. tl_struct. Qed.
  Global Instance ic_pay_timeless γfs γi cov logstart k inum x :
    Timeless (ic_pay γfs γi cov logstart k inum x).
  Proof. rewrite /ic_pay. destruct x; tl_struct. Qed.
  Global Instance ic_meta_rest_timeless ip d : Timeless (ic_meta_rest ip d).
  Proof. rewrite /ic_meta_rest. tl_struct. Qed.
  Global Instance ic_rest_amb_timeless k x : Timeless (ic_rest_amb k x).
  Proof. rewrite /ic_rest_amb. destruct x; tl_struct. Qed.
  Global Instance ic_hdr_amb_timeless cn γfs γi cov logstart k i x :
    Timeless (ic_hdr_amb cn γfs γi cov logstart k i x).
  Proof.
    rewrite /ic_hdr_amb /inode_ident. destruct i as [[dev inum]|]; [destruct x|]; tl_struct.
  Qed.

  Lemma ic_bundle_loaded_intro cn γfs γi cov logstart k dev inum g dn bm :
    length (bm_cells bm) = 13%nat ->
    inode_ident k (DfracOwn (1/2)) dev inum -∗
    i_valid (ientry k) ↦₄ valid_word true -∗
    ic_loaded γfs γi cov logstart k inum dn bm -∗
    ity_shot g (di_type dn) -∗ ifreeze_off (bv_unsigned inum) -∗ live_gen k (1/2) g -∗
    ic_id cn k (1/4) true dev inum -∗
    ic_hdr_amb cn γfs γi cov logstart k (Some (dev, inum)) (IcLoaded g dn bm) ∗
    ic_rest_amb k (IcLoaded g dn bm).
  Proof.
    iIntros (Hlen) "Hid Hv Hl Hty Hoff Hlg Hgid".
    rewrite /ic_loaded. iDestruct "Hl" as (data) "(%H1 & %H2 & %H3 & %H4 & %H5 & Hleg & Hmeta & Haddr)".
    rewrite /inode_meta. iDestruct "Hmeta" as "(Hty2 & Hmaj & Hmin & Hnl & Hsz)".
    iSplitR "Hty2 Hmaj Hmin Hsz Haddr".
    - rewrite /ic_hdr_amb. iFrame "Hv Hid Hnl Hgid". rewrite /ic_pay. iLeft.
      iFrame "Hty Hoff Hlg". rewrite /ic_loaded_ghost. iExists data. iFrame "Hleg". done.
    - rewrite /ic_rest_amb /ic_meta_rest. iFrame "Hty2 Hmaj Hmin Hsz Haddr". done.
  Qed.
  Lemma ic_bundle_loaded_elim cn γfs γi cov logstart k dev inum g dn bm :
    ic_hdr_amb cn γfs γi cov logstart k (Some (dev, inum)) (IcLoaded g dn bm) -∗
    ic_rest_amb k (IcLoaded g dn bm) -∗
    inode_ident k (DfracOwn (1/2)) dev inum ∗
    i_valid (ientry k) ↦₄ valid_word true ∗
    ic_id cn k (1/4) true dev inum ∗
    ((ic_loaded γfs γi cov logstart k inum dn bm ∗ ity_shot g (di_type dn) ∗
      ifreeze_off (bv_unsigned inum) ∗ live_gen k (1/2) g)
     ∨ (frzsel k ((1/2)/2)%Qp true ∗ ic_pin_tx k ∗
        inode_meta (ientry k) dn ∗ inode_addrs (ientry k) (bm_cells bm))).
  Proof.
    rewrite /ic_hdr_amb /ic_rest_amb /ic_meta_rest.
    iIntros "(Hv & Hid & Hnl & Hpay & Hgid) (%Hlen & (Hty2 & Hmaj & Hmin & Hsz) & Haddr)".
    iFrame "Hid Hv Hgid". rewrite /ic_pay.
    iDestruct "Hpay" as "[(Hg & Hty & Hoff & Hlg) | [Hfs Hpin]]".
    - iLeft. iFrame "Hty Hoff Hlg". rewrite /ic_loaded /ic_loaded_ghost.
      iDestruct "Hg" as (data) "(%H1 & %H2 & %H3 & %H4 & %H5 & Hleg)".
      iExists data. rewrite /inode_meta. iFrame "Hleg Haddr Hty2 Hmaj Hmin Hnl Hsz". done.
    - iRight. iFrame "Hfs Hpin Haddr". rewrite /inode_meta. iFrame "Hty2 Hmaj Hmin Hnl Hsz".
  Qed.
  Lemma ic_bundle_unloaded_intro cn γfs γi cov logstart k dev inum g :
    inode_ident k (DfracOwn (1/2)) dev inum -∗
    i_valid (ientry k) ↦₄ valid_word false -∗
    (∃ n : bv 16, i_nlink (ientry k) ↦₂ n) -∗
    (∃ d : dinode, ic_meta_rest (ientry k) d) -∗
    (∃ l : list (bv 32), ⌜length l = 13%nat⌝ ∗ inode_addrs (ientry k) l) -∗
    ipool_shape_np γfs γi cov logstart inum -∗
    ity_pending g -∗ ifreeze_off (bv_unsigned inum) -∗ live_gen k (1/2) g -∗
    ic_id cn k (1/4) true dev inum -∗
    ic_hdr_amb cn γfs γi cov logstart k (Some (dev, inum)) (IcUnloaded g) ∗
    ic_rest_amb k (IcUnloaded g).
  Proof.
    iIntros "Hid Hv Hnl Hm Ha Hpool Hty Hoff Hlg Hgid".
    rewrite /ic_hdr_amb /ic_rest_amb. iFrame "Hv Hid Hnl Hm Ha Hgid".
    rewrite /ic_pay. iLeft. iFrame "Hpool Hty Hoff Hlg".
  Qed.
  Lemma ic_bundle_unloaded_elim cn γfs γi cov logstart k dev inum g :
    ic_hdr_amb cn γfs γi cov logstart k (Some (dev, inum)) (IcUnloaded g) -∗
    ic_rest_amb k (IcUnloaded g) -∗
    inode_ident k (DfracOwn (1/2)) dev inum ∗
    i_valid (ientry k) ↦₄ valid_word false ∗
    (∃ n : bv 16, i_nlink (ientry k) ↦₂ n) ∗
    (∃ d : dinode, ic_meta_rest (ientry k) d) ∗
    (∃ l : list (bv 32), ⌜length l = 13%nat⌝ ∗ inode_addrs (ientry k) l) ∗
    ic_id cn k (1/4) true dev inum ∗
    ((ipool_shape_np γfs γi cov logstart inum ∗ ity_pending g ∗
      ifreeze_off (bv_unsigned inum) ∗ live_gen k (1/2) g)
     ∨ (frzsel k ((1/2)/2)%Qp true ∗ ic_pin_tx k)).
  Proof.
    rewrite /ic_hdr_amb /ic_rest_amb. iIntros "(Hv & Hid & Hnl & Hpay & Hgid) (Hm & Ha)".
    iFrame "Hid Hv Hnl Hm Ha Hgid". iExact "Hpay".
  Qed.
  (* the dead header from raw cells *)
  Lemma ic_hdr_dead_intro cn γfs γi cov logstart k :
    (∃ v : mword 32, i_valid (ientry k) ↦₄ v) -∗
    (∃ dev inum : mword 32, inode_ident k (DfracOwn (1/2)) dev inum) -∗
    (∃ n : bv 16, i_nlink (ientry k) ↦₂ n) -∗
    (∃ dev inum : mword 32, ic_id cn k (1/4) false dev inum) -∗
    ic_hdr_amb cn γfs γi cov logstart k None IcRaw.
  Proof. iIntros "Hv Hid Hnl Hgid". rewrite /ic_hdr_amb. iFrame "Hv Hid Hnl Hgid". done. Qed.
  (* the LOADED bundle's ghost side goes back to the free pool as the
     pool's [np] shape -- the eviction's re-pack (today's
     ic_close_to_empty_core, minus the cells the box keeps) *)
  Lemma ic_loaded_ghost_to_np γfs γi cov logstart (inum : mword 32) (dn : dinode) (bm : blkmap) :
    ic_loaded_ghost γfs γi cov logstart inum dn bm -∗
    ipool_shape_np γfs γi cov logstart inum.
  Proof.
    rewrite /ic_loaded_ghost.
    iIntros "(%data & %Hok & %Hdok & %Hddix & %Hdoc & %Hduq & Hleg)".
    rewrite /ipool_shape_np /ipool_alloc. iLeft. iExists dn, bm, data.
    iSplitR; [iPureIntro; exact Hok |].
    iSplitR; [iPureIntro; exact Hdok |].
    iSplitR; [iPureIntro; exact Hddix |].
    iSplitR; [iPureIntro; exact Hdoc |].
    iSplitR; [iPureIntro; exact Hduq |].
    iExact "Hleg".
  Qed.

  (* the identified header's identity halves and (loaded) nlink cell,
     borrowed and returned unchanged -- iput's guard reads them off the
     header in hand *)
  Lemma ic_hdr_ident_acc cn γfs γi cov logstart k dev inum x :
    ic_hdr_amb cn γfs γi cov logstart k (Some (dev, inum)) x -∗
    inode_ident k (DfracOwn (1/2)) dev inum ∗
    (inode_ident k (DfracOwn (1/2)) dev inum -∗
     ic_hdr_amb cn γfs γi cov logstart k (Some (dev, inum)) x).
  Proof.
    rewrite /ic_hdr_amb. iIntros "(Hv & Hid & Hnl & Hpay & Hgid)". iFrame "Hid".
    iIntros "Hid". iFrame "Hv Hid Hnl Hpay Hgid".
  Qed.
  Lemma ic_hdr_nlink_acc cn γfs γi cov logstart k dev inum g dn bm :
    ic_hdr_amb cn γfs γi cov logstart k (Some (dev, inum)) (IcLoaded g dn bm) -∗
    i_nlink (ientry k) ↦₂ di_nlink dn ∗
    (i_nlink (ientry k) ↦₂ di_nlink dn -∗
     ic_hdr_amb cn γfs γi cov logstart k (Some (dev, inum)) (IcLoaded g dn bm)).
  Proof.
    rewrite /ic_hdr_amb. iIntros "(Hv & Hid & Hnl & Hpay & Hgid)". iFrame "Hnl".
    iIntros "Hnl". iFrame "Hv Hid Hnl Hpay Hgid".
  Qed.

  (* the identified header's valid cell, borrowed and returned unchanged:
     ilock reads it before it knows the shape *)
  Lemma ic_hdr_valid_acc cn γfs γi cov logstart k dev inum x :
    ic_hdr_amb cn γfs γi cov logstart k (Some (dev, inum)) x -∗
    i_valid (ientry k) ↦₄ valid_word (ic_x_loaded x) ∗
    (i_valid (ientry k) ↦₄ valid_word (ic_x_loaded x) -∗
     ic_hdr_amb cn γfs γi cov logstart k (Some (dev, inum)) x).
  Proof.
    rewrite /ic_hdr_amb. iIntros "(Hv & Hid & Hnl & Hpay & Hgid)". iFrame "Hv".
    iIntros "Hv". iFrame "Hv Hid Hnl Hpay Hgid".
  Qed.

  (* the LOADED payload's GHOST side, opened and closed the way
     [ic_loaded_open] / [ic_mk_loaded] open and close the whole payload:
     the era bundle splits into the record, the indirect resources, the
     blocks and the era's abstract value, and joins back.  What iput's
     guard reads the record through while the cells ride the box. *)
  Lemma ic_loaded_ghost_open γfs γi cov logstart (inum : mword 32)
      (dn : dinode) (bm : blkmap) :
    ic_loaded_ghost γfs γi cov logstart inum dn bm -∗
    ∃ (data : nat -> list (bv 8)),
       ⌜inode_ok cov logstart dn bm data⌝ ∗
       ⌜dir_ok icfg_nib dn data⌝ ∗
       ⌜dir_dots_ix (bv_unsigned inum) dn data⌝ ∗
       ⌜dir_orphan_clean dn data⌝ ∗
       ⌜dir_uniq dn data⌝ ∗
       ic_inode_leg γfs (DfracOwn 1) γi inum (era_node dn bm data).
  Proof. rewrite /ic_loaded_ghost. iIntros "H". iExact "H". Qed.
  Lemma ic_mk_loaded_ghost γfs γi cov logstart (inum : mword 32)
      (dn : dinode) (bm : blkmap) (data : nat -> list (bv 8)) :
    inode_ok cov logstart dn bm data ->
    dir_ok icfg_nib dn data ->
    dir_dots_ix (bv_unsigned inum) dn data ->
    dir_orphan_clean dn data ->
    dir_uniq dn data ->
    ic_inode_leg γfs (DfracOwn 1) γi inum (era_node dn bm data) -∗
    ic_loaded_ghost γfs γi cov logstart inum dn bm.
  Proof.
    iIntros (H1 H2 H3 H4 H5) "Hleg". rewrite /ic_loaded_ghost. iExists data.
    iFrame "Hleg". iPureIntro. split_and!; assumption.
  Qed.

  (* the LOADED payload is its ghost side beside its two cell rows -- what
     the free path keeps in hand across the box while the cells ride the
     header and the rest *)
  Lemma ic_loaded_ghost_split γfs γi cov logstart k (inum : mword 32) (dn : dinode) (bm : blkmap) :
    ic_loaded γfs γi cov logstart k inum dn bm ⊣⊢
    ic_loaded_ghost γfs γi cov logstart inum dn bm ∗
    inode_meta (ientry k) dn ∗ inode_addrs (ientry k) (bm_cells bm).
  Proof.
    rewrite /ic_loaded /ic_loaded_ghost. iSplit.
    - iIntros "(%data & %H1 & %H2 & %H3 & %H4 & %H5 & Hleg & Hmeta & Haddr)".
      iFrame "Hmeta Haddr". iExists data. iFrame "Hleg". done.
    - iIntros "[(%data & %H1 & %H2 & %H3 & %H4 & %H5 & Hleg) [Hmeta Haddr]]".
      iExists data. iFrame "Hleg Hmeta Haddr". done.
  Qed.

  (* the UNLOADED bundle's cells re-form today's [inode_raw] (what
     ilock's fill, [il_load], takes): the nlink cell rejoins the four meta
     cells at a record that agrees with them *)
  Lemma ic_raw_of_rest k :
    (∃ n : bv 16, i_nlink (ientry k) ↦₂ n) -∗
    (∃ d : dinode, ic_meta_rest (ientry k) d) -∗
    (∃ l : list (bv 32), ⌜length l = 13%nat⌝ ∗ inode_addrs (ientry k) l) -∗
    inode_raw (ientry k).
  Proof.
    iIntros "(%n & Hnl) (%d & (Hty & Hmaj & Hmin & Hsz)) Ha".
    rewrite /inode_raw. iFrame "Ha".
    iExists (MkDinode (di_type d) (di_major d) (di_minor d) n (di_size d) (di_addrs d)).
    rewrite /inode_meta. cbn. iFrame "Hty Hmaj Hmin Hnl Hsz".
  Qed.


  (* ---- THE READ ARM'S HELD PAYLOAD (main's [ic_rd_held], ghost side) ----
     the leg at a QUARTER; the arm's three quarters ([ic_rd_arm]) ride the
     OUT_L2 residue, where the commit's collection reads them (F40). *)
  Definition ic_rd_held_ghost (γfs : fs_names) (cov : gset Z) (logstart : Z)
      (inum : mword 32) (dn : dinode) (bm : blkmap) : iProp Σ :=
    (∃ (data : nat -> list (bv 8)),
       ⌜inode_ok cov logstart dn bm data⌝ ∗
       ⌜inode_local (bv_unsigned inum) (era_node dn bm data)⌝ ∗
       inode_rd_era γfs (DfracOwn (1/4)) inum (era_node dn bm data))%I.
  Global Instance ic_rd_held_ghost_timeless γfs cov logstart inum dn bm :
    Timeless (ic_rd_held_ghost γfs cov logstart inum dn bm).
  Proof. rewrite /ic_rd_held_ghost. tl_struct. Qed.
  (* the shed and the join, [ic_loaded_shed]/[ic_rd_join] minus the cells *)
  Lemma ic_loaded_ghost_shed γfs γi cov logstart (inum : mword 32) dn bm :
    ic_loaded_ghost γfs γi cov logstart inum dn bm -∗
    ic_rd_arm γfs γi cov logstart inum ∗ ic_rd_held_ghost γfs cov logstart inum dn bm.
  Proof.
    rewrite /ic_loaded_ghost /ic_rd_arm /ic_rd_held_ghost. iIntros "H".
    iDestruct "H" as (data) "(%Hok & %Hdok & %Hddix & %Hdoc & %Hduq & Hleg)".
    iDestruct (ic_inode_leg_local with "Hleg") as %Hloc.
    iDestruct (ic_inode_leg_shed_to with "Hleg") as "[Hleg34 Hn14]".
    iSplitL "Hleg34".
    - iExists dn, bm, data. iFrame "Hleg34".
      iSplitR; [iPureIntro; exact Hok |].
      iSplitR; [iPureIntro; exact Hdok |].
      iSplitR; [iPureIntro; exact Hddix |].
      iSplitR; [iPureIntro; exact Hdoc |].
      iPureIntro; exact Hduq.
    - iExists data. iFrame "Hn14".
      iSplitR; [iPureIntro; exact Hok |].
      iPureIntro; exact Hloc.
  Qed.
  Lemma ic_rd_ghost_join γfs γi cov logstart (inum : mword 32) dn bm :
    ic_rd_arm γfs γi cov logstart inum -∗
    ic_rd_held_ghost γfs cov logstart inum dn bm -∗
    ic_loaded_ghost γfs γi cov logstart inum dn bm.
  Proof.
    rewrite /ic_rd_arm /ic_rd_held_ghost /ic_loaded_ghost. iIntros "Harm Hheld".
    iDestruct "Harm" as (dn' bm' data') "(%Hok' & %Hdok & %Hddix & %Hdoc & %Hduq & Hleg)".
    iDestruct "Hheld" as (data) "(%Hok & %Hloc & Hn14)".
    iDestruct (ic_inode_leg_rd_agree with "Hleg Hn14") as %Hnode.
    destruct (era_node_pair_inj cov logstart dn' dn bm' bm data' data Hok' Hok Hnode) as [<- <-].
    rewrite -Hnode. iExists data'.
    iSplitR; [iPureIntro; exact Hok' |].
    iSplitR; [iPureIntro; exact Hdok |].
    iSplitR; [iPureIntro; exact Hddix |].
    iSplitR; [iPureIntro; exact Hdoc |].
    iSplitR; [iPureIntro; exact Hduq |].
    iApply (ic_inode_leg_shed_of with "Hleg Hn14").
  Qed.

  (* F40 (endgame §6¹¹/§6¹²/§6²⁰): THE HELD HEADER -- what an L2 holder has
     in hand.  The identified header MINUS the identification quarter, which
     rides the OUT_L2 residue [ic_q2] while the header is out (moved by
     (e′)'s split wand, back by (f′)'s join wand), so the commit's collection
     can tie the residue's identity to the slot's.  At the READ ARM
     ([rd = true]) the payload is the holder's quarter of the leg
     ([ic_rd_held_ghost]), LOADED and ORDINARY only: the split refuted the
     unloaded shape by the reader's type one-shot and the frozen alternative
     by its live slice, inside the checkout's own ghost step (main's
     [ic_swap_checkout_rd]).  Dead: the header itself (no checkout at a dead
     slot; the definition is total for the box's ∀ i x). *)
  Definition ic_pay_held (γfs : fs_names) (γi : gname) (cov : gset Z) (logstart : Z)
      (k : nat) (inum : mword 32) (rd : bool) (x : ic_x) : iProp Σ :=
    if rd then
      match x with
      | IcLoaded g dn bm =>
          (ic_rd_held_ghost γfs cov logstart inum dn bm ∗ ity_shot g (di_type dn) ∗
           ifreeze_off (bv_unsigned inum) ∗ live_gen k (1/2) g)%I
      | _ => False%I
      end
    else ic_pay γfs γi cov logstart k inum x.
  Definition ic_hdr_held_amb cn (γfs : fs_names) (γi : gname) (cov : gset Z) (logstart : Z)
      (k : nat) (rd : bool) (i : ic_bid) (x : ic_x) : iProp Σ :=
    match i with
    | None => ic_hdr_amb cn γfs γi cov logstart k None x
    | Some (dev, inum) =>
        (i_valid (ientry k) ↦₄ valid_word (ic_x_loaded x) ∗
         inode_ident k (DfracOwn (1/2)) dev inum ∗
         (match x with
          | IcLoaded _ dn _ => i_nlink (ientry k) ↦₂ di_nlink dn
          | _ => ∃ n : bv 16, i_nlink (ientry k) ↦₂ n
          end) ∗
         ic_pay_held γfs γi cov logstart k inum rd x)%I
    end.
  Global Instance ic_pay_held_timeless γfs γi cov logstart k inum rd x :
    Timeless (ic_pay_held γfs γi cov logstart k inum rd x).
  Proof. rewrite /ic_pay_held. destruct rd; [destruct x; tl_struct | apply _]. Qed.
  Global Instance ic_hdr_held_amb_timeless cn γfs γi cov logstart k rd i x :
    Timeless (ic_hdr_held_amb cn γfs γi cov logstart k rd i x).
  Proof.
    rewrite /ic_hdr_held_amb. destruct i as [[dev inum]|]; [| apply _].
    rewrite /inode_ident. destruct x; tl_struct.
  Qed.
  (* the write arm's (and the free path's) split and join: pure, the quarter
     alone moves *)
  Lemma ic_hdr_amb_split cn γfs γi cov logstart k dev inum x :
    ic_hdr_amb cn γfs γi cov logstart k (Some (dev, inum)) x -∗
    ic_hdr_held_amb cn γfs γi cov logstart k false (Some (dev, inum)) x ∗
    ic_id cn k (1/4) true dev inum.
  Proof.
    rewrite /ic_hdr_amb /ic_hdr_held_amb /ic_pay_held. iIntros "(Hv & Hid & Hnl & Hpay & Hgid)".
    iFrame "Hv Hid Hnl Hpay Hgid".
  Qed.
  Lemma ic_hdr_amb_join cn γfs γi cov logstart k dev inum x :
    ic_hdr_held_amb cn γfs γi cov logstart k false (Some (dev, inum)) x -∗
    ic_id cn k (1/4) true dev inum -∗
    ic_hdr_amb cn γfs γi cov logstart k (Some (dev, inum)) x.
  Proof.
    rewrite /ic_hdr_amb /ic_hdr_held_amb /ic_pay_held. iIntros "(Hv & Hid & Hnl & Hpay) Hgid".
    iFrame "Hv Hid Hnl Hpay Hgid".
  Qed.
  (* the read arm's join: the arm's three quarters come home to the quarter *)
  Lemma ic_hdr_amb_join_rd cn γfs γi cov logstart k dev inum x :
    ic_hdr_held_amb cn γfs γi cov logstart k true (Some (dev, inum)) x -∗
    ic_id cn k (1/4) true dev inum -∗
    ic_rd_arm γfs γi cov logstart inum -∗
    ic_hdr_amb cn γfs γi cov logstart k (Some (dev, inum)) x.
  Proof.
    rewrite /ic_hdr_amb /ic_hdr_held_amb /ic_pay_held. iIntros "(Hv & Hid & Hnl & Hpay) Hgid Harm".
    destruct x as [|g|g dn bm]; [iDestruct "Hpay" as %[] | iDestruct "Hpay" as %[] |].
    iDestruct "Hpay" as "(Hheld & Hty & Hoff & Hlg)".
    iFrame "Hv Hid Hnl Hgid". rewrite /ic_pay. iLeft. iFrame "Hty Hoff Hlg".
    iApply (ic_rd_ghost_join with "Harm Hheld").
  Qed.
  (* the read arm's split: a VIEW SHIFT (the reader's type one-shot kills the
     unloaded shape, its live slice kills the frozen alternative through
     [itable_inv]), the three quarters shed *)
  Lemma ic_hdr_amb_split_rd (E : coPset) cn γfs γi cov logstart k (dev inum : mword 32) x
      (s : Qp) (g : gname) (lo : nat) (ty : bv 16) :
    ↑icacheN ⊆ E -> (k < NINODE)%nat ->
    itable_inv -∗ ity_shot g ty -∗ live_genlo k s g lo -∗
    ic_hdr_amb cn γfs γi cov logstart k (Some (dev, inum)) x ={E}=∗
    ic_hdr_held_amb cn γfs γi cov logstart k true (Some (dev, inum)) x ∗
    ic_id cn k (1/4) true dev inum ∗
    ic_rd_arm γfs γi cov logstart inum ∗ live_genlo k s g lo.
  Proof.
    iIntros (HE Hk) "#Hinv #Hshot Hlv (Hv & Hid & Hnl & Hpay & Hgid)".
    iAssert itable_inv_pinw with "[]" as "#Hinvp". { rewrite /itable_inv_pinw. iExact "Hinv". }
    rewrite /ic_hdr_held_amb /ic_pay_held /ic_pay. destruct x as [|g'|g' dn bm].
    - iDestruct "Hpay" as %[].
    - iDestruct "Hpay" as "[(_ & Hpend & _ & Hlg) | [Hfs _]]".
      + iEval (rewrite /live_gen) in "Hlg". iDestruct "Hlg" as (lo') "Hlg".
        iDestruct (live_genlo_agree with "Hlv Hlg") as %[<- _].
        iDestruct (ity_pending_shot_excl with "Hpend Hshot") as %[].
      + iMod (frz_slot_kill_pinw E k ((1/2)/2)%Qp s g lo HE Hk with "Hinvp Hfs Hlv") as "[]".
    - iDestruct "Hpay" as "[(Hg & Hty & Hoff & Hlg) | [Hfs _]]".
      + iDestruct (ic_loaded_ghost_shed with "Hg") as "[Harm Hheld]".
        iModIntro. iFrame "Hv Hid Hnl Hgid Harm Hlv Hheld Hty Hoff Hlg".
      + iMod (frz_slot_kill_pinw E k ((1/2)/2)%Qp s g lo HE Hk with "Hinvp Hfs Hlv") as "[]".
  Qed.

  (* THE HELD BUNDLE FROM WHAT A HOLDER CARRIES (iunlock's park input): the
     cells, [ic_dep_held] at the descriptor's arm, the one-shot, the freeze
     token and the liveness half the handle carried -- by arm kind. *)
  Lemma ic_dep_held_bm_len γfs γi cov logstart d k (inum : mword 32) dn bm :
    ic_dep_held γfs γi cov logstart d k inum dn bm -∗ ⌜length (bm_cells bm) = 13%nat⌝.
  Proof.
    rewrite /ic_dep_held. destruct (ic_dep_rd d); [| apply ic_loaded_bm_len].
    rewrite /ic_rd_held. iIntros "H". iDestruct "H" as (data) "(%Hok & _)".
    iPureIntro. destruct Hok as (Hwf & _).
    rewrite /bm_cells length_app (blkmap_wf_dir_len _ _ _ Hwf). reflexivity.
  Qed.
  Lemma ic_dep_held_intro_held cn γfs γi cov logstart k d (s : Qp) (dev inum : mword 32)
      (g : gname) (lo : nat) dn bm :
    ic_dep_shr d = Some (s, dev, inum, g, lo) ->
    length (bm_cells bm) = 13%nat ->
    inode_ident k (DfracOwn (1/2)) dev inum -∗
    i_valid (ientry k) ↦₄ valid_word true -∗
    ic_dep_held γfs γi cov logstart d k inum dn bm -∗
    ity_shot g (di_type dn) -∗ ifreeze_off (bv_unsigned inum) -∗ live_gen k (1/2) g -∗
    ic_hdr_held_amb cn γfs γi cov logstart k (ic_dep_rd d) (Some (dev, inum)) (IcLoaded g dn bm) ∗
    ic_rest_amb k (IcLoaded g dn bm).
  Proof.
    iIntros (Hshr Hlen) "Hid Hv Hheld Hty Hoff Hlg".
    rewrite /ic_dep_held /ic_hdr_held_amb /ic_pay_held. destruct (ic_dep_rd d).
    - rewrite /ic_rd_held.
      iDestruct "Hheld" as (data) "(%Hok & %Hloc & Hmeta & Haddr & Hn14)".
      rewrite /inode_meta. iDestruct "Hmeta" as "(Hty2 & Hmaj & Hmin & Hnl & Hsz)".
      iSplitR "Hty2 Hmaj Hmin Hsz Haddr".
      + iFrame "Hv Hid Hnl Hty Hoff Hlg". rewrite /ic_rd_held_ghost. iExists data.
        iFrame "Hn14". done.
      + rewrite /ic_rest_amb /ic_meta_rest. iFrame "Hty2 Hmaj Hmin Hsz Haddr". done.
    - rewrite /ic_loaded.
      iDestruct "Hheld" as (data) "(%H1 & %H2 & %H3 & %H4 & %H5 & Hleg & Hmeta & Haddr)".
      rewrite /inode_meta. iDestruct "Hmeta" as "(Hty2 & Hmaj & Hmin & Hnl & Hsz)".
      iSplitR "Hty2 Hmaj Hmin Hsz Haddr".
      + iFrame "Hv Hid Hnl". rewrite /ic_pay. iLeft. iFrame "Hty Hoff Hlg".
        rewrite /ic_loaded_ghost. iExists data. iFrame "Hleg". done.
      + rewrite /ic_rest_amb /ic_meta_rest. iFrame "Hty2 Hmaj Hmin Hsz Haddr". done.
  Qed.

  (* ---- ilock's readings of the HELD header ---- *)
  (* the valid cell, borrowed and returned unchanged (the +0x1a read) *)
  Lemma ic_hdr_held_valid_acc cn γfs γi cov logstart k rd dev inum x :
    ic_hdr_held_amb cn γfs γi cov logstart k rd (Some (dev, inum)) x -∗
    i_valid (ientry k) ↦₄ valid_word (ic_x_loaded x) ∗
    (i_valid (ientry k) ↦₄ valid_word (ic_x_loaded x) -∗
     ic_hdr_held_amb cn γfs γi cov logstart k rd (Some (dev, inum)) x).
  Proof.
    rewrite /ic_hdr_held_amb. iIntros "(Hv & Hid & Hnl & Hpay)". iFrame "Hv".
    iIntros "Hv". iFrame "Hv Hid Hnl Hpay".
  Qed.
  (* the LOADED held bundle, by arm kind: the cells, and either the ordinary
     payload as the arm's [ic_dep_held] (the whole [ic_loaded] at a
     bundleless descriptor, the reader's quarter at DepRd) with the one-shot,
     the freeze token and the liveness half, or the frozen alternative *)
  Lemma ic_bundle_loaded_elim_held cn γfs γi cov logstart k d dev inum g dn bm :
    ic_hdr_held_amb cn γfs γi cov logstart k (ic_dep_rd d) (Some (dev, inum)) (IcLoaded g dn bm) -∗
    ic_rest_amb k (IcLoaded g dn bm) -∗
    inode_ident k (DfracOwn (1/2)) dev inum ∗
    i_valid (ientry k) ↦₄ valid_word true ∗
    ((ic_dep_held γfs γi cov logstart d k inum dn bm ∗ ity_shot g (di_type dn) ∗
      ifreeze_off (bv_unsigned inum) ∗ live_gen k (1/2) g)
     ∨ (frzsel k ((1/2)/2)%Qp true ∗ ic_pin_tx k ∗
        inode_meta (ientry k) dn ∗ inode_addrs (ientry k) (bm_cells bm))).
  Proof.
    rewrite /ic_hdr_held_amb /ic_pay_held /ic_rest_amb /ic_meta_rest /ic_dep_held.
    iIntros "(Hv & Hid & Hnl & Hpay) (%Hlen & (Hty2 & Hmaj & Hmin & Hsz) & Haddr)".
    iFrame "Hid Hv". destruct (ic_dep_rd d).
    - iDestruct "Hpay" as "(Hheld & Hty & Hoff & Hlg)". iLeft. iFrame "Hty Hoff Hlg".
      rewrite /ic_rd_held /ic_rd_held_ghost. iDestruct "Hheld" as (data) "(%Hok & %Hloc & Hn14)".
      iExists data. rewrite /inode_meta. iFrame "Hn14 Haddr Hty2 Hmaj Hmin Hnl Hsz". done.
    - rewrite /ic_pay. iDestruct "Hpay" as "[(Hg & Hty & Hoff & Hlg) | [Hfs Hpin]]".
      + iLeft. iFrame "Hty Hoff Hlg". rewrite /ic_loaded /ic_loaded_ghost.
        iDestruct "Hg" as (data) "(%H1 & %H2 & %H3 & %H4 & %H5 & Hleg)".
        iExists data. rewrite /inode_meta. iFrame "Hleg Haddr Hty2 Hmaj Hmin Hnl Hsz". done.
      + iRight. iFrame "Hfs Hpin Haddr". rewrite /inode_meta. iFrame "Hty2 Hmaj Hmin Hnl Hsz".
  Qed.
  (* the UNLOADED held bundle (a bundleless descriptor only: the read arm's
     held payload is loaded by construction) *)
  Lemma ic_bundle_unloaded_elim_held cn γfs γi cov logstart k dev inum g :
    ic_hdr_held_amb cn γfs γi cov logstart k false (Some (dev, inum)) (IcUnloaded g) -∗
    ic_rest_amb k (IcUnloaded g) -∗
    inode_ident k (DfracOwn (1/2)) dev inum ∗
    i_valid (ientry k) ↦₄ valid_word false ∗
    (∃ n : bv 16, i_nlink (ientry k) ↦₂ n) ∗
    (∃ dd : dinode, ic_meta_rest (ientry k) dd) ∗
    (∃ l : list (bv 32), ⌜length l = 13%nat⌝ ∗ inode_addrs (ientry k) l) ∗
    ((ipool_shape_np γfs γi cov logstart inum ∗ ity_pending g ∗
      ifreeze_off (bv_unsigned inum) ∗ live_gen k (1/2) g)
     ∨ (frzsel k ((1/2)/2)%Qp true ∗ ic_pin_tx k)).
  Proof.
    rewrite /ic_hdr_held_amb /ic_pay_held /ic_rest_amb.
    iIntros "(Hv & Hid & Hnl & Hpay) (Hm & Ha)". iFrame "Hid Hv Hnl Hm Ha". iExact "Hpay".
  Qed.

End IcacheBoxAmb.

(* ====================================================================== *)
(*  The instantiation                                                      *)
(* ====================================================================== *)
Section IcacheBox.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !irefslotG Σ}.
  Context `{GEN : GenId} `{ICFG : icfg}.
  (* the ambient context for the HOLDER-side rows (inode_ref / inode_shr /
     the handle's identity cells); the box λs below take an explicit ξ *)
  Context `{XI : CurCtx}.

  Implicit Types (cn : ic_names).

  (* the box λs: the ambient bundle at an explicit context *)
  Definition ic_hdr cn (γfs : fs_names) (γi : gname) (cov : gset Z) (logstart : Z)
      (k : nat) (i : ic_bid) (x : ic_x) (ξ : CtxId) : iProp Σ :=
    ic_hdr_amb (XI := ξ) cn γfs γi cov logstart k i x.
  Definition ic_rest (k : nat) (x : ic_x) (ξ : CtxId) : iProp Σ :=
    ic_rest_amb (XI := ξ) k x.

  (* ---- the client obligations (CtxBox's section Context) ------------ *)
  Global Instance ic_hdr_morph cn γfs γi cov logstart k i x : CtxMorph (ic_hdr cn γfs γi cov logstart k i x).
  Proof.
    rewrite /ic_hdr /ic_hdr_amb /inode_ident.
    destruct i as [[dev inum]|].
    - apply ctx_morph_sep; [apply ctx_morph_word4|].
      apply ctx_morph_sep; [apply ctx_morph_sep; apply ctx_morph_word4|].
      apply ctx_morph_sep; [| apply ctx_morph_sep; apply ctx_morph_const].
      destruct x; [apply ctx_morph_exist => n; apply ctx_morph_word2
                  | apply ctx_morph_exist => n; apply ctx_morph_word2
                  | apply ctx_morph_word2].
    - apply ctx_morph_sep; [apply ctx_morph_const|].
      apply ctx_morph_sep; [apply ctx_morph_exist => v; apply ctx_morph_word4|].
      apply ctx_morph_sep.
      + apply ctx_morph_exist => d. apply ctx_morph_exist => n. apply ctx_morph_sep; apply ctx_morph_word4.
      + apply ctx_morph_sep; [apply ctx_morph_exist => n; apply ctx_morph_word2|].
        apply ctx_morph_const.
  Qed.
  Global Instance ic_rest_morph k x : CtxMorph (ic_rest k x).
  Proof.
    rewrite /ic_rest /ic_rest_amb /ic_meta_rest /inode_addrs.
    destruct x as [|g|g dn bm].
    1,2: apply ctx_morph_sep;
         [apply ctx_morph_exist => d; apply ctx_morph_sep; [apply ctx_morph_word2|];
          apply ctx_morph_sep; [apply ctx_morph_word2|]; apply ctx_morph_sep; [apply ctx_morph_word2 | apply ctx_morph_word4]
         | apply ctx_morph_exist => l; apply ctx_morph_sep; [apply ctx_morph_const|];
           apply ctx_morph_big_sepL; intros j a; apply ctx_morph_word4].
    apply ctx_morph_sep; [apply ctx_morph_const|].
    apply ctx_morph_sep;
      [apply ctx_morph_sep; [apply ctx_morph_word2|]; apply ctx_morph_sep; [apply ctx_morph_word2|];
       apply ctx_morph_sep; [apply ctx_morph_word2 | apply ctx_morph_word4]
      | apply ctx_morph_big_sepL; intros j a; apply ctx_morph_word4].
  Qed.
  Global Instance ic_hdr_timeless cn γfs γi cov logstart k i x ξ : Timeless (ic_hdr cn γfs γi cov logstart k i x ξ).
  Proof. rewrite /ic_hdr. apply ic_hdr_amb_timeless. Qed.
  (* the held header as a box λ (P_hdr' of (e′)/(f′)), by arm kind *)
  Definition ic_hdr_held cn (γfs : fs_names) (γi : gname) (cov : gset Z) (logstart : Z)
      (k : nat) (rd : bool) (i : ic_bid) (x : ic_x) (ξ : CtxId) : iProp Σ :=
    ic_hdr_held_amb (XI := ξ) cn γfs γi cov logstart k rd i x.
  Global Instance ic_hdr_held_morph cn γfs γi cov logstart k rd i x : CtxMorph (ic_hdr_held cn γfs γi cov logstart k rd i x).
  Proof.
    destruct i as [[dev inum]|]; [| exact (ic_hdr_morph cn γfs γi cov logstart k None x)].
    rewrite /ic_hdr_held /ic_hdr_held_amb /inode_ident.
    apply ctx_morph_sep; [apply ctx_morph_word4|].
    apply ctx_morph_sep; [apply ctx_morph_sep; apply ctx_morph_word4|].
    apply ctx_morph_sep; [| apply ctx_morph_const].
    destruct x; [apply ctx_morph_exist => n; apply ctx_morph_word2
                | apply ctx_morph_exist => n; apply ctx_morph_word2
                | apply ctx_morph_word2].
  Qed.
  Global Instance ic_hdr_held_timeless cn γfs γi cov logstart k rd i x ξ : Timeless (ic_hdr_held cn γfs γi cov logstart k rd i x ξ).
  Proof. rewrite /ic_hdr_held. apply ic_hdr_held_amb_timeless. Qed.
  (* the read arm's split wand needs the reader's slice and two persistent
     facts INSIDE the box's fupd; they ride the caller residue Qc *)
  Global Instance ic_rest_timeless k x ξ : Timeless (ic_rest k x ξ).
  Proof. rewrite /ic_rest. apply ic_rest_amb_timeless. Qed.
  Lemma ic_hdr_excl cn γfs γi cov logstart k : forall (i i' : ic_bid) (x x' : ic_x) (ξ ξ' : CtxId),
    ic_hdr cn γfs γi cov logstart k i x ξ -∗ ic_hdr cn γfs γi cov logstart k i' x' ξ' -∗ False.
  Proof.
    iIntros (i i' x x' ξ ξ') "H1 H2".
    iAssert (∃ w : mword 32, ctx_word4_pointsto ξ (i_valid (ientry k)) (DfracOwn 1) w)%I
      with "[H1]" as (w1) "H1".
    { rewrite /ic_hdr /ic_hdr_amb. destruct i as [[dev inum]|].
      - iDestruct "H1" as "(Hv & _)". iExists _. iExact "Hv".
      - iDestruct "H1" as "(_ & Hv & _)". iExact "Hv". }
    iAssert (∃ w : mword 32, ctx_word4_pointsto ξ' (i_valid (ientry k)) (DfracOwn 1) w)%I
      with "[H2]" as (w2) "H2".
    { rewrite /ic_hdr /ic_hdr_amb. destruct i' as [[dev inum]|].
      - iDestruct "H2" as "(Hv & _)". iExists _. iExact "Hv".
      - iDestruct "H2" as "(_ & Hv & _)". iExact "Hv". }
    iApply (ctx_word4_excl_x with "H1 H2").
  Qed.
  Lemma ic_rest_excl k : forall (x x' : ic_x) (ξ ξ' : CtxId),
    ic_rest k x ξ -∗ ic_rest k x' ξ' -∗ False.
  Proof.
    iIntros (x x' ξ ξ') "H1 H2".
    iAssert (∃ w : mword 32, ctx_word4_pointsto ξ (i_size (ientry k)) (DfracOwn 1) w)%I
      with "[H1]" as (w1) "H1".
    { rewrite /ic_rest /ic_rest_amb /ic_meta_rest. destruct x.
      1,2: iDestruct "H1" as "[(%d & _ & _ & _ & Hs) _]"; iExists _; iExact "Hs".
      iDestruct "H1" as "(_ & (_ & _ & _ & Hs) & _)". iExists _. iExact "Hs". }
    iAssert (∃ w : mword 32, ctx_word4_pointsto ξ' (i_size (ientry k)) (DfracOwn 1) w)%I
      with "[H2]" as (w2) "H2".
    { rewrite /ic_rest /ic_rest_amb /ic_meta_rest. destruct x'.
      1,2: iDestruct "H2" as "[(%d & _ & _ & _ & Hs) _]"; iExists _; iExact "Hs".
      iDestruct "H2" as "(_ & (_ & _ & _ & Hs) & _)". iExists _. iExact "Hs". }
    iApply (ctx_word4_excl_x with "H1 H2").
  Qed.
  Lemma ic_tok_excl cn k : ic_tok cn k -∗ ic_tok cn k -∗ False.
  Proof. apply ic_tok_exclusive. Qed.

  (* THE STITCH'S Q -- main's durable-disk ghost that rides the box while a
     slot is checked out under ip->lock: the arm's half of the descriptor
     variable and, per descriptor, what main's OUT arm kept beside it: the
     parked [ln_tx] share of a write checkout ([ic_dep_side]), the reader's
     three quarters at [DepRd] ([ic_out_rd]), and the free path's freeze
     content at [DepFrz] (the count fragment, the selector's quarter, the
     window's [(t, qt)] share -- main's [ic_out_frz] minus its cells, which
     are the box's).  All ξ-free. *)
  Definition ic_q_side (γfs : fs_names) (γi : gname) (cov : gset Z) (logstart : Z)
      (k : nat) (d : ic_dep) : iProp Σ :=
    match d with
    | DepTx _ _ _ _ _ t q => tx_pin icfg_log t q
    | DepRd _ _ inum _ _ => ic_rd_arm γfs γi cov logstart inum
    | DepFrz qf dev inum t qt =>
        (iref_frag k qf ∗ frzsel k ((1/2)/2)%Qp true ∗ tx_pin icfg_log t qt)%I
    | _ => False%I
    end.
  (* every credential-bearing descriptor names its identity; [DepFrz] too
     (the free path's OUT_L2 hold is at the slot's identity, (g)) *)
  Definition ic_dep_id (d : ic_dep) : ic_bid :=
    match d with
    | DepTx _ dev inum _ _ _ _ | DepRd _ dev inum _ _ | DepFrz _ dev inum _ _ => Some (dev, inum)
    | DepNone => None
    end.
  (* iget's RECYCLE window (OUT_L1 at c = 0) parks THIS: a FALSE identity
     quarter, so the collection's partition (r21) reads the slot dead while
     its header is out (endgame F38/F44 -- the viewer's obligation is over
     every state the rows admit, and {OUT_L1, c = 0, live pool entry} is
     one; the quarter refutes it against the pool's true quarter).  The
     recycler supplies it from the table's half at (a) -- the dead row's
     [islot_empty] holds 1/2 -- and gets it back at (b′) BEFORE the
     identification flip, which needs table 1/2 + header 1/4 + pool 1/4 in
     one hand ([ic_id_quarters_join]). *)
  Definition ic_q_recycle cn (k : nat) : iProp Σ :=
    (∃ dev inum : mword 32, ic_id cn k (1/4) false dev inum)%I.
  (* Q1: THE OUT_L1 RESIDUE BY COUNT (the second CtxBox edit, endgame
     §6¹²–§6¹⁸).  c = 0 is the recycler's window, c ≥ 1 iput's ref == 1
     GUARD -- main's [ic_held] pin, the [ln_tx] share the commit refutes.
     Indexed by the count so each returner ((b)/(b′)/(g)) gets exactly its
     own residue back and selects nothing (F41). *)
  Definition ic_q1 cn (k : nat) (c : nat) : iProp Σ :=
    match c with
    | O => ic_q_recycle cn k
    | S _ => ic_pin_tx k
    end.
  (* Q2: THE OUT_L2 RESIDUE (F40).  The descriptor's half, its side share
     ([ic_q_side]) and -- the tie -- the header's identification quarter at
     the identity the descriptor names, moved here by (e′)'s split wand and
     back by (f′)'s join wand; the parker selects by descriptor agreement
     (F43's Qc'), the viewer reads DepRd with the identity tied to the pool's
     quarter and refutes DepTx/DepFrz by their shares. *)
  Definition ic_q2 cn (γfs : fs_names) (γi : gname) (cov : gset Z) (logstart : Z)
      (k : nat) : iProp Σ :=
    (∃ (d : ic_dep) (dev inum : mword 32),
       ⌜ic_dep_id d = Some (dev, inum)⌝ ∗
       ic_deposit cn k d ∗ ic_q_side γfs γi cov logstart k d ∗
       ic_id cn k (1/4) true dev inum)%I.
  Local Ltac tl_struct :=
    lazymatch goal with
    | |- Timeless (bi_exist _) => apply bi.exist_timeless; intro; tl_struct
    | |- Timeless (bi_sep _ _) => apply bi.sep_timeless; [tl_struct | tl_struct]
    | |- Timeless (bi_or _ _)  => apply bi.or_timeless;  [tl_struct | tl_struct]
    | |- Timeless (bi_pure _)  => apply bi.pure_timeless
    | |- _ => apply _
    end.
  Global Instance ic_q_side_timeless γfs γi cov logstart k d :
    Timeless (ic_q_side γfs γi cov logstart k d).
  Proof. rewrite /ic_q_side. destruct d; tl_struct. Qed.
  Global Instance ic_q_recycle_timeless cn k : Timeless (ic_q_recycle cn k).
  Proof. rewrite /ic_q_recycle. tl_struct. Qed.
  Global Instance ic_q1_timeless cn k c : Timeless (ic_q1 cn k c).
  Proof. rewrite /ic_q1. destruct c; apply _. Qed.
  Global Instance ic_q2_timeless cn γfs γi cov logstart k :
    Timeless (ic_q2 cn γfs γi cov logstart k).
  Proof. rewrite /ic_q2. tl_struct. Qed.
  Lemma ic_q1_0 cn k : ic_q1 cn k 0%nat = ic_q_recycle cn k.
  Proof. reflexivity. Qed.
  Lemma ic_q1_S cn k c : ic_q1 cn k (S c) = ic_pin_tx k.
  Proof. reflexivity. Qed.
  Lemma ic_q2_intro cn γfs γi cov logstart k d dev inum :
    ic_dep_id d = Some (dev, inum) ->
    ic_deposit cn k d -∗ ic_q_side γfs γi cov logstart k d -∗ ic_id cn k (1/4) true dev inum -∗
    ic_q2 cn γfs γi cov logstart k.
  Proof. iIntros (Hid) "Hd Hs Hq". rewrite /ic_q2. iExists d, dev, inum. iFrame. done. Qed.
  (* THE BOX, per slot: Q1 := ic_q1 (by count), Q2 := ic_q2 (the stitch) *)
  Definition ic_box cn (γfs : fs_names) (γi : gname) (cov : gset Z) (logstart : Z)
      (k : nat) : iProp Σ :=
    is_box (ic_hdr cn γfs γi cov logstart k) (ic_rest k) (ic_q1 cn k) (ic_q2 cn γfs γi cov logstart k)
           (icBoxN .@ k) (icfg_box k).
  Definition ic_boxes_all cn γfs γi cov logstart : iProp Σ :=
    ([∗ list] k ∈ seq 0 NINODE, ic_box cn γfs γi cov logstart k)%I.

  (* ---- registers, named per slot ------------------------------------- *)
  Definition ic_cnt k (c : nat) : iProp Σ := cnt_half (X := ic_x) (icfg_box k) c.
  Definition ic_regd k (r : slot_reg ic_bid ic_x) : iProp Σ := slotd_half (icfg_box k) r.
  Definition ic_regp k (s : l2_reg ic_bid) : iProp Σ := slotp_half (X := ic_x) (icfg_box k) s.

  (* ---- the reference rows (M-5) live in IcacheRef now: inode_ref /
     inode_shr / inode_ref_short carry [ic_ref_stamps] / [ic_lent_stamps]
     (the skeleton's inode_ref2 / inode_shr2 / inode_ref_lent2 and their
     carve / gather are IcacheRef.inode_ref_carve / inode_ref_gather). --- *)

  (* ---- the holder's handle row (M-4, F7's tool, R-1) ----------------- *)
  (* F21: the parked fragment is ANY map of the descriptor's mass -- a unit
     gathered from shares that parked at different stamps has several keys
     and may legitimately be checked out.  The MASS is pinned by the pure
     row (all (d) needs: R-1's reason); the KEYS are recovered at (f) by
     agreement on the register, which records the exact map. *)
  Definition ic_hold k (dev inum : mword 32) (μ : Qp) : iProp Σ :=
    (∃ m : gmap (ic_bid * nat) ufrac,
       ⌜qsum m = Qp_to_Qc μ⌝ ∗
       CtxBox.l2_hold (X := ic_x) (icfg_box k) (Some (dev, inum)) m)%I.
  (* what the holder has IN HAND of its share / reference once acquiresleep
     has deposited slh_tok into the tracked lock (F15): the identity cells
     and the liveness slice, plus the count fragment for a whole reference
     (F16).  DepFrz dies (the receipt is a payload-arm alternative). *)
  Definition ic_body (k : nat) (d : ic_dep) : iProp Σ :=
    match d with
    | DepTx s dev inum g lo _ _ | DepRd s dev inum g lo =>
        (inode_ident k (DfracOwn s) dev inum ∗ live_genlo k s g lo)%I
    | _ => False%I
    end.
  (* the stamps mass the descriptor's holder parked: a share its fraction
     (M-5), a whole reference 1 *)
  Definition ic_dep_mass (d : ic_dep) : Qp :=
    match d with DepTx s _ _ _ _ _ _ | DepRd s _ _ _ _ => s | _ => 1%Qp end.
  (* [ic_deposit cn k d] REDEFINED (name and arity kept for its opaque
     sites): the parked-fragment register half at the holder's singleton --
     keys and mass pinned (R-1) -- and the holder's body.  The sleeplock
     holder carries this and nothing else of the box's across its hold. *)
  Definition ic_deposit2 (k : nat) (d : ic_dep) : iProp Σ :=
    match ic_dep_id d with
    | Some (dev, inum) => (ic_hold k dev inum (ic_dep_mass d) ∗ ic_body k d)%I
    | None => False%I
    end.

  (* ---- THE ESCROW IS THE BOX (R3.3) --------------------------------- *)
  (* name and arity kept for the ~70 files that take them opaquely *)
  Definition ic_escrow cn (γfs : fs_names) (γi : gname) (cov : gset Z) (logstart : Z)
      (k : nat) : iProp Σ :=
    ic_box cn γfs γi cov logstart k.
  Definition ic_escrows cn (γfs : fs_names) (γi : gname) (cov : gset Z) (logstart : Z) : iProp Σ :=
    ic_boxes_all cn γfs γi cov logstart.
  Global Instance ic_escrow_persistent cn γfs γi cov logstart k :
    Persistent (ic_escrow cn γfs γi cov logstart k).
  Proof. rewrite /ic_escrow /ic_box. apply _. Qed.
  Global Instance ic_escrows_persistent cn γfs γi cov logstart :
    Persistent (ic_escrows cn γfs γi cov logstart).
  Proof. rewrite /ic_escrows /ic_boxes_all. apply _. Qed.
  (* the holder's handle row under its old name (M-4/F7: 21 opaque sites).
     F27: (e) hands the holder P_hdr WHOLE, and the payload ghost's liveness
     half [live_gen k ½ g] is the one piece of it no spec row of ilock's
     post / iunlock's pre names (the cells, ic_loaded, ity_shot and
     ifreeze_off are all rows there) -- so across a SHARE's hold it rides
     the handle row, beside the skeleton's [ic_deposit2] (whose body is what
     (e) takes in and (f) hands back), where the spec boundary already
     carries it opaquely. *)
  Definition ic_pay_live (k : nat) (d : ic_dep) : iProp Σ :=
    match d with DepTx _ _ _ g _ _ _ | DepRd _ _ _ g _ => live_gen k (1/2) g | _ => emp%I end.
  (* THE STITCH: the holder's HANDLE across its checkout -- flip's
     [ic_deposit2] (the parked-fragment register half and the body) and
     [ic_pay_live], PLUS main's half of the descriptor variable
     ([ic_deposit cn k d], which keeps main's name and meaning: the ghost
     half whose agreement at the park hands back exactly the [(t, q)] share
     the checkout parked).  Flip's inode proofs spell the handle
     [ic_deposit cn k d]; on this branch that is [ic_handle]. *)
  Definition ic_handle (cn : ic_names) (k : nat) (d : ic_dep) : iProp Σ :=
    (ic_deposit2 k d ∗ ic_pay_live k d ∗ ic_deposit cn k d ∗
     (* ...AND THE SLEEPLOCK'S TOKEN [ic_tok], which rides the L2 payload
        [ic_slp] while the lock is free: the holder takes it at acquiresleep
        and hands it back at releasesleep ([ic_slp_dep]); across the hold it
        lives HERE (main put it into the escrow arm at the checkout; the box
        has no token slot after the second edit). *)
     ic_tok cn k)%I.
  (* the descriptor's PURE projections at a share-bearing descriptor *)
  Lemma ic_dep_id_of_shr d (s : Qp) (dev inum : mword 32) (g : gname) (lo : nat) :
    ic_dep_shr d = Some (s, dev, inum, g, lo) -> ic_dep_id d = Some (dev, inum).
  Proof.
    rewrite /ic_dep_shr /ic_dep_id.
    destruct d; try discriminate; intros H; injection H as _ <- <- _ _; reflexivity.
  Qed.
  Lemma ic_dep_mass_of_shr d (s : Qp) (dev inum : mword 32) (g : gname) (lo : nat) :
    ic_dep_shr d = Some (s, dev, inum, g, lo) -> ic_dep_mass d = s.
  Proof.
    rewrite /ic_dep_shr /ic_dep_mass.
    destruct d; try discriminate; intros H; injection H as <- _ _ _ _; reflexivity.
  Qed.
  Lemma ic_pay_live_of_shr k d (s : Qp) (dev inum : mword 32) (g : gname) (lo : nat) :
    ic_dep_shr d = Some (s, dev, inum, g, lo) -> ic_pay_live k d = live_gen k (1/2) g.
  Proof.
    rewrite /ic_dep_shr /ic_pay_live.
    destruct d; try discriminate; intros H; injection H as _ _ _ <- _; reflexivity.
  Qed.
  Lemma ic_body_of_shr k d (s : Qp) (dev inum : mword 32) (g : gname) (lo : nat) :
    ic_dep_shr d = Some (s, dev, inum, g, lo) ->
    ic_body k d = (inode_ident k (DfracOwn s) dev inum ∗ live_genlo k s g lo)%I.
  Proof.
    rewrite /ic_dep_shr /ic_body.
    destruct d; try discriminate; intros H; injection H as <- <- <- <- <-; reflexivity.
  Qed.

  (* ---- THE TRANSACTION-DEPOSIT BUNDLE (main's durable-disk B''-tx3), over
     the handle: moved here from the first section because it names
     [ic_handle]. ---- *)

  (* ------------------------------------------------------------------ *)
  (*  THE FREE PATH's FROZEN PARK (iclaim-ledger.md §3.16, RULING A⁗)     *)
  (* ------------------------------------------------------------------ *)

  (* (d') THE MID-FREE PARK, and the re-open the +0x70 store needs.

     Between iput's window exit at +0x5e and its last close at +0x8a the
     escrow sits on [ic_parked]'s FROZEN alternative: the cells, the recycle
     token, the identification ghost and the freeze RECEIPT -- no payload, no
     liveness half, no deposit.  That is what lets the freer

       * carry [dinode_at], the block resources and [inode_raw] in its own
         hand across [itrunc], the [ip->type = 0] store and [releasesleep]
         (B2 dissolved), and
       * leave the arm's liveness half and its own reference slice parked in
         [islot2]'s FROZEN PARK for the whole lock-free span (OPEN(2.6b)
         closed),

     and it costs the escrow's five-arm shape nothing: the alternative lives
     inside [ic_payload_arm], where the token slot's disjunction already was.

     THE ARM IS DECIDED BY [ifreeze_pre] AT EVERY READER, which is why the
     freer keeps that fragment in hand from the mint at +0x50 to the close at
     +0x8a and parks the receipt instead. *)

  (* ...and its opener.  The freer identifies the arm by the identity slice it
     kept when the window exit split [i_inum] three ways (its own [q], the
     arm's ½ and the table's ½ − q), refutes OUT with the sleeplock's own
     token, MID/HELD/EMPTY with the cells, and [ic_parked]'s ORDINARY
     alternative with the [ifreeze_pre] in its hand. *)

  (* (e) THE RECYCLER'S RE-OPEN AT ITS VALID STORE (iget, +0x7c)
     (BioInv.escrow_open_mid).

     Its recycle token refutes BOTH normal arms, so the body is the window
     it parked; the reclose is at a normal parked arm, which re-absorbs the
     token.  The valid cell comes out for the physical [sw zero,64(s3)], and
     the inum cell comes out FULL so that the closer can split ½ back to the
     table and leave ½ in the arm. *)

  Definition ic_tx_dep (cn : ic_names) (k : nat) (s : Qp)
      (dev inum : mword 32) (g : gname) (lo : nat) : iProp Σ :=
    (* THE STITCH: the holder's HANDLE ([ic_handle]: the box register half,
       the body, main's descriptor half) beside the transaction share -- what
       a write checkout leaves in the caller's hand *)
    (∃ t : nat, ic_handle cn k (DepTx s dev inum g lo t (1/2))
                ∗ t ↪[ln_tx icfg_log]{#(1/2)} tt)%I.

  Global Instance ic_tx_dep_timeless cn k s dev inum g lo :
    Timeless (ic_tx_dep cn k s dev inum g lo).
  Proof. rewrite /ic_tx_dep. tl_struct. Qed.

  Lemma ic_tx_dep_intro cn k s dev inum g lo (t : nat) :
    ic_handle cn k (DepTx s dev inum g lo t (1/2)) -∗
    t ↪[ln_tx icfg_log]{#(1/2)} tt -∗
    ic_tx_dep cn k s dev inum g lo.
  Proof. iIntros "Hd Ht". iExists t. iFrame. Qed.

  (* ------------------------------------------------------------------ *)
  (*  4c-2.  TWO SLOTS AT ONE TRANSACTION (durable-disk B''-tx2)          *)
  (* ------------------------------------------------------------------ *)

  (* WHY A SECOND SHAPE AT ALL.  [ic_tx_dep]'s invariant is "the arm holds
     [q] and the holder holds [q] beside it", which forces [q = 1/2] for the
     two to rejoin into the whole element [LogInv.log_tx] closes -- so TWO of
     them at one transaction claim 2 and the pair is UNSATISFIABLE, a premise
     nobody can discharge.  [create] (parent + fresh child) and [sys_unlink]
     ([dp] + [ip]) each hold two write locks at once, so each needs the arms
     at a QUARTER: two arms of 1/4 and a residue of 1/2 rejoin to 1 exactly
     as one arm of 1/2 and a residue of 1/2 do.

     THE ID IS NAMED HERE and closed existentially only at a boundary.  Two
     arms of one transaction must be at the SAME [t] -- shares at different
     ghost-map keys never rejoin into a whole element -- and nothing about
     the escrow determines an id, so a walk that holds two locks binds [t]
     in its stage statement and
     spells each conjunct at [ic_tx_dep_at]'s own arity.  That is what keeps
     the sweep POSITION-STABLE: a stage's bare [ic_deposit cn k d]
     becomes [ic_tx_dep_at cn k .. t (1/4)] in place, its [log_tx g] (or its
     whole [log_op g u], which becomes [log_opb g u]) loses the residue the
     two [ic_tx_dep_at]s now carry, and only ONE binder is added. *)
  Definition ic_tx_dep_at (cn : ic_names) (k : nat) (s : Qp)
      (dev inum : mword 32) (g : gname) (lo : nat) (t : nat) (q : Qp) : iProp Σ :=
    (ic_handle cn k (DepTx s dev inum g lo t q)
     ∗ t ↪[ln_tx icfg_log]{#q} tt)%I.

  Global Instance ic_tx_dep_at_timeless cn k s dev inum g lo t q :
    Timeless (ic_tx_dep_at cn k s dev inum g lo t q).
  Proof. rewrite /ic_tx_dep_at. tl_struct. Qed.


  Lemma ic_tx_dep_at_of_half cn k s dev inum g lo :
    ic_tx_dep cn k s dev inum g lo -∗
    ∃ t : nat, ic_tx_dep_at cn k s dev inum g lo t (1/2).
  Proof.
    rewrite /ic_tx_dep /ic_tx_dep_at. iIntros "H".
    iDestruct "H" as (t) "[Hd Ht]". iExists t. iFrame.
  Qed.

  (* the element's own splitting, spelled once: a [ghost_map] element at
     [#(q1 + q2)] IS the two, by the library's [Fractional] instance. *)
  Local Lemma ic_tx_share_split (t : nat) (q q1 q2 : Qp) :
    q = (q1 + q2)%Qp ->
    t ↪[ln_tx icfg_log]{#q} tt -∗
    t ↪[ln_tx icfg_log]{#q1} tt ∗ t ↪[ln_tx icfg_log]{#q2} tt.
  Proof. intros ->. iIntros "H". iDestruct "H" as "[$ $]". Qed.

  Local Lemma ic_tx_share_join (t : nat) (q q1 q2 : Qp) :
    q = (q1 + q2)%Qp ->
    t ↪[ln_tx icfg_log]{#q1} tt -∗ t ↪[ln_tx icfg_log]{#q2} tt -∗
    t ↪[ln_tx icfg_log]{#q} tt.
  Proof.
    intros ->. iIntros "H1 H2".
    iDestruct (ghost_map_elem_combine with "H1 H2") as "[H _]".
    rewrite dfrac_op_own. iExact "H".
  Qed.

  (* ---- the two payload rows (M-6) ------------------------------------ *)
  (* L2: the inode sleeplock's λ payload -- CtxBox.l2_row at ic_tok *)
  Definition ic_slp cn k : CtxId -> iProp Σ :=
    fun ξ => (∃ s : l2_reg ic_bid,
      CtxBox.l2_row (X := ic_x) (icfg_box k) s ξ ∗
      ic_tok cn k ∗ ic_dep_neutral cn k)%I.
  Global Instance ic_slp_morph cn k : CtxMorph (ic_slp cn k).
  Proof.
    rewrite /ic_slp. apply ctx_morph_exist => s.
    apply ctx_morph_sep; [apply _ |].
    apply ctx_morph_sep; apply ctx_morph_const.
  Qed.
  (* the releaser's UNFLOORED row at a known park stamp (R2's Rdep, the
     bcache's bslp_dep): what (f) leaves in hand; the _in release re-floors
     it at the parked context through the fold *)
  Definition ic_slp_dep cn k (T' : nat) : iProp Σ :=
    (ic_tok cn k ∗ ic_regp k (L2Reg T' None) ∗ ic_dep_neutral cn k)%I.
  Lemma ic_slp_fold cn k T' (ξ : CtxId) :
    ic_slp_dep cn k T' ∗ ctx_floor ξ T' ⊢ ic_slp cn k ξ.
  Proof.
    iIntros "[(Ht & Hrp & Hn) #Hfl]". rewrite /ic_slp. iExists (L2Reg T' None).
    rewrite /CtxBox.l2_row /ic_regp. iFrame "Ht Hrp Hn". iSplitR; [done |]. iExact "Hfl".
  Qed.
  Global Instance ic_slp_dep_morph cn k T' : CtxMorph (fun _ => ic_slp_dep cn k T').
  Proof. apply ctx_morph_const. Qed.
  (* L1: the slot's row in itable_res2 -- the register half, shut and
     empty, IDENTITY = the table's ci !! k (None when unidentified: M-1'),
     bounded by the payload's floor slot [tl] *)
  Definition ic_slot_row k (oi : ic_bid) (c : nat) (tl : nat) : iProp Σ :=
    (∃ r : slot_reg ic_bid ic_x,
       ic_regd k r ∗ ⌜sr_win r = false⌝ ∗ ⌜sr_x r = None⌝ ∗ ⌜sr_ident r = oi⌝ ∗
       llb loglen_name (sr_td r) ∗ ⌜(sr_td r ≤ tl)%nat⌝ ∗
       ic_cnt k c)%I.
  (* F17: [c] is M !! k's count (0 at None).  The table's DEAD row keeps
     today's [islot_free_at k dev inum] -- the identity halves complementary
     to the dead header's, which the recycler joins for its stores; the
     map's deletion of islot_free is withdrawn. *)

  (* ====================================================================== *)
  (*  THE SITES (R3's map), as statements over CtxBox's six lemmas            *)
  (* ====================================================================== *)

  (* iget's RECYCLE, part 1 -- (a) at c = 0 on a DEAD slot: the raw header
     comes out, its shape known from the identity (M-1'). *)
  Lemma ic_recycle_withdraw `{CID : RiscvLang.CpuId} cn γfs γi cov logstart (k : nat)
      (ξ : CtxId) (r : slot_reg ic_bid ic_x) (Kd : nat) (E : coPset) :
    ↑icBoxN ⊆ E ->
    sr_win r = false -> sr_ident r = None -> (sr_td r <= Kd)%nat ->
    ic_box cn γfs γi cov logstart k -∗
    own_context ξ -∗ ctx_floor ξ Kd -∗
    ic_regd k r -∗ ic_cnt k 0 -∗ ic_q_recycle cn k ={E}=∗
    own_context ξ ∗ ic_cnt k 0 ∗
    ∃ T0 : nat, ⌜(T0 <= Kd)%nat⌝ ∗
      ic_regd k (SlotReg (sr_td r) true None (Some (IcRaw, T0))) ∗
      ic_hdr cn γfs γi cov logstart k None IcRaw ξ.
  Proof.
    iIntros (HE Hw Hid HKd) "#Hbox Hrun #Hfl Hrd Hc Hqr".
    assert (HEk : ↑(icBoxN .@ k) ⊆ E) by (etrans; [apply nclose_subseteq | exact HE]).
    iMod (own_unit (authUR (gmapUR (ic_bid * nat) ufracR)) (bx_stamps (icfg_box k))) as "Hf0".
    assert (Hq0 : qsum (∅ : gmap (ic_bid * nat) ufrac) = nat_Qc 0).
    { rewrite /qsum map_fold_empty /nat_Qc /=. symmetry. apply Z2Qc_inj_0. }
    assert (Hm0 : (max_stamp (∅ : gmap (ic_bid * nat) ufrac) <= 0)%nat).
    { rewrite /max_stamp map_fold_empty. lia. }
    iMod (CtxBox.box_withdraw_L1 (ic_hdr cn γfs γi cov logstart k) (ic_rest k) (ic_q1 cn k) (ic_q2 cn γfs γi cov logstart k)
            (icBoxN .@ k) (icfg_box k) ξ r 0 ∅ Kd 0 E HEk Hw Hq0 HKd Hm0
            with "Hbox Hrun Hfl [] [] Hrd Hc [Hf0] [Hqr]") as "(Hrun & Hc & Hout)".
    { iApply ctx_floor_0. }
    { rewrite /max_stamp map_fold_empty. iApply TsoGhost.llb_0. }
    { rewrite /stamps_frag. iExact "Hf0". }
    { rewrite ic_q1_0. iExact "Hqr". }
    iDestruct "Hout" as (x0 T0) "(%HT0 & Hrd & Hhdr)". rewrite Hid.
    iDestruct (ic_hdr_dead_raw (XI := ξ) cn γfs γi cov logstart k x0 with "Hhdr") as %Hx0. subst x0.
    iModIntro. iFrame "Hrun Hc". iExists T0. iFrame "Hrd Hhdr". iPureIntro. lia.
  Qed.

  (* iget's RECYCLE, part 2 -- (b') at c = 0 with the bump (F14: x0 = IcRaw,
     x1 = IcUnloaded g, entailment ic_rest_raw_unloaded): the header
     re-deposited at the NEW identity, UNLOADED at a fresh generation (the
     pool's bundle for inum taken under itable.lock, [live_slot_alloc]'s
     half and pending); the new reference is a unit at the deposit stamp. *)
  Lemma ic_recycle_deposit `{CID : RiscvLang.CpuId} cn γfs γi cov logstart (k : nat)
      (ξ : CtxId) (r : slot_reg ic_bid ic_x) (dev inum : mword 32) (g : gname) (T0 : nat) (E : coPset) :
    ↑icBoxN ⊆ E ->
    sr_win r = true -> sr_x r = Some (IcRaw, T0) ->
    ic_box cn γfs γi cov logstart k -∗
    own_context ξ -∗
    ic_regd k r -∗ ic_cnt k 0 -∗
    ic_hdr cn γfs γi cov logstart k (Some (dev, inum)) (IcUnloaded g) ξ ={E}=∗
    own_context ξ ∗ ic_q_recycle cn k ∗
    ∃ T' : nat,
      ic_regd k (SlotReg T' false (Some (dev, inum)) None) ∗
      ic_cnt k 1 ∗
      ic_ref_stamps k dev inum 1%Qp ∗
      llb loglen_name T'.
  Proof.
    iIntros (HE Hw Hx) "#Hbox Hrun Hrd Hc Hhdr".
    assert (HEk : ↑(icBoxN .@ k) ⊆ E) by (etrans; [apply nclose_subseteq | exact HE]).
    iMod (CtxBox.box_deposit_L1_shape (ic_hdr cn γfs γi cov logstart k) (ic_rest k) (ic_q1 cn k) (ic_q2 cn γfs γi cov logstart k)
            (icBoxN .@ k) (icfg_box k) ξ r 0 (Some (dev, inum)) IcRaw (IcUnloaded g) T0 E HEk Hw Hx
            ltac:(intros ξb; rewrite /ic_rest; simpl; reflexivity)
            with "Hbox Hrun Hrd Hc Hhdr") as "(Hrun & HQ & %T' & Hrd & Hc & Href & #Hllb)".
    rewrite ic_q1_0.
    iModIntro. iFrame "Hrun HQ". iExists T'. iFrame "Hrd Hllb".
    iSplitL "Hc"; [iExact "Hc"|].
    rewrite /ic_ref_stamps /ic_ref_stamps_at /ic_stamps. iExists _. iFrame "Href".
    iPureIntro. rewrite /qsum map_fold_singleton /qsum_step Qcplus_0_r.
    change (unit_mass 0) with 1%Qp. reflexivity.
  Qed.

  (* iget's HIT -- (c) at c ≥ 1 (xv6 matches only ref > 0 slots) *)
  Lemma ic_hit_incr cn γfs γi cov logstart (k : nat) (r : slot_reg ic_bid ic_x)
      (c : nat) (dev inum : mword 32) (E : coPset) :
    ↑icBoxN ⊆ E ->
    sr_win r = false -> sr_ident r = Some (dev, inum) ->
    ic_box cn γfs γi cov logstart k -∗
    ic_regd k r -∗ ic_cnt k (S c) ={E}=∗
    ic_regd k r ∗ ic_cnt k (S (S c)) ∗ ic_ref_stamps k dev inum 1%Qp.
  Proof.
    iIntros (HE Hw Hid) "#Hbox Hrd Hc".
    assert (HEk : ↑(icBoxN .@ k) ⊆ E) by (etrans; [apply nclose_subseteq | exact HE]).
    iMod (CtxBox.box_ref_incr (ic_hdr cn γfs γi cov logstart k) (ic_rest k) (ic_q1 cn k) (ic_q2 cn γfs γi cov logstart k)
            (icBoxN .@ k) (icfg_box k) r (S c) E HEk Hw with "Hbox Hrd Hc") as "(Hrd & Hc & %T & Href)".
    iModIntro. iFrame "Hrd Hc". iEval (rewrite Hid) in "Href".
    rewrite /ic_ref_stamps /ic_ref_stamps_at /ic_stamps. iExists _. iFrame "Href".
    iPureIntro. rewrite /qsum map_fold_singleton /qsum_step Qcplus_0_r. reflexivity.
  Qed.

  (* iput's ref-- -- (d): the unit's debt paid into the L1 register *)
  Lemma ic_decr cn γfs γi cov logstart (k : nat) (r : slot_reg ic_bid ic_x)
      (c : nat) (i : ic_bid) (E : coPset) :
    ↑icBoxN ⊆ E ->
    sr_win r = false ->
    ic_box cn γfs γi cov logstart k -∗
    ic_regd k r -∗ llb loglen_name (sr_td r) -∗ ic_cnt k (S c) -∗
    ic_ref_stamps_at k i 1%Qp ={E}=∗
    ∃ td' : nat, ⌜(sr_td r <= td')%nat⌝ ∗
      ic_regd k (SlotReg td' false (sr_ident r) (sr_x r)) ∗ ic_cnt k c ∗
      llb loglen_name td'.
  Proof.
    iIntros (HE Hw) "#Hbox Hrd #Hllb Hc Href". iDestruct "Href" as (m) "[%Hm Href]".
    assert (HEk : ↑(icBoxN .@ k) ⊆ E) by (etrans; [apply nclose_subseteq | exact HE]).
    assert (Hq : qsum m = nat_Qc 1) by (rewrite Hm Qp_to_Qc_1 nat_Qc_1; reflexivity).
    iMod (CtxBox.box_ref_decr (ic_hdr cn γfs γi cov logstart k) (ic_rest k) (ic_q1 cn k) (ic_q2 cn γfs γi cov logstart k)
            (icBoxN .@ k) (icfg_box k) r c i m E HEk Hw Hq with "Hbox Hrd Hllb Hc Href") as "(Hrd & Hc & #Hllb')".
    iModIntro. iExists (Nat.max (sr_td r) (max_stamp m)). iSplitR; [iPureIntro; lia|].
    iFrame "Hrd Hc Hllb'".
  Qed.

  (* the park's return by arm kind: the read arm's three quarters went home
     into the header, the others hand their side share back *)
  Definition ic_park_side (γfs : fs_names) (γi : gname) (cov : gset Z) (logstart : Z)
      (k : nat) (d : ic_dep) : iProp Σ :=
    match d with
    | DepRd _ _ _ _ _ => emp%I
    | _ => ic_q_side γfs γi cov logstart k d
    end.

  Lemma ic_dep_side_q_side γfs γi cov logstart k d (s : Qp) (dev inum : mword 32) (g : gname) (lo : nat) :
    ic_dep_shr d = Some (s, dev, inum, g, lo) -> ic_dep_rd d = false ->
    ic_dep_side d -∗ ic_q_side γfs γi cov logstart k d.
  Proof.
    rewrite /ic_q_side /ic_dep_side /ic_dep_side_tx /tx_pin_o /ic_dep_shr /ic_dep_rd.
    destruct d; try discriminate; intros _ _; iIntros "H"; iExact "H".
  Qed.
  Lemma ic_park_side_dep_side γfs γi cov logstart k d (s : Qp) (dev inum : mword 32) (g : gname) (lo : nat) :
    ic_dep_shr d = Some (s, dev, inum, g, lo) ->
    ic_park_side γfs γi cov logstart k d -∗ ic_dep_side d.
  Proof.
    rewrite /ic_park_side /ic_q_side /ic_dep_side /ic_dep_side_tx /tx_pin_o.
    destruct d; try discriminate; intros _; iIntros "H"; [iExact "H" | done].
  Qed.

  (* ilock's CHECKOUT at the WRITE arm (and any non-read descriptor) -- (e′)
     with the descriptor's holder body (F15: the share minus slh_tok; no
     whole-unit hold, F39).  R1 at the genl_llb acquiresleep presents the
     fragment's stamp; the L2 row's pieces come from the payload.  F40: the
     caller brings the descriptor half it minted ([ic_dep_checkout]) and the
     side share; the split wand moves them and the header's identification
     quarter into the OUT_L2 residue [ic_q2] and hands the HELD header back.
     Out: the held bundle at the identity (one binder over the shape), and
     the handle row [ic_deposit2 k d]. *)
  Lemma ic_checkout `{CID : RiscvLang.CpuId} cn γfs γi cov logstart (k : nat)
      (ξ : CtxId) (d : ic_dep) (dev inum : mword 32)
      (s0 : l2_reg ic_bid) (Kt Kp : nat) (E : coPset) :
    ↑icBoxN ⊆ E ->
    ic_dep_id d = Some (dev, inum) -> ic_dep_rd d = false ->
    lr_hold s0 = None -> (lr_tp s0 <= Kp)%nat ->
    ic_box cn γfs γi cov logstart k -∗
    own_context ξ -∗
    ctx_floor ξ Kt -∗ ctx_floor ξ Kp -∗
    ic_body k d -∗
    (* F21: any fragment of the descriptor's mass, its stamps covered by Kt
       (R1 at Tl := max_stamp m) -- what ic_ref_stamps / inode_shr2 give *)
    (∃ m : gmap (ic_bid * nat) ufrac,
       ⌜qsum m = Qp_to_Qc (ic_dep_mass d)⌝ ∗ ⌜(max_stamp m <= Kt)%nat⌝ ∗
       CtxBox.reference (X := ic_x) (icfg_box k) (Some (dev, inum)) m) -∗
    ic_deposit cn k d -∗ ic_q_side γfs γi cov logstart k d -∗
    ic_regp k s0 ={E}=∗
    own_context ξ ∗
    (∃ x : ic_x, ic_hdr_held cn γfs γi cov logstart k false (Some (dev, inum)) x ξ ∗ ic_rest k x ξ) ∗
    ic_deposit2 k d.
  Proof.
    iIntros (HE Hid Hrd Hs0 HKp) "#Hbox Hrun #Hflt #Hflp Hbody Href Hd Hs Hrp".
    assert (HEk : ↑(icBoxN .@ k) ⊆ E) by (etrans; [apply nclose_subseteq | exact HE]).
    iDestruct "Href" as (m) "(%Hm & %Hmt & Href)".
    assert (Hsplit : ∀ (x : ic_x) (ξ' : CtxId),
              (ic_deposit cn k d ∗ ic_q_side γfs γi cov logstart k d) ∗
              ic_hdr cn γfs γi cov logstart k (Some (dev, inum)) x ξ'
              ={E ∖ ↑(icBoxN .@ k)}=∗
              ic_hdr_held cn γfs γi cov logstart k false (Some (dev, inum)) x ξ' ∗
              ic_q2 cn γfs γi cov logstart k).
    { intros x ξ'. iIntros "[[Hd Hs] Hh]". iModIntro. rewrite /ic_hdr /ic_hdr_held.
      iDestruct (ic_hdr_amb_split (XI := ξ') with "Hh") as "[Hh Hq]". iFrame "Hh".
      iApply (ic_q2_intro _ _ _ _ _ _ d dev inum Hid with "Hd Hs Hq"). }
    iMod (CtxBox.box_checkout_split (ic_hdr cn γfs γi cov logstart k) (ic_rest k) (ic_q1 cn k) (ic_q2 cn γfs γi cov logstart k)
            (icBoxN .@ k) (icfg_box k) ξ (Some (dev, inum))
            (ic_hdr_held cn γfs γi cov logstart k false)
            (ic_deposit cn k d ∗ ic_q_side γfs γi cov logstart k d)%I
            m s0 Kt Kp E HEk Hs0 Hmt HKp Hsplit
            with "Hbox Hrun Hflt Hflp Href [$Hd $Hs] Hrp") as "(Hrun & Hbun & Hhold)".
    iModIntro. iFrame "Hrun". iSplitL "Hbun"; [iExact "Hbun"|].
    rewrite /ic_deposit2 Hid. iFrame "Hbody". rewrite /ic_hold. iExists m. iFrame "Hhold". done.
  Qed.

  (* ilock's CHECKOUT at the READ arm (fileread, filestat: a [ShotK]
     licence, no transaction).  The split is a view shift (§6²⁰): the
     reader's type one-shot refutes the unloaded shape, its live slice
     refutes the frozen alternative through [itable_inv], and the loaded
     payload sheds three quarters of the leg into [ic_q2] -- exactly main's
     [ic_swap_checkout_rd], inside the checkout's own ghost step.  The slice
     rides the caller residue in and the held bundle out. *)
  Definition ic_hdr_held_rd_sl cn (γfs : fs_names) (γi : gname) (cov : gset Z) (logstart : Z)
      (k : nat) (s : Qp) (g : gname) (lo : nat) (i : ic_bid) (x : ic_x) (ξ : CtxId) : iProp Σ :=
    (ic_hdr_held cn γfs γi cov logstart k true i x ξ ∗ live_genlo k s g lo)%I.
  Global Instance ic_hdr_held_rd_sl_morph cn γfs γi cov logstart k s g lo i x :
    CtxMorph (ic_hdr_held_rd_sl cn γfs γi cov logstart k s g lo i x).
  Proof. rewrite /ic_hdr_held_rd_sl. apply ctx_morph_sep; [apply _ | apply ctx_morph_const]. Qed.
  Lemma ic_checkout_rd `{CID : RiscvLang.CpuId} cn γfs γi cov logstart (k : nat)
      (ξ : CtxId) (s : Qp) (dev inum : mword 32) (g : gname) (lo : nat) (ty : bv 16)
      (s0 : l2_reg ic_bid) (Kt Kp : nat) (E : coPset) :
    ↑icBoxN ⊆ E -> ↑icacheN ⊆ E -> (k < NINODE)%nat ->
    lr_hold s0 = None -> (lr_tp s0 <= Kp)%nat ->
    ic_box cn γfs γi cov logstart k -∗
    own_context ξ -∗
    ctx_floor ξ Kt -∗ ctx_floor ξ Kp -∗
    itable_inv -∗ ity_shot g ty -∗
    ic_body k (DepRd s dev inum g lo) -∗
    (∃ m : gmap (ic_bid * nat) ufrac,
       ⌜qsum m = Qp_to_Qc s⌝ ∗ ⌜(max_stamp m <= Kt)%nat⌝ ∗
       CtxBox.reference (X := ic_x) (icfg_box k) (Some (dev, inum)) m) -∗
    ic_deposit cn k (DepRd s dev inum g lo) -∗
    ic_regp k s0 ={E}=∗
    own_context ξ ∗
    (∃ x : ic_x, ic_hdr_held cn γfs γi cov logstart k true (Some (dev, inum)) x ξ ∗ ic_rest k x ξ) ∗
    ic_deposit2 k (DepRd s dev inum g lo).
  Proof.
    iIntros (HE HEi Hk Hs0 HKp) "#Hbox Hrun #Hflt #Hflp #Hinv #Hshot Hbody Href Hd Hrp".
    assert (HEk : ↑(icBoxN .@ k) ⊆ E) by (etrans; [apply nclose_subseteq | exact HE]).
    assert (HEi' : ↑icacheN ⊆ E ∖ ↑(icBoxN .@ k)) by solve_ndisj.
    iDestruct "Href" as (m) "(%Hm & %Hmt & Href)".
    rewrite /ic_body. iDestruct "Hbody" as "[Hident Hlv]".
    assert (Hsplit : ∀ (x : ic_x) (ξ' : CtxId),
              (ic_deposit cn k (DepRd s dev inum g lo) ∗ live_genlo k s g lo ∗
               itable_inv ∗ ity_shot g ty) ∗
              ic_hdr cn γfs γi cov logstart k (Some (dev, inum)) x ξ'
              ={E ∖ ↑(icBoxN .@ k)}=∗
              ic_hdr_held_rd_sl cn γfs γi cov logstart k s g lo (Some (dev, inum)) x ξ' ∗
              ic_q2 cn γfs γi cov logstart k).
    { intros x ξ'. iIntros "[(Hd & Hlv & #Hinv' & #Hshot') Hh]".
      rewrite /ic_hdr /ic_hdr_held_rd_sl /ic_hdr_held.
      iMod (ic_hdr_amb_split_rd (XI := ξ') (E ∖ ↑(icBoxN .@ k)) cn γfs γi cov logstart k dev inum x s g lo ty HEi' Hk
              with "Hinv' Hshot' Hlv Hh") as "(Hh & Hq & Harm & Hlv)".
      iModIntro. iFrame "Hh Hlv".
      iApply (ic_q2_intro _ _ _ _ _ _ (DepRd s dev inum g lo) dev inum eq_refl with "Hd [Harm] Hq").
      rewrite /ic_q_side. iExact "Harm". }
    iMod (CtxBox.box_checkout_split (ic_hdr cn γfs γi cov logstart k) (ic_rest k) (ic_q1 cn k) (ic_q2 cn γfs γi cov logstart k)
            (icBoxN .@ k) (icfg_box k) ξ (Some (dev, inum))
            (ic_hdr_held_rd_sl cn γfs γi cov logstart k s g lo)
            (ic_deposit cn k (DepRd s dev inum g lo) ∗ live_genlo k s g lo ∗ itable_inv ∗ ity_shot g ty)%I
            m s0 Kt Kp E HEk Hs0 Hmt HKp Hsplit
            with "Hbox Hrun Hflt Hflp Href [$Hd $Hlv] Hrp") as "(Hrun & Hbun & Hhold)".
    { iFrame "Hinv Hshot". }
    iDestruct "Hbun" as (x) "[[Hh Hlv] Hrest]".
    iModIntro. iFrame "Hrun". iSplitL "Hh Hrest"; [iExists x; iFrame "Hh Hrest"|].
    rewrite /ic_deposit2 /ic_dep_id /ic_body. iFrame "Hident Hlv". rewrite /ic_hold. iExists m. iFrame "Hhold". done.
  Qed.

  (* iunlock's PARK -- (f′) with the parker's descriptor half as the caller
     residue (F43): the join agrees it with the arm's, rebuilds the header
     with the quarter out of [ic_q2] (and, at the read arm, the three
     quarters), and hands back the two halves and the side share; the halves
     rejoin to the NEUTRAL descriptor here ([ic_dep_park]), ready for
     releasesleep.  The parker names its shape x0 (it holds the bundle).
     Two forms: over the handle row [ic_deposit2] (the descriptor's mass),
     and over a bare hold at mass μ. *)
  Lemma ic_park_hold `{CID : RiscvLang.CpuId} cn γfs γi cov logstart (k : nat)
      (ξ : CtxId) (d : ic_dep) (dev inum : mword 32) (x0 : ic_x) (μ : Qp) (E : coPset) :
    ↑icBoxN ⊆ E ->
    ic_dep_id d = Some (dev, inum) ->
    ic_box cn γfs γi cov logstart k -∗
    own_context ξ -∗
    ic_hdr_held cn γfs γi cov logstart k (ic_dep_rd d) (Some (dev, inum)) x0 ξ -∗ ic_rest k x0 ξ -∗
    ic_deposit cn k d -∗
    ic_hold k dev inum μ ={E}=∗
    own_context ξ ∗ ic_dep_neutral cn k ∗ ic_park_side γfs γi cov logstart k d ∗
    ∃ T' : nat,
      ic_regp k (L2Reg T' None) ∗
      CtxBox.reference (X := ic_x) (icfg_box k) (Some (dev, inum))
        {[ (Some (dev, inum), T') := μ ]} ∗
      llb loglen_name T'.
  Proof.
    iIntros (HE Hid) "#Hbox Hrun Hhdr Hrest Hd Hhold".
    assert (HEk : ↑(icBoxN .@ k) ⊆ E) by (etrans; [apply nclose_subseteq | exact HE]).
    iDestruct "Hhold" as (m) "[%Hm Hhold]".
    assert (Hjoin : ∀ (x : ic_x) (ξ' : CtxId),
              ic_deposit cn k d ∗
              ic_hdr_held cn γfs γi cov logstart k (ic_dep_rd d) (Some (dev, inum)) x ξ' ∗
              ic_q2 cn γfs γi cov logstart k
              ⊢ ic_hdr cn γfs γi cov logstart k (Some (dev, inum)) x ξ' ∗
                (ic_deposit cn k d ∗ ic_deposit cn k d ∗ ic_park_side γfs γi cov logstart k d)).
    { intros x ξ'. iIntros "(Hd & Hh & HQ)". rewrite /ic_q2.
      iDestruct "HQ" as (d' dev' inum') "(%Hid' & Hd' & Hs & Hq)".
      iDestruct (ic_deposit_agree with "Hd Hd'") as %<-.
      rewrite Hid in Hid'. injection Hid' as <- <-.
      rewrite /ic_hdr /ic_hdr_held /ic_park_side.
      destruct d as [| qf dv nu t qt | s' dv nu g' lo' t q | s' dv nu g' lo']; [discriminate Hid | | |];
        cbn [ic_dep_id] in Hid; injection Hid as -> ->; cbn [ic_dep_rd].
      - iDestruct (ic_hdr_amb_join (XI := ξ') with "Hh Hq") as "Hh". iFrame.
      - iDestruct (ic_hdr_amb_join (XI := ξ') with "Hh Hq") as "Hh". iFrame.
      - iEval (rewrite /ic_q_side) in "Hs".
        iDestruct (ic_hdr_amb_join_rd (XI := ξ') with "Hh Hq Hs") as "Hh". iFrame. }
    iMod (CtxBox.box_park_join (ic_hdr cn γfs γi cov logstart k) (ic_rest k) (ic_q1 cn k) (ic_q2 cn γfs γi cov logstart k)
            (icBoxN .@ k) (icfg_box k) ξ (Some (dev, inum))
            (ic_hdr_held cn γfs γi cov logstart k (ic_dep_rd d)) (ic_deposit cn k d)
            (ic_deposit cn k d ∗ ic_deposit cn k d ∗ ic_park_side γfs γi cov logstart k d)%I
            m E HEk Hjoin
            with "Hbox Hrun [Hhdr Hrest] Hd Hhold")
      as "(Hrun & (Hd1 & Hd2 & Hs) & %T' & %q & %Hq & Hrp & Href & #Hllb)".
    { iExists x0. iFrame "Hhdr Hrest". }
    iMod (ic_dep_park with "Hd1 Hd2") as "[_ Hn]".
    assert (q = μ) as ->. { apply Qp.to_Qc_inj_iff. by rewrite Hq Hm. }
    iModIntro. iFrame "Hrun Hn Hs". iExists T'. iFrame "Hrp Href Hllb".
  Qed.
  Lemma ic_park `{CID : RiscvLang.CpuId} cn γfs γi cov logstart (k : nat)
      (ξ : CtxId) (d : ic_dep) (dev inum : mword 32) (x0 : ic_x) (E : coPset) :
    ↑icBoxN ⊆ E ->
    ic_dep_id d = Some (dev, inum) ->
    ic_box cn γfs γi cov logstart k -∗
    own_context ξ -∗
    ic_hdr_held cn γfs γi cov logstart k (ic_dep_rd d) (Some (dev, inum)) x0 ξ -∗ ic_rest k x0 ξ -∗
    ic_deposit cn k d -∗
    ic_deposit2 k d ={E}=∗
    own_context ξ ∗ ic_dep_neutral cn k ∗ ic_park_side γfs γi cov logstart k d ∗ ic_body k d ∗
    ∃ T' : nat,
      ic_regp k (L2Reg T' None) ∗
      CtxBox.reference (X := ic_x) (icfg_box k) (Some (dev, inum))
        {[ (Some (dev, inum), T') := ic_dep_mass d ]} ∗
      llb loglen_name T'.
  Proof.
    iIntros (HE Hid) "#Hbox Hrun Hhdr Hrest Hd Hdep".
    rewrite /ic_deposit2 Hid. iDestruct "Hdep" as "[Hhold Hbody]".
    iMod (ic_park_hold cn γfs γi cov logstart k ξ d dev inum x0 (ic_dep_mass d) E HE Hid
            with "Hbox Hrun Hhdr Hrest Hd Hhold") as "(Hrun & Hn & Hs & Hout)".
    iModIntro. iFrame "Hrun Hn Hs Hbody". iExact "Hout".
  Qed.

  (* iput's ref == 1 GUARD -- (a) at c = 1 with the WHOLE unit (inode_refp,
     shares gathered): the header comes out at a NAMED shape, so the guard's
     valid and nlink reads are exact; (b) re-deposits at that shape with no
     bump (cnt stays 1).  One lemma per half. *)
  Lemma ic_guard_withdraw `{CID : RiscvLang.CpuId} cn γfs γi cov logstart (k : nat)
      (ξ : CtxId) (r : slot_reg ic_bid ic_x) (dev inum : mword 32) (Kd Kt : nat) (E : coPset) :
    ↑icBoxN ⊆ E ->
    sr_win r = false -> sr_ident r = Some (dev, inum) -> (sr_td r <= Kd)%nat ->
    ic_box cn γfs γi cov logstart k -∗
    own_context ξ -∗ ctx_floor ξ Kd -∗ ctx_floor ξ Kt -∗
    ic_regd k r -∗ ic_cnt k 1 -∗
    (* the unit, its stamps covered by Kt (R1 at the itable acquire) *)
    (∃ m : gmap (ic_bid * nat) ufrac, ⌜qsum m = Qp_to_Qc 1⌝ ∗ ⌜(max_stamp m <= Kt)%nat⌝ ∗
       CtxBox.reference (X := ic_x) (icfg_box k) (Some (dev, inum)) m) -∗
    (* the guard window's residue: main's [ic_held] pin (F32 as Q-reuse) *)
    ic_pin_tx k ={E}=∗
    own_context ξ ∗ ic_cnt k 1 ∗
    ∃ (x0 : ic_x) (T0 : nat), ⌜x0 ≠ IcRaw⌝ ∗ ⌜(T0 <= Nat.max Kd Kt)%nat⌝ ∗
      ic_regd k (SlotReg (sr_td r) true (Some (dev, inum)) (Some (x0, T0))) ∗
      ic_hdr cn γfs γi cov logstart k (Some (dev, inum)) x0 ξ.
  Proof.
    iIntros (HE Hw Hid HKd) "#Hbox Hrun #Hfld #Hflt Hrd Hc Href Hpin".
    assert (HEk : ↑(icBoxN .@ k) ⊆ E) by (etrans; [apply nclose_subseteq | exact HE]).
    iDestruct "Href" as (m) "(%Hm & %Hmt & Href)".
    iDestruct "Href" as "(%Hne & %Hk & Hf & #Hl)".
    assert (Hq : qsum m = nat_Qc 1) by (rewrite Hm Qp_to_Qc_1 nat_Qc_1; reflexivity).
    iMod (CtxBox.box_withdraw_L1 (ic_hdr cn γfs γi cov logstart k) (ic_rest k) (ic_q1 cn k) (ic_q2 cn γfs γi cov logstart k)
            (icBoxN .@ k) (icfg_box k) ξ r 1 m Kd Kt E HEk Hw Hq HKd Hmt
            with "Hbox Hrun Hfld Hflt Hl Hrd Hc Hf [Hpin]") as "(Hrun & Hc & Hout)".
    { rewrite ic_q1_S. iExact "Hpin". }
    iDestruct "Hout" as (x0 T0) "(%HT0 & Hrd & Hhdr)". rewrite Hid.
    destruct x0 as [|g|g dn bm].
    { rewrite /ic_hdr /ic_hdr_amb. iDestruct "Hhdr" as "(_ & _ & _ & Hpay & _)".
      rewrite /ic_pay. iDestruct "Hpay" as %[]. }
    all: iModIntro; iFrame "Hrun Hc"; iExists _, T0;
         iSplitR; [| iSplitR; [iPureIntro; exact HT0 |]; iFrame "Hrd"; iExact "Hhdr"];
         iPureIntro; congruence.
  Qed.

  Lemma ic_guard_deposit `{CID : RiscvLang.CpuId} cn γfs γi cov logstart (k : nat)
      (ξ : CtxId) (r : slot_reg ic_bid ic_x) (dev inum : mword 32) (x0 : ic_x) (T0 : nat) (E : coPset) :
    ↑icBoxN ⊆ E ->
    sr_win r = true -> sr_x r = Some (x0, T0) -> sr_ident r = Some (dev, inum) ->
    ic_box cn γfs γi cov logstart k -∗
    own_context ξ -∗
    ic_regd k r -∗ ic_cnt k 1 -∗
    ic_hdr cn γfs γi cov logstart k (Some (dev, inum)) x0 ξ ={E}=∗
    own_context ξ ∗ ic_pin_tx k ∗
    ∃ T' : nat,
      ic_regd k (SlotReg T' false (Some (dev, inum)) None) ∗
      ic_cnt k 1 ∗
      ic_ref_stamps k dev inum 1%Qp ∗
      llb loglen_name T'.
  Proof.
    iIntros (HE Hw Hx Hid) "#Hbox Hrun Hrd Hc Hhdr".
    assert (HEk : ↑(icBoxN .@ k) ⊆ E) by (etrans; [apply nclose_subseteq | exact HE]).
    iMod (CtxBox.box_deposit_L1 (ic_hdr cn γfs γi cov logstart k) (ic_rest k) (ic_q1 cn k) (ic_q2 cn γfs γi cov logstart k)
            (icBoxN .@ k) (icfg_box k) ξ r 1 (Some (dev, inum)) x0 T0 E HEk Hw Hx
            with "Hbox Hrun Hrd Hc Hhdr") as "(Hrun & HQ & %T' & Hrd & Hc & Href & #Hllb)".
    rewrite ic_q1_S.
    iModIntro. iFrame "Hrun HQ". iExists T'. iFrame "Hrd Hllb". iSplitL "Hc"; [iExact "Hc"|].
    rewrite /ic_ref_stamps /ic_ref_stamps_at /ic_stamps. iExists _. iFrame "Href". iPureIntro.
    rewrite /qsum map_fold_singleton /qsum_step Qcplus_0_r. change (unit_mass 1) with 1%Qp. reflexivity.
  Qed.

  (* iput's guard re-deposit AT A FRESH GENERATION (R3 / F29): the mint at
     +0x50 regenerates the slot's liveness generation before the free path's
     acquiresleep, so the header goes back at [IcLoaded g' dn bm] where the
     register holds [IcLoaded g dn bm] -- (b') with the identity entailment
     on the rest (P_rest does not mention the generation). *)
  Lemma ic_guard_deposit_gen `{CID : RiscvLang.CpuId} cn γfs γi cov logstart (k : nat)
      (ξ : CtxId) (r : slot_reg ic_bid ic_x) (dev inum : mword 32)
      (g g' : gname) (dn : dinode) (bm : blkmap) (T0 : nat) (E : coPset) :
    ↑icBoxN ⊆ E ->
    sr_win r = true -> sr_x r = Some (IcLoaded g dn bm, T0) -> sr_ident r = Some (dev, inum) ->
    ic_box cn γfs γi cov logstart k -∗
    own_context ξ -∗
    ic_regd k r -∗ ic_cnt k 1 -∗
    ic_hdr cn γfs γi cov logstart k (Some (dev, inum)) (IcLoaded g' dn bm) ξ ={E}=∗
    own_context ξ ∗ ic_pin_tx k ∗
    ∃ T' : nat,
      ic_regd k (SlotReg T' false (Some (dev, inum)) None) ∗
      ic_cnt k 1 ∗
      ic_ref_stamps k dev inum 1%Qp ∗
      llb loglen_name T'.
  Proof.
    iIntros (HE Hw Hx Hid) "#Hbox Hrun Hrd Hc Hhdr".
    assert (HEk : ↑(icBoxN .@ k) ⊆ E) by (etrans; [apply nclose_subseteq | exact HE]).
    iMod (CtxBox.box_deposit_L1_shape (ic_hdr cn γfs γi cov logstart k) (ic_rest k) (ic_q1 cn k) (ic_q2 cn γfs γi cov logstart k)
            (icBoxN .@ k) (icfg_box k) ξ r 1 (Some (dev, inum)) (IcLoaded g dn bm) (IcLoaded g' dn bm) T0 E HEk Hw Hx
            ltac:(intros ξb; rewrite /ic_rest; simpl; reflexivity)
            with "Hbox Hrun Hrd Hc Hhdr") as "(Hrun & HQ & %T' & Hrd & Hc & Href & #Hllb)".
    rewrite ic_q1_S.
    iModIntro. iFrame "Hrun HQ". iExists T'. iFrame "Hrd Hllb". iSplitL "Hc"; [iExact "Hc"|].
    rewrite /ic_ref_stamps /ic_ref_stamps_at /ic_stamps. iExists _. iFrame "Href". iPureIntro.
    rewrite /qsum map_fold_singleton /qsum_step Qcplus_0_r. change (unit_mass 1) with 1%Qp. reflexivity.
  Qed.

  (* iput's LAST CLOSE with eviction -- (a) at c = 1 as above, the client
     returns the payload to the pool (icnt_half 0 in hand under itable), then
     (b') at c = 1 with the DEAD identity and the raw header (F14: x0 the
     withdrawn shape, x1 = IcRaw, entailment ic_rest_to_raw): the slot is
     dead from here (M-1'), and (d) at None drops the unit (F18). *)
  Lemma ic_evict_deposit `{CID : RiscvLang.CpuId} cn γfs γi cov logstart (k : nat)
      (ξ : CtxId) (r : slot_reg ic_bid ic_x) (x0 : ic_x) (T0 : nat) (E : coPset) :
    ↑icBoxN ⊆ E ->
    sr_win r = true -> sr_x r = Some (x0, T0) ->
    ic_box cn γfs γi cov logstart k -∗
    own_context ξ -∗
    ic_regd k r -∗ ic_cnt k 1 -∗
    ic_hdr cn γfs γi cov logstart k None IcRaw ξ ={E}=∗
    own_context ξ ∗ ic_pin_tx k ∗
    ∃ T' : nat,
      ic_regd k (SlotReg T' false None None) ∗
      ic_cnt k 1 ∗
      (∃ m : gmap (ic_bid * nat) ufrac, ⌜qsum m = Qp_to_Qc 1⌝ ∗
         CtxBox.reference (X := ic_x) (icfg_box k) None m) ∗
      llb loglen_name T'.
  Proof.
    iIntros (HE Hw Hx) "#Hbox Hrun Hrd Hc Hhdr".
    assert (HEk : ↑(icBoxN .@ k) ⊆ E) by (etrans; [apply nclose_subseteq | exact HE]).
    iMod (CtxBox.box_deposit_L1_shape (ic_hdr cn γfs γi cov logstart k) (ic_rest k) (ic_q1 cn k) (ic_q2 cn γfs γi cov logstart k)
            (icBoxN .@ k) (icfg_box k) ξ r 1 None x0 IcRaw T0 E HEk Hw Hx
            ltac:(intros ξb; apply ic_rest_to_raw)
            with "Hbox Hrun Hrd Hc Hhdr") as "(Hrun & HQ & %T' & Hrd & Hc & Href & #Hllb)".
    rewrite ic_q1_S.
    iModIntro. iFrame "Hrun HQ". iExists T'. iFrame "Hrd Hllb". iSplitL "Hc"; [iExact "Hc"|].
    iExists _. iFrame "Href". iPureIntro.
    rewrite /qsum map_fold_singleton /qsum_step Qcplus_0_r. change (unit_mass 1) with 1%Qp. reflexivity.
  Qed.

  (* iput's FREE PATH -- (g) under both locks (F30): P_rest comes out to the
     freer at the window's shape, the L1 register closes at its own stamp
     (no header goes back), and the unit's fragment parks in OUT_L2 as the
     handle row (e) would have returned -- [ic_hold] at mass 1, which the
     caller pairs with its [ic_body] into [ic_deposit2].  Cover: the
     register's stamp T0 (bounded by (a)'s post) under a floor the caller
     holds -- the itable acquire's Kt, or Kd, whichever (a) named. *)
  Lemma ic_free_take `{CID : RiscvLang.CpuId} cn γfs γi cov logstart (k : nat)
      (ξ : CtxId) (r : slot_reg ic_bid ic_x) (dev inum : mword 32) (x0 : ic_x)
      (T0 K : nat) (s0 : l2_reg ic_bid) (E : coPset) :
    ↑icBoxN ⊆ E ->
    sr_win r = true -> sr_x r = Some (x0, T0) -> sr_ident r = Some (dev, inum) ->
    (T0 <= K)%nat -> lr_hold s0 = None ->
    ic_box cn γfs γi cov logstart k -∗
    own_context ξ -∗ ctx_floor ξ K -∗
    ic_regd k r -∗ ic_cnt k 1 -∗ ic_q2 cn γfs γi cov logstart k -∗ ic_regp k s0 ={E}=∗
    own_context ξ ∗ ic_pin_tx k ∗
    ic_rest k x0 ξ ∗
    ic_regd k (SlotReg (sr_td r) false (Some (dev, inum)) None) ∗
    ic_cnt k 1 ∗
    ic_hold k dev inum 1%Qp.
  Proof.
    iIntros (HE Hw Hx Hid HTK Hs0) "#Hbox Hrun #Hfl Hrd Hc Hq Hrp".
    assert (HEk : ↑(icBoxN .@ k) ⊆ E) by (etrans; [apply nclose_subseteq | exact HE]).
    iMod (CtxBox.box_l1_to_l2 (ic_hdr cn γfs γi cov logstart k) (ic_rest k) (ic_q1 cn k) (ic_q2 cn γfs γi cov logstart k)
            (icBoxN .@ k) (icfg_box k) ξ r x0 T0 K s0 E HEk Hw Hx HTK Hs0
            with "Hbox Hrun Hfl Hrd Hc Hq Hrp")
      as "(Hrun & HQo & Hrest & Hrd & Hc & %m & %Hm & Hhold)".
    rewrite ic_q1_S.
    iModIntro. iFrame "Hrun HQo Hrest Hc". rewrite Hid. iFrame "Hrd".
    rewrite /ic_hold. iExists m. iFrame "Hhold". iPureIntro.
    rewrite Hm nat_Qc_1 Qp_to_Qc_1. reflexivity.
  Qed.

  (* boot: every slot dead and IN, at the boot deposit's stamp.  Over
     PRE-MINTED names (CtxBox.box_alloc_at, as bio_init does): with F19 the
     box gnames are fields of ic_names, minted before MkIcNames -- the
     caller presents the fresh ghosts and receives the boxes. *)
  Lemma ic_box_alloc_at `{CID : RiscvLang.CpuId} cn γfs γi cov logstart (ξ : CtxId) (E : coPset) :
    own_context ξ -∗
    ([∗ list] k ∈ seq 0 NINODE,
       CtxBox.stamps_auth (X := ic_x) (icfg_box k) ∅ ∗
       ghost_var (ghost_varG0 := kalloc_count_inG) (bx_cnt (icfg_box k)) 1 0%nat ∗
       ghost_var (bx_slotd (icfg_box k)) 1 (inhabitant : slot_reg ic_bid ic_x) ∗
       ghost_var (bx_slotp (icfg_box k)) 1 (inhabitant : l2_reg ic_bid) ∗
       ic_hdr cn γfs γi cov logstart k None IcRaw ξ ∗ ic_rest k IcRaw ξ) ={E}=∗
    own_context ξ ∗
    ic_boxes_all cn γfs γi cov logstart ∗
    ([∗ list] k ∈ seq 0 NINODE, ∃ T_boot : nat,
       ic_regd k (SlotReg T_boot false None None) ∗ llb loglen_name T_boot ∗
       ic_cnt k 0 ∗ ic_regp k (L2Reg 0 None)).
  Proof.
    iIntros "Hrun Hall".
    iAssert ([∗ list] i↦k ∈ seq 0 NINODE,
               own_context ξ -∗
               (CtxBox.stamps_auth (X := ic_x) (icfg_box k) ∅ ∗
                ghost_var (ghost_varG0 := kalloc_count_inG) (bx_cnt (icfg_box k)) 1 0%nat ∗
                ghost_var (bx_slotd (icfg_box k)) 1 (inhabitant : slot_reg ic_bid ic_x) ∗
                ghost_var (bx_slotp (icfg_box k)) 1 (inhabitant : l2_reg ic_bid) ∗
                ic_hdr cn γfs γi cov logstart k None IcRaw ξ ∗ ic_rest k IcRaw ξ) ={E}=∗
               own_context ξ ∗
               (ic_box cn γfs γi cov logstart k ∗
                ∃ T_boot : nat,
                  ic_regd k (SlotReg T_boot false None None) ∗ llb loglen_name T_boot ∗
                  ic_cnt k 0 ∗ ic_regp k (L2Reg 0 None)))%I as "Hstep".
    { iApply big_sepL_intro. iIntros "!>" (i k _) "Hrun (Hst & Hc & Hd & Hp & Hhdr & Hrest)".
      iMod (CtxBox.box_alloc_at (ic_hdr cn γfs γi cov logstart k) (ic_rest k) (ic_q1 cn k) (ic_q2 cn γfs γi cov logstart k)
              (icBoxN .@ k) (icfg_box k) ξ None E with "Hst Hc Hd Hp Hrun [Hhdr Hrest]")
        as "(Hrun & %Tb & #Hbx & Hrd & #Hllb & Hc2 & Hp2)".
      { iExists IcRaw. iFrame "Hhdr Hrest". }
      iModIntro. iFrame "Hrun". iSplitR; [iExact "Hbx"|]. iExists Tb. iFrame "Hrd Hllb Hc2 Hp2". }
    iMod (big_sepL_fupd_thread E (own_context ξ) _ _ (seq 0 NINODE) with "Hrun Hstep Hall")
      as "[Hrun Hpost]".
    iModIntro. iFrame "Hrun". rewrite big_sepL_sep. iDestruct "Hpost" as "[Hboxes Hrows]".
    iFrame "Hrows". iExact "Hboxes".
  Qed.

End IcacheBox.

Section IcacheTable.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !irefslotG Σ}.
  Context `{GEN : GenId}.
  Context `{ICFG : icfg}.
  Context `{XI : CurCtx}.

  (* ------------------------------------------------------------------ *)
  (*  6.  THE itable LOCK'S RESOURCE, v2                                 *)
  (* ------------------------------------------------------------------ *)

  (* [IcacheInv.islot] with the identity VALUES pinned by [ci] rather than
     ∃-bound: that is what makes "the cached inums" a function of the pure
     state, which is what the pool's domain is stated against.

     FOUR arms, not three (§13.7).  The (Some, Some) and (None, None) arms
     are §13.2's; the (None, Some) arm is the CACHED, REF-0 entry iput's last
     close leaves behind -- identity still written, payload still parked in
     the escrow, so its inum must stay OUT of the pool, which is exactly what
     keeping it in [ci] does.  It holds the table's whole share of both
     identity cells (the escrow keeps the other half of each forever,
     §13.1e), i.e. [islot_free_at] at [ci]'s values, and no [iref_slots]:
     there is no outstanding reference to account for.  Only (Some, None) is
     [False], and [dom M ⊆ dom ci] is what makes it unreachable -- which is
     what lets a slot accessor read [ci !! k] off a live [M !! k]. *)
  (* THE TABLE'S SHARE OF A NOT-LIVE SLOT (§13.8/§13.9).  Half the inum
     cell and NOTHING of the dev cell: the escrow's empty arm holds that one
     whole, and that is what a reference holder refutes it with.  Plus the
     table's [false] half of the identification ghost, which is what the
     RECYCLER arriving here reads -- it has no dev fraction to reason with,
     by construction. *)
  (* R3 (M-1'/F17): a DEAD slot's table half is the identity halves
     complementary to the dead header's ([islot_free_at]); the LIVE/EMPTY
     agreement [ic_id] retired -- the box register's identity IS [ci !! k]
     ([ic_slot_row] below, in the ξ-row). *)
  Definition islot_empty (cn : ic_names) (k : nat) : iProp Σ :=
    (∃ dev inum : mword 32,
       (* THE CELLS follow the box (tso-flip M-1'/F17): the table's share of
          a DEAD slot is the identity halves complementary to the dead
          header's ([islot_free_at]). *)
       islot_free_at k dev inum ∗
       (* THE GHOST follows main (durable-disk C-3b), re-homed by the stitch
          (endgame plan §6′): the identity IS the register's [sr_ident]
          (= [ci !! k]), so both halves of the table's side of the
          identification ghost live HERE, under itable.lock, beside the pool
          invariant's quarter: 1/2 in the slot, 1/4 in the box's header, 1/4 in the pool. *)
       ic_id cn k (1/2) false dev inum ∗
       (* F42 (endgame §6¹²): main's window pin AT REST rides the table row --
          dead here, live in [IcacheInv.frz_park]'s OFF arm (F42′) -- so the
          recycler and iput's guard, who hold the row, can produce the box's
          OUT_L1 residue at their (a). *)
       ic_pin_rest k)%I.

  (* THE COUNT COUPLING's SLOT HALF (iclaim-ledger.md §2.2) rides on the LIVE
     arm, at this slot's own count: [icnt_half (bv_unsigned inum)
     (Pos.to_nat n)].  It is what every count-move lemma takes as an argument
     and hands back moved ([IcacheInv]'s five [*_store_au]s), and it is
     lock-held for the reason the rest of this record is -- iput has to hold
     it across an [acquiresleep] and no invariant survives that.  The REGION
     holds the other half ([InodeRegion.ireg_slot]), which is why a count move
     needs an [↑iregN] open (the probe's structural mask verdict).

     THE NOT-LIVE ARM DOES NOT GAIN ONE, and that is a recorded DEVIATION
     from §2.2 ("[islot_empty] gains it at 0").  It cannot: [islot_empty]'s
     [inum] is the value of the slot's own inum CELL, and at boot every one of
     the fifty cells reads ZERO ([IcacheBoot.itable_boot]'s zeroed BSS), so
     §2.2's ruling asks for fifty copies of [icnt_half 0 0] -- fraction 25 at
     one key, i.e. FALSE, and [IcacheBoot] would not close.  The uncached
     inums' halves have exactly one coherent home, the free POOL (whose domain
     [region_inums nib ∖ ci_inums ci] is precisely the complement of the live
     arms' inums, so pool ⊎ live = every region inum, one half each); wiring
     it is the recycle/eviction increment's, together with the boot premise
     that supplies them. *)
  Definition islot2 (cn : ic_names) (M : gmap nat (Qp * positive))
      (ci : gmap nat (mword 32 * mword 32)) (k : nat) : iProp Σ :=
    match M !! k, ci !! k with
    | None, None => islot_empty cn k
    | Some (q, n), Some (dev, inum) =>
        (islot_rest_at k q dev inum ∗ iref_slots (Pos.to_nat n) ∗
         (* A QUARTER since durable-disk C-3b: see [islot_empty]. *)
         ic_id cn k (1/2) true dev inum ∗
         icnt_half (bv_unsigned inum) (Pos.to_nat n) ∗
         (* THE FREEZE MIRROR's LOCK HALF, AND THE FROZEN PARK
            (iclaim-ledger.md §3.16, RULING A⁗).  Ordinarily the bare
            [false] bit -- the mirror's twin of the [icnt] half above it,
            and in the same home for the same reason.  Inside iput's free
            window it is the FROZEN PARK: the bit UP, and beside it the
            dying reference's own liveness slice [q] and the escrow arm's
            [1/2], both put here BY THE MINT at +0x50 (the one instant at
            which they are in one hand) and reclaimed by the last close at
            +0x82.  A foreign [idup] that takes this lock in between finds
            them and dies on [IcacheInv.live_whole_share_absurd] --
            [ProofIdup]'s OPEN(2.6b), closed. *)
         frz_park k (bv_unsigned inum))%I
    | _, _ => False%I
    end.

  (* A6.145: the per-slot PAYLOAD row.  A FREE slot's count cell rides the
     lock as a plain ctx cell (value 0 -- boot's and every retire's), with
     the FULL stamp auth and its loglen receipt; a LIVE slot's row is the
     A6.144 exact-read credential: the stamp half (the invariant holds the
     other), its receipt, and the ctx floor AT it -- re-minted at each
     release, which is what makes the holder's first read EXACT. *)
  (* R3 (M-6/F17): THE BOX'S L1 ROW rides the ξ-row, FLOORED.  The slot
     register's drop half, shut and empty, at the table's identity [ci !! k]
     and count [icM_count M k], its drop stamp floored at the lock's context
     -- what the recycler's (a) and iput's guard (a) present as
     [ctx_floor ξ Kd].  [tb] is the row's own bound, re-floored at each
     release exactly like the exact-read stamps ([itable_slot_row_raise]). *)
  Definition icM_count (M : gmap nat (Qp * positive)) (k : nat) : nat :=
    match M !! k with Some (_, n) => Pos.to_nat n | None => 0%nat end.
  Definition ic_slot_row_fl (ξ : TsoCtx.CtxId) (k : nat) (oi : ic_bid) (c : nat) : iProp Σ :=
    (∃ tb : nat, ic_slot_row k oi c tb ∗ TsoGhost.llb loglen_name tb ∗
                 TsoCtx.ctx_floor ξ tb)%I.
  Definition ic_slot_row_llb (k : nat) (oi : ic_bid) (c : nat) : iProp Σ :=
    (∃ tb : nat, ic_slot_row k oi c tb ∗ TsoGhost.llb loglen_name tb)%I.
  Definition ic_slot_row_bare (tl k : nat) (oi : ic_bid) (c : nat) : iProp Σ :=
    (∃ tb : nat, ⌜(tb <= tl)%nat⌝ ∗ ic_slot_row k oi c tb ∗ TsoGhost.llb loglen_name tb)%I.

  Definition itable_slot_res (ξ : TsoCtx.CtxId)
      (M : gmap nat (Qp * positive)) (ci : gmap nat (mword 32 * mword 32))
      (k : nat) : iProp Σ :=
    ic_slot_row_fl ξ k (ci !! k) (icM_count M k) ∗
    match M !! k with
    | None => (∃ tst : nat,
        TsoCtx.ctx_word4_pointsto ξ (i_ref (ientry k))
          (DfracOwn 1) (mword_of_int 0 : mword 32) ∗
        mono_nat_auth_own (icfg_istmp k) 1 tst ∗
        TsoGhost.llb loglen_name tst)%I
    | Some _ => (∃ tst : nat,
        mono_nat_auth_own (icfg_istmp k) (1/2) tst ∗
        TsoGhost.llb loglen_name tst ∗
        TsoCtx.ctx_floor ξ tst)%I
    end.

  (* the same rows with the live floors STRIPPED -- what a releaser can
     hand ([lock_finisher_close_in_llb]'s Rdep side; the fold reinserts
     the floors at the parked ξ, bounded by the twins' llb receipt). *)
  Definition itable_slot_res_bare (ξ : TsoCtx.CtxId) (tl : nat)
      (M : gmap nat (Qp * positive)) (ci : gmap nat (mword 32 * mword 32))
      (k : nat) : iProp Σ :=
    ic_slot_row_bare tl k (ci !! k) (icM_count M k) ∗
    match M !! k with
    | None => (∃ tst : nat,
        TsoCtx.ctx_word4_pointsto ξ (i_ref (ientry k))
          (DfracOwn 1) (mword_of_int 0 : mword 32) ∗
        mono_nat_auth_own (icfg_istmp k) 1 tst ∗
        TsoGhost.llb loglen_name tst)%I
    | Some _ => (∃ tst : nat,
        ⌜(tst <= tl)%nat⌝ ∗
        mono_nat_auth_own (icfg_istmp k) (1/2) tst ∗
        TsoGhost.llb loglen_name tst)%I
    end.

  Lemma itable_slot_res_of_bare (ξ : TsoCtx.CtxId) (tl : nat)
      (M : gmap nat (Qp * positive)) (ci : gmap nat (mword 32 * mword 32))
      (k : nat) :
    itable_slot_res_bare ξ tl M ci k ∗ TsoCtx.ctx_floor ξ tl ⊢
    itable_slot_res ξ M ci k.
  Proof.
    rewrite /itable_slot_res_bare /itable_slot_res /ic_slot_row_bare /ic_slot_row_fl.
    iIntros "[[Hrow H] #Hfl]".
    iSplitL "Hrow".
    { iDestruct "Hrow" as (tb) "(%Htb & Hrow & #Hllb)". iExists tb. iFrame "Hrow Hllb".
      iApply (TsoCtx.ctx_floor_le ξ tl tb Htb with "Hfl"). }
    destruct (M !! k) as [[qt n]|].
    - iDestruct "H" as (tst) "(%Htl & Hst & #Hllb)".
      iExists tst. iFrame "Hst Hllb".
      iApply (TsoCtx.ctx_floor_le ξ tl tst Htl with "Hfl").
    - iExact "H".
  Qed.

  (* the release-time rows: floors STRIPPED, llb-backed only -- what a
     holder can hand back after bumping stamps.  [itable_pay_intro] below
     re-floors them at the parked context, one raise per live slot. *)
  Definition itable_slot_res_llb (ξ : TsoCtx.CtxId)
      (M : gmap nat (Qp * positive)) (ci : gmap nat (mword 32 * mword 32))
      (k : nat) : iProp Σ :=
    ic_slot_row_llb k (ci !! k) (icM_count M k) ∗
    match M !! k with
    | None => (∃ tst : nat,
        TsoCtx.ctx_word4_pointsto ξ (i_ref (ientry k))
          (DfracOwn 1) (mword_of_int 0 : mword 32) ∗
        mono_nat_auth_own (icfg_istmp k) 1 tst ∗
        TsoGhost.llb loglen_name tst)%I
    | Some _ => (∃ tst : nat,
        mono_nat_auth_own (icfg_istmp k) (1/2) tst ∗
        TsoGhost.llb loglen_name tst)%I
    end.

  Global Instance itable_slot_res_llb_morph (M : gmap nat (Qp * positive))
      (ci : gmap nat (mword 32 * mword 32)) (k : nat) :
    CtxMorph (fun ξ => itable_slot_res_llb ξ M ci k).
  Proof.
    rewrite /itable_slot_res_llb.
    destruct (M !! k) as [[qt n]|].
    - iIntros (ξ ξ') "Hd H". iModIntro. iFrame.
    - iIntros (ξ ξ') "Hd [Hrow H]". iDestruct "H" as (tst) "(Hcell & Hst & #Hllb)".
      iMod (ctx_morph_word4 _ (i_ref (ientry k)) (DfracOwn 1)
              (mword_of_int 0 : mword 32) ξ ξ' with "Hd Hcell")
        as "[Hd Hcell]".
      iModIntro. iFrame "Hd Hrow". iExists tst. iFrame "Hcell Hst Hllb".
  Qed.

    Global Instance itable_slot_res_morph (M : gmap nat (Qp * positive))
      (ci : gmap nat (mword 32 * mword 32)) (k : nat) :
    CtxMorph (fun ξ => itable_slot_res ξ M ci k).
  Proof.
    rewrite /itable_slot_res /ic_slot_row_fl.
    iIntros (ξ ξ') "Hd [Hrow H]".
    iDestruct "Hrow" as (tb) "(Hrow & #Hllb & #Hfl)".
    iDestruct (TsoCtx.ctx_floor_dom with "Hd Hfl") as "[Hd #Hfl']".
    destruct (M !! k) as [[qt n]|].
    - iDestruct "H" as (tst) "(Hst & #Hllb2 & #Hfl2)".
      iDestruct (TsoCtx.ctx_floor_dom with "Hd Hfl2") as "[Hd #Hfl2']".
      iModIntro. iFrame "Hd". iSplitL "Hrow".
      { iExists tb. iFrame "Hrow Hllb Hfl'". }
      iExists tst. iFrame "Hst Hllb2 Hfl2'".
    - iDestruct "H" as (tst) "(Hcell & Hst & #Hllb2)".
      iMod (ctx_morph_word4 _ (i_ref (ientry k)) (DfracOwn 1)
              (mword_of_int 0 : mword 32) ξ ξ' with "Hd Hcell")
        as "[Hd Hcell]".
      iModIntro. iFrame "Hd". iSplitL "Hrow".
      { iExists tb. iFrame "Hrow Hllb Hfl'". }
      iExists tst. iFrame "Hcell Hst Hllb2".
  Qed.

    Lemma itable_slot_res_acc_upd (ξ : TsoCtx.CtxId)
      (M : gmap nat (Qp * positive)) (ci : gmap nat (mword 32 * mword 32))
      (k : nat) :
    (k < NINODE)%nat ->
    ([∗ list] j ∈ seq 0 NINODE, itable_slot_res ξ M ci j) -∗
      itable_slot_res ξ M ci k ∗
      (∀ (M' : gmap nat (Qp * positive)) (ci' : gmap nat (mword 32 * mword 32)),
         ⌜forall j, j <> k -> M' !! j = M !! j⌝ -∗
         ⌜forall j, j <> k -> ci' !! j = ci !! j⌝ -∗
         itable_slot_res ξ M' ci' k -∗
         [∗ list] j ∈ seq 0 NINODE, itable_slot_res ξ M' ci' j).
  Proof.
    intros Hk. iIntros "Hs".
    iDestruct (big_sepL_delete _ (seq 0 NINODE) k k
                 ltac:(apply lookup_seq; split; [lia|exact Hk]) with "Hs")
      as "[Hslot Hrest]".
    iFrame "Hslot". iIntros (M' ci') "%Hagree %Hagc Hslot".
    iApply (big_sepL_delete _ (seq 0 NINODE) k k
              ltac:(apply lookup_seq; split; [lia|exact Hk])).
    iFrame "Hslot".
    iApply (big_sepL_impl with "Hrest").
    iIntros "!>" (j x Hjx) "H".
    destruct (decide (j = k)) as [->|Hne]; [iExact "H"|].
    apply lookup_seq in Hjx as [Hx _].
    assert (Hxk : x <> k) by lia.
    rewrite /itable_slot_res /icM_count (Hagree x Hxk) (Hagc x Hxk). iExact "H".
  Qed.

  Lemma itable_slot_res_to_llb (ξ : TsoCtx.CtxId)
      (M : gmap nat (Qp * positive)) (ci : gmap nat (mword 32 * mword 32))
      (k : nat) :
    itable_slot_res ξ M ci k ⊢ itable_slot_res_llb ξ M ci k.
  Proof.
    rewrite /itable_slot_res /itable_slot_res_llb /ic_slot_row_fl /ic_slot_row_llb.
    iIntros "[Hrow H]". iSplitL "Hrow".
    { iDestruct "Hrow" as (tb) "(Hrow & #Hllb & _)". iExists tb. iFrame "Hrow Hllb". }
    destruct (M !! k) as [[qt n]|].
    - iDestruct "H" as (tst) "(Hst & #Hllb & _)".
      iExists tst. iFrame "Hst Hllb".
    - iExact "H".
  Qed.

  (* the A6.144 section accessor: the extracted row keeps its acquire-time
     floor (the exact/racy read PRECEDES the slot's store), but the CLOSE
     is into the LLB world -- a holder cannot mint a [cur_ctx] floor for
     its own buffered store; the release's park re-floors every row. *)
  Lemma itable_slot_res_acc_upd_llb (ξ : TsoCtx.CtxId)
      (M : gmap nat (Qp * positive)) (ci : gmap nat (mword 32 * mword 32))
      (k : nat) :
    (k < NINODE)%nat ->
    ([∗ list] j ∈ seq 0 NINODE, itable_slot_res ξ M ci j) -∗
      itable_slot_res ξ M ci k ∗
      (∀ (M' : gmap nat (Qp * positive)) (ci' : gmap nat (mword 32 * mword 32)),
         ⌜forall j, j <> k -> M' !! j = M !! j⌝ -∗
         ⌜forall j, j <> k -> ci' !! j = ci !! j⌝ -∗
         itable_slot_res_llb ξ M' ci' k -∗
         [∗ list] j ∈ seq 0 NINODE, itable_slot_res_llb ξ M' ci' j).
  Proof.
    intros Hk. iIntros "Hs".
    iDestruct (big_sepL_delete _ (seq 0 NINODE) k k
                 ltac:(apply lookup_seq; split; [lia|exact Hk]) with "Hs")
      as "[Hslot Hrest]".
    iFrame "Hslot". iIntros (M' ci') "%Hagree %Hagc Hslot".
    iApply (big_sepL_delete _ (seq 0 NINODE) k k
              ltac:(apply lookup_seq; split; [lia|exact Hk])).
    iFrame "Hslot".
    iApply (big_sepL_impl with "Hrest").
    iIntros "!>" (j x Hjx) "H".
    destruct (decide (j = k)) as [->|Hne]; [iExact "H"|].
    apply lookup_seq in Hjx as [Hx _].
    assert (Hxk : x <> k) by lia.
    iApply itable_slot_res_to_llb.
    rewrite /itable_slot_res /icM_count (Hagree x Hxk) (Hagc x Hxk). iExact "H".
  Qed.

  Lemma itable_rows_to_llb (ξ : TsoCtx.CtxId)
      (M : gmap nat (Qp * positive)) (ci : gmap nat (mword 32 * mword 32)) :
    ([∗ list] k ∈ seq 0 NINODE, itable_slot_res ξ M ci k) ⊢
    ([∗ list] k ∈ seq 0 NINODE, itable_slot_res_llb ξ M ci k).
  Proof.
    apply big_sepL_mono. intros n y Hny. apply itable_slot_res_to_llb.
  Qed.

  Definition itable_res2 (ξ : TsoCtx.CtxId)
      (cn : ic_names) (γfs : fs_names) (γi : gname)
      (cov : gset Z) (logstart : Z) (nib : nat) (dv : mword 32) : iProp Σ :=
    (∃ (M : gmap nat (Qp * positive)) (ci : gmap nat (mword 32 * mword 32)),
       itable_half M ∗
       ([∗ list] k ∈ seq 0 NINODE, itable_slot_res ξ M ci k) ∗
       ⌜icM_wf M⌝ ∗ ⌜ic_ci_wf M ci nib dv⌝ ∗
       iref_slots_auth ∗
       (* THE SLOTS' SHARE AUTHORITIES.  Under the LOCK, not in
          [itable_body]'s invariant: every step that moves one runs while
          holding itable.lock, and iput has to hold a slot's authoritative
          zero across a whole [acquiresleep] call -- which it can, because
          [release(&itable.lock)] comes AFTER that call in the C, but which no
          invariant could survive
          (claude-notes/projects/iput-acquiresleep.md). *)
       isl_pool M ∗
       ([∗ list] k ∈ seq 0 NINODE, islot2 cn M ci k) ∗
       ipool γfs γi cov logstart (region_inums nib ∖ ci_inums ci) ∅)%I.

  Definition itable_res2_llb (ξ : TsoCtx.CtxId)
      (cn : ic_names) (γfs : fs_names) (γi : gname)
      (cov : gset Z) (logstart : Z) (nib : nat) (dv : mword 32) : iProp Σ :=
    (∃ (M : gmap nat (Qp * positive)) (ci : gmap nat (mword 32 * mword 32)),
       itable_half M ∗
       ([∗ list] k ∈ seq 0 NINODE, itable_slot_res_llb ξ M ci k) ∗
       ⌜icM_wf M⌝ ∗ ⌜ic_ci_wf M ci nib dv⌝ ∗
       iref_slots_auth ∗
       isl_pool M ∗
       ([∗ list] k ∈ seq 0 NINODE, islot2 cn M ci k) ∗
       ipool γfs γi cov logstart (region_inums nib ∖ ci_inums ci) ∅)%I.

  Global Instance itable_res2_llb_morph (cn : ic_names) (γfs : fs_names)
      (γi : gname) (cov : gset Z) (logstart : Z) (nib : nat)
      (dv : mword 32) :
    CtxMorph (fun ξ => itable_res2_llb ξ cn γfs γi cov logstart nib dv).
  Proof. rewrite /itable_res2_llb. apply _. Qed.

  (* THE BARE TABLE: every row's floor stripped and bounded by ONE [tl] --
     what the boot deposits through [newlock_at_llb] (the fifty boot stamps
     under one llb, CtxBox.big_sepL_llb_max) and what an _in release hands
     as its Rdep; [itable_res2_of_bare] re-floors it at the parked ξ. *)
  Global Instance itable_slot_res_bare_morph (tl : nat) (M : gmap nat (Qp * positive))
      (ci : gmap nat (mword 32 * mword 32)) (k : nat) :
    CtxMorph (fun ξ => itable_slot_res_bare ξ tl M ci k).
  Proof.
    rewrite /itable_slot_res_bare.
    destruct (M !! k) as [[qt n]|].
    - iIntros (ξ ξ') "Hd H". iModIntro. iFrame.
    - iIntros (ξ ξ') "Hd [Hrow H]". iDestruct "H" as (tst) "(Hcell & Hst & #Hllb)".
      iMod (ctx_morph_word4 _ (i_ref (ientry k)) (DfracOwn 1)
              (mword_of_int 0 : mword 32) ξ ξ' with "Hd Hcell")
        as "[Hd Hcell]".
      iModIntro. iFrame "Hd Hrow". iExists tst. iFrame "Hcell Hst Hllb".
  Qed.

  Definition itable_res2_bare (ξ : TsoCtx.CtxId) (tl : nat)
      (cn : ic_names) (γfs : fs_names) (γi : gname)
      (cov : gset Z) (logstart : Z) (nib : nat) (dv : mword 32) : iProp Σ :=
    (∃ (M : gmap nat (Qp * positive)) (ci : gmap nat (mword 32 * mword 32)),
       itable_half M ∗
       ([∗ list] k ∈ seq 0 NINODE, itable_slot_res_bare ξ tl M ci k) ∗
       ⌜icM_wf M⌝ ∗ ⌜ic_ci_wf M ci nib dv⌝ ∗
       iref_slots_auth ∗
       isl_pool M ∗
       ([∗ list] k ∈ seq 0 NINODE, islot2 cn M ci k) ∗
       ipool γfs γi cov logstart (region_inums nib ∖ ci_inums ci) ∅)%I.

  Global Instance itable_res2_bare_morph (tl : nat) (cn : ic_names) (γfs : fs_names)
      (γi : gname) (cov : gset Z) (logstart : Z) (nib : nat) (dv : mword 32) :
    CtxMorph (fun ξ => itable_res2_bare ξ tl cn γfs γi cov logstart nib dv).
  Proof. rewrite /itable_res2_bare. apply _. Qed.

  Lemma itable_res2_of_bare (ξ : TsoCtx.CtxId) (tl : nat)
      (cn : ic_names) (γfs : fs_names) (γi : gname)
      (cov : gset Z) (logstart : Z) (nib : nat) (dv : mword 32) :
    itable_res2_bare ξ tl cn γfs γi cov logstart nib dv ∗ TsoCtx.ctx_floor ξ tl ⊢
    itable_res2 ξ cn γfs γi cov logstart nib dv.
  Proof.
    iIntros "[H #Hfl]".
    iDestruct "H" as (M ci) "(Hhalf & Hrows & %Hwf & %Hciwf & Hia & Hip & Hslots & Hpool)".
    iExists M, ci. iFrame "Hhalf Hia Hip Hslots Hpool".
    iSplitL "Hrows".
    { iApply (big_sepL_impl with "Hrows"). iIntros "!>" (i k _) "H".
      iApply (itable_slot_res_of_bare ξ tl M ci k). iFrame "H Hfl". }
    iSplitR; [by iPureIntro|]. by iPureIntro.
  Qed.

  Local Lemma itable_slot_row_raise (ξc : TsoCtx.CtxId) (T : nat)
      (M : gmap nat (Qp * positive)) (ci : gmap nat (mword 32 * mword 32))
      (k : nat) :
    ctx_parked ξc T -∗ itable_slot_res_llb ξc M ci k ==∗
    ∃ T' : nat, ctx_parked ξc T' ∗ itable_slot_res ξc M ci k.
  Proof.
    rewrite /itable_slot_res_llb /itable_slot_res /ic_slot_row_llb /ic_slot_row_fl.
    iIntros "Hpk [Hrow H]".
    iDestruct "Hrow" as (tb) "(Hrow & #Hllb)".
    iMod (TsoCtxPark.ctx_parked_raise ξc T tb with "Hllb Hpk") as "[Hpk #Hfl]".
    destruct (M !! k) as [[qt n]|].
    - iDestruct "H" as (tst) "(Hst & #Hllb2)".
      iMod (TsoCtxPark.ctx_parked_raise ξc _ tst with "Hllb2 Hpk")
        as "[Hpk #Hfl2]".
      iModIntro. iExists _. iFrame "Hpk".
      iSplitL "Hrow". { iExists tb. iFrame "Hrow Hllb Hfl". }
      iExists tst. iFrame "Hst". iSplit; [iExact "Hllb2" | iExact "Hfl2"].
    - iModIntro. iExists _. iFrame "Hpk".
      iSplitL "Hrow". { iExists tb. iFrame "Hrow Hllb Hfl". }
      iExact "H".
  Qed.

  Local Lemma itable_rows_raise (ξc : TsoCtx.CtxId) (T : nat)
      (M : gmap nat (Qp * positive)) (ci : gmap nat (mword 32 * mword 32))
      (l : list nat) :
    ctx_parked ξc T -∗
    ([∗ list] k ∈ l, itable_slot_res_llb ξc M ci k) ==∗
    ∃ T' : nat, ctx_parked ξc T' ∗
    ([∗ list] k ∈ l, itable_slot_res ξc M ci k).
  Proof.
    iIntros "Hpk Hrows".
    iInduction l as [| k l] "IH" forall (T).
    - iModIntro. iExists T. iFrame "Hpk". done.
    - iDestruct "Hrows" as "[Hrow Hrows]".
      iMod (itable_slot_row_raise ξc T M ci k with "Hpk Hrow") as (T1) "[Hpk Hrow]".
      iMod ("IH" with "Hpk Hrows") as (T') "[Hpk Hrows]".
      iModIntro. iExists T'. iFrame "Hpk".
      iSplitR "Hrows"; [iExact "Hrow" | iExact "Hrows"].
  Qed.
  (* THE A6.144 RELEASE MINT for the itable: deposit the llb-backed
     payload into a fresh parked context and RAISE it once per live slot,
     minting each exact-read floor at the parked ξ -- which is where the
     next acquirer's credentials transport from. *)
  Lemma itable_pay_intro `{CIDr : RiscvLang.CpuId} (cn : ic_names) (γfs : fs_names)
      (γi : gname) (cov : gset Z) (logstart : Z) (nib : nat)
      (dv : mword 32) :
    TsoCtx.own_context TsoCtx.cur_ctx -∗
    itable_res2_llb TsoCtx.cur_ctx cn γfs γi cov logstart nib dv ==∗
    TsoCtx.own_context TsoCtx.cur_ctx ∗
    lock_pay (fun ξ => itable_res2 ξ cn γfs γi cov logstart nib dv).
  Proof.
    iIntros "Hrun HR".
    iMod TsoCtx.ctx_parked_alloc as (ξc) "Hpk".
    iMod (TsoCtx.ctx_deposit
            (fun ξ => itable_res2_llb ξ cn γfs γi cov logstart nib dv)
            TsoCtx.cur_ctx ξc 0 with "Hrun Hpk HR")
      as "(Hrun & %T' & _ & Hpk & HR)".
    iDestruct "HR" as (M ci) "(Hhalf & Hrows & %Hwf & %Hciwf & Hia & Hip &
                               Hslots & Hpool)".
    iMod (itable_rows_raise ξc T' M ci (seq 0 NINODE) with "Hpk Hrows")
      as (T'') "[Hpk Hrows]".
    iModIntro. iFrame "Hrun".
    iExists ξc, T''. iFrame "Hpk".
    rewrite /itable_res2. iExists M, ci.
    iFrame "Hhalf Hrows Hia Hip Hslots Hpool".
    iSplitR; [by iPureIntro|]. by iPureIntro.
  Qed.

    Global Instance itable_res2_morph (cn : ic_names) (γfs : fs_names)
      (γi : gname) (cov : gset Z) (logstart : Z) (nib : nat)
      (dv : mword 32) :
    CtxMorph (fun ξ => itable_res2 ξ cn γfs γi cov logstart nib dv).
  Proof. rewrite /itable_res2. apply _. Qed.

    Definition is_itable2 (γl : gname) (cn : ic_names) (γfs : fs_names)
      (γi : gname) (cov : gset Z) (logstart : Z) (nib : nat)
      (dv : mword 32) : iProp Σ :=
    (is_lock γl itable_lock "itable"%string
       (fun ξ => itable_res2 ξ cn γfs γi cov logstart nib dv) ∗
     (* A6.145: the pinw read leaves' address claims ride the icache's
        persistent handle -- minted once at boot off the pre-conversion
        cells. *)
     iref_claims ∗
     (* R3 (F26): THE ESCROW FAMILY rides the itable handle too.  Under the
        box every [ref++] under itable.lock is the box's (c) -- iget's hit
        AND idup's -- and idup's contract never took the escrows; the
        persistent handle every itable user already holds is where the
        family belongs (one row here, no spec sweep). *)
     ic_escrows cn γfs γi cov logstart ∗
     (* THE POOL INVARIANT RIDES HERE (durable-disk lane B''-esc, main):
        it reaches the same four files the itable lock does, and this
        handle already carries its arguments. *)
     ipool_inv cn γfs γi cov logstart nib)%I.

  Lemma is_itable2_lock (γl : gname) (cn : ic_names) (γfs : fs_names)
      (γi : gname) (cov : gset Z) (logstart : Z) (nib : nat)
      (dv : mword 32) :
    is_itable2 γl cn γfs γi cov logstart nib dv -∗
    is_lock γl itable_lock "itable"%string
      (fun ξ => itable_res2 ξ cn γfs γi cov logstart nib dv).
  Proof. iIntros "($ & _ & _ & _)". Qed.

  Lemma is_itable2_claims (γl : gname) (cn : ic_names) (γfs : fs_names)
      (γi : gname) (cov : gset Z) (logstart : Z) (nib : nat)
      (dv : mword 32) :
    is_itable2 γl cn γfs γi cov logstart nib dv -∗ iref_claims.
  Proof. iIntros "(_ & $ & _ & _)". Qed.

  Lemma is_itable2_escrows (γl : gname) (cn : ic_names) (γfs : fs_names)
      (γi : gname) (cov : gset Z) (logstart : Z) (nib : nat)
      (dv : mword 32) :
    is_itable2 γl cn γfs γi cov logstart nib dv -∗ ic_escrows cn γfs γi cov logstart.
  Proof. iIntros "(_ & _ & $ & _)". Qed.
  Lemma is_itable2_pool (γl : gname) (cn : ic_names) (γfs : fs_names)
      (γi : gname) (cov : gset Z) (logstart : Z) (nib : nat)
      (dv : mword 32) :
    is_itable2 γl cn γfs γi cov logstart nib dv -∗ ipool_inv cn γfs γi cov logstart nib.
  Proof. iIntros "(_ & _ & _ & $)". Qed.

  Lemma ic_escrows_lookup (cn : ic_names) (γfs : fs_names) (γi : gname)
      (cov : gset Z) (logstart : Z) (k : nat) :
    (k < NINODE)%nat ->
    ic_escrows cn γfs γi cov logstart -∗ ic_escrow cn γfs γi cov logstart k.
  Proof.
    iIntros (Hk) "H". rewrite /ic_escrows /ic_boxes_all /ic_escrow.
    assert (Hl : seq 0 NINODE !! k = Some k) by (rewrite lookup_seq; lia).
    iDestruct (big_sepL_lookup _ _ k k Hl with "H") as "$".
  Qed.

  Global Instance is_itable2_persistent γl cn γfs γi cov logstart nib dv :
    Persistent (is_itable2 γl cn γfs γi cov logstart nib dv).
  Proof. apply _. Qed.

  (* the slot accessor a WRITER needs: BOTH pure maps may come back changed,
     provided they changed only at [k].  [big_sepL_delete] over
     [seq 0 NINODE], with one more map to carry than
     [IcacheInv.live_pool_acc_upd]. *)
  Lemma islots2_acc_upd (cn : ic_names) (M : gmap nat (Qp * positive))
      (ci : gmap nat (mword 32 * mword 32)) (k : nat) :
    (k < NINODE)%nat ->
    ([∗ list] j ∈ seq 0 NINODE, islot2 cn M ci j) -∗
      islot2 cn M ci k ∗
      (∀ (M' : gmap nat (Qp * positive)) (ci' : gmap nat (mword 32 * mword 32)),
         ⌜forall j, j <> k -> M' !! j = M !! j⌝ -∗
         ⌜forall j, j <> k -> ci' !! j = ci !! j⌝ -∗
         islot2 cn M' ci' k -∗
         [∗ list] j ∈ seq 0 NINODE, islot2 cn M' ci' j).
  Proof.
    intros Hk. iIntros "Hs".
    iDestruct (big_sepL_delete _ (seq 0 NINODE) k k
                 ltac:(apply lookup_seq; split; [lia | exact Hk]) with "Hs")
      as "[Hslot Hrest]".
    iFrame "Hslot". iIntros (M' ci') "%HagM %Hagc Hslot".
    iApply (big_sepL_delete _ (seq 0 NINODE) k k
              ltac:(apply lookup_seq; split; [lia | exact Hk])).
    iFrame "Hslot".
    iApply (big_sepL_impl with "Hrest").
    iIntros "!>" (j x Hjx) "H".
    destruct (decide (j = k)) as [->|Hne]; [iExact "H" |].
    apply lookup_seq in Hjx as [Hx _].
    assert (Hxk : x <> k) by lia.
    iEval (rewrite /islot2) in "H".
    rewrite /islot2 (HagM x Hxk) (Hagc x Hxk). iExact "H".
  Qed.

  (* ================================================================== *)
  (*  6b.  EVERY ENTRY'S INODE SLEEPLOCK                                 *)
  (* ================================================================== *)

  (* The per-slot inode sleeplock family, in the shape
     [IcacheBoot.icache_alloc] hands it out.  iput names ONE slot's lock;
     a caller that cannot know which entry an [iget] will return -- dirlink,
     create, fileclose, and the whole namei walk -- takes the family, exactly
     as it takes [ic_escrows] rather than [ic_escrow].  Persistent, so it
     costs a caller nothing.

     IT LIVES HERE, and that placement is load-bearing rather than tidy.  It
     was defined TWICE, identically, in [SpecDirlink.v] and
     [SpecFileclose.v] -- two *function* specs -- and [FsReady.v] reached it
     by requiring the first.  That import is what put [ProcInv] in
     [fs_ready]'s dependency cone (SpecDirlink -> SpecWritei -> ProcInv,
     writei taking the process block for its user-memory copy), and hence
     what made the file system look as though it depended on process
     abstractions.  It does not: nothing below is process-shaped, and every
     ingredient -- [is_sleeplock_gen], [ic_tok], [ientry], [icfg_isl] -- is
     in scope one layer down from any spec.  A spec file must not own a
     definition the invariant layer needs; this is that rule applied. *)
  Definition ic_sleeplocks (cn : ic_names) : iProp Σ :=
    ([∗ list] k ∈ seq 0 NINODE,
       ∃ γil γisl : gname,
         is_sleeplock_genl γil γisl (i_lock (ientry k)) "inode"%string
                           (ic_slp cn k) (slh_tok (icfg_isl k)))%I.

  Global Instance ic_sleeplocks_persistent cn : Persistent (ic_sleeplocks cn).
  Proof. apply _. Qed.

  (* A BIG-OP UNDER A TRANSPARENT NAME IS AN [iFrame] BOMB (optimization.md,
     the [InodeInv.inode_blocks] entry): [iFrame]'s [Frame] search unfolds a
     transparent constant to get at the [big_sepL] underneath and then tries
     every candidate hypothesis against every one of its NINODE elements.
     This is the last-but-five conjunct of [FsReady.fs_ready_pre], so every
     frame that rebuilds that bundle paid for it -- [FirstTok]'s
     [first_persist_pre] was 5.6 s of one [iFrame], and 4.7 s of that was
     this constant alone (measured 2026-08-27 by sealing it and nothing
     else).  [Global], not bare: the bare form is compilation-local. *)
  Global Typeclasses Opaque ic_sleeplocks.

  (* ...AND ITS ACCESSOR.  This is the ONLY copy of either; every consumer
     projects the family through this lemma.  Do not restate it in a
     caller's own file -- seven files did, and retiring the seven is what
     made [IcacheBoot.v] stop being a second home for the family. *)
  Lemma ic_sleeplocks_lookup (cn : ic_names) (k : nat) :
    (k < NINODE)%nat ->
    ic_sleeplocks cn -∗
    ∃ γil γisl : gname,
      is_sleeplock_genl γil γisl (i_lock (ientry k)) "inode"%string
                        (ic_slp cn k) (slh_tok (icfg_isl k)).
  Proof.
    iIntros (Hk) "H". rewrite /ic_sleeplocks.
    assert (Hl : seq 0 NINODE !! k = Some k) by (rewrite lookup_seq; lia).
    iDestruct (big_sepL_lookup _ _ k k Hl with "H") as "$".
  Qed.

End IcacheTable.

(* ===================================================================== *)
(*  7.  ALLOCATION OF THE TOKEN FAMILIES                                  *)
(* ===================================================================== *)

Section IcacheEscrowAlloc.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ}.

  Local Lemma ic_seq_cons (j n : nat) : seq j (S n) = j :: seq (S j) n.
  Proof. reflexivity. Qed.

  (* GNAMES BEFORE THE RECORD (BioInv.tok_fun_alloc): [ic_names] cannot be
     built until every per-entry gname exists, and [ic_tok cn k] -- the
     resource each entry's sleeplock seals -- mentions [cn].  The way out is
     to allocate the tokens as a bare [nat -> gname] function first and
     assemble the record at the end, after which [ic_tok cn k] IS
     [lock_tok_excl (f k)] by construction. *)
  Lemma ic_tok_fun_alloc (n j : nat) :
    ⊢ |==> ∃ f : nat -> gname, [∗ list] k ∈ seq j n, lock_tok_excl (f k).
  Proof.
    iInduction n as [|n IH] forall (j).
    { iModIntro. iExists (fun _ => inhabitant). cbn [seq]. done. }
    iMod lock_tok_excl_alloc as (γ) "Hg".
    iMod ("IH" $! (S j)) as (f) "Hf".
    iModIntro. iExists (fun k => if decide (k = j) then γ else f k).
    rewrite ic_seq_cons. iSplitL "Hg".
    { case_decide as Hd; [iExact "Hg" | congruence]. }
    iApply (big_sepL_mono with "Hf"). intros i k Hk.
    apply lookup_seq in Hk as [-> _].
    case_decide as Hd; [exfalso; lia | done].
  Qed.

  (* the CHECKOUT DESCRIPTOR's family (§14.8), allocated the same way and at
     [DepNone]: at boot no entry is checked out, and a whole variable at the
     neutral descriptor IS [ic_tok].  It replaces the [lock_tok_excl] family
     the esc names used to be, and reuses [ic_id_fun_alloc]'s shape verbatim. *)
  Lemma ic_dep_fun_alloc (n j : nat) :
    ⊢ |==> ∃ f : nat -> gname,
      [∗ list] k ∈ seq j n, ghost_var (f k) 1 DepNone.
  Proof.
    iInduction n as [|n IH] forall (j).
    { iModIntro. iExists (fun _ => inhabitant). cbn [seq]. done. }
    iMod (ghost_var_alloc DepNone) as (γ) "Hg".
    iMod ("IH" $! (S j)) as (f) "Hf".
    iModIntro. iExists (fun k => if decide (k = j) then γ else f k).
    rewrite ic_seq_cons. iSplitL "Hg".
    { case_decide as Hd; [iExact "Hg" | congruence]. }
    iApply (big_sepL_mono with "Hf"). intros i k Hk.
    apply lookup_seq in Hk as [-> _].
    case_decide as Hd; [exfalso; lia | done].
  Qed.

  (* the IDENTIFICATION ghost's family (§13.8), allocated the same way and at
     [false]: at boot every entry is empty.  Each slot's variable comes out
     WHOLE, so the caller splits it into the escrow's half and the table's. *)
  Lemma ic_id_fun_alloc (dvs : nat -> mword 32 * mword 32) (n j : nat) :
    ⊢ |==> ∃ f : nat -> gname,
      [∗ list] k ∈ seq j n, ghost_var (f k) 1 (false, (dvs k).1, (dvs k).2).
  Proof.
    iInduction n as [|n IH] forall (j).
    { iModIntro. iExists (fun _ => inhabitant). cbn [seq]. done. }
    iMod (ghost_var_alloc (false, (dvs j).1, (dvs j).2)) as (γ) "Hg".
    iMod ("IH" $! (S j)) as (f) "Hf".
    iModIntro. iExists (fun k => if decide (k = j) then γ else f k).
    rewrite ic_seq_cons. iSplitL "Hg".
    { case_decide as Hd; [iExact "Hg" | congruence]. }
    iApply (big_sepL_mono with "Hf"). intros i k Hk.
    apply lookup_seq in Hk as [-> _].
    case_decide as Hd; [exfalso; lia | done].
  Qed.

  (* the whole layer's names, at a given reference authority: NINODE
     checkout tokens, NINODE recycle tokens and NINODE identification
     variables (all [false] -- every entry starts empty), all fresh. *)
  Lemma ic_names_alloc (dvs : nat -> mword 32 * mword 32) :
    ⊢ |==> ∃ cn : ic_names,
      ([∗ list] k ∈ seq 0 NINODE, ic_tok cn k) ∗
      ([∗ list] k ∈ seq 0 NINODE, ic_dep_neutral cn k) ∗
      ([∗ list] k ∈ seq 0 NINODE, ic_id cn k 1 false (dvs k).1 (dvs k).2).
  Proof.
    iMod (ic_dep_fun_alloc NINODE 0) as (fesc) "Hesc".
    iMod (ic_dep_fun_alloc NINODE 0) as (fdep) "Hdep".
    iMod (ic_id_fun_alloc dvs NINODE 0) as (fid) "Hid".
    iModIntro. iExists (MkIcNames fesc fdep fid).
    rewrite /ic_tok /ic_dep_neutral /ic_id.
    cbn [icn_esc icn_dep icn_id].
    iFrame.
  Qed.

End IcacheEscrowAlloc.
