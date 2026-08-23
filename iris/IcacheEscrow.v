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
From iris.base_logic.lib Require Import gen_heap invariants own ghost_map ghost_var.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvPtsto RiscvExtras.
Require Import WpLock.
Require Import FsBlocks.
Require Import DinodeEnc.
Require Import DirView.
Require Import DirLinks.
Require Import FsTree.        (* [dir_uniq] -- the name-uniqueness payload clause *)
(* EXPORTED, not merely imported: [dv_ride] is a conjunct of [ipool_alloc] and
   [ic_loaded], so every file that destructs either one names it -- and its
   whole arm is [DirViewG]'s [dv_hold], so both leaves are exported. *)
Require Export DirViewG.
Require Export DirViewLend.  (* N-4 PHASE B: the custody chain rides the lend *)
Require Import InodeInv.
Require Import InodeLock.
Require Import SleepLock.  (* [is_sleeplock_gen] / [slh_tok] -- see [ic_sleeplocks] below *)
Require Import InodeRegion.
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

Local Open Scope Z_scope.

(* ===================================================================== *)
(*  0.  GHOST NAMES                                                       *)
(* ===================================================================== *)

(* the escrow layer's names, as one record (BioInv.bio_names' shape): the
   reference authority IcacheInv's lemmas take, and per slot the checkout
   token's gname and the recycle token's gname.  The itable spinlock's own
   gname stays a separate argument, exactly as [is_itable] takes it. *)
Record ic_names := MkIcNames {
  icn_esc : nat -> gname;   (* entry k's CHECKOUT token                  *)
  icn_mid : nat -> gname;   (* entry k's RECYCLE token                   *)
  icn_id  : nat -> gname;   (* entry k's LIVE / EMPTY agreement          *)
}.

Section IcacheEscrow.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !irefslotG Σ}.
  Context `{GEN : GenId}.
  Context `{ICFG : icfg}.

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
  Proof. rewrite /word2_pointsto. apply _. Qed.

  Global Instance word2_pointsto_timeless' (ktr : ktier) (a : Arch.pa) (dq : dfrac) (w : bv 16) :
    Timeless (word2_pointsto (KTR := ktr) a dq w).
  Proof. exact (word2_pointsto_timeless ktr a dq w). Qed.

  Global Instance inode_meta_timeless (ip : mword 64) (d : dinode) :
    Timeless (inode_meta ip d).
  Proof. rewrite /inode_meta. apply _. Qed.

  Global Instance inode_addrs_timeless (ip : mword 64) (l : list (bv 32)) :
    Timeless (inode_addrs ip l).
  Proof. rewrite /inode_addrs. apply _. Qed.

  Global Instance inode_raw_timeless (ip : mword 64) : Timeless (inode_raw ip).
  Proof. rewrite /inode_raw. apply _. Qed.

  Global Instance ind_blk_timeless γfs bm : Timeless (ind_blk γfs bm).
  Proof. rewrite /ind_blk. case_decide; apply _. Qed.


  Global Instance ind_res_timeless γfs bm : Timeless (ind_res γfs bm).
  Proof. rewrite /ind_res. apply _. Qed.

  Global Instance blk_res_timeless γfs w bs : Timeless (blk_res γfs w bs).
  Proof. rewrite /blk_res. case_decide; apply _. Qed.

  Global Instance inode_blocks_timeless γfs bm data :
    Timeless (inode_blocks γfs bm data).
  Proof. rewrite /inode_blocks. apply _. Qed.

  (* full ownership of a 4-byte cell is exclusive AGAINST ANY FRACTION --
     which is what makes the FULL-versus-½ inum cell a discriminator.
     (BioInv and FileOff each carry a private copy; the real home is
     RiscvPtsto's [word4_pointsto] section, and moving it there is a
     whole-tree rebuild this additive file does not take.) *)
  Lemma ic_word4_excl (a : Arch.pa) (w1 w2 : bv 32) (dq : dfrac) :
    a ↦₄ w1 -∗ a ↦₄{dq} w2 -∗ False.
  Proof.
    iIntros "H1 H2".
    rewrite !word4_pointsto_unfold.
    iDestruct "H1" as "[_ H1]". iDestruct "H2" as "[_ H2]".
    change (seq 0 4) with ([0; 1; 2; 3]%nat).
    iDestruct "H1" as "[Hb1 _]". iDestruct "H2" as "[Hb2 _]".
    iDestruct (mem_pointsto_ne with "Hb1 Hb2") as %Hne.
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

  (* HALF the variable, at a concrete descriptor: one of these sits in the OUT
     arm and the other travels with the checked-out thread, from the checkout
     to the park. *)
  Definition ic_deposit (cn : ic_names) (k : nat) (d : ic_dep) : iProp Σ :=
    ghost_var (icn_esc cn k) (1/2) d.

  (* the recycle token (BioInv.bmid): parked in PARKED and OUT, in the
     recycler's hand during the MID window. *)
  Definition ic_mid (cn : ic_names) (k : nat) : iProp Σ :=
    lock_tok_excl (icn_mid cn k).

  Lemma ic_tok_exclusive cn k : ic_tok cn k -∗ ic_tok cn k -∗ False.
  Proof.
    rewrite /ic_tok. iIntros "H1 H2".
    iDestruct (ghost_var_valid_2 with "H1 H2") as %[Hv _].
    iPureIntro. by apply (Qp.not_add_le_l 1 1).
  Qed.

  (* ...and the WHOLE variable against a DEPOSITED half, which is what
     [ic_swap_checkout] refutes the checked-out arm with -- the same one line
     the old [lock_tok_excl] version used, now as fraction overflow. *)
  Lemma ic_tok_deposit_excl cn k d : ic_tok cn k -∗ ic_deposit cn k d -∗ False.
  Proof.
    rewrite /ic_tok /ic_deposit. iIntros "H1 H2".
    iDestruct (ghost_var_valid_2 with "H1 H2") as %[Hv _].
    iPureIntro. by apply (Qp.not_add_le_l 1 (1/2)).
  Qed.

  (* THE CHECKOUT'S GHOST STEP: the winner turns the sleeplock's variable into
     the descriptor of what it is about to deposit, and splits.  One half goes
     into the arm, the other travels with it. *)
  Lemma ic_dep_checkout cn k (d : ic_dep) :
    ic_tok cn k ==∗ ic_deposit cn k d ∗ ic_deposit cn k d.
  Proof.
    rewrite /ic_tok /ic_deposit. iIntros "H".
    iMod (ghost_var_update d with "H") as "H".
    iModIntro. iDestruct "H" as "[H1 H2]". iFrame.
  Qed.

  (* ...AND THE PARK'S: the two halves meet, AGREE (which is what selects the
     arm), rejoin and go back to the neutral descriptor, ready for
     releasesleep. *)
  Lemma ic_dep_park cn k (d1 d2 : ic_dep) :
    ic_deposit cn k d1 -∗ ic_deposit cn k d2 ==∗ ⌜d1 = d2⌝ ∗ ic_tok cn k.
  Proof.
    rewrite /ic_deposit /ic_tok. iIntros "H1 H2".
    iDestruct (ghost_var_agree with "H1 H2") as %<-.
    iMod (ghost_var_update_halves DepNone with "H1 H2") as "[H1 H2]".
    iModIntro. iSplitR; [done |].
    iCombine "H1 H2" as "H". iExact "H".
  Qed.

  Lemma ic_deposit_agree cn k d1 d2 :
    ic_deposit cn k d1 -∗ ic_deposit cn k d2 -∗ ⌜d1 = d2⌝.
  Proof. rewrite /ic_deposit. iIntros "H1 H2". by iApply (ghost_var_agree with "H1 H2"). Qed.

  Lemma ic_mid_exclusive cn k : ic_mid cn k -∗ ic_mid cn k -∗ False.
  Proof. apply lock_tok_excl_exclusive. Qed.

  Global Instance ic_tok_timeless cn k : Timeless (ic_tok cn k).
  Proof. rewrite /ic_tok. apply _. Qed.
  Global Instance ic_deposit_timeless cn k d : Timeless (ic_deposit cn k d).
  Proof. rewrite /ic_deposit. apply _. Qed.
  Global Instance ic_mid_timeless cn k : Timeless (ic_mid cn k).
  Proof. rewrite /ic_mid. apply _. Qed.

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
  Proof. rewrite /ic_id. apply _. Qed.

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

     ...AND ITS RESOURCE TWIN (§20.3, stage B).  [DirLinks.dir_links] rides
     BESIDE [dir_ok], not inside it: one ledger fragment per live non-self
     record, in one of the two colours [ilink]/[igrey].  [dir_ok] says the
     named inum is IN RANGE; the twin says it is ALLOCATED, which is a fact
     about another inum's REGION record and therefore cannot be a [Prop]
     over [data] (§20.1, §20.9(a)).  No arity moves -- the colour
     disjunction is inside [dir_link_at] -- and both fragments are timeless,
     so the [Timeless] instance below survives verbatim.

     ...AND THE ".." INDEX CLAUSE (fs-icache §20.17.4, fs-fragments R9).
     [DirView.dir_dots_ix]: a LIVE directory ([T_DIR] and [nlink <> 0]) has
     at least two records and its record 1 is the live [".."].  It is what
     lets S7 name the one [ilink dp] it must convert -- [dir_link_at] is
     keyed by record INDEX and is name-blind, so without it nothing says
     WHICH ticket in a child's [dir_links] is the parent's.  It rides HERE,
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
     [DirLinks.dir_links_unlink]'s home-live premise. *)
  Definition ipool_alloc (γfs : fs_names) (γi : gname) (cov : gset Z)
      (logstart : Z) (inum : mword 32) : iProp Σ :=
    (∃ (dn0 : dinode) (bm0 : blkmap) (data0 : nat -> list (bv 8)),
       ⌜inode_ok cov logstart dn0 bm0 data0⌝ ∗
       ⌜dir_ok icfg_nib dn0 data0⌝ ∗
       ⌜dir_dots_ix (bv_unsigned inum) dn0 data0⌝ ∗
       ⌜dir_orphan_clean dn0 data0⌝ ∗
       ⌜dir_uniq dn0 data0⌝ ∗
       dir_links (bv_unsigned inum) dn0 data0 ∗
       dinode_at γi inum dn0 ∗
       ind_res γfs bm0 ∗
       inode_blocks γfs bm0 data0 ∗
       (* ...AND THE CONTENTS HOLD, TIED (namei-pinned-lookup.md §9 W2).  The
          tie is DEFINITIONAL (Revision 1): the abstract entry map is a
          function of the record and the bytes this arm already owns, so the
          conjunct is a value and not a guarded claim.  Of a FILE the value is
          determined garbage; no client reads it and no site proves anything
          about it. *)
       dv_ride (bv_unsigned inum) (dv_of dn0 data0) ∗
       (* ...AND ITS PER-FILE TWIN (namei-pinned-lookup.md §13, N-5.2A),
          beside it and tied the same way.  Of a DIRECTORY this value is
          determined garbage exactly as [dv_of] is of a file: neither ghost
          is type-guarded, and every byte-write re-pack moves BOTH by one
          [InodeRegion.dvw_set_rt] (D-52b). *)
       fv_ride (bv_unsigned inum) (fv_of dn0 data0))%I.

  (* OPTION A: the NON-PENDING (Timeless) pool shape -- the ORIGINAL two-arm
     shape, unchanged.  It is what the escrow's parked bundle [ic_unloaded]
     carries, so the escrow (and the whole loaded/unloaded/evict/fill/recycle
     lifecycle) is untouched.  [reg_full] does NOT ride here: it lives in the
     [regN] invariant, borrowed by [ireg_claim_au]'s callers. *)
  Definition ipool_shape_np (γfs : fs_names) (γi : gname) (cov : gset Z)
      (logstart : Z) (inum : mword 32) : iProp Σ :=
    (ipool_alloc γfs γi cov logstart inum
     ∨ (imark γi (bv_unsigned inum) ∗
        (* the MARKER arm has no bytes, so it carries the hold UNTIED
           (namei-pinned-lookup.md §9 W2): a tied->untied peel forgets the
           value, and the fill that re-ties it [dv_set]s to the fresh
           record's own [dv_of]. *)
        (∃ e, dv_ride (bv_unsigned inum) e) ∗
        (∃ b, fv_ride (bv_unsigned inum) b)))%I.

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
  (* ...AND THE CONTENTS HOLD, UNTIED, for [pool_pending]'s reason verbatim:
     this arm is byte-less, and the peel that turns it into an [imark] must
     find the inum's [dv_ride] somewhere. *)
  Definition pool_await (γi : gname) (z : Z) : iProp Σ :=
    (∃ ge gr gd (rg : bool),
       escA_inv ge gr gd γi z rg ∗ redeem_ticketA gr ∗
       (∃ e, dv_ride z e) ∗ (∃ b, fv_ride z b))%I.

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
  Definition ipool_shape (γfs : fs_names) (γi : gname) (cov : gset Z)
      (logstart : Z) (inum : mword 32) : iProp Σ :=
    (icnt_half (bv_unsigned inum) 0%nat ∗
     (* THE FREEZE MIRROR's UNCACHED HALF (iclaim-ledger.md §3.16), beside
        the count half and for its reason verbatim: the pool's domain is the
        complement of the live arms' inums, so one half per pool entry is one
        half per uncached inum.  The value is the literal [false] on all
        three arms: [FrzOff] on the two ordinary ones and [FrzPost] on the
        await arm, and [ireg_frzm_ok] is down at both. *)
     frzm_h (bv_unsigned inum) false ∗
     (ipool_shape_np γfs γi cov logstart inum ∗ ifreeze_off (bv_unsigned inum)
      (* THE PENDING ARM's TOKEN MOVED INTO ITS ESCROW (A⁗, §3.16): the
         off-lock deposit hands the retired [ifreeze_off] to
         [EscrowInode.escA_deposit_acc], which parks it in the escrow's FILLED
         state, and [escA_redeem] gives it to whoever converts this entry to
         an [imark].  Two copies of one exclusive ledger cell is not a
         choice -- and the placement is what lets the AWAIT arm below carry
         the STANDING freeze in the same escrow, which is the refuter §1.3
         always wanted. *)
      ∨ pool_pending γi (bv_unsigned inum)
      ∨ pool_await γi (bv_unsigned inum)))%I.

  (* OPTION A (b)(ii): turn a pending-CAPABLE pool shape into the Timeless
     [ipool_shape_np] the escrow's unloaded arm needs, REDEEMING a genuine
     pending entry to its [imark] pool-locally.  This is what lets the iget
     recycle and the ilock fill convert [ipool_acc]'s full shape without the
     region invariant.  Walk-stable: it discharges real deposits, not just the
     flip-gate's empty pool.

     THE AWAIT CASE (§1.3) IS A REFUTATION, NOT A CONVERSION, and the licence
     premise §1.3 asks for is spelled here as [ifreeze_off]: the caller of a
     fill or a recycle at this inum presents the inum's "right to freeze", the
     parked arm holds the freer's [ifreeze_post], and the two are one
     exclusive ledger cell ([IcacheRef.ifreeze_excl]).  The token goes back
     out untouched on every arm, so the premise costs a caller nothing beyond
     having it -- which, per §2.9's third honest risk, is new plumbing the
     iget/ilock cone owns (increment 4).

     ---- WHY THE PREMISE CHANGES SHAPE IN INCREMENT IIIa (recorded) ------

     Increment II spelled §1.3's "caller's licence" as a caller-held
     [ifreeze_off].  That spelling is no longer AVAILABLE to a caller: since
     the pool is now where an uncached inum's freeze token lives, a second
     copy in the caller's hand would collide with the pool's own on the two
     ordinary arms ([ifreeze_excl] does not care that both are [FrzOff]), and
     the lemma would be vacuous rather than usable.  So the premise is
     restated as the REFUTATION it was only ever used for --
     [ipool_await_refuter], i.e. "no [ifreeze_post] stands at this inum".
     It is strictly WEAKER than II's version ([ipool_await_refuter_off] is
     the one-line derivation from an [ifreeze_off] a caller does hold, e.g.
     a CACHED-side mover's), it keeps §1.3's discharge exactly as II proved
     it, and it leaves the real §2.6 argument -- a licence's [nlink <> 0]
     against the freeze pin's [nlink = 0] -- as the discharge increment 4
     will supply at the two call sites (ProofIget, ProofIlock).

     WHAT COMES OUT is now the pool's own [icnt] half and [ifreeze_off]
     alongside the [ipool_shape_np]: the recycler that takes an inum OUT of
     the pool takes its uncached ledger resources with it, which is exactly
     the pair [IcacheInv.iref_upgrade_store_au] then consumes (count 0 -> 1
     under the standing [FrzOff] pin). *)
  (* ---- THE REFUTER IS DELETED (iclaim-ledger.md §3.1, A-refuter) -------

     IIIa's [ipool_await_refuter z := ifreeze_post z -* False] is gone, and
     its deletion was FORCED rather than chosen.  IIIb proved the shape
     unbuildable at BOTH call sites: at the recycle (ProofIget +0x6a) the
     inum is uncached and its one token is inside the very bundle being
     peeled, so [ipool_await_refuter_off] cannot fire; and the licence route
     -- the one §1.3 always intended -- cannot fire either, because a bare
     wand into [False] is not producible from an [ireg_inv] opening ( that
     opening is a fupd, and [(|={E}=> False)] does not entail [False] ).

     The RULING was to change the shape of the premise, not its discharge.
     So the peel now takes the borrowed licence and the region invariant,
     and does the refutation INSIDE its own fupd, through
     [IgetLic.iname_freeze_off] -- §2.6's table, at whichever of the five
     licences the caller presented.  The licence comes back out.  Both call
     sites (ProofIget's recycle, ProofIlock's fill) run under an iget/ilock
     contract that carries one, which is what §2.9's third honest risk
     priced. *)
  (* A NESTED SECTION, and it costs the file nothing: [ireg_inv] carries
     [InodeRegion.ireg_ep]'s log-epoch lower bound, so naming it needs
     [Xv6Cameras.logG] -- a class this file's outer context deliberately does
     not have (the escrow itself never mentions the log).  Adding it to the
     outer [Section IcacheEscrow] would put an instance argument on all
     ~120 of its lemmas; a nested section puts it on this one. *)
  Section PoolPeelLic.
    (* QUALIFIED, and that is load-bearing: this file does not [Require
       Import LogInv], so a bare [!logG Σ] would silently generalise a NEW
       variable of that name instead of the class (the trap IcacheInv's
       preamble records), and every use of [ireg_inv] below would then fail
       to find the real instance. *)

  Lemma ipool_shape_to_np E γfs γi (inodestart : Z) (nib : nat)
      cov logstart (inum : mword 32) (l : ilic) :
    ↑escAN (bv_unsigned inum) ⊆ E ->
    ↑iregN ⊆ E ->
    (* ...AND STILL INSIDE the escrow's own opening (§3.16): the await arm's
       refutation runs at the region while [escAN inum] is held, so the two
       namespaces must be disjoint at the call site.  They are, by
       construction -- see [icEscN]'s note. *)
    ↑iregN ⊆ E ∖ ↑escAN (bv_unsigned inum) ->
    bv_unsigned inum < 16 * Z.of_nat nib ->
    ireg_inv γi γfs inodestart nib -∗
    iname γi γfs inodestart inum l -∗
    ipool_shape γfs γi cov logstart inum ={E}=∗
    iname γi γfs inodestart inum l ∗
    ipool_shape_np γfs γi cov logstart inum ∗
    icnt_half (bv_unsigned inum) 0%nat ∗
    (* the MIRROR's uncached half rides out with the count half (§3.16): the
       recycler that takes an inum OUT of the pool takes its whole uncached
       ledger row, and [IcacheInv.iref_alloc_store_au] then parks the mirror
       in [islot2]'s live arm on its ordinary ([false]) alternative. *)
    frzm_h (bv_unsigned inum) false ∗
    ifreeze_off (bv_unsigned inum).
  Proof.
    iIntros (HE HER HERE Hin) "#Hrinv Hl H". rewrite /ipool_shape.
    iDestruct "H" as "[Hcnt [Hmir [[Hnp Hoff] | [Hpp | Haw]]]]".
    - iModIntro. iFrame "Hl Hnp Hcnt Hmir Hoff".
    - iDestruct "Hpp" as (ge gr gd rg) "(#Hesc & #Hcom & Htk & Hdv & Hfv)".
      iMod (escA_redeem E ge gr gd γi (bv_unsigned inum) rg HE with "Hesc Htk Hcom")
        as "[Hmk Hoff]".
      (* DISPATCH THE [ipool_shape_np] CONJUNCT BEFORE FRAMING ANYTHING
         (optimization.md, "A NAMED iFrame still pays a GOAL-side search").
         [ipool_shape_np] unfolds to [ipool_alloc ∨ imark], and [ipool_alloc]
         is an ∃ over a block-map big-op, so an [iFrame] that still has that
         conjunct in the goal tries all four named hypotheses against every
         one of its leaves: 83 s here and 91 s in the await arm below, the two
         most expensive statements in the tree after the assumption audit.
         Splitting it off first leaves a three-conjunct goal where the frame
         is syntactic. *)
      iModIntro. iSplitL "Hl"; [iExact "Hl"|].
      iSplitR "Hcnt Hmir Hoff".
      { rewrite /ipool_shape_np. iRight.
        iSplitL "Hmk"; [iExact "Hmk" |].
        iSplitL "Hdv"; [iExact "Hdv" | iExact "Hfv"]. }
      iFrame "Hcnt Hmir Hoff".
    - (* THE AWAIT ARM (§1.3, as A⁗ rebuilt it).  There is no [committedA]
         until the off-lock deposit runs, so the peel cannot redeem -- and
         must not: what the escrow holds before the deposit is the STANDING
         freeze, and the caller's LICENCE refutes it at the region.  After the
         deposit the escrow hands back the marker AND the re-armed
         [ifreeze_off], which is exactly the ordinary arm's token. *)
      iDestruct "Haw" as (ge gr gd rg) "(#Hesc & Htk & Hdv & Hfv)".
      iMod (escA_await_peel E ge gr gd γi (bv_unsigned inum) rg
              (iname γi γfs inodestart inum l) HE with "Hesc Htk Hl []")
        as "(Hl & Hmk & Hoff)".
      { iIntros "Hl Hpost". rewrite /ifreeze_post.
        iMod (iname_freeze_off (E ∖ ↑escAN (bv_unsigned inum))
                γi γfs inodestart nib inum l (FrzPost rg) HERE Hin
                with "Hrinv Hl Hpost") as "(%Hc & _ & _)".
        discriminate Hc. }
      (* same shape as the redeem arm above, same reason. *)
      iModIntro. iSplitL "Hl"; [iExact "Hl"|].
      iSplitR "Hcnt Hmir Hoff".
      { rewrite /ipool_shape_np. iRight.
        iSplitL "Hmk"; [iExact "Hmk" |].
        iSplitL "Hdv"; [iExact "Hdv" | iExact "Hfv"]. }
      iFrame "Hcnt Hmir Hoff".
  Qed.

  End PoolPeelLic.

  Global Instance ipool_alloc_timeless γfs γi cov logstart inum :
    Timeless (ipool_alloc γfs γi cov logstart inum).
  Proof. rewrite /ipool_alloc. apply _. Qed.

  Global Instance ipool_shape_np_timeless γfs γi cov logstart inum :
    Timeless (ipool_shape_np γfs γi cov logstart inum).
  Proof. rewrite /ipool_shape_np. apply _. Qed.

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

     THE DIRECTORY-WF CONJUNCT (§15(a)), the twin of [ipool_shape]'s: a
     parked DIRECTORY's live records all name inums the inode region
     covers.  This is what namex destructs out of ilock's postcondition,
     and it is the reason dirlookup's [dir_inums_ok] premise is
     dischargeable at a directory nobody named in advance.

     ...AND ITS RESOURCE TWIN (§20.3, stage B), the twin of [ipool_alloc]'s:
     [DirLinks.dir_links] over this record's own [data].  It is what
     dirlookup will hand [iget] as licence (a)/(b) in stage C, borrowed out
     of this payload at the matched index and returned before the holder's
     iunlock.  Every re-park in the landed tree carries it unchanged
     ([dir_links_eq]) because none of them changes a DIRECTORY's bytes.

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
       dir_links (bv_unsigned inum) dn data ∗
       dinode_at γi inum dn ∗
       inode_meta (ientry k) dn ∗
       inode_addrs (ientry k) (bm_cells bm) ∗
       ind_res γfs bm ∗
       inode_blocks γfs bm data ∗
       (* ...AND THE CONTENTS HOLD, TIED, the twin of [ipool_alloc]'s: see
          there.  A checked-out holder therefore owns the abstract contents
          outright while it owns the bytes, which is what makes every write
          mover a free [dv_set] and what N-3 lends at a walk's hop instants. *)
       dv_ride (bv_unsigned inum) (dv_of dn data) ∗
       (* ...AND ITS PER-FILE TWIN, the twin of [ipool_alloc]'s: see there. *)
       fv_ride (bv_unsigned inum) (fv_of dn data))%I.

  (* An UNLOADED entry's parked content: the cells at no particular value
     (iget minted the entry and nobody has read the dinode yet) plus the
     inum's pool bundle, parked here on its way past the recycler so that
     WHOEVER wins the sleeplock race finds what the fill needs. *)
  Definition ic_unloaded (γfs : fs_names) (γi : gname) (cov : gset Z)
      (logstart : Z) (k : nat) (inum : mword 32) : iProp Σ :=
    (inode_raw (ientry k) ∗ ipool_shape_np γfs γi cov logstart inum)%I.

  Global Instance ic_loaded_timeless γfs γi cov logstart k inum dn bm :
    Timeless (ic_loaded γfs γi cov logstart k inum dn bm).
  Proof. rewrite /ic_loaded. apply _. Qed.

  Global Instance ic_unloaded_timeless γfs γi cov logstart k inum :
    Timeless (ic_unloaded γfs γi cov logstart k inum).
  Proof. rewrite /ic_unloaded. apply _. Qed.

  (* THE PAYLOAD THE VALID WORD KEYS, AT THE SLOT'S GENERATION, AND THE
     GENERATION'S TYPE ONE-SHOT ON ITS TWO POLARITIES (design §17.3 (A) /
     §17.6, ratified §17.4 / §17.7).

     [ic_loaded] DOES NOT MOVE -- it is named in nineteen files and this is
     why none of them changed; the generation rides HERE, where three files
     name it, and so does the witness: [ity_shot g (di_type dn)] on the
     LOADED polarity, [ity_pending g] on the UNLOADED one.

     WHY THE PENDING RIDES HERE AND NOT ONE LEVEL DOWN.  §17.3 (B) put it
     with [ipool_shape]'s ALLOCATED disjunct, on the argument that "ilock's
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
     re-parks UNLOADED with a fresh pending.  [ipool_shape], [imark],
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
  Proof. rewrite /ic_payload_np. destruct v; apply _. Qed.

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
      the expensive one would also have poisoned [ic_close_to_empty_await],
      whose payload is the FREEZER's (its token is standing at [FrzPost],
      not [FrzOff]); with the split, that lemma keeps its exact signature by
      speaking at [_np].

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
  Proof. rewrite /ic_payload. apply _. Qed.

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

  (* ---- THE PARKED ARM's TOKEN SLOT (iclaim-ledger.md §3.14 as built) ----

     DEVIATION 1 (§3.10) left the parked arm carrying [ifreeze_off], and
     A‴ asks for it to carry [(ifreeze_off ∨ ifreeze_pre)] so that iput's
     mid-free park at +0x70 -- which happens INSIDE the freeze window -- has
     somewhere to put the phase the mint left standing.  What lands here is
     that widening with the RIGHT arm's content changed, and the change is
     what makes the +0x8a re-open decidable:

       [ifreeze_off z ∨ frzown z]

     The free path does NOT park its [ifreeze_pre]; it keeps that in hand
     from the mint at +0x50 all the way to the last close at +0x8a (a pure
     ghost, untouched by the escrow choreography) and parks the RECEIPT
     [InodeRegion]'s slot lent it instead.  So when [ic_open_auth_ref] hands
     the arm back at +0x8a, the left disjunct dies on [IcacheRef.ifreeze_excl]
     against the token still in the freezer's hand -- one line, no region
     open, no licence.  Had the arm carried [ifreeze_pre] the freezer would
     have had nothing left to decide the disjunction WITH.

     WHAT IT COSTS A CHECKOUT.  [ic_swap_checkout] now hands the holder
     [ic_payload_arm] rather than [ic_payload], so ilock owes the refutation
     of the [frzown] arm -- which its licence pays for
     ([IgetLic.iname_not_frozen] puts the column at [FrzOff], at which the
     region's own clause holds the receipt, and [frzown_excl] closes it).
     That is ProofIlock's item and is recorded there.  Every other consumer
     of [ic_payload] is unmoved: [ic_swap_park], [ic_parked_intro],
     [ic_close_mid_to_parked] and [ic_payload_at_pack] keep their exact
     signatures and take the LEFT arm internally. *)
  Definition ic_frz_park (z : Z) : iProp Σ :=
    (ifreeze_off z ∨ frzown z)%I.

  Global Instance ic_frz_park_timeless z : Timeless (ic_frz_park z).
  Proof. rewrite /ic_frz_park. apply _. Qed.

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
         the RIGHT arm, which its licence pays for
         ([IgetLic.iname_not_frozen] puts the column at [FrzOff], at which
         the region's own receipt clause holds [frzown] and
         [IcacheRef.frzown_excl] closes it) -- DEVIATION 1's obligation,
         unchanged in kind, recorded at ProofIlock.
     Every LEFT-only consumer ([ic_payload], [ic_mk_parked], [ic_swap_park],
     [ic_close_to_empty]) keeps its exact signature. *)
  Definition ic_payload_arm (γfs : fs_names) (γi : gname) (cov : gset Z)
      (logstart : Z) (k : nat) (inum : mword 32) (g : gname)
      (v : bool) : iProp Σ :=
    ((ic_payload_np γfs γi cov logstart k inum g v
      ∗ ifreeze_off (bv_unsigned inum)
      ∗ live_gen k (1/2) g)
     (* RULING R-e (iclaim-ledger.md §5⁗⁗): the frozen alternative carries the
        SELECTOR's quarter beside the receipt.  That quarter is what turns
        ProofIlock:2422 from an unpayable obligation into one line: with it
        and the live slice inside the deposit [ic_swap_checkout] hands back,
        [IcacheInv.frz_slot_kill] closes -- no lock, no licence, no region
        open, no index. *)
     ∨ (frzown (bv_unsigned inum) ∗ frzsel k ((1/2)/2)%Qp true))%I.

  Global Instance ic_payload_arm_timeless γfs γi cov logstart k inum g v :
    Timeless (ic_payload_arm γfs γi cov logstart k inum g v).
  Proof. rewrite /ic_payload_arm. apply _. Qed.

  (* the ordinary holder's bundle + the arm's liveness half IS an arm's tail,
     on its LEFT alternative *)
  Lemma ic_payload_to_arm γfs γi cov logstart k inum g v :
    ic_payload γfs γi cov logstart k inum g v -∗
    live_gen k (1/2) g -∗
    ic_payload_arm γfs γi cov logstart k inum g v.
  Proof.
    rewrite /ic_payload /ic_payload_arm.
    iIntros "[H Ht] Hl". iLeft. iFrame.
  Qed.

  (* ...and the FROZEN alternative, which is the receipt alone *)
  Lemma ic_payload_arm_frz γfs γi cov logstart k inum g v :
    frzown (bv_unsigned inum) -∗ frzsel k ((1/2)/2)%Qp true -∗
    ic_payload_arm γfs γi cov logstart k inum g v.
  Proof. rewrite /ic_payload_arm. iIntros "H Hs". iRight. iFrame. Qed.

  (* THE DECIDER at the free path's two readers (+0x70, +0x8a): the
     [ifreeze_pre] the walk has kept in hand since the mint kills the LEFT
     alternative outright ([ifreeze_excl] -- one exclusive ledger cell, two
     fragments), so what comes back is the receipt. *)
  Lemma ic_payload_arm_decide_frz γfs γi cov logstart k inum g v (rg : bool) :
    ifreeze_pre rg (bv_unsigned inum) -∗
    ic_payload_arm γfs γi cov logstart k inum g v -∗
    ifreeze_pre rg (bv_unsigned inum) ∗ frzown (bv_unsigned inum) ∗
    frzsel k ((1/2)/2)%Qp true.
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
  Proof. rewrite /ic_payload_at. apply _. Qed.

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
  Lemma ic_payload_at_pack γfs γi cov logstart k inum g dn bm :
    ic_payload_at γfs γi cov logstart k inum g dn bm -∗
    ifreeze_off (bv_unsigned inum) -∗
    ic_payload γfs γi cov logstart k inum g true.
  Proof.
    iIntros "H Ht". iApply (ic_payload_join with "[H] Ht").
    iApply (ic_payload_at_pack_np with "H").
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  3.  THE THREE ARMS                                                 *)
  (* ------------------------------------------------------------------ *)

  (* THE ARM-RESIDENT LIVENESS SLICE (design §17.3 (A), ratified §17.4).
     A live slot's unit is [qt] (holders) + 1/2 (HERE) + (1/2 - qt) (the
     table), and the 1/2 names the slot's GENERATION -- the same one the
     payload is stated at, because one existential binds both.  §17.2 put
     the 1/2 in [ic_loaded], i.e. in the checked-out thread's hand, and that
     kills [ic_open_auth_ref]'s REF-1 refutation of the OUT/[DepShr] arm:
     the live mass in hand drops from [q + (1-q) + s] to [1/2 + s], which is
     satisfiable.  In the ARM it is the exact complement again.

     The 1/2 travels PARKED -> OUT (inside [ic_dep_res], at the descriptor's
     generation) -> PARKED, and PARKED -> the closer's hand -> the free unit
     at the last close.  It is NOT in [ic_mid_arm] or [ic_held]: both are
     windows ONE thread holds exclusively between two stores, the 1/2 is in
     that thread's hand across them, and no opener's refutation of either
     arm uses liveness (both are refuted by a FULL [i_inum] cell). *)
  Definition ic_parked (cn : ic_names) (γfs : fs_names) (γi : gname)
      (cov : gset Z) (logstart : Z) (k : nat) : iProp Σ :=
    (∃ (dev inum : mword 32) (v : bool) (g : gname),
       i_dev (ientry k) ↦₄{DfracOwn (1/2)} dev ∗
       i_inum (ientry k) ↦₄{DfracOwn (1/2)} inum ∗
       i_valid (ientry k) ↦₄ valid_word v ∗
       (* THE TAIL (A⁗, §3.16): the payload + token + the arm's liveness
          half, OR the free path's frozen park -- the receipt alone.  The
          [live_gen] conjunct that used to stand here is inside the LEFT
          alternative; see [ic_payload_arm]. *)
       ic_payload_arm γfs γi cov logstart k inum g v ∗
       ic_mid cn k ∗
       ic_id cn k (1/2) true dev inum)%I.

  (* WHAT A DESCRIPTOR SAYS THE ARM IS HOLDING (design §14.8).  The two live
     shapes are the two entries into a critical section:

       DepRef -- iput's authority-side window exit, which deposits its WHOLE
                 reference (count fragment, liveness slice and identity
                 fraction) and takes it back at the park;
       DepShr -- ilock's checkout under SpecIlock v3, whose caller holds only
                 a SHARE (no count fragment exists for it: [positiveR] has no
                 zero, design §14.5).

     [DepNone] is [False] here: it is the sleeplock's neutral value, and a
     checked-out arm is by construction not neutral.  The descriptor carries
     the identity it was taken at, which is what makes the park's
     [ghost_var_agree] pin dev/inum with no cell agreement at all -- and what
     retires SpecIunlock's and fileread's postcondition existentials. *)
  (* WHAT THE DEPOSITOR PUT IN, at the descriptor's own generation.  The
     slice is NAMED here (rather than [inode_ref] / [inode_shr]'s existential
     form) for one reason: the checkout has to pin the ARM's 1/2 to the
     depositor's generation, and [live_gen_agree] needs both sides named.
     [SpecIlock]'s precondition therefore states the share generation-named
     too -- mechanically, since a caller reaches it by destructing the
     existential its [inode_shr] already carries. *)
  Definition ic_dep_own (k : nat) (d : ic_dep) (dev inum : mword 32) : iProp Σ :=
    match d with
    | DepNone => False%I
    | DepRef q dv nu g =>
        (⌜dv = dev /\ nu = inum⌝ ∗ inode_ref_gen_bare k q dev inum g)%I
    | DepShr s dv nu g =>
        (⌜dv = dev /\ nu = inum⌝ ∗ inode_shr_gen_bare k s dev inum g)%I
    (* the FROZEN window (IVd) holds no ordinary deposit at all -- see
       [ic_out_frz], which is what its arm holds instead *)
    | DepFrz _ _ _ => False%I
    end.

  (* ...and the ARM's OWN 1/2, which the checkout takes out of PARKED and the
     park puts back (design §17.3 (A)).  [ic_out]'s text does not move
     because the slice rides here. *)
  Definition ic_dep_half (k : nat) (d : ic_dep) : iProp Σ :=
    match d with
    | DepNone => False%I
    | DepRef _ _ _ g => live_gen k (1/2) g
    | DepShr _ _ _ g => live_gen k (1/2) g
    | DepFrz _ _ _ => False%I
    end.

  Definition ic_dep_res (k : nat) (d : ic_dep) (dev inum : mword 32) : iProp Σ :=
    (ic_dep_own k d dev inum ∗ ic_dep_half k d)%I.

  Global Instance ic_dep_own_timeless k d dev inum :
    Timeless (ic_dep_own k d dev inum).
  Proof. rewrite /ic_dep_own. destruct d; apply _. Qed.

  Global Instance ic_dep_half_timeless k d :
    Timeless (ic_dep_half k d).
  Proof. rewrite /ic_dep_half. destruct d; apply _. Qed.

  Global Instance ic_dep_res_timeless k d dev inum :
    Timeless (ic_dep_res k d dev inum).
  Proof. rewrite /ic_dep_res. apply _. Qed.

  (* the descriptor's generation is the one its slice names -- the bridge
     between the pure [IcacheRef.ic_dep_gname] side condition every swap
     lemma carries and the resource. *)
  Lemma ic_dep_half_gname k d :
    ic_dep_half k d -∗
    ∃ g : gname, ⌜ic_dep_gname d = Some g⌝ ∗ live_gen k (1/2) g.
  Proof.
    rewrite /ic_dep_half /ic_dep_gname.
    destruct d as [| q dv nu g | s dv nu g | qf dv nu];
      [iIntros "[]" | | | iIntros "[]"];
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
    destruct d as [| q dv nu g | s dv nu g | qf dv nu];
      [iIntros "[]" | | | iIntros "[]"].
    - iIntros "[%Heq (Hfr & Hlv & Hid)]". iExists q. iFrame "Hid".
      iIntros "Hid". iSplitR; [iPureIntro; exact Heq |].
      rewrite /inode_ref_gen. iFrame.
    - iIntros "[%Heq [Hid Hlv]]". iExists s. iFrame "Hid".
      iIntros "Hid". iSplitR; [iPureIntro; exact Heq |].
      rewrite /inode_shr_gen. iFrame.
  Qed.

  Lemma ic_dep_res_ident k d dev inum :
    ic_dep_res k d dev inum -∗
    ∃ f : Qp,
      inode_ident k (DfracOwn f) dev inum ∗
      (inode_ident k (DfracOwn f) dev inum -∗ ic_dep_res k d dev inum).
  Proof.
    rewrite /ic_dep_res. iIntros "[Hown Hhalf]".
    iDestruct (ic_dep_own_ident with "Hown") as (f) "[Hid Hback]".
    iExists f. iFrame "Hid". iIntros "Hid". iFrame "Hhalf".
    iApply ("Hback" with "Hid").
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
    destruct d as [| q dv nu g | s dv nu g | qf dv nu];
      [iIntros "[[] _]" | | | iIntros "[[] _]"].
    - iIntros "[Hown Hhalf]". iExists (1/2)%Qp.
      iSplitL "Hhalf"; [iExists g; iExact "Hhalf" |].
      iIntros "[%g2 Hhalf]".
      iDestruct "Hown" as "[%Heq (Hfr & Hlv & Hid)]".
      iDestruct (live_gen_agree with "Hlv Hhalf") as %<-.
      iFrame "Hhalf". iSplitR; [iPureIntro; exact Heq |].
      rewrite /inode_ref_gen. iFrame.
    - iIntros "[Hown Hhalf]". iExists (1/2)%Qp.
      iSplitL "Hhalf"; [iExists g; iExact "Hhalf" |].
      iIntros "[%g2 Hhalf]".
      iDestruct "Hown" as "[%Heq [Hid Hlv]]".
      iDestruct (live_gen_agree with "Hlv Hhalf") as %<-.
      iFrame "Hhalf". iSplitR; [iPureIntro; exact Heq |].
      rewrite /inode_shr_gen. iFrame.
  Qed.

  (* the depositor's OWN slice, named -- what the checkout agrees against *)
  Lemma ic_dep_own_live k d dev inum :
    ic_dep_own k d dev inum -∗
    ∃ (s : Qp) (g : gname), ⌜ic_dep_gname d = Some g⌝ ∗ live_gen k s g ∗
      (live_gen k s g -∗ ic_dep_own k d dev inum).
  Proof.
    rewrite /ic_dep_own /ic_dep_gname.
    destruct d as [| q dv nu g | s dv nu g | qf dv nu];
      [iIntros "[]" | | | iIntros "[]"].
    - iIntros "[%Heq (Hfr & Hlv & Hid)]". iExists q, g. iSplitR; [done |].
      iFrame "Hlv". iIntros "Hlv". iSplitR; [iPureIntro; exact Heq |].
      rewrite /inode_ref_gen. iFrame.
    - iIntros "[%Heq [Hid Hlv]]". iExists s, g. iSplitR; [done |].
      iFrame "Hlv". iIntros "Hlv". iSplitR; [iPureIntro; exact Heq |].
      rewrite /inode_shr_gen. iFrame.
  Qed.

  Lemma ic_dep_half_intro k d g :
    ic_dep_gname d = Some g -> live_gen k (1/2) g -∗ ic_dep_half k d.
  Proof.
    rewrite /ic_dep_gname /ic_dep_half.
    destruct d as [| q dv nu g2 | s dv nu g2 | qf dv nu]; intros H;
      [discriminate | | | discriminate];
      injection H as <-; iIntros "$".
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
     conjunct, read with [word4_pointsto_agree] exactly as there.  It is a
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
    | DepFrz qf dv nu =>
        (⌜dv = dev /\ nu = inum⌝ ∗
         iref_frag k qf ∗
         inode_ident k (DfracOwn qf) dev inum ∗
         frzown (bv_unsigned inum) ∗
         (* RULING R-e: the selector's quarter rides the DepFrz window too --
            it is the same quarter, moving from the mint through the OUT arm
            to [ic_parked]'s frozen tail at the +0x70 park. *)
         frzsel k ((1/2)/2)%Qp true)%I
    | _ => False%I
    end.

  Global Instance ic_out_frz_timeless k d dev inum :
    Timeless (ic_out_frz k d dev inum).
  Proof. rewrite /ic_out_frz /inode_ident. destruct d; apply _. Qed.

  Definition ic_out (cn : ic_names) (k : nat) : iProp Σ :=
    (∃ (d : ic_dep) (dev inum : mword 32),
       ic_deposit cn k d ∗
       (ic_dep_res k d dev inum ∨ ic_out_frz k d dev inum) ∗
       ic_mid cn k ∗
       ic_id cn k (1/2) true dev inum)%I.

  (* the recycle window.  The inum cell is FULL (the discriminator) and the
     valid word is an ARBITRARY stale value, decoupled from the payload's
     shape -- which is the whole reason this arm exists.  The dev cell is at
     HALF, exactly as in PARKED (§13.1e). *)
  Definition ic_mid_arm (cn : ic_names) (γfs : fs_names) (γi : gname)
      (cov : gset Z) (logstart : Z) (k : nat) : iProp Σ :=
    (∃ (dev inum w : mword 32),
       i_dev (ientry k) ↦₄{DfracOwn (1/2)} dev ∗
       i_inum (ientry k) ↦₄ inum ∗
       i_valid (ientry k) ↦₄ w ∗
       ic_unloaded γfs γi cov logstart k inum ∗
       ic_id cn k (1/2) true dev inum)%I.

  (* THE EMPTY ARM (§13.8, renamed by §13.9): the arm of every slot the
     table does not show LIVE -- the state of all fifty entries at boot, and
     what iput's last close leaves behind.  No payload at all -- no bundle
     and no [dinode_at], the record having gone home to the pool -- which is
     exactly what makes [dom ci = dom M] satisfiable at boot with [ci = ∅]
     and the pool holding every inum (§13.9).

     THE DEV CELL IS FULL, AND THAT IS NOT AN ACCIDENT.  It is the
     discriminator: every opener that must rule this arm out while holding a
     REFERENCE ([ic_swap_checkout], [ic_open_auth_ref]) holds a dev fraction
     through [inode_ident], and a fraction against a full cell is
     [ic_word4_excl].  §13.7 put the full dev cell on [islot2]'s
     identified-ref-0 arm, where it is unsatisfiable against [ic_parked]'s
     permanent half; here it is both satisfiable and load-bearing, and the
     table's never-identified share ([islot_empty]) is exactly the inum half
     that is left over.  The inum cell stays at HALF so that it remains the
     parked/mid discriminator alone (§13.1c) -- an empty arm and a parked one
     are told apart by DEV, never by inum. *)
  Definition ic_empty_arm (cn : ic_names) (k : nat) : iProp Σ :=
    (∃ (dev inum w : mword 32),
       i_dev (ientry k) ↦₄ dev ∗
       i_inum (ientry k) ↦₄{DfracOwn (1/2)} inum ∗
       i_valid (ientry k) ↦₄ w ∗
       inode_raw (ientry k) ∗
       ic_mid cn k ∗
       ic_id cn k (1/2) false dev inum)%I.

  (* THE AUTHORITY-SIDE WINDOW (§13.13).  [ic_mid_arm] with the payload
     removed and the recycle token parked -- and that pair of differences is
     the whole design:

       the payload is GONE from the arm because it is in the holder's hand,
       at the polarity the holder observed, which is the only way iput's
       [ip->valid] reading at +0x3c survives the [acquiresleep] at +0x50;

       [ic_mid] is PARKED here (unlike MID) so that iget's recycler, which
       carries it, refutes this arm with the line it already has.

     The [i_inum] cell is FULL, as in MID and for the same reason: it is what
     makes a concurrent [ic_swap_checkout] impossible.  Its extra half is the
     one the entering holder joins in from its own reference plus the table's
     retained share ([IcacheInv.islot_rest_join]'s arithmetic, ½ = q + (½−q)),
     and the exit splits it back three ways.  The valid word is at an
     ARBITRARY value [w] -- but only at HALF, the holder keeping the other.
     That half is not decoration: closing the window back at PARKED (the
     +0x44 nlink exit) needs the cell AT THE POLARITY OF THE PAYLOAD the
     holder carries, and a cell the arm owned WHOLE would hand its value back
     existentially bound -- §13.13's own failure, one level down.  A half
     leaves every existing refutation intact: [ic_word4_excl] kills a
     fraction with the FULL cell the parker and [ic_open_out] carry. *)
  Definition ic_held (cn : ic_names) (k : nat) : iProp Σ :=
    (∃ (dev inum w : mword 32),
       i_dev (ientry k) ↦₄{DfracOwn (1/2)} dev ∗
       i_inum (ientry k) ↦₄ inum ∗
       i_valid (ientry k) ↦₄{DfracOwn (1/2)} w ∗
       ic_mid cn k ∗
       ic_id cn k (1/2) true dev inum)%I.

  Definition ic_escrow_body (cn : ic_names) (γfs : fs_names) (γi : gname)
      (cov : gset Z) (logstart : Z) (k : nat) : iProp Σ :=
    (ic_parked cn γfs γi cov logstart k
     ∨ ic_out cn k
     ∨ ic_mid_arm cn γfs γi cov logstart k
     ∨ ic_empty_arm cn k
     ∨ ic_held cn k)%I.

  (* distinct from [IcacheInv.icacheN] (the ref words) and
     [InodeRegion.iregN] (the dinode blocks): an opener of this escrow may
     hold either of those open at the same instruction. *)
  Definition icEscN : namespace := nroot .@ "icesc".

  Definition ic_escrow (cn : ic_names) (γfs : fs_names) (γi : gname)
      (cov : gset Z) (logstart : Z) (k : nat) : iProp Σ :=
    inv icEscN (ic_escrow_body cn γfs γi cov logstart k).

  Global Instance ic_escrow_persistent cn γfs γi cov logstart k :
    Persistent (ic_escrow cn γfs γi cov logstart k).
  Proof. apply _. Qed.

  (* EVERY entry's escrow, as one persistent bundle.  ilock and iunlock name
     the ONE slot they were handed, but [iget]'s scan walks all fifty and
     opens whichever it stops at, so its contract cannot name a slot: the
     resource it takes is the whole family.  Persistent, so this costs a
     caller nothing beyond having allocated the layer. *)
  Definition ic_escrows (cn : ic_names) (γfs : fs_names) (γi : gname)
      (cov : gset Z) (logstart : Z) : iProp Σ :=
    ([∗ list] k ∈ seq 0 NINODE, ic_escrow cn γfs γi cov logstart k)%I.

  Global Instance ic_escrows_persistent cn γfs γi cov logstart :
    Persistent (ic_escrows cn γfs γi cov logstart).
  Proof. apply _. Qed.

  (* The arms' [Timeless]es are proven STRUCTURALLY -- one connective per
     step, [apply _] only at the leaves.  One monolithic [apply _] over an
     arm backtracks across the whole ∃/∗ tower: 2-3 s each, ~11 s of this
     file, for facts whose every leaf instance already exists.  Same rule as
     [FileOff.off_body_timeless]; see optimization.md.

     THE DISPATCH MUST BE SYNTACTIC, i.e. a [lazymatch] on the goal and NOT
     a [first [apply bi.sep_timeless | …]].  [apply] unifies up to delta, so
     the [first] form peels straight THROUGH a named abstraction that
     already has its own instance -- through [ic_unloaded] into
     [ipool_shape]'s disjunction and [inode_blocks]' 268-element big-op --
     and then backtracks over all of it: measured 33 s and 42 s on
     [ic_mid_arm] and [ic_escrow_body], i.e. an order of magnitude WORSE
     than the monolithic [apply _] it replaced.  Matching [bi_sep]/[bi_or]/
     [bi_exist] as syntax stops at [ic_unloaded] and lets [apply _] use
     [ic_unloaded_timeless], which is the whole point. *)
  Local Ltac tl_struct :=
    lazymatch goal with
    | |- Timeless (bi_exist _) => apply bi.exist_timeless; intro; tl_struct
    | |- Timeless (bi_sep _ _) => apply bi.sep_timeless; [tl_struct | tl_struct]
    | |- Timeless (bi_or _ _) => apply bi.or_timeless; [tl_struct | tl_struct]
    | |- _ => apply _
    end.

  Global Instance ic_parked_timeless cn γfs γi cov logstart k :
    Timeless (ic_parked cn γfs γi cov logstart k).
  Proof. rewrite /ic_parked. tl_struct. Qed.

  Global Instance ic_out_timeless cn k : Timeless (ic_out cn k).
  Proof. rewrite /ic_out. tl_struct. Qed.

  Global Instance ic_mid_arm_timeless cn γfs γi cov logstart k :
    Timeless (ic_mid_arm cn γfs γi cov logstart k).
  Proof. rewrite /ic_mid_arm. tl_struct. Qed.

  Global Instance ic_empty_arm_timeless cn k : Timeless (ic_empty_arm cn k).
  Proof. rewrite /ic_empty_arm /inode_raw. tl_struct. Qed.

  Global Instance ic_held_timeless cn k : Timeless (ic_held cn k).
  Proof. rewrite /ic_held. tl_struct. Qed.

  Global Instance ic_escrow_body_timeless cn γfs γi cov logstart k :
    Timeless (ic_escrow_body cn γfs γi cov logstart k).
  Proof. rewrite /ic_escrow_body. tl_struct. Qed.

  (* ------------------------------------------------------------------ *)
  (*  THE ARMS' CONSTRUCTORS                                             *)
  (*                                                                     *)
  (*  A caller that has the pieces of an arm in hand must NOT assemble it *)
  (*  with [iExists …; iFrame]: framing searches the goal, and an arm's    *)
  (*  payload conjunct ([ic_payload] / [ic_unloaded]) is a disjunction of  *)
  (*  existentials over [inode_blocks]' 268-element big-op, re-searched    *)
  (*  once per hypothesis.  Measured at ProofIput's two close sites and    *)
  (*  ProofIget's re-tag: 172 s, 101 s and 48 s in three sentences.        *)
  (*  Assembled HERE instead, structurally and where the context is six    *)
  (*  hypotheses wide, it is free -- and a caller writes one [iApply].     *)
  (*  (optimization.md, BioInv's "split structurally and [iExact]".)       *)
  (* ------------------------------------------------------------------ *)
  Lemma ic_mk_parked_arm cn γfs γi cov logstart k (dev inum : mword 32)
      (v : bool) (g : gname) :
    i_dev (ientry k) ↦₄{DfracOwn (1/2)} dev -∗
    i_inum (ientry k) ↦₄{DfracOwn (1/2)} inum -∗
    i_valid (ientry k) ↦₄ valid_word v -∗
    ic_payload_arm γfs γi cov logstart k inum g v -∗
    ic_mid cn k -∗
    ic_id cn k (1/2) true dev inum -∗
    ic_parked cn γfs γi cov logstart k.
  Proof.
    iIntros "Hd Hn Hv Hp Hm Hg". rewrite /ic_parked. iExists dev, inum, v, g.
    iSplitL "Hd"; [iExact "Hd" |]. iSplitL "Hn"; [iExact "Hn" |].
    iSplitL "Hv"; [iExact "Hv" |]. iSplitL "Hp"; [iExact "Hp" |].
    iSplitL "Hm"; [iExact "Hm" | iExact "Hg"].
  Qed.

  Lemma ic_mk_parked cn γfs γi cov logstart k (dev inum : mword 32) (v : bool)
      (g : gname) :
    i_dev (ientry k) ↦₄{DfracOwn (1/2)} dev -∗
    i_inum (ientry k) ↦₄{DfracOwn (1/2)} inum -∗
    i_valid (ientry k) ↦₄ valid_word v -∗
    ic_payload γfs γi cov logstart k inum g v -∗
    live_gen k (1/2) g -∗
    ic_mid cn k -∗
    ic_id cn k (1/2) true dev inum -∗
    ic_parked cn γfs γi cov logstart k.
  Proof.
    iIntros "Hd Hn Hv Hp Hl Hm Hg".
    iDestruct (ic_payload_to_arm with "Hp Hl") as "Hp".
    iApply (ic_mk_parked_arm cn γfs γi cov logstart k dev inum v g
              with "Hd Hn Hv Hp Hm Hg").
  Qed.

  Lemma ic_mk_mid_arm cn γfs γi cov logstart k (dev inum w : mword 32) :
    i_dev (ientry k) ↦₄{DfracOwn (1/2)} dev -∗
    i_inum (ientry k) ↦₄ inum -∗
    i_valid (ientry k) ↦₄ w -∗
    ic_unloaded γfs γi cov logstart k inum -∗
    ic_id cn k (1/2) true dev inum -∗
    ic_mid_arm cn γfs γi cov logstart k.
  Proof.
    iIntros "Hd Hn Hv Hu Hg". rewrite /ic_mid_arm. iExists dev, inum, w.
    iSplitL "Hd"; [iExact "Hd" |]. iSplitL "Hn"; [iExact "Hn" |].
    iSplitL "Hv"; [iExact "Hv" |].
    iSplitL "Hu"; [iExact "Hu" | iExact "Hg"].
  Qed.

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
  Lemma ic_mk_loaded γfs γi cov logstart k (inum : mword 32)
      (dn : dinode) (bm : blkmap) (data : nat -> list (bv 8)) :
    inode_ok cov logstart dn bm data ->
    dir_ok icfg_nib dn data ->
    dir_dots_ix (bv_unsigned inum) dn data ->
    dir_orphan_clean dn data ->
    dir_uniq dn data ->
    dir_links (bv_unsigned inum) dn data -∗
    dinode_at γi inum dn -∗
    inode_meta (ientry k) dn -∗
    inode_addrs (ientry k) (bm_cells bm) -∗
    ind_res γfs bm -∗
    inode_blocks γfs bm data -∗
    dv_ride (bv_unsigned inum) (dv_of dn data) -∗
    fv_ride (bv_unsigned inum) (fv_of dn data) -∗
    ic_loaded γfs γi cov logstart k inum dn bm.
  Proof.
    intros Hok Hdok Hddix Hdoc Hduq. iIntros "Hl Hd Hm Ha Hr Hb Hv Hw".
    rewrite /ic_loaded.
    iExists data. iSplitR; [done |]. iSplitR; [done |]. iSplitR; [done |].
    iSplitR; [done |]. iSplitR; [done |].
    iSplitL "Hl"; [iExact "Hl" |]. iSplitL "Hd"; [iExact "Hd" |].
    iSplitL "Hm"; [iExact "Hm" |]. iSplitL "Ha"; [iExact "Ha" |].
    iSplitL "Hr"; [iExact "Hr" |].
    iSplitL "Hb"; [iExact "Hb" |].
    iSplitL "Hv"; [iExact "Hv" | iExact "Hw"].
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  4.  THE SWAPS AND THE OPENINGS                                     *)
  (* ------------------------------------------------------------------ *)

  (* (a) CHECKOUT, post-[acquiresleep] (BioInv.escrow_swap_checkout).

     The opener's [ic_tok] refutes OUT -- as fraction overflow against that
     arm's deposited half (§14.8), where v2 used [lock_tok_excl]'s
     exclusivity.  Its DEPOSIT's inum-cell fraction refutes MID (whose inum
     cell is FULL) and AGREES with PARKED's half, which is what pins the
     withdrawn payload to the winner's own inode -- §13.1b's tie, doing its
     one job.  The dev half comes out at the opener's OWN dev by the same
     agreement, which is what lets the winner read [ip->dev] after it has
     deposited (§13.1e).  The deposited OUT absorbs the parked arm's recycle
     token, so the critical section need not carry it.

     GENERIC IN THE DEPOSIT (§14.8): the refutations only ever use the
     identity fraction, which both a reference and a share carry, so ONE
     lemma serves ilock's share checkout and any future reference one.  What
     the winner keeps is the descriptor's other half, and that is what lets
     it find its own arm again at the park. *)
  Lemma ic_swap_checkout cn γfs γi cov logstart k (d : ic_dep) (g : gname)
      (dev inum : mword 32) :
    ic_dep_gname d = Some g ->
    ic_escrow_body cn γfs γi cov logstart k -∗
    ic_tok cn k -∗
    ic_dep_own k d dev inum -∗
    |==> (* THE CHECKOUT'S TWO OUTCOMES (A⁗, §3.16), and they are the two
            alternatives of [ic_payload_arm]'s tail:

            SUCCESS -- the arm was ordinary, the payload comes out at the
            CALLER's generation, the deposit lands in OUT;
            FROZEN  -- the arm was the free path's frozen park, so there is
            no payload to hand out at all.  The body goes back UNMOVED, the
            checkout's own [ic_tok] and deposit-descriptor come back
            untouched, and what the caller gets instead is the standing
            [frzown] -- which its LICENCE refutes
            ([IgetLic.iname_not_frozen] puts the column at [FrzOff], at which
            the region's own receipt clause holds the receipt and
            [IcacheRef.frzown_excl] closes it).  DEVIATION 1's obligation,
            unchanged in kind and recorded at ProofIlock. *)
      ((ic_escrow_body cn γfs γi cov logstart k ∗
        ic_deposit cn k d ∗
        (∃ v : bool,
           i_dev (ientry k) ↦₄{DfracOwn (1/2)} dev ∗
           i_inum (ientry k) ↦₄{DfracOwn (1/2)} inum ∗
           i_valid (ientry k) ↦₄ valid_word v ∗
           ic_payload γfs γi cov logstart k inum g v))
       ∨ (ic_tok cn k ∗ ic_dep_own k d dev inum ∗
          frzown (bv_unsigned inum) ∗ frzsel k ((1/2)/2)%Qp true ∗
          (frzown (bv_unsigned inum) -∗ frzsel k ((1/2)/2)%Qp true -∗
             ic_escrow_body cn γfs γi cov logstart k))).
  Proof.
    iIntros (Hdg) "Hbody Htok Hown".
    iDestruct (ic_dep_own_ident with "Hown") as (f) "[[Hrd Hrn] Hresb]".
    iDestruct "Hbody" as "[Hpk | [Hout | [Hmid | [Hvg | Hhd]]]]".
    - iDestruct "Hpk" as (dev' inum' v ga)
        "(Hid & Hin & Hvld & Hpay & Hmid & Hgid)".
      iDestruct (word4_pointsto_agree with "Hrd Hid") as %<-.
      iDestruct (word4_pointsto_agree with "Hrn Hin") as %<-.
      iDestruct ("Hresb" with "[$Hrd $Hrn]") as "Hown".
      rewrite /ic_payload_arm.
      iDestruct "Hpay" as "[(Hpay & Hoff & Hhalf) | Hrcpt]"; last first.
      { (* THE FROZEN PARK: nothing to check out, and nothing moves.  The
           receipt is LENT to the caller (whose licence turns it into
           [False] against the region's own copy) with the wand that puts it
           back -- the arm cannot simply give it away, being the only home
           it has while the column reads [FrzPre]. *)
        iDestruct "Hrcpt" as "[Hrcpt Hsel]".
        iModIntro. iRight.
        iSplitL "Htok"; [iExact "Htok" |].
        iSplitL "Hown"; [iExact "Hown" |].
        iSplitL "Hrcpt"; [iExact "Hrcpt" |].
        iSplitL "Hsel"; [iExact "Hsel" |].
        iIntros "Hrcpt Hsel".
        iLeft. rewrite /ic_parked. iExists dev, inum, v, ga.
        iFrame "Hid Hin Hvld Hmid Hgid".
        rewrite /ic_payload_arm. iRight. iFrame. }
      (* THE GENERATION AGREEMENT (§17.3 (A)): the arm's 1/2 and the
         depositor's own slice are two slices of ONE slot's unit, so they
         name one generation -- which is what lets the payload come out at
         the CALLER's [g] and not at an existential of the arm's. *)
      iDestruct (ic_dep_own_live with "Hown") as (s0 g0) "(%Hg0 & Hlv & Hownb)".
      rewrite Hdg in Hg0. injection Hg0 as <-.
      iDestruct (live_gen_agree with "Hlv Hhalf") as %<-.
      iDestruct ("Hownb" with "Hlv") as "Hown".
      iDestruct (ic_dep_half_intro k d g Hdg with "Hhalf") as "Hhalf".
      iAssert (ic_dep_res k d dev inum) with "[Hown Hhalf]" as "Hres".
      { rewrite /ic_dep_res. iFrame. }
      iMod (ic_dep_checkout cn k d with "Htok") as "[Hdep1 Hdep2]".
      (* structurally: the goal's FIRST conjunct is [ic_escrow_body], five
         arms each existentially quantifying [ic_payload] over
         [inode_blocks]' 268-element big-op, and any framing search walks it
         before it reaches the deposit -- 100 s for this one [iFrame]
         (optimization.md's 2026-08-11 section). *)
      iModIntro. iLeft.
      iSplitR "Hdep2 Hid Hin Hvld Hpay Hoff".
      { iRight; iLeft. rewrite /ic_out. iExists d, dev, inum. iFrame. }
      iSplitL "Hdep2"; [iExact "Hdep2" |].
      iExists v. rewrite /ic_payload. iFrame.
    - iDestruct "Hout" as (d' dev' inum') "(Hdep' & _ & _ & _)".
      iExFalso. iApply (ic_tok_deposit_excl with "Htok Hdep'").
    - iDestruct "Hmid" as (dev' inum' w) "(_ & Hin & _ & _ & _)".
      iExFalso. iApply (ic_word4_excl with "Hin Hrn").
    - (* EMPTY (13.8): the arm owns the WHOLE dev cell and the winner
         brought a fraction of it inside its deposit. *)
      iDestruct "Hvg" as (dev' inum' w) "(Hidv & _ & _ & _ & _ & _)".
      iExFalso. iApply (ic_word4_excl with "Hidv Hrd").
    - (* HELD (§13.13): the FULL inum cell, exactly as MID above *)
      iDestruct "Hhd" as (dev' inum' w) "(_ & Hin & _ & _ & _)".
      iExFalso. iApply (ic_word4_excl with "Hin Hrn").
  Qed.

  (* (b) PARK, [iunlock]'s release (BioInv.escrow_swap_park).

     The opener's FULL valid cell refutes PARKED and MID -- both hold that
     cell full -- so the body is OUT, and what it parked comes back out.

     THE DESCRIPTOR IS WHAT MAKES THIS DETERMINISTIC (§14.8).  With OUT able
     to hold either deposit kind, the valid cell no longer decides WHICH: the
     two parkers (iunlock, holding a share's deposit; iput's window exit,
     holding a reference's) carry identical cells and payload and could not
     refute one another.  The parker's own half of the descriptor variable
     agrees with the arm's, and that single [ghost_var_agree] pins the KIND,
     the FRACTION and the IDENTITY at once.  So the deposit comes back
     EXACTLY as it went in -- no existential fraction, unlike
     [BioInv.escrow_swap_park] and unlike v2 -- and the dev/inum equalities
     that §13.1e used to read off the cells are now the descriptor's own.
     The deposited PARKED re-absorbs the recycle token OUT was keeping, and
     the descriptor variable goes back WHOLE at [DepNone], which is exactly
     [ic_tok] for releasesleep. *)
  (* STATED AT THE ARM's BUNDLE (iclaim-ledger.md §3.14 as built), so that
     iput's MID-FREE park at +0x70 -- which runs inside the freeze window
     and therefore has no [ifreeze_off] to give -- can park the receipt
     instead.  [ic_swap_park] below is this lemma at the token's left
     disjunct, i.e. every landed parker's exact signature. *)
  Lemma ic_swap_park_arm cn γfs γi cov logstart k (d : ic_dep) (g : gname)
      (v : bool) (dev inum : mword 32) :
    ic_dep_gname d = Some g ->
    ic_escrow_body cn γfs γi cov logstart k -∗
    ic_deposit cn k d -∗
    i_dev (ientry k) ↦₄{DfracOwn (1/2)} dev -∗
    i_inum (ientry k) ↦₄{DfracOwn (1/2)} inum -∗
    i_valid (ientry k) ↦₄ valid_word v -∗
    ic_payload γfs γi cov logstart k inum g v -∗
    |==> ic_escrow_body cn γfs γi cov logstart k ∗
      ic_tok cn k ∗
      ic_dep_own k d dev inum.
  Proof.
    iIntros (Hdg) "Hbody Hdep Hid Hin Hvld Hpay".
    iDestruct "Hbody" as "[Hpk | [Hout | [Hmid | [Hvg | Hhd]]]]".
    - iDestruct "Hpk" as (dev' inum' v' ga) "(_ & _ & Hvld' & _ & _ & _)".
      iExFalso. iApply (ic_word4_excl with "Hvld Hvld'").
    - iDestruct "Hout" as (d' dev' inum') "(Hdep' & Hres & Hmid & Hgid)".
      iMod (ic_dep_park cn k d d' with "Hdep Hdep'") as "[<- Htok]".
      (* THE FROZEN ALTERNATIVE (IVd) dies on the parker's OWN descriptor:
         an ordinary parker names a [d] with a generation ([Hdg]) and the
         frozen window deposited a [DepFrz], which has none. *)
      iDestruct "Hres" as "[Hres | Hfrz]".
      2:{ rewrite /ic_out_frz. destruct d; try (iDestruct "Hfrz" as "[]").
          cbn in Hdg. discriminate. }
      iDestruct "Hres" as "[Hown Hhalf]".
      iDestruct (ic_dep_own_ident with "Hown") as (f) "[[Hrd Hrn] Hresb]".
      iDestruct (word4_pointsto_agree with "Hrd Hid") as %->.
      iDestruct (word4_pointsto_agree with "Hrn Hin") as %->.
      iDestruct ("Hresb" with "[$Hrd $Hrn]") as "Hown".
      (* THE PARKED ARM'S 1/2 COMES BACK OUT OF THE DESCRIPTOR (§17.3 (A1)):
         a parker holds no [live_frac] of its own, so the descriptor's
         [ghost_var_agree] is what pins the returning payload's generation to
         the arm's -- [Hdg] is that pin, made pure. *)
      iDestruct (ic_dep_half_gname with "Hhalf") as (g2) "[%Hg2 Hhalf]".
      rewrite Hdg in Hg2. injection Hg2 as <-.
      (* structurally, for the reason at [ic_swap_checkout] above: 102 s
         when the two names were framed against a goal whose first conjunct
         is the whole five-armed body. *)
      iModIntro.
      iSplitR "Htok Hown"; [| iSplitL "Htok"; [iExact "Htok" | iExact "Hown"]].
      iLeft. rewrite /ic_parked. iExists dev, inum, v, g.
      iFrame "Hid Hin Hvld Hmid Hgid".
      iApply (ic_payload_to_arm with "Hpay Hhalf").
    - iDestruct "Hmid" as (dev' inum' w) "(_ & _ & Hvld' & _ & _)".
      iExFalso. iApply (ic_word4_excl with "Hvld Hvld'").
    - (* EMPTY: it holds the valid cell too, and the parker is carrying it *)
      iDestruct "Hvg" as (dev' inum' w) "(_ & _ & Hvld' & _ & _ & _)".
      iExFalso. iApply (ic_word4_excl with "Hvld Hvld'").
    - (* HELD (13.13): so does it *)
      iDestruct "Hhd" as (dev' inum' w) "(_ & _ & Hvld' & _ & _)".
      iExFalso. iApply (ic_word4_excl with "Hvld Hvld'").
  Qed.

  (* ...and the ORDINARY parker's signature, unchanged from IIId: a holder
     that came in through [SpecIlock] carries the payload with the inum's
     unfrozen token, which is the arm's left disjunct. *)
  Lemma ic_swap_park cn γfs γi cov logstart k (d : ic_dep) (g : gname)
      (v : bool) (dev inum : mword 32) :
    ic_dep_gname d = Some g ->
    ic_escrow_body cn γfs γi cov logstart k -∗
    ic_deposit cn k d -∗
    i_dev (ientry k) ↦₄{DfracOwn (1/2)} dev -∗
    i_inum (ientry k) ↦₄{DfracOwn (1/2)} inum -∗
    i_valid (ientry k) ↦₄ valid_word v -∗
    ic_payload γfs γi cov logstart k inum g v -∗
    |==> ic_escrow_body cn γfs γi cov logstart k ∗
      ic_tok cn k ∗
      ic_dep_own k d dev inum.
  Proof.
    iIntros (Hdg) "Hbody Hdep Hid Hin Hvld Hpay".
    iApply (ic_swap_park_arm cn γfs γi cov logstart k d g v dev inum Hdg
              with "Hbody Hdep Hid Hin Hvld Hpay").
  Qed.

  (* ...AND THE FREE PATH'S PARK (IVd, iput +0x70), which is the ONE parker
     that arrives with no payload: [ic_out]'s frozen alternative goes to
     [ic_payload_arm]'s frozen alternative and the receipt never leaves the
     escrow.  The cells go back exactly as in [ic_swap_park_arm] -- their
     dev/inum are pinned to the arm's existentials by the identity FRACTION
     the window exit deposited, which is what [ic_dep_own_ident] does on the
     ordinary path -- and the COUNT FRAGMENT the arm was keeping comes home,
     because the eviction at +0x8a reads the map off it
     ([IcacheInv.iref_frag_lookup]).

     The other four arms die on the parker's FULL valid cell, verbatim as in
     [ic_swap_park_arm]; the LEFT alternative of OUT dies because
     [ic_dep_park] has just pinned the descriptor to [DepNone], at which
     [ic_dep_res] is [False]. *)
  Lemma ic_swap_park_frz cn γfs γi cov logstart k
      (v : bool) (qf : Qp) (dev inum : mword 32) :
    ic_escrow_body cn γfs γi cov logstart k -∗
    ic_deposit cn k (DepFrz qf dev inum) -∗
    i_dev (ientry k) ↦₄{DfracOwn (1/2)} dev -∗
    i_inum (ientry k) ↦₄{DfracOwn (1/2)} inum -∗
    i_valid (ientry k) ↦₄ valid_word v -∗
    |==> ic_escrow_body cn γfs γi cov logstart k ∗
      ic_tok cn k ∗
      iref_frag k qf ∗
      inode_ident k (DfracOwn qf) dev inum.
  Proof.
    iIntros "Hbody Hdep Hid Hin Hvld".
    iDestruct "Hbody" as "[Hpk | [Hout | [Hmid | [Hvg | Hhd]]]]".
    - iDestruct "Hpk" as (dev' inum' v' ga) "(_ & _ & Hvld' & _ & _ & _)".
      iExFalso. iApply (ic_word4_excl with "Hvld Hvld'").
    - iDestruct "Hout" as (d' dev' inum') "(Hdep' & Hres & Hmid & Hgid)".
      iMod (ic_dep_park cn k (DepFrz qf dev inum) d' with "Hdep Hdep'")
        as "[<- Htok]".
      iDestruct "Hres" as "[Hres | Hfrz]".
      { rewrite /ic_dep_res /ic_dep_own /ic_dep_half /=.
        iDestruct "Hres" as "[[] _]". }
      rewrite /ic_out_frz.
      iDestruct "Hfrz" as "([%Hdv %Hnu] & Hfr & [Hrd Hrn] & Hrc & Hsel)".
      subst dev' inum'.
      iModIntro.
      iSplitR "Htok Hfr Hrd Hrn";
        [| iFrame "Htok Hfr"; iFrame "Hrd Hrn"].
      iLeft. rewrite /ic_parked. iExists dev, inum, v, inhabitant.
      iFrame "Hid Hin Hvld Hmid Hgid".
      iApply (ic_payload_arm_frz with "Hrc Hsel").
    - iDestruct "Hmid" as (dev' inum' w) "(_ & _ & Hvld' & _ & _)".
      iExFalso. iApply (ic_word4_excl with "Hvld Hvld'").
    - iDestruct "Hvg" as (dev' inum' w) "(_ & _ & Hvld' & _ & _ & _)".
      iExFalso. iApply (ic_word4_excl with "Hvld Hvld'").
    - iDestruct "Hhd" as (dev' inum' w) "(_ & _ & Hvld' & _ & _)".
      iExFalso. iApply (ic_word4_excl with "Hvld Hvld'").
  Qed.

  (* (c) THE AUTHORITY-SIDE OPENING AT REF-1 (iput's two lock-free reads).

     [iput] holds the table's authority half showing [M !! k = Some (q,1)]
     -- REF-1, established by the caller with [iref_lookup] -- plus its own
     reference AT THAT VERY [q].  OUT is impossible, and under the descriptor
     (§14.8) that takes TWO arguments, one per deposit kind:

       a REFERENCE deposit -- the arm's count fragment and the opener's would
       make the outstanding count at least two ([iref_tok_two_lookup]) against
       a count of one, exactly as in v2;

       a SHARE deposit -- there is no count fragment to argue with, and §14.6's
       identity-mass argument does not close (the arm holds only [s] of each
       cell; the parked ½ is in the checked-out thread's hand).  What closes is
       LIVE mass: the opener's [q = qt] carries the slot's WHOLE outstanding
       liveness, the invariant's arm is the exact complement, and the share's
       own slice is over budget ([IcacheInv.live_whole_share_absurd]).

     That second refutation is why this lemma is a FUPD taking [itable_inv]:
     [live_slot] lives in there and iput holds no piece of it.  Both call
     sites are inside an [ic_escrow] opening with [↑icacheN] free.

     MID is impossible: its inum cell is FULL and the opener holds a fraction
     of it.  So the body IS the parked bundle, at the opener's OWN inum, and
     everything the opener brought comes back.

     The rebuild wand takes a WHOLE [ic_parked], so the same lemma serves a
     read-only opening (put the pieces straight back) and one that changes
     the cells -- which is why §13's read-only variant is not a separate
     lemma. *)
  Lemma ic_open_auth_ref cn γfs γi cov logstart k (Eo : coPset)
      (M : gmap nat (Qp * positive)) (q qi : Qp) (dev inum : mword 32) :
    ↑icacheN ⊆ Eo ->
    M !! k = Some (q, 1%positive) ->
    itable_inv -∗
    ic_escrow_body cn γfs γi cov logstart k -∗
    itable_half M -∗
    iref_tok k q -∗
    inode_ident k (DfracOwn qi) dev inum -∗
    |={Eo}=>
    itable_half M ∗
    iref_tok k q ∗
    inode_ident k (DfracOwn qi) dev inum ∗
    (∃ (v : bool) (g : gname),
       i_dev (ientry k) ↦₄{DfracOwn (1/2)} dev ∗
       i_inum (ientry k) ↦₄{DfracOwn (1/2)} inum ∗
       i_valid (ientry k) ↦₄ valid_word v ∗
       (* THE ARM's TAIL (A⁗, §3.16): the ordinary payload + token + the
          arm's liveness half, or the free path's FROZEN PARK -- the receipt
          alone.  iput's last close decides it with the [ifreeze_pre] it has
          kept in hand since the mint
          ([ic_payload_arm_decide_frz]); every other opener is on the
          ordinary alternative and says so with its own token. *)
       ic_payload_arm γfs γi cov logstart k inum g v ∗
       ic_mid cn k ∗
       ic_id cn k (1/2) true dev inum) ∗
    (ic_parked cn γfs γi cov logstart k -∗
     ic_escrow_body cn γfs γi cov logstart k).
  Proof.
    iIntros (HE HMk) "#Hinv Hbody Hhalf Htok Hid".
    iDestruct "Hbody" as "[Hpk | [Hout | [Hmid | [Hvg | Hhd]]]]".
    - iDestruct "Hpk" as (dev' inum' v ga)
        "(Hidv & Hin & Hvld & Hpay & Hmidt & Hgid)".
      iDestruct "Hid" as "[Hidd Hidn]".
      iDestruct (word4_pointsto_agree with "Hidd Hidv") as %<-.
      iDestruct (word4_pointsto_agree with "Hidn Hin") as %<-.
      iModIntro. iFrame "Hhalf Htok Hidd Hidn".
      iSplitR "".
      { iExists v, ga. iFrame. }
      iIntros "Hp". by iLeft.
    - iDestruct "Hout" as (d dev' inum') "(_ & Hres & _ & _)".
      iDestruct "Hres" as "[Hres | Hfrz]".
      2:{ (* THE FROZEN ALTERNATIVE (IVd): no live mass to argue with -- the
             freer parked it -- and no live-mass complement to appeal to.
             The COUNT FRAGMENT is what it left behind, and REF-1 kills it
             with the opener's own, exactly as on the reference deposit. *)
          rewrite /ic_out_frz. destruct d; try (iDestruct "Hfrz" as "[]").
          iDestruct "Hfrz" as "(_ & Hfr' & _ & _)".
          iDestruct "Htok" as "(Hfrq & _ & _)".
          iDestruct (iref_frag_two_lookup with "Hhalf Hfrq Hfr'")
            as %(qt' & n & HMk' & Hn).
          rewrite HMk in HMk'. injection HMk' as _ Hn1. subst n.
          iExFalso. iPureIntro. cbn in Hn. lia. }
      rewrite /ic_dep_res /ic_dep_own /ic_dep_half.
      destruct d as [| q' dv nu gd | s dv nu gd | qf dv nu];
        [| | | iDestruct "Hres" as "[[] _]"].
      + iDestruct "Hres" as "[[] _]".
      + iDestruct "Hres" as "[[_ (Hfr' & Hlv' & _)] _]".
        (* the arm's reference has no sleeplock slice of its own (the lock
           holds it), so the refutation's [iref_tok] borrows the OPENER's --
           which is sound because the two are refuted together. *)
        (* the arm's reference has no sleeplock slice of its own -- the
           entry's LOCK holds it -- so the refutation reads the bare count
           fragments, which is all it ever used. *)
        iDestruct "Htok" as "(Hfrq & Hlvq & Hshq)".
        iDestruct (iref_frag_two_lookup with "Hhalf Hfrq Hfr'")
          as %(qt' & n & HMk' & Hn).
        rewrite HMk in HMk'. injection HMk' as _ Hn1. subst n.
        iExFalso. iPureIntro. cbn in Hn. lia.
      + (* THE REF-1 REFUTATION OF A SHARE DEPOSIT, under the restated
           ledger (§17.3 (A)): the opener's [q = qt], the invariant's
           [1/2 - qt], the ARM's own 1/2 and the share's [s] sum past one.
           The 1/2 is what §17.2's placement lost and what puts this back. *)
        iDestruct "Hres" as "[[_ [_ Hlvs]] Hhf]".
        iDestruct "Htok" as "(_ & Hlv & _)".
        iAssert (live_frac k (1/2)%Qp) with "[Hhf]" as "Hfh";
          [iExists gd; iExact "Hhf" |].
        iAssert (live_frac k s) with "[Hlvs]" as "Hfs";
          [iExists gd; iExact "Hlvs" |].
        iMod (live_whole_share_absurd Eo M k q s 1%positive HE HMk
                with "Hinv Hhalf Hlv Hfh Hfs") as "[]".
    - iDestruct "Hmid" as (dev' inum' w) "(_ & Hin & _ & _ & _)".
      iDestruct "Hid" as "[_ Hqi]".
      iExFalso. iApply (ic_word4_excl with "Hin Hqi").
    - (* EMPTY: the opener's own dev fraction against the arm's full cell *)
      iDestruct "Hvg" as (dev' inum' w) "(Hidv & _ & _ & _ & _ & _)".
      iDestruct "Hid" as "[Hqd _]".
      iExFalso. iApply (ic_word4_excl with "Hidv Hqd").
    - (* HELD (§13.13): the opener's inum fraction against the FULL cell.
         This is what keeps iput's own LAST CLOSE (which is this lemma) from
         ever meeting its own window arm. *)
      iDestruct "Hhd" as (dev' inum' w) "(_ & Hin & _ & _ & _)".
      iDestruct "Hid" as "[_ Hqi]".
      iExFalso. iApply (ic_word4_excl with "Hin Hqi").
  Qed.

  Lemma ic_open_auth_frz cn γfs γi cov logstart k (Eo : coPset)
      (M : gmap nat (Qp * positive)) (q qi : Qp) (dev inum : mword 32) :
    ↑icacheN ⊆ Eo -> (k < NINODE)%nat ->
    M !! k = Some (q, 1%positive) ->
    itable_inv -∗
    ic_escrow_body cn γfs γi cov logstart k -∗
    itable_half M -∗
    (* RULING R-e: at iput+0x82 the freezer's live slice is NOT in its hand --
       it has been in [IcacheInv.live_slot]'s frozen alternative since the mint
       -- so this opener arrives with the bare COUNT FRAGMENT and the freeze
       SELECTOR's quarter, and the [DepShr] arm's REF-1 refutation runs off
       [IcacheInv.frz_slot_kill] instead of [live_whole_share_absurd]. *)
    iref_frag k q -∗ frzsel k ((1/2)/2)%Qp true -∗
    inode_ident k (DfracOwn qi) dev inum -∗
    |={Eo}=>
    itable_half M ∗
    iref_frag k q ∗ frzsel k ((1/2)/2)%Qp true ∗
    inode_ident k (DfracOwn qi) dev inum ∗
    (∃ (v : bool) (g : gname),
       i_dev (ientry k) ↦₄{DfracOwn (1/2)} dev ∗
       i_inum (ientry k) ↦₄{DfracOwn (1/2)} inum ∗
       i_valid (ientry k) ↦₄ valid_word v ∗
       (* THE ARM's TAIL (A⁗, §3.16): the ordinary payload + token + the
          arm's liveness half, or the free path's FROZEN PARK -- the receipt
          alone.  iput's last close decides it with the [ifreeze_pre] it has
          kept in hand since the mint
          ([ic_payload_arm_decide_frz]); every other opener is on the
          ordinary alternative and says so with its own token. *)
       ic_payload_arm γfs γi cov logstart k inum g v ∗
       ic_mid cn k ∗
       ic_id cn k (1/2) true dev inum) ∗
    (ic_parked cn γfs γi cov logstart k -∗
     ic_escrow_body cn γfs γi cov logstart k).
  Proof.
    iIntros (HE Hk HMk) "#Hinv Hbody Hhalf Hfrq Hsel Hid".
    iDestruct "Hbody" as "[Hpk | [Hout | [Hmid | [Hvg | Hhd]]]]".
    - iDestruct "Hpk" as (dev' inum' v ga)
        "(Hidv & Hin & Hvld & Hpay & Hmidt & Hgid)".
      iDestruct "Hid" as "[Hidd Hidn]".
      iDestruct (word4_pointsto_agree with "Hidd Hidv") as %<-.
      iDestruct (word4_pointsto_agree with "Hidn Hin") as %<-.
      iModIntro. iFrame "Hhalf Hfrq Hsel Hidd Hidn".
      iSplitR "".
      { iExists v, ga. iFrame. }
      iIntros "Hp". by iLeft.
    - iDestruct "Hout" as (d dev' inum') "(_ & Hres & _ & _)".
      iDestruct "Hres" as "[Hres | Hfrz]".
      2:{ (* THE FROZEN ALTERNATIVE (IVd): no live mass to argue with -- the
             freer parked it -- and no live-mass complement to appeal to.
             The COUNT FRAGMENT is what it left behind, and REF-1 kills it
             with the opener's own, exactly as on the reference deposit. *)
          rewrite /ic_out_frz. destruct d; try (iDestruct "Hfrz" as "[]").
          iDestruct "Hfrz" as "(_ & Hfr' & _ & _ & _)".
          iDestruct (iref_frag_two_lookup with "Hhalf Hfrq Hfr'")
            as %(qt' & n & HMk' & Hn).
          rewrite HMk in HMk'. injection HMk' as _ Hn1. subst n.
          iExFalso. iPureIntro. cbn in Hn. lia. }
      rewrite /ic_dep_res /ic_dep_own /ic_dep_half.
      destruct d as [| q' dv nu gd | s dv nu gd | qf dv nu];
        [| | | iDestruct "Hres" as "[[] _]"].
      + iDestruct "Hres" as "[[] _]".
      + iDestruct "Hres" as "[[_ (Hfr' & Hlv' & _)] _]".
        (* the arm's reference has no sleeplock slice of its own (the lock
           holds it), so the refutation's [iref_tok] borrows the OPENER's --
           which is sound because the two are refuted together. *)
        (* the arm's reference has no sleeplock slice of its own -- the
           entry's LOCK holds it -- so the refutation reads the bare count
           fragments, which is all it ever used. *)
        iDestruct (iref_frag_two_lookup with "Hhalf Hfrq Hfr'")
          as %(qt' & n & HMk' & Hn).
        rewrite HMk in HMk'. injection HMk' as _ Hn1. subst n.
        iExFalso. iPureIntro. cbn in Hn. lia.
      + (* THE REF-1 REFUTATION OF A SHARE DEPOSIT, under the restated
           ledger (§17.3 (A)): the opener's [q = qt], the invariant's
           [1/2 - qt], the ARM's own 1/2 and the share's [s] sum past one.
           The 1/2 is what §17.2's placement lost and what puts this back. *)
        iDestruct "Hres" as "[[_ [_ Hlvs]] Hhf]".
        iAssert (live_frac k s) with "[Hlvs]" as "Hfs";
          [iExists gd; iExact "Hlvs" |].
        iMod (frz_slot_kill Eo k ((1/2)/2)%Qp s HE Hk with "Hinv Hsel Hfs") as "[]".
    - iDestruct "Hmid" as (dev' inum' w) "(_ & Hin & _ & _ & _)".
      iDestruct "Hid" as "[_ Hqi]".
      iExFalso. iApply (ic_word4_excl with "Hin Hqi").
    - (* EMPTY: the opener's own dev fraction against the arm's full cell *)
      iDestruct "Hvg" as (dev' inum' w) "(Hidv & _ & _ & _ & _ & _)".
      iDestruct "Hid" as "[Hqd _]".
      iExFalso. iApply (ic_word4_excl with "Hidv Hqd").
    - (* HELD (§13.13): the opener's inum fraction against the FULL cell.
         This is what keeps iput's own LAST CLOSE (which is this lemma) from
         ever meeting its own window arm. *)
      iDestruct "Hhd" as (dev' inum' w) "(_ & Hin & _ & _ & _)".
      iDestruct "Hid" as "[_ Hqi]".
      iExFalso. iApply (ic_word4_excl with "Hin Hqi").
  Qed.

  (* (d1) THE RECYCLER'S OPENING (iget, the [sw] at +0x72).  Under §13.9
     there is only ONE of these: a slot iget recycles is not live, so its arm
     is EMPTY, so there is NO payload to evict -- the eviction argument is
     iput's, at the last close, where the flush semantics hold.  The table's
     share at such a slot carries no dev fraction (the arm owns that cell
     whole), so the ONLY thing that tells this arm from an ordinary parked
     one is the identification ghost.  This is also where the FLIP happens:
     past this opening the entry is live, and both halves are in the
     recycler's hand exactly here.

     §13.10: the arm's dev cell -- which the recycler wrote at +0x6e and
     could not keep a fraction of -- comes out AT THE VALUE THE TABLE'S
     GHOST HALF NAMES, and the flip retags both halves to the identity the
     entry is being recycled TO.  Without that the recycled entry's dev
     would be unrecoverable here and the postcondition unstatable. *)
  Lemma ic_open_empty_free cn γfs γi cov logstart k
      (devT inumT devN inumN : mword 32) :
    ic_escrow_body cn γfs γi cov logstart k -∗
    ic_id cn k (1/2) false devT inumT -∗
    i_inum (ientry k) ↦₄{DfracOwn (1/2)} inumT -∗
    |==> i_inum (ientry k) ↦₄ inumT ∗
      i_dev (ientry k) ↦₄ devT ∗
      (∃ w : mword 32, i_valid (ientry k) ↦₄ w) ∗
      inode_raw (ientry k) ∗
      ic_mid cn k ∗
      ic_id cn k (1/2) true devN inumN ∗
      ic_id cn k (1/2) true devN inumN.
  Proof.
    iIntros "Hbody Hgf HinT".
    iDestruct "Hbody" as "[Hpk | [Hout | [Hmid | [Hvg | Hhd]]]]".
    - iDestruct "Hpk" as (dev' inum' v ga) "(_ & _ & _ & _ & _ & Hgt)".
      iDestruct (ic_id_agree with "Hgf Hgt") as %(Hc & _ & _). discriminate.
    - iDestruct "Hout" as (q dev' inum') "(_ & _ & _ & Hgt)".
      iDestruct (ic_id_agree with "Hgf Hgt") as %(Hc & _ & _). discriminate.
    - iDestruct "Hmid" as (dev' inum' w) "(_ & _ & _ & _ & Hgt)".
      iDestruct (ic_id_agree with "Hgf Hgt") as %(Hc & _ & _). discriminate.
    - iDestruct "Hvg" as (devA inum' w) "(Hidv & Hin & Hvld & Hraw & Hmidt & Hgf')".
      iDestruct (ic_id_agree with "Hgf Hgf'") as %(_ & <- & <-).
      iDestruct (word4_pointsto_half_join with "HinT Hin") as "Hin".
      iMod (ic_id_flip cn k false true devT inumT devN inumN with "Hgf Hgf'")
        as "[Hg1 Hg2]".
      iModIntro. iFrame "Hin Hidv Hraw Hmidt Hg1 Hg2".
      iExists w. iFrame.
    - (* HELD (§13.13): the identification ghost, exactly as for the other
         three live arms *)
      iDestruct "Hhd" as (dev' inum' w) "(_ & _ & _ & _ & Hgt)".
      iDestruct (ic_id_agree with "Hgf Hgt") as %(Hc & _ & _). discriminate.
  Qed.

  (* (d0) THE RECYCLER'S DEV STORE (iget, the [sw] at +0x6e).  The empty arm
     already owns the WHOLE dev cell -- the table has no share to join in --
     so the recycler borrows it, stores, and hands it straight back, leaving
     the arm empty at its new (still meaningless) device.  Nothing about the
     empty arm couples dev to anything, which is why this is a plain
     open/close pair, and why the recycler keeps NO dev fraction across the
     gap to +0x72: the arm must still hold the cell whole, or
     [ic_swap_checkout] would lose its refutation.

     §13.10: the arm's dev cell is FULL and the recycler may keep no
     fraction of it, so the re-tag of the AGREEMENT GHOST is what carries
     the stored value to +0x72 -- the two halves are in one hand here, and
     nowhere else between the two stores.  [devN] is the value the caller is
     about to store; the cell comes out at the OLD value [devT], which the
     ghost names. *)
  Lemma ic_open_empty_dev cn γfs γi cov logstart k (devT inumT devN : mword 32) :
    ic_escrow_body cn γfs γi cov logstart k -∗
    ic_id cn k (1/2) false devT inumT -∗
    |==> i_dev (ientry k) ↦₄ devT ∗
      ic_id cn k (1/2) false devN inumT ∗
      (i_dev (ientry k) ↦₄ devN -∗
       ic_escrow_body cn γfs γi cov logstart k).
  Proof.
    iIntros "Hbody Hgf".
    iDestruct "Hbody" as "[Hpk | [Hout | [Hmid | [Hvg | Hhd]]]]".
    - iDestruct "Hpk" as (dev' inum' v ga) "(_ & _ & _ & _ & _ & Hgt)".
      iDestruct (ic_id_agree with "Hgf Hgt") as %(Hc & _ & _). discriminate.
    - iDestruct "Hout" as (q dev' inum') "(_ & _ & _ & Hgt)".
      iDestruct (ic_id_agree with "Hgf Hgt") as %(Hc & _ & _). discriminate.
    - iDestruct "Hmid" as (dev' inum' w) "(_ & _ & _ & _ & Hgt)".
      iDestruct (ic_id_agree with "Hgf Hgt") as %(Hc & _ & _). discriminate.
    - iDestruct "Hvg" as (devA inum' w) "(Hidv & Hin & Hvld & Hraw & Hmidt & Hgf')".
      iDestruct (ic_id_agree with "Hgf Hgf'") as %(_ & <- & <-).
      iMod (ic_id_flip cn k false false devT inumT devN inumT with "Hgf Hgf'")
        as "[Hg1 Hg2]".
      iModIntro. iFrame "Hidv Hg1".
      iIntros "Hd".
      iRight; iRight; iRight; iLeft. rewrite /ic_empty_arm.
      iExists devN, inumT, w. iFrame.
    - (* HELD (§13.13): the identification ghost *)
      iDestruct "Hhd" as (dev' inum' w) "(_ & _ & _ & _ & Hgt)".
      iDestruct (ic_id_agree with "Hgf Hgt") as %(Hc & _ & _). discriminate.
  Qed.

  (* closing the window OPEN: any mid bundle is a legal body
     (BioInv.escrow_close_mid). *)
  Lemma ic_close_mid cn γfs γi cov logstart k :
    ic_mid_arm cn γfs γi cov logstart k -∗
    ic_escrow_body cn γfs γi cov logstart k.
  Proof. iIntros "H". iRight; iRight; iLeft. iExact "H". Qed.

  (* ...and closing at the EMPTY arm, which is what [ic_open_empty_dev]'s
     wand does and what C7's boot stocking will do fifty times. *)
  Lemma ic_close_empty cn γfs γi cov logstart k :
    ic_empty_arm cn k -∗
    ic_escrow_body cn γfs γi cov logstart k.
  Proof. iIntros "H". iRight; iRight; iRight; iLeft. iExact "H". Qed.

  (* ...and closing at a normal parked arm *)
  Lemma ic_close_parked cn γfs γi cov logstart k :
    ic_parked cn γfs γi cov logstart k -∗
    ic_escrow_body cn γfs γi cov logstart k.
  Proof. iIntros "H". by iLeft. Qed.

  (* (d2) THE LAST CLOSE'S EVICTION (iput, §13.9) -- [ic_open_empty_free]
     run backwards, and the one place the eviction argument lives.

     The closer has opened the parked arm at REF-1 ([ic_open_auth_ref]) and
     joined its own departing identity share with the table's retained one
     ([IcacheInv.islot_rest_join] gives [islot_free_at], i.e. ½ of each
     cell); the arm's own halves complete the DEV cell to FULL, which is what
     the empty arm demands, while the inum cell's spare half stays with the
     table ([islot_empty]).  Both identification halves are in hand at this
     opening, so the flip true -> false happens here.

     WHAT COMES OUT IS THE POOL SHAPE, on both payload polarities, and this
     is PARKED-MEANS-FLUSHED (§13.1d) doing its one job: the loaded arm's
     [dinode_at] is at the IN-MEMORY record, so its [inode_ok] -- which the
     pool's allocated shape is about the ON-DISK record -- transfers with no
     re-reading.  The metadata and addrs CELLS drop out of the bundle and
     become the empty arm's [inode_raw]; their thirteen-element length comes
     from [blkmap_wf], which [inode_ok] carries.

     ---- THE TWO CLOSE FLAVOURS (increment IIIa) -------------------------

     The insertion contract is the mirror of what [IcacheInv]'s last close
     hands back, so it comes in the same two flavours [frz_close ph] fuses:

       ORDINARY last close (ref 1, nlink nonzero, no freeze anywhere):
         [iref_close_last_store_au] threaded [FrzOff] through unchanged and
         drove the count 1 -> 0, so the closer surrenders
         [icnt_half z 0 ∗ ifreeze_off z] and the pool takes a NORMAL arm.
         That is [ic_close_to_empty] below, unchanged but for the two new
         premises.

       FREE path (iput's +0x8a, strictly inside the freeze window): the same
         AU stepped [FrzPre -> FrzPost], so what the closer holds is
         [icnt_half z 0 ∗ ifreeze_post z] and the pool must take the AWAIT
         arm instead.  That is [ic_close_to_empty_await]; it also hands the
         displaced [ipool_shape_np] BACK to the freer, which is §1.2's whole
         point -- the freer keeps [dinode_at] (with its identity intact) and
         the block resources across releasesleep, and parks only the escrow.

     Both share [ic_close_to_empty_core], which is the eviction argument
     proper; only the arm the pool ends on differs. *)
  Local Lemma ic_close_to_empty_core cn γfs γi cov logstart k (v : bool)
      (g : gname) (dev inum : mword 32) :
    ic_id cn k (1/2) true dev inum -∗
    ic_id cn k (1/2) true dev inum -∗
    i_dev (ientry k) ↦₄{DfracOwn (1/2)} dev -∗
    i_dev (ientry k) ↦₄{DfracOwn (1/2)} dev -∗
    i_inum (ientry k) ↦₄{DfracOwn (1/2)} inum -∗
    i_valid (ientry k) ↦₄ valid_word v -∗
    ic_payload_np γfs γi cov logstart k inum g v -∗
    ic_mid cn k -∗
    |==> ic_escrow_body cn γfs γi cov logstart k ∗
         ic_id cn k (1/2) false dev inum ∗
         ipool_shape_np γfs γi cov logstart inum.
  Proof.
    iIntros "Hg1 Hg2 Hd1 Hd2 Hin Hvld Hpay Hmt".
    iMod (ic_id_flip cn k true false dev inum dev inum with "Hg1 Hg2")
      as "[Hgf1 Hgf2]".
    iDestruct (word4_pointsto_half_join with "Hd1 Hd2") as "Hd".
    (* the payload splits into the cells the empty arm keeps and the bundle
       the pool takes back *)
    iAssert (inode_raw (ientry k) ∗ ipool_shape_np γfs γi cov logstart inum)%I
      with "[Hpay]" as "[Hraw Hpool]".
    (* THE GENERATION'S ONE-SHOT DIES HERE, unspent or spent (design §17.6
       (7)): an evicted slot leaves [M], its whole unit goes back to the free
       arm, and the next recycle bumps again -- so a free slot carries no
       obligation and dropping the token is exactly right. *)
    { destruct v;
        [| iDestruct "Hpay" as "[[Hr Hp] _]"; iFrame "Hr"; iExact "Hp" ].
      iDestruct "Hpay" as (dn bm) "[Hlk _]".
      iDestruct "Hlk" as (data)
        "(%Hok & %Hdok & %Hddix & %Hdoc & %Hduq & Hdlk & Hdat & Hmeta & Haddrs & Hind &
          Hblks & Hdv & Hfv)".
      pose proof Hok as Hok'.
      destruct Hok' as (Hwf & _ & Hda & _ & _ & _ & _).
      assert (Hcelllen : length (bm_cells bm) = 13%nat).
      { rewrite /bm_cells length_app (blkmap_wf_dir_len _ _ _ Hwf). reflexivity. }
      iSplitL "Hmeta Haddrs".
      { rewrite /inode_raw. iSplitL "Hmeta"; [by iExists dn |].
        iExists (bm_cells bm). iSplitR; [iPureIntro; exact Hcelllen |].
        iExact "Haddrs". }
      rewrite /ipool_shape_np /ipool_alloc. iLeft. iExists dn, bm, data.
      iSplitR; [iPureIntro; exact Hok |].
      iSplitR; [iPureIntro; exact Hdok |].
      (* the eviction moves no byte and no field: the clause goes back to the
         pool exactly as the loaded arm held it *)
      iSplitR; [iPureIntro; exact Hddix |].
      iSplitR; [iPureIntro; exact Hdoc |].
      iSplitR; [iPureIntro; exact Hduq |].
      iSplitL "Hdlk"; [iExact "Hdlk" |]. iFrame. }
    (* the two right-hand conjuncts go out structurally: [iFrame "Hgf2
       Hpool"] would search the [ic_escrow_body] conjunct -- five arms, each
       an existential over [ic_payload]/[inode_raw] -- for each of the two
       names (88 s measured; see [ipool_insert] below and optimization.md). *)
    iModIntro.
    iSplitR "Hgf2 Hpool"; [| iSplitL "Hgf2"; [iExact "Hgf2" | iExact "Hpool"]].
    iApply ic_close_empty. rewrite /ic_empty_arm.
    iExists dev, inum, (valid_word v). iFrame.
  Qed.

  (* FLAVOUR 1: the ORDINARY last close.  The closer surrenders the uncached
     ledger pair its [iref_close_last_store_au] just produced -- the count at
     zero and the still-unfrozen token -- and the pool takes a normal arm. *)
  Lemma ic_close_to_empty cn γfs γi cov logstart k (v : bool) (g : gname)
      (dev inum : mword 32) :
    ic_id cn k (1/2) true dev inum -∗
    ic_id cn k (1/2) true dev inum -∗
    i_dev (ientry k) ↦₄{DfracOwn (1/2)} dev -∗
    i_dev (ientry k) ↦₄{DfracOwn (1/2)} dev -∗
    i_inum (ientry k) ↦₄{DfracOwn (1/2)} inum -∗
    i_valid (ientry k) ↦₄ valid_word v -∗
    ic_payload_np γfs γi cov logstart k inum g v -∗
    ic_mid cn k -∗
    icnt_half (bv_unsigned inum) 0%nat -∗
    (* the MIRROR's half rides into the pool beside the count half (§3.16) *)
    frzm_h (bv_unsigned inum) false -∗
    ifreeze_off (bv_unsigned inum) -∗
    |==> ic_escrow_body cn γfs γi cov logstart k ∗
         ic_id cn k (1/2) false dev inum ∗
         ipool_shape γfs γi cov logstart inum.
  Proof.
    iIntros "Hg1 Hg2 Hd1 Hd2 Hin Hvld Hpay Hmt Hcnt Hmir Hoff".
    iMod (ic_close_to_empty_core cn γfs γi cov logstart k v g dev inum
            with "Hg1 Hg2 Hd1 Hd2 Hin Hvld Hpay Hmt") as "(Hbody & Hgf2 & Hnp)".
    iModIntro.
    iSplitL "Hbody"; [iExact "Hbody" |].
    iSplitL "Hgf2"; [iExact "Hgf2" |].
    rewrite /ipool_shape. iSplitL "Hcnt"; [iExact "Hcnt" |].
    iSplitL "Hmir"; [iExact "Hmir" |].
    iLeft. iSplitL "Hnp"; [iExact "Hnp" | iExact "Hoff"].
  Qed.

  (* FLAVOUR 1', THE SAME EVICTION WITH ITS LEDGER TRIPLE ARRIVING LATE.

     [ic_close_to_empty] above asks for the count at zero -- and the ORDINARY
     last close cannot have it when it must run.  The eviction has to happen
     BEFORE the [sw] that zeroes [ip->ref] ([ic_open_auth_ref] wants the
     table authority still showing the slot at REF-1, and the store deletes
     it), while [icnt_half _ 0] does not exist until AFTER it: the count is
     moved by [IcacheInv.iref_close_last_store_au], which fires with the
     instruction.  That is the same ordering observation §3.16 records for
     the FROZEN eviction, and it has the same answer -- run the eviction on
     what the caller does hold and hand the pool bundle back as a WAND, to
     be fed the three ledger outputs the store produces.

     Not a second proof: [ic_close_to_empty] is this one applied
     immediately. *)
  Lemma ic_close_to_empty_late cn γfs γi cov logstart k (v : bool) (g : gname)
      (dev inum : mword 32) :
    ic_id cn k (1/2) true dev inum -∗
    ic_id cn k (1/2) true dev inum -∗
    i_dev (ientry k) ↦₄{DfracOwn (1/2)} dev -∗
    i_dev (ientry k) ↦₄{DfracOwn (1/2)} dev -∗
    i_inum (ientry k) ↦₄{DfracOwn (1/2)} inum -∗
    i_valid (ientry k) ↦₄ valid_word v -∗
    ic_payload_np γfs γi cov logstart k inum g v -∗
    ic_mid cn k -∗
    |==> ic_escrow_body cn γfs γi cov logstart k ∗
         ic_id cn k (1/2) false dev inum ∗
         (icnt_half (bv_unsigned inum) 0%nat -∗
          frzm_h (bv_unsigned inum) false -∗
          ifreeze_off (bv_unsigned inum) -∗
          ipool_shape γfs γi cov logstart inum).
  Proof.
    iIntros "Hg1 Hg2 Hd1 Hd2 Hin Hvld Hpay Hmt".
    iMod (ic_close_to_empty_core cn γfs γi cov logstart k v g dev inum
            with "Hg1 Hg2 Hd1 Hd2 Hin Hvld Hpay Hmt") as "(Hbody & Hgf2 & Hnp)".
    iModIntro.
    iSplitL "Hbody"; [iExact "Hbody" |].
    iSplitL "Hgf2"; [iExact "Hgf2" |].
    iIntros "Hcnt Hmir Hoff".
    rewrite /ipool_shape. iSplitL "Hcnt"; [iExact "Hcnt" |].
    iSplitL "Hmir"; [iExact "Hmir" |].
    iLeft. iSplitL "Hnp"; [iExact "Hnp" | iExact "Hoff"].
  Qed.

  (* FLAVOUR 2: the FREE path's eviction (§1.3).  Same eviction, but the
     freeze is standing at [FrzPost], so the pool takes the AWAIT arm and the
     bundle the loaded/unloaded payload was carrying goes back to the FREER
     rather than into the pool -- which is exactly B2's resolution: the
     record keeps its identity, no existential, all the way to the off-lock
     deposit.  The escrow and its ticket are the freer's own
     ([EscrowInode.escA_alloc], mask-only, minted before the park). *)
  (* ...AND B2 IS GONE WITH IT (iclaim-ledger.md §3.16).  IVa's complaint --
     "the eviction hands back exactly one [ipool_shape], and the reorder needs
     BOTH the free-pool entry and the record out of it, and [ipool_shape_np]
     existentially erases which arm and which record it is" -- was a
     consequence of the FREER having given its payload back to the escrow at
     the +0x70 mid-free park.  Under A⁗ it never does: the parked arm's
     frozen alternative holds the RECEIPT and nothing else, so from the +0x5e
     window exit to the +0xa8 deposit the record, the block resources and
     [inode_raw] are all in the freer's own hand, named and un-existentialised.
     The eviction therefore takes [inode_raw] (which the empty arm keeps) and
     hands back ONE bundle -- the pool's -- with nothing to share. *)
  (* ...AND THE EVICTION PROPER, split from the pool-bundle assembly (§3.16).
     The free path's last close is ONE atomic store, and its three ledger
     outputs -- the count at zero, the mirror DOWN and the [FrzPost] phase --
     do not exist until it has fired.  So the eviction runs FIRST, on what the
     frozen park does hold, and hands the RECEIPT back for the close to take
     home; the pool bundle is assembled afterwards out of what the close
     produced ([ipool_shape_await] below). *)
  Lemma ic_close_to_empty_frz cn γfs γi cov logstart k (v : bool)
      (dev inum : mword 32) :
    ic_id cn k (1/2) true dev inum -∗
    ic_id cn k (1/2) true dev inum -∗
    i_dev (ientry k) ↦₄{DfracOwn (1/2)} dev -∗
    i_dev (ientry k) ↦₄{DfracOwn (1/2)} dev -∗
    i_inum (ientry k) ↦₄{DfracOwn (1/2)} inum -∗
    i_valid (ientry k) ↦₄ valid_word v -∗
    inode_raw (ientry k) -∗
    ic_mid cn k -∗
    frzown (bv_unsigned inum) -∗
    |==> ic_escrow_body cn γfs γi cov logstart k ∗
         ic_id cn k (1/2) false dev inum ∗
         frzown (bv_unsigned inum).
  Proof.
    iIntros "Hg1 Hg2 Hd1 Hd2 Hin Hvld Hraw Hmt Hrc".
    iMod (ic_id_flip cn k true false dev inum dev inum with "Hg1 Hg2")
      as "[Hgf1 Hgf2]".
    iDestruct (word4_pointsto_half_join with "Hd1 Hd2") as "Hd".
    iModIntro.
    iSplitR "Hgf2 Hrc"; [| iSplitL "Hgf2"; [iExact "Hgf2" | iExact "Hrc"]].
    iApply ic_close_empty. rewrite /ic_empty_arm.
    iExists dev, inum, (valid_word v). iFrame.
  Qed.

  (* the pool entry the free path parks at iput+0x94, on its AWAIT arm: the
     uncached ledger row the last close produced, and the escrow the freer
     minted around the [FrzPost] token it left standing. *)
  Lemma ipool_shape_await γfs γi cov logstart (inum : mword 32)
      (ge gr gd : gname) (rg : bool) :
    icnt_half (bv_unsigned inum) 0%nat -∗
    frzm_h (bv_unsigned inum) false -∗
    escA_inv ge gr gd γi (bv_unsigned inum) rg -∗
    redeem_ticketA gr -∗
    (* the freer's own contents hold, which came out of the payload it
       evicted and which the AWAIT arm parks untied (§9 W2) *)
    (∃ e, dv_ride (bv_unsigned inum) e) -∗
    (∃ b, fv_ride (bv_unsigned inum) b) -∗
    ipool_shape γfs γi cov logstart inum.
  Proof.
    iIntros "Hcnt Hmir #Hesc Htk Hdv Hfv". rewrite /ipool_shape.
    iSplitL "Hcnt"; [iExact "Hcnt" |].
    iSplitL "Hmir"; [iExact "Hmir" |].
    iRight. iRight. rewrite /pool_await. iExists ge, gr, gd, rg.
    iSplitR; [iExact "Hesc" |].
    iSplitL "Htk"; [iExact "Htk" |].
    iSplitL "Hdv"; [iExact "Hdv" | iExact "Hfv"].
  Qed.

  Lemma ic_close_to_empty_await cn γfs γi cov logstart k (v : bool)
      (ge gr gd : gname) (rg : bool) (dev inum : mword 32) :
    ic_id cn k (1/2) true dev inum -∗
    ic_id cn k (1/2) true dev inum -∗
    i_dev (ientry k) ↦₄{DfracOwn (1/2)} dev -∗
    i_dev (ientry k) ↦₄{DfracOwn (1/2)} dev -∗
    i_inum (ientry k) ↦₄{DfracOwn (1/2)} inum -∗
    i_valid (ientry k) ↦₄ valid_word v -∗
    (* the five metadata cells and the thirteen addrs cells, which the EMPTY
       arm keeps -- the freer hands them over and keeps everything else *)
    inode_raw (ientry k) -∗
    ic_mid cn k -∗
    icnt_half (bv_unsigned inum) 0%nat -∗
    frzm_h (bv_unsigned inum) false -∗
    escA_inv ge gr gd γi (bv_unsigned inum) rg -∗
    redeem_ticketA gr -∗
    (∃ e, dv_ride (bv_unsigned inum) e) -∗
    (∃ b, fv_ride (bv_unsigned inum) b) -∗
    |==> ic_escrow_body cn γfs γi cov logstart k ∗
         ic_id cn k (1/2) false dev inum ∗
         ipool_shape γfs γi cov logstart inum.
  Proof.
    iIntros "Hg1 Hg2 Hd1 Hd2 Hin Hvld Hraw Hmt Hcnt Hmir #Hesc Htk Hdv Hfv".
    iMod (ic_id_flip cn k true false dev inum dev inum with "Hg1 Hg2")
      as "[Hgf1 Hgf2]".
    iDestruct (word4_pointsto_half_join with "Hd1 Hd2") as "Hd".
    iModIntro.
    iSplitR "Hgf2 Hcnt Hmir Htk Hdv Hfv";
      [| iSplitL "Hgf2"; [iExact "Hgf2" |]].
    { iApply ic_close_empty. rewrite /ic_empty_arm.
      iExists dev, inum, (valid_word v). iFrame. }
    rewrite /ipool_shape. iSplitL "Hcnt"; [iExact "Hcnt" |].
    iSplitL "Hmir"; [iExact "Hmir" |].
    iRight. iRight. rewrite /pool_await. iExists ge, gr, gd, rg.
    iSplitR; [iExact "Hesc" |].
    iSplitL "Htk"; [iExact "Htk" |].
    iSplitL "Hdv"; [iExact "Hdv" | iExact "Hfv"].
  Qed.

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
  Lemma ic_close_frozen cn γfs γi cov logstart k (dev inum : mword 32)
      (v : bool) :
    i_dev (ientry k) ↦₄{DfracOwn (1/2)} dev -∗
    i_inum (ientry k) ↦₄{DfracOwn (1/2)} inum -∗
    i_valid (ientry k) ↦₄ valid_word v -∗
    frzown (bv_unsigned inum) -∗ frzsel k ((1/2)/2)%Qp true -∗
    ic_mid cn k -∗
    ic_id cn k (1/2) true dev inum -∗
    ic_escrow_body cn γfs γi cov logstart k.
  Proof.
    iIntros "Hd Hn Hv Hrc Hsel Hm Hg". iLeft.
    rewrite /ic_parked. iExists dev, inum, v, inhabitant.
    iFrame "Hd Hn Hv Hm Hg".
    iApply (ic_payload_arm_frz with "Hrc Hsel").
  Qed.

  (* ...and its opener.  The freer identifies the arm by the identity slice it
     kept when the window exit split [i_inum] three ways (its own [q], the
     arm's ½ and the table's ½ − q), refutes OUT with the sleeplock's own
     token, MID/HELD/EMPTY with the cells, and [ic_parked]'s ORDINARY
     alternative with the [ifreeze_pre] in its hand. *)
  Lemma ic_open_frozen cn γfs γi cov logstart k (q : Qp) (dev inum : mword 32)
      (rg : bool) :
    ic_escrow_body cn γfs γi cov logstart k -∗
    ifreeze_pre rg (bv_unsigned inum) -∗
    inode_ident k (DfracOwn q) dev inum -∗
    ic_tok cn k -∗
    ifreeze_pre rg (bv_unsigned inum) ∗ inode_ident k (DfracOwn q) dev inum ∗
    ic_tok cn k ∗ frzown (bv_unsigned inum) ∗ frzsel k ((1/2)/2)%Qp true ∗
    (∃ v : bool,
       i_dev (ientry k) ↦₄{DfracOwn (1/2)} dev ∗
       i_inum (ientry k) ↦₄{DfracOwn (1/2)} inum ∗
       i_valid (ientry k) ↦₄ valid_word v ∗
       ic_mid cn k ∗
       ic_id cn k (1/2) true dev inum).
  Proof.
    iIntros "Hbody Hpre Hid Htok".
    iDestruct "Hid" as "[Hrd Hrn]".
    iDestruct "Hbody" as "[Hpk | [Hout | [Hmid | [Hvg | Hhd]]]]".
    - iDestruct "Hpk" as (dev' inum' v ga) "(Hidv & Hin & Hvld & Hpay & Hmid & Hgid)".
      iDestruct (word4_pointsto_agree with "Hrd Hidv") as %<-.
      iDestruct (word4_pointsto_agree with "Hrn Hin") as %<-.
      iDestruct (ic_payload_arm_decide_frz with "Hpre Hpay") as "(Hpre & Hrc & Hsel)".
      iFrame "Hpre Hrd Hrn Htok Hrc Hsel".
      iExists v. iFrame.
    - iDestruct "Hout" as (d' dev' inum') "(Hdep' & _ & _ & _)".
      iExFalso. iApply (ic_tok_deposit_excl with "Htok Hdep'").
    - iDestruct "Hmid" as (dev' inum' w) "(_ & Hin & _ & _ & _)".
      iExFalso. iApply (ic_word4_excl with "Hin Hrn").
    - iDestruct "Hvg" as (dev' inum' w) "(Hidv & _ & _ & _ & _ & _)".
      iExFalso. iApply (ic_word4_excl with "Hidv Hrd").
    - iDestruct "Hhd" as (dev' inum' w) "(_ & Hin & _ & _ & _)".
      iExFalso. iApply (ic_word4_excl with "Hin Hrn").
  Qed.

  (* (e) THE RECYCLER'S RE-OPEN AT ITS VALID STORE (iget, +0x7c)
     (BioInv.escrow_open_mid).

     Its recycle token refutes BOTH normal arms, so the body is the window
     it parked; the reclose is at a normal parked arm, which re-absorbs the
     token.  The valid cell comes out for the physical [sw zero,64(s3)], and
     the inum cell comes out FULL so that the closer can split ½ back to the
     table and leave ½ in the arm. *)
  Lemma ic_open_mid cn γfs γi cov logstart k :
    ic_mid cn k -∗
    ic_escrow_body cn γfs γi cov logstart k -∗
    ic_mid cn k ∗ ic_mid_arm cn γfs γi cov logstart k.
  Proof.
    iIntros "Hmt Hbody".
    iDestruct "Hbody" as "[Hpk | [Hout | [Hmid | [Hvg | Hhd]]]]".
    - iDestruct "Hpk" as (dev inum v ga) "(_ & _ & _ & _ & Hmt' & _)".
      iExFalso. iApply (ic_mid_exclusive with "Hmt Hmt'").
    - iDestruct "Hout" as (q dev inum) "(_ & _ & Hmt' & _)".
      iExFalso. iApply (ic_mid_exclusive with "Hmt Hmt'").
    - iFrame.
    - iDestruct "Hvg" as (dev inum w) "(_ & _ & _ & _ & Hmt' & _)".
      iExFalso. iApply (ic_mid_exclusive with "Hmt Hmt'").
    - (* HELD (§13.13): it parks the recycle token, which is exactly why it
         does -- so that this line, which the recycler already had, covers
         the new arm with no new token anywhere. *)
      iDestruct "Hhd" as (dev inum w) "(_ & _ & _ & Hmt' & _)".
      iExFalso. iApply (ic_mid_exclusive with "Hmt Hmt'").
  Qed.

  (* the reclose after the valid store: the window's FULL inum cell splits
     back into the arm's permanent half and the half the table retains, and
     the parked arm is deposited at v = false (the recycled entry is
     unloaded by construction).  Stating the split HERE is what keeps
     iget's proof from having to know the budget.

     THIS IS WHERE THE FRESH GENERATION'S PENDING ONE-SHOT LANDS (design
     §17.6 (1)/(3)).  [IcacheInv.live_slot_alloc] minted it four instructions
     earlier with the [sw 1] to [ip->ref]; the recycler carries it (and the
     arm's 1/2) by hand from +0x78 to here, because MID was sealed before any
     unit existed to split.  Until §17.6 this proof simply DROPPED it. *)
  Lemma ic_close_mid_to_parked cn γfs γi cov logstart k (dev inum : mword 32)
      (g : gname) :
    ic_mid cn k -∗
    ic_id cn k (1/2) true dev inum -∗
    i_dev (ientry k) ↦₄{DfracOwn (1/2)} dev -∗
    i_inum (ientry k) ↦₄ inum -∗
    i_valid (ientry k) ↦₄ valid_word false -∗
    ic_unloaded γfs γi cov logstart k inum -∗
    live_gen k (1/2) g -∗
    ity_pending g -∗
    (* THE PEELED TOKEN (iclaim-ledger.md §3.9).  The recycler took the
       inum's [ifreeze_off] out of the pool at [ipool_shape_to_np] and
       [IcacheInv.iref_alloc_store_au] handed it straight back ("the token
       travels on into the entry's parked arm" -- that lemma's own header);
       this is where it lands. *)
    ifreeze_off (bv_unsigned inum) -∗
    ic_escrow_body cn γfs γi cov logstart k ∗
    i_inum (ientry k) ↦₄{DfracOwn (1/2)} inum.
  Proof.
    iIntros "Hmt Hgid Hid Hin Hvld Hpay Hlv Hpend Hoff".
    iDestruct (word4_pointsto_half_split with "Hin") as "[Hin1 Hin2]".
    iSplitR "Hin2"; [| iExact "Hin2"].
    iLeft. rewrite /ic_parked.
    iExists dev, inum, false, g.
    iSplitL "Hid"; [iExact "Hid" |]. iSplitL "Hin1"; [iExact "Hin1" |].
    iSplitL "Hvld"; [iExact "Hvld" |].
    iSplitL "Hpay Hpend Hoff Hlv";
      [rewrite /ic_payload_arm /ic_payload_np; iLeft;
       iSplitR "Hoff Hlv";
         [iSplitL "Hpay"; [iExact "Hpay" | iExact "Hpend"]
         | iSplitL "Hoff"; [iExact "Hoff" | iExact "Hlv"]] |].
    iSplitL "Hmt"; [iExact "Hmt" | iExact "Hgid"].
  Qed.

  (* (f) BORROWING THE ARM'S REFERENCE, for a lock-free read INSIDE the
     critical section (iunlock's [ip->ref] panic guard).

     A thread that has checked the entry out holds the payload and nothing
     reference-shaped -- the deviation note in the header -- but it does hold
     the FULL valid cell, which refutes PARKED and MID.  So it can open the
     escrow and borrow from OUT for the duration of one atomic update.

     WHAT IT BORROWS IS THE LIVENESS SLICE, NOT A REFERENCE (§14.8).  Under the
     descriptor the arm may hold a SHARE, which has no count fragment at all
     ([positiveR] has no zero, §14.5) -- but both deposit shapes carry a slice
     of the slot's liveness unit, and a slice is exactly what the [ip->ref]
     guard read needs ([IcacheInv.iref_live_load_au], the share-holder's twin of
     [iref_load_au]).  The borrow is therefore INDEPENDENT of the kind, and the
     caller needs no descriptor half to perform it. *)
  (* IVd: THE BORROWER NOW NAMES ITS OWN DESCRIPTOR.  Under the widened
     [ic_out] the arm may be on the FROZEN alternative, which holds no live
     mass at all -- the freer parked it -- so there is nothing to borrow and
     the case must be refuted rather than served.  The refuter is the caller's
     own half of the descriptor variable: the frozen window deposits a
     [DepFrz], which names no generation, every ordinary checkout deposits one
     that does, and [ic_deposit_agree] closes it.  The half is free at both
     call sites (it is what [ic_swap_park] will consume at the park) and it is
     handed straight back. *)
  Lemma ic_open_out cn γfs γi cov logstart k (d0 : ic_dep) (g0 : gname)
      (v : bool) :
    ic_dep_gname d0 = Some g0 ->
    ic_escrow_body cn γfs γi cov logstart k -∗
    i_valid (ientry k) ↦₄ valid_word v -∗
    ic_deposit cn k d0 -∗
    i_valid (ientry k) ↦₄ valid_word v ∗
    ic_deposit cn k d0 ∗
    (∃ s : Qp,
       live_frac k s ∗
       (live_frac k s -∗ ic_escrow_body cn γfs γi cov logstart k)).
  Proof.
    iIntros (Hd0) "Hbody Hvld Hdep0".
    iDestruct "Hbody" as "[Hpk | [Hout | [Hmid | [Hvg | Hhd]]]]".
    - iDestruct "Hpk" as (dev' inum v' ga) "(_ & _ & Hvld' & _ & _ & _)".
      iExFalso. iApply (ic_word4_excl with "Hvld Hvld'").
    - iDestruct "Hout" as (d dev inum) "(Hdep & Hres & Hmt & Hgid)".
      iDestruct (ic_deposit_agree with "Hdep0 Hdep") as %<-.
      iDestruct "Hres" as "[Hres | Hfrz]".
      2:{ rewrite /ic_out_frz. destruct d0; try (iDestruct "Hfrz" as "[]").
          cbn in Hd0. discriminate. }
      iDestruct (ic_dep_res_live with "Hres") as (s) "[Hlv Hresb]".
      iFrame "Hvld Hdep0". iExists s. iFrame "Hlv".
      iIntros "Hlv". iRight; iLeft. rewrite /ic_out.
      iExists d0, dev, inum. iFrame "Hdep Hmt Hgid". iLeft.
      iApply ("Hresb" with "Hlv").
    - iDestruct "Hmid" as (dev' inum w) "(_ & _ & Hvld' & _ & _)".
      iExFalso. iApply (ic_word4_excl with "Hvld Hvld'").
    - iDestruct "Hvg" as (dev' inum w) "(_ & _ & Hvld' & _ & _ & _)".
      iExFalso. iApply (ic_word4_excl with "Hvld Hvld'").
    - (* HELD (§13.13): the FULL valid cell again *)
      iDestruct "Hhd" as (dev' inum w) "(_ & _ & Hvld' & _ & _)".
      iExFalso. iApply (ic_word4_excl with "Hvld Hvld'").
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  4b. THE AUTHORITY-SIDE WINDOW (§13.13) -- iput's, and only iput's   *)
  (* ------------------------------------------------------------------ *)

  (* CLOSING INTO THE WINDOW.  Trivial, like [ic_close_mid] / [ic_close_empty]:
     the entering holder has already opened the parked arm with
     [ic_open_auth_ref] (whose rebuild wand it simply does not use), joined
     the inum cell to FULL out of its own reference share and the table's,
     and kept the payload. *)
  Lemma ic_close_held cn γfs γi cov logstart k :
    ic_held cn k -∗ ic_escrow_body cn γfs γi cov logstart k.
  Proof. iIntros "H". iRight; iRight; iRight; iRight. iExact "H". Qed.

  (* ...and closing back at OUT, which is where the window EXITS: the
     checkout state, reached by hand rather than through
     [ic_swap_checkout] because the payload never went back into the
     invariant in between.  Same arm, same contents -- this is only the
     constructor, exported so ProofIput need not unfold [ic_escrow_body]. *)
  Lemma ic_close_out cn γfs γi cov logstart k (d : ic_dep) (dev inum : mword 32) :
    ic_deposit cn k d -∗
    ic_dep_res k d dev inum -∗
    ic_mid cn k -∗
    ic_id cn k (1/2) true dev inum -∗
    ic_escrow_body cn γfs γi cov logstart k.
  Proof.
    iIntros "Hdep Hres Hmt Hgid".
    (* [iFrame] takes the LEFT alternative on its own: the frozen one needs a
       [frzown] nobody here has. *)
    iRight; iLeft. rewrite /ic_out. iExists d, dev, inum. iFrame.
  Qed.

  (* ...AND THE FREE PATH'S WINDOW EXIT (IVd, +0x5e), which closes at the
     SECOND alternative.  What goes in is the reference MINUS its two live
     slices -- those are in [islot2]'s frozen park from the +0x62 re-park --
     plus the freeze RECEIPT the mint produced.  What stays in the freer's
     hand is what itrunc needs: the ½ dev and inum cells, the whole valid
     cell, and the payload (B2's dissolution).

     The descriptor is [DepFrz q dev inum]: the freer keeps one half and gives
     the arm the other, so that no concurrent checkout can agree with it, the
     fraction it will want back is written down, and the +0x70 park can rejoin
     the two halves into [ic_tok] for releasesleep. *)
  Lemma ic_close_out_frz cn γfs γi cov logstart k (dev inum : mword 32)
      (qf : Qp) :
    ic_deposit cn k (DepFrz qf dev inum) -∗
    iref_frag k qf -∗
    inode_ident k (DfracOwn qf) dev inum -∗
    frzown (bv_unsigned inum) -∗ frzsel k ((1/2)/2)%Qp true -∗
    ic_mid cn k -∗
    ic_id cn k (1/2) true dev inum -∗
    ic_escrow_body cn γfs γi cov logstart k.
  Proof.
    iIntros "Hdep Hfr Hid Hrc Hsel Hmt Hgid".
    iRight; iLeft. rewrite /ic_out. iExists (DepFrz qf dev inum), dev, inum.
    iFrame "Hdep Hmt Hgid". iRight.
    rewrite /ic_out_frz. iSplitR; [iPureIntro; split; reflexivity |].
    iFrame "Hfr Hid Hrc Hsel".
  Qed.

  (* full ownership of a word is EXCLUSIVE -- [FileOff.word4_pointsto_excl]
     restated, because this file must not depend on the file layer *)
  Local Lemma iesc_word4_excl (a : Arch.pa) (dq : dfrac) (w1 w2 : bv 32) :
    a ↦₄ w1 -∗ a ↦₄{dq} w2 -∗ False.
  Proof.
    iIntros "H1 H2".
    rewrite !word4_pointsto_unfold.
    iDestruct "H1" as "[_ H1]". iDestruct "H2" as "[_ H2]".
    change (seq 0 4) with ([0; 1; 2; 3]%nat).
    iDestruct "H1" as "[Hb1 _]". iDestruct "H2" as "[Hb2 _]".
    iDestruct (mem_pointsto_ne with "Hb1 Hb2") as %Hne.
    iPureIntro. exact (Hne eq_refl).
  Qed.

  (* EVERY PAYLOAD OWNS THIS ENTRY'S METADATA CELLS, on both polarities and
     on both pool shapes: the loaded arm holds [inode_meta] outright, the
     unloaded one holds it inside [InodeLock.inode_raw].  That is the
     credential half of the window's re-open.

     (§16.4 replaced the old [ic_payload_dinode] here.  That lemma pulled a
     [dinode_at] out of any payload and refuted a rival arm by
     [InodeRegion.dinode_at_excl]; since the free arm slimmed to a MARKER,
     no [dinode_at] is extractable from it.  The metadata CELLS are a
     strictly better credential anyway -- they are slot-keyed rather than
     inum-keyed, so the refutation no longer needs [ic_id_agree] to pin the
     two arms' inums first.) *)
  (* the UNLOADED stock's own credential.  It is stated separately from
     [ic_payload_size] because since §17.6 [ic_unloaded] is no longer
     definitionally [ic_payload … false] -- the pending one-shot rides beside
     it -- and [ic_mid_arm] holds the bare [ic_unloaded]. *)
  Local Lemma ic_unloaded_size γfs γi cov logstart k inum :
    ic_unloaded γfs γi cov logstart k inum -∗
    ∃ w : bv 32, i_size (ientry k) ↦₄ w.
  Proof.
    rewrite /ic_unloaded /inode_raw.
    iIntros "[[Hmeta _] _]".
    iDestruct "Hmeta" as (d) "Hmeta".
    rewrite /inode_meta. iDestruct "Hmeta" as "(_ & _ & _ & _ & Hsz)".
    iExists (di_size d). iExact "Hsz".
  Qed.

  Local Lemma ic_payload_size γfs γi cov logstart k inum g (v : bool) :
    ic_payload_np γfs γi cov logstart k inum g v -∗
    ∃ w : bv 32, i_size (ientry k) ↦₄ w.
  Proof.
    rewrite /ic_payload_np. destruct v.
    - iIntros "Hpay".
      iDestruct "Hpay" as (dn bm) "[Hlk _]".
      iDestruct "Hlk" as (data) "(_ & _ & _ & _ & _ & _ & _ & Hmeta & _)".
      rewrite /inode_meta. iDestruct "Hmeta" as "(_ & _ & _ & _ & Hsz)".
      iExists (di_size dn). iExact "Hsz".
    - iIntros "[Hu _]". iApply (ic_unloaded_size with "Hu").
  Qed.

  Lemma ic_payload_excl γfs γi cov logstart k inum1 inum2 g1 g2 (v1 v2 : bool) :
    ic_payload γfs γi cov logstart k inum1 g1 v1 -∗
    ic_payload γfs γi cov logstart k inum2 g2 v2 -∗ False.
  Proof.
    iIntros "H1 H2".
    iDestruct (ic_payload_split with "H1") as "[Hp1 _]".
    iDestruct (ic_payload_split with "H2") as "[Hp2 _]".
    iDestruct (ic_payload_size with "Hp1") as (w1) "H1".
    iDestruct (ic_payload_size with "Hp2") as (w2) "H2".
    iApply (iesc_word4_excl with "H1 H2").
  Qed.

  (* ...and the same against a bare MID stock, which is what [ic_open_held]'s
     third branch meets (§17.6: [ic_mid_arm] holds [ic_unloaded] directly). *)
  Lemma ic_payload_unloaded_excl γfs γi cov logstart k inum1 inum2 g1 (v1 : bool) :
    ic_payload γfs γi cov logstart k inum1 g1 v1 -∗
    ic_unloaded γfs γi cov logstart k inum2 -∗ False.
  Proof.
    iIntros "H1 H2".
    iDestruct (ic_payload_split with "H1") as "[Hp1 _]".
    iDestruct (ic_payload_size with "Hp1") as (w1) "H1".
    iDestruct (ic_unloaded_size with "H2") as (w2) "H2".
    iApply (iesc_word4_excl with "H1 H2").
  Qed.

  (* The size cell of a record-named payload -- the ONE thing the window
     opener below uses its caller's bundle for (both refutations go through
     it), which is why that opener can be stated at [ic_payload_at] with no
     other change to its proof. *)
  Local Lemma ic_payload_at_size γfs γi cov logstart k inum g dn bm :
    ic_payload_at γfs γi cov logstart k inum g dn bm -∗
    ∃ w : bv 32, i_size (ientry k) ↦₄ w.
  Proof.
    iIntros "Hpay".
    iApply (ic_payload_size γfs γi cov logstart k inum g true).
    iApply (ic_payload_at_pack_np with "Hpay").
  Qed.



  (* RE-OPENING THE WINDOW.  iput does this TWICE, on two different paths,
     and that is what fixes the credential: once at the post-[acquiresleep]
     checkout (+0x54), and once at +0x44 when [ip->nlink] turns out to be
     nonzero and the window must be UNDONE without truncating -- at which
     point [acquiresleep] has not run and there is no [ic_tok] to be had.  So
     the credential is REF-1, exactly [ic_open_auth_ref]'s, plus the payload:

       [itable_half] at count 1 + the holder's own [iref_tok] kill OUT, by
                    [IcacheInv.iref_tok_two_lookup] -- the arm's reference and
                    the holder's would make the count at least two.  This is
                    also what makes the credential EXCLUSIVE: no second
                    thread can hold a reference to this slot at all;
       the PAYLOAD -- carried across the window, and by [ic_payload_dinode]
                    it names this inum's [dinode_at] -- kills PARKED and MID,
                    whose payloads name it too
                    ([InodeRegion.dinode_at_excl], after [ic_id_agree] has
                    pinned the arm's inum to the holder's);
       the table's [ic_id] half at [true] -- held continuously since the
                    [acquire] at +0x14 -- kills EMPTY.

     What comes back is the arm verbatim: the permanent dev half, the FULL
     inum cell (which the caller re-splits into the arm's ½, its reference's
     q and the table's (½−q)), the stale valid word, the recycle token and
     the escrow's own identification half.  The escrow body is CONSUMED:
     the caller closes with [ic_close_out] (the checkout path) or rebuilds a
     [ic_parked] and closes with [ic_close_parked] (the nlink path).

     TWO GNAMES, NOT ONE (design §17.6 (4)).  At the +0x54 checkout iput has
     already RETIRED the slot's generation ([IcacheInv.live_slot_regen]), so
     the arm-half in its hand is at [g1] while the payload it is carrying is
     still the LOADED one at [g2] -- and it must stay there, because
     restating it at [g1] would mean shooting the fresh pending the +0x74
     park needs.  This costs nothing: the payload is threaded through
     untouched, its only use is refuting PARKED and MID via
     [ic_payload_excl], which is already generic in both gnames, and the OUT
     and EMPTY refutations use REF-1, the live mass and the ghost, never the
     payload's generation.  The stale [ity_shot g2 ty] dies with the
     generation that named it, on iput's own path: itrunc and [ip->type = 0]
     turn [ic_loaded] into raw cells and a marker.  The +0x44 nlink-undo
     caller, which takes no bump, passes the two equal.

     RECORD-PARAMETRIC (design §20.14's (R1), fs-sysfile S5g).  The bundle
     goes in and comes out at the SAME [dn]/[bm] -- [ic_payload_at], not
     [ic_payload]'s existential -- which is what carries iput's +0x40
     reading of [ip->nlink] across the [acquiresleep] window and down to
     the region free, where (L3) needs [di_nlink = 0] of the record it is
     about to write.  Through the existential the record that came back was
     a fresh [dn2] and the zero was lost; that lost fact is the whole of
     S5f's (L1)/(L3) knot.  The polarity is fixed at LOADED because that is
     the only one either caller passes and the only one a record names; the
     [v] parameter is therefore gone.  Nothing else in the proof moves: the
     bundle's only use here is its SIZE cell, in the two refutations. *)
  Lemma ic_open_held cn γfs γi cov logstart k (Eo : coPset)
      (M : gmap nat (Qp * positive)) (q : Qp) (g1 g2 : gname)
      (dev inum : mword 32) (dn : dinode) (bm : blkmap) :
    ↑icacheN ⊆ Eo ->
    M !! k = Some (q, 1%positive) ->
    itable_inv -∗
    ic_escrow_body cn γfs γi cov logstart k -∗
    itable_half M -∗
    (* the reference's two BARE slices, not [iref_tok]: its sleeplock slice
       is in the entry's lock while the holder has it checked out. *)
    iref_frag k q -∗ live_frac k q -∗
    live_gen k (1/2) g1 -∗
    ic_id cn k (1/2) true dev inum -∗
    (* THE HOLDER's OWN HALF OF THE VALID CELL (A⁗, §3.16), borrowed and
       handed straight back.  It is what refutes the FROZEN PARK -- the
       alternative [ic_payload_arm] gained at A⁗, which carries no payload
       and so is invisible to the size-cell argument the ordinary parked arm
       dies on.  The parked arm owns the valid cell WHOLE (both flavours), so
       a half in any hand closes it.  The holder has it by construction: it
       is the half [ic_open_auth_ref] left in its hand at the window-entering
       read. *)
    i_valid (ientry k) ↦₄{DfracOwn (1/2)} (valid_word true) -∗
    ic_payload_at γfs γi cov logstart k inum g2 dn bm -∗
    |={Eo}=>
    itable_half M ∗
    iref_frag k q ∗ live_frac k q ∗
    live_gen k (1/2) g1 ∗
    ic_id cn k (1/2) true dev inum ∗
    i_valid (ientry k) ↦₄{DfracOwn (1/2)} (valid_word true) ∗
    ic_payload_at γfs γi cov logstart k inum g2 dn bm ∗
    i_dev (ientry k) ↦₄{DfracOwn (1/2)} dev ∗
    i_inum (ientry k) ↦₄ inum ∗
    (∃ w : mword 32, i_valid (ientry k) ↦₄{DfracOwn (1/2)} w) ∗
    ic_mid cn k ∗
    ic_id cn k (1/2) true dev inum.
  Proof.
    iIntros (HE HMk) "#Hinv Hbody Hhalf Hfrq Hlvq Hlvh Hgid Hvh Hpay".
    iDestruct "Hbody" as "[Hpk | [Hout | [Hmid | [Hvg | Hhd]]]]".
    - (* PARKED (both flavours): the arm owns the valid cell WHOLE and the
         holder brought a half of it. *)
      iDestruct "Hpk" as (dev' inum' v' ga) "(_ & _ & Hvld' & _ & _ & _)".
      iExFalso. iApply (ic_word4_excl with "Hvld' Hvh").
    - (* OUT: REF-1, on both deposit kinds, exactly as in
         [ic_open_auth_ref] -- the count for a reference, the LIVE mass for a
         share (14.8), the arm's own 1/2 restoring the exact complement
         (17.3 (A)). *)
      iDestruct "Hout" as (d dev' inum') "(_ & Hres & _ & _)".
      iDestruct "Hres" as "[Hres | Hfrz]".
      2:{ (* THE FROZEN ALTERNATIVE (IVd), refuted by REF-1 on the count
             fragment the freer left in the arm -- the live mass is in
             [islot2]'s frozen park and cannot be argued with here. *)
          rewrite /ic_out_frz. destruct d; try (iDestruct "Hfrz" as "[]").
          iDestruct "Hfrz" as "(_ & Hfr' & _ & _)".
          iDestruct (iref_frag_two_lookup with "Hhalf Hfrq Hfr'")
            as %(qt' & n & HMk' & Hn).
          rewrite HMk in HMk'. injection HMk' as _ Hn1. subst n.
          iExFalso. iPureIntro. cbn in Hn. lia. }
      rewrite /ic_dep_res /ic_dep_own /ic_dep_half.
      destruct d as [| q' dv nu gd | s dv nu gd | qf dv nu];
        [| | | iDestruct "Hres" as "[[] _]"].
      + iDestruct "Hres" as "[[] _]".
      + iDestruct "Hres" as "[[_ (Hfr' & Hlv' & _)] _]".
        (* the arm's reference has no sleeplock slice of its own (the lock
           holds it), so the refutation's [iref_tok] borrows the OPENER's --
           which is sound because the two are refuted together. *)
        (* the arm's reference has no sleeplock slice of its own -- the
           entry's LOCK holds it -- so the refutation reads the bare count
           fragments, which is all it ever used. *)
        iDestruct (iref_frag_two_lookup with "Hhalf Hfrq Hfr'")
          as %(qt' & n & HMk' & Hn).
        rewrite HMk in HMk'. injection HMk' as _ Hn1. subst n.
        iExFalso. iPureIntro. cbn in Hn. lia.
      + iDestruct "Hres" as "[[_ [_ Hlvs]] Hhf]".
        iAssert (live_frac k (1/2)%Qp) with "[Hhf]" as "Hfh";
          [iExists gd; iExact "Hhf" |].
        iAssert (live_frac k s) with "[Hlvs]" as "Hfs";
          [iExists gd; iExact "Hlvs" |].
        iMod (live_whole_share_absurd Eo M k q s 1%positive HE HMk
                with "Hinv Hhalf Hlvq Hfh Hfs") as "[]".
    - (* MID: its stock carries this entry's metadata cells too *)
      iDestruct "Hmid" as (dev' inum' w) "(_ & _ & _ & Hpay' & Hgt)".
      iExFalso.
      iDestruct (ic_payload_at_size with "Hpay") as (w1) "Hsz1".
      iDestruct (ic_unloaded_size with "Hpay'") as (w2) "Hsz2".
      iApply (iesc_word4_excl with "Hsz1 Hsz2").
    - (* EMPTY: the identification ghost *)
      iDestruct "Hvg" as (dev' inum' w) "(_ & _ & _ & _ & _ & Hgt)".
      iDestruct (ic_id_agree with "Hgid Hgt") as %(Hc & _ & _). discriminate.
    - iDestruct "Hhd" as (dev' inum' w) "(Hidv & Hin & Hvld & Hmt & Hgt)".
      iDestruct (ic_id_agree with "Hgid Hgt") as %(_ & <- & <-).
      iModIntro.
      iFrame "Hhalf Hfrq Hlvq Hlvh Hgid Hvh Hpay Hidv Hin Hmt Hgt".
      iExists w. iFrame.
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  5.  THE POOL (§13.2 / §13.3)                                       *)
  (* ------------------------------------------------------------------ *)

  (* THE CACHED SET, speakable.  [M] is slot-keyed and value-blind and the
     inums live in identity CELLS, so [itable_res] carries a pure
     slot -> (dev, inum) map alongside; the pool then covers the region's
     inums MINUS the cached ones. *)
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

  Definition ipool (γfs : fs_names) (γi : gname) (cov : gset Z)
      (logstart : Z) (P : gset Z) : iProp Σ :=
    ([∗ set] z ∈ P, ipool_shape γfs γi cov logstart (mword_of_int z))%I.

  Lemma ipool_acc γfs γi cov logstart (P : gset Z) (z : Z) :
    z ∈ P ->
    ipool γfs γi cov logstart P -∗
      ipool_shape γfs γi cov logstart (mword_of_int z) ∗
      ipool γfs γi cov logstart (P ∖ {[z]}).
  Proof.
    intros Hz. rewrite /ipool (big_sepS_delete _ P z Hz). iIntros "[$ $]".
  Qed.

  Lemma ipool_insert γfs γi cov logstart (P : gset Z) (z : Z) :
    z ∉ P ->
    ipool_shape γfs γi cov logstart (mword_of_int z) -∗
    ipool γfs γi cov logstart P -∗
    ipool γfs γi cov logstart ({[z]} ∪ P).
  Proof.
    intros Hz. rewrite /ipool (big_sepS_insert _ P z Hz).
    (* structurally, NOT [iFrame]: the goal's left conjunct is an
       [ipool_shape], whose body is a disjunction of existentials over
       [inode_blocks]' 268-element big-op, and a bare [iFrame] searches all
       of it per hypothesis (106 s measured -- optimization.md's BioInv
       rule: naming fixes the CONTEXT-side scan, a big GOAL still costs a
       goal-side one, so split and [iExact]). *)
    iIntros "H1 H2". iSplitL "H1"; [iExact "H1" | iExact "H2"].
  Qed.

  (* the round trip, so a read-only user needs no set algebra of its own *)
  Lemma ipool_acc_back γfs γi cov logstart (P : gset Z) (z : Z) :
    z ∈ P ->
    ipool γfs γi cov logstart P -∗
      ipool_shape γfs γi cov logstart (mword_of_int z) ∗
      (ipool_shape γfs γi cov logstart (mword_of_int z) -∗
       ipool γfs γi cov logstart P).
  Proof.
    intros Hz. rewrite /ipool (big_sepS_delete _ P z Hz). iIntros "[$ Hr]".
    iIntros "H". iFrame.
  Qed.

  (* [ipool] is NO LONGER Timeless (its pending arm holds an [esc_inv]); the
     instance was unused (verified) and is removed.  The itable free pool is
     lock-held, never [iInv .. as ">"], so Timelessness is not needed there. *)

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
  Definition islot_empty (cn : ic_names) (k : nat) : iProp Σ :=
    (∃ dev inum : mword 32,
       i_inum (ientry k) ↦₄{DfracOwn (1/2)} inum ∗
       ic_id cn k (1/2) false dev inum)%I.

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

  Definition itable_res2 (cn : ic_names) (γfs : fs_names) (γi : gname)
      (cov : gset Z) (logstart : Z) (nib : nat) (dv : mword 32) : iProp Σ :=
    (∃ (M : gmap nat (Qp * positive)) (ci : gmap nat (mword 32 * mword 32)),
       itable_half M ∗
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
       ipool γfs γi cov logstart (region_inums nib ∖ ci_inums ci))%I.

  Definition is_itable2 (γl : gname) (cn : ic_names) (γfs : fs_names)
      (γi : gname) (cov : gset Z) (logstart : Z) (nib : nat)
      (dv : mword 32) : iProp Σ :=
    is_lock γl itable_lock "itable"%string
      (itable_res2 cn γfs γi cov logstart nib dv).

  Global Instance is_itable2_persistent γl cn γfs γi cov logstart nib dv :
    Persistent (is_itable2 γl cn γfs γi cov logstart nib dv).
  Proof. apply _. Qed.

  (* the slot accessor a WRITER needs: BOTH pure maps may come back changed,
     provided they changed only at [k].  [IcacheInv.islots_acc_upd]'s shape
     and proof, with one more map to carry. *)
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
         is_sleeplock_gen γil γisl (i_lock (ientry k)) "inode"%string
                          (ic_tok cn k) (slh_tok (icfg_isl k)))%I.

  Global Instance ic_sleeplocks_persistent cn : Persistent (ic_sleeplocks cn).
  Proof. apply _. Qed.

  (* ...AND ITS ACCESSOR.  This is the ONLY copy of either; every consumer
     projects the family through this lemma.  Do not restate it in a
     caller's own file -- seven files did, and retiring the seven is what
     made [IcacheBoot.v] stop being a second home for the family. *)
  Lemma ic_sleeplocks_lookup (cn : ic_names) (k : nat) :
    (k < NINODE)%nat ->
    ic_sleeplocks cn -∗
    ∃ γil γisl : gname,
      is_sleeplock_gen γil γisl (i_lock (ientry k)) "inode"%string
                       (ic_tok cn k) (slh_tok (icfg_isl k)).
  Proof.
    iIntros (Hk) "H". rewrite /ic_sleeplocks.
    assert (Hl : seq 0 NINODE !! k = Some k) by (rewrite lookup_seq; lia).
    iDestruct (big_sepL_lookup _ _ k k Hl with "H") as "$".
  Qed.

End IcacheEscrow.

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
      ([∗ list] k ∈ seq 0 NINODE, ic_mid cn k) ∗
      ([∗ list] k ∈ seq 0 NINODE, ic_id cn k 1 false (dvs k).1 (dvs k).2).
  Proof.
    iMod (ic_dep_fun_alloc NINODE 0) as (fesc) "Hesc".
    iMod (ic_tok_fun_alloc NINODE 0) as (fmid) "Hmid".
    iMod (ic_id_fun_alloc dvs NINODE 0) as (fid) "Hid".
    iModIntro. iExists (MkIcNames fesc fmid fid).
    rewrite /ic_tok /ic_mid /ic_id.
    cbn [icn_esc icn_mid icn_id].
    iFrame.
  Qed.

End IcacheEscrowAlloc.
