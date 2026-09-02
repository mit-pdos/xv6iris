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
  Context `{XI : CurCtx}.

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
  Global Instance ic_tok_timeless cn k : Timeless (ic_tok cn k).
  Proof. rewrite /ic_tok. apply _. Qed.

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
  (* ---- THE LINKS CONJUNCT, DURING THE FLIP (durable-disk 2b-inode-5) --

     The payload's links half is the counting RA's TOKENS
     ([FsStateInode.ent_toks] at this payload's own node): one per entry of
     this directory that names another inum, drawn out of that inum's
     region-side authority at the [iupdate] that raised its count.

     WHILE THE LEDGER IS STILL ALIVE the two supplies ride TOGETHER in one
     conjunct.  That is what keeps the flip off the ~forty payload sites
     that only pass the conjunct through: their [iDestruct] patterns and
     their [with "[...]"] selections do not move at all, and only the
     handful of walks that actually SPEND or MINT a unit open the pair.
     When [DirLinks.v] goes, this definition loses its first conjunct and
     the payloads keep their arity again. *)
  Definition dlinks (γfs : fs_names) (self : Z) (dn : dinode) (bm : blkmap)
      (data : nat -> list (bv 8)) : iProp Σ :=
    (dir_links self dn data
     ∗ FsStateInode.ent_toks (fs_gamma_L γfs) self
         (era_node dn bm data))%I.

  Global Instance dlinks_timeless γfs self dn bm data :
    Timeless (dlinks γfs self dn bm data).
  Proof. rewrite /dlinks. apply _. Qed.

  Lemma dlinks_open γfs self dn bm data :
    dlinks γfs self dn bm data -∗
      dir_links self dn data
      ∗ FsStateInode.ent_toks (fs_gamma_L γfs) self (era_node dn bm data).
  Proof. iIntros "H"; iExact "H". Qed.

  Lemma dlinks_intro γfs self dn bm data :
    dir_links self dn data -∗
    FsStateInode.ent_toks (fs_gamma_L γfs) self (era_node dn bm data) -∗
    dlinks γfs self dn bm data.
  Proof. iIntros "H1 H2". iFrame. Qed.

  (* the two free discharges: a NON-directory owns no links at all, and
     neither does a record whose size is zero (a claim box, a corpse) *)
  Lemma dlinks_not_dir γfs self dn bm data :
    bv_unsigned (di_type dn) <> T_DIR_z -> ⊢ dlinks γfs self dn bm data.
  Proof.
    intros Hne. rewrite /dlinks. iSplitR.
    - iApply (dir_links_not_dir self dn data Hne).
    - iApply (FsStateEra.ent_toks_era_not_dir _ self dn bm data Hne).
  Qed.

  Lemma dlinks_size_zero γfs self dn bm data :
    bv_unsigned (di_size dn) = 0 ->
    bv_unsigned (di_nlink dn) <= 1 -> ⊢ dlinks γfs self dn bm data.
  Proof.
    intros Hsz Hnl. rewrite /dlinks. iSplitR.
    - iApply (dir_links_size_zero self dn data Hsz Hnl).
    - iApply (FsStateEra.ent_toks_era_size0 _ self dn bm data Hsz).
  Qed.

  Definition ipool_alloc (γfs : fs_names) (γi : gname) (cov : gset Z)
      (logstart : Z) (inum : mword 32) : iProp Σ :=
    (∃ (dn0 : dinode) (bm0 : blkmap) (data0 : nat -> list (bv 8)),
       ⌜inode_ok cov logstart dn0 bm0 data0⌝ ∗
       ⌜dir_ok icfg_nib dn0 data0⌝ ∗
       ⌜dir_dots_ix (bv_unsigned inum) dn0 data0⌝ ∗
       ⌜dir_orphan_clean dn0 data0⌝ ∗
       ⌜dir_uniq dn0 data0⌝ ∗
       dlinks γfs (bv_unsigned inum) dn0 bm0 data0 ∗
       inode_owned_era γfs γi inum (era_node dn0 bm0 data0) ∗
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
        (∃ b, fv_ride (bv_unsigned inum) b) ∗
        (* ...AND THE ERA'S ABSTRACT VALUE, UNTIED FOR THE SAME REASON
           (durable-disk 2b-inode-3).  Every inum in the region owns exactly
           one [top_frag]; on the ALLOCATED arm it rides tied inside
           [inode_owned_era], and a free inum's has to be somewhere or
           ialloc could never mint the bundle for the inode it claims.  It
           is the POOL's marker arm and not the region's slot because this
           is where a free inum's other untied holds already live, and
           because the region's [ireg_slot] is destructured at twenty
           accessors that have no business seeing it. *)
        (∃ n : fs_node, top_frag (fs_gamma_L γfs) (bv_unsigned inum) n)))%I.

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
      (* THE ERA'S ABSTRACT VALUE RIDES BESIDE THE TWO IN-TRANSITION ARMS
         (durable-disk 2b-inode-3), untied, exactly as it does on the
         marker arm inside [ipool_shape_np].  It sits OUTSIDE
         [pool_pending] / [pool_await] so that neither of those keeps its
         [γfs]-free arity. *)
      ∨ (pool_pending γi (bv_unsigned inum)
         ∗ (∃ n : fs_node, top_frag (fs_gamma_L γfs) (bv_unsigned inum) n))
      ∨ (pool_await γi (bv_unsigned inum)
         ∗ (∃ n : fs_node, top_frag (fs_gamma_L γfs) (bv_unsigned inum) n))))%I.

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
    iDestruct "H" as "[Hcnt [Hmir [[Hnp Hoff] | [[Hpp Htop] | [Haw Htop]]]]]".
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
        iSplitL "Hdv"; [iExact "Hdv" |].
        iSplitL "Hfv"; [iExact "Hfv" | iExact "Htop"]. }
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
        iSplitL "Hdv"; [iExact "Hdv" |].
        iSplitL "Hfv"; [iExact "Hfv" | iExact "Htop"]. }
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
       dlinks γfs (bv_unsigned inum) dn bm data ∗
       (* THE OWNERSHIP IS THE ERA BUNDLE (durable-disk 2b-inode-3), at this
          payload's own node.  It CONTAINS what three conjuncts used to say
          separately -- [dinode_at], [ind_res] and [inode_blocks] -- and
          adds the era's abstract value [top_frag], which is what a holder
          retags at its writes ([InodeRegion.ireg_top_retag]).  A consumer
          that wants the old shape back applies [ic_loaded_open], an
          ordinary entailment; see [ipool_alloc]'s note for why [inode_ok]
          stays a conjunct rather than being derived. *)
       inode_owned_era γfs γi inum (era_node dn bm data) ∗
       inode_meta (ientry k) dn ∗
       inode_addrs (ientry k) (bm_cells bm) ∗
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
    dv_ride (bv_unsigned inum) (dv_of dn data) -∗
    fv_ride (bv_unsigned inum) (fv_of dn data) -∗
    top_frag (fs_gamma_L γfs) (bv_unsigned inum) (era_node dn bm data) -∗
    ic_loaded γfs γi cov logstart k inum dn bm.
  Proof.
    intros Hok Hrl Hdok Hddix Hdoc Hduq.
    iIntros "Hl Hd Hm Ha Hr Hb Hv Hw Ht".
    pose proof (node_shape_ok_of_inode_ok cov logstart dn bm data Hok) as Hsh.
    pose proof (inode_local_of_ok_rec (bv_unsigned inum) cov logstart dn bm
                  data Hok Hrl Hduq Hddix) as Hloc.
    pose proof Hok as Hok'. destruct Hok' as (_ & _ & _ & Hty & _ & _ & _).
    rewrite /ic_loaded.
    iExists data. iSplitR; [done |]. iSplitR; [done |]. iSplitR; [done |].
    iSplitR; [done |]. iSplitR; [done |].
    iSplitL "Hl"; [iExact "Hl" |].
    iSplitR "Hm Ha Hv Hw".
    { iApply (inode_owned_era_era_node_of γfs γi inum dn bm data Hsh Hloc
                with "Hd Hr Hb Ht"). }
    iSplitL "Hm"; [iExact "Hm" |]. iSplitL "Ha"; [iExact "Ha" |].
    iSplitL "Hv"; [iExact "Hv" | iExact "Hw"].
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
       dv_ride (bv_unsigned inum) (dv_of dn data) ∗
       (* LAST, and that position is load-bearing: a consumer's existing
          eight-name spatial pattern binds its last name to
          [fv_ride ∗ top_frag], so the flip costs the ~forty payload sites
          one PURE conjunct and no re-plumbing of any [with "[...]"]
          selection at all. *)
       fv_ride (bv_unsigned inum) (fv_of dn data) ∗
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
      "(%Hok & %Hdok & %Hddix & %Hdoc & %Hduq & Hl & Hn & Hm & Ha & Hv & Hw)".
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
    iSplitL "Hb"; [iExact "Hb" |].
    iSplitL "Hv"; [iExact "Hv" |].
    iSplitL "Hw"; [iExact "Hw" | iExact "Ht"].
  Qed.

  Lemma ic_loaded_flat γfs γi cov logstart k (inum : mword 32)
      (dn : dinode) (bm : blkmap) :
    ic_loaded_flat_body γfs γi cov logstart k inum dn bm -∗
    ic_loaded γfs γi cov logstart k inum dn bm.
  Proof.
    rewrite /ic_loaded_flat_body. iIntros "H".
    iDestruct "H" as (data)
      "(%Hok & %Hrl & %Hdok & %Hddix & %Hdoc & %Hduq & Hl & Hd & Hm & Ha & Hr & Hb
        & Hv & Hw & Ht)".
    iApply (ic_mk_loaded γfs γi cov logstart k inum dn bm data
              Hok Hrl Hdok Hddix Hdoc Hduq
              with "Hl Hd Hm Ha Hr Hb Hv Hw Ht").
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
    (* ...and the era's abstract value, untied, which the freer's payload
       carried in ([FsStateEra.inode_owned_era]'s [top_frag]) *)
    (∃ n : fs_node, top_frag (fs_gamma_L γfs) (bv_unsigned inum) n) -∗
    ipool_shape γfs γi cov logstart inum.
  Proof.
    iIntros "Hcnt Hmir #Hesc Htk Hdv Hfv Htop". rewrite /ipool_shape.
    iSplitL "Hcnt"; [iExact "Hcnt" |].
    iSplitL "Hmir"; [iExact "Hmir" |].
    iRight. iRight. iSplitR "Htop"; [| iExact "Htop"].
    rewrite /pool_await. iExists ge, gr, gd, rg.
    iSplitR; [iExact "Hesc" |].
    iSplitL "Htk"; [iExact "Htk" |].
    iSplitL "Hdv"; [iExact "Hdv" | iExact "Hfv"].
  Qed.

  (* R3.3: ic_payload_excl / ic_payload_unloaded_excl retired with the arms
     (no user outside them). *)


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
   F16  iput's own (e)/(f) run at mass 1 with the WHOLE unit: DepRef stays
        as the descriptor of that hold (its identity fraction q, its slice,
        its count fragment, hold mass 1).  ic_deposit2 has both arms.
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

  (* the payload's GHOST side: [ic_loaded] minus its two cell conjuncts
     ([inode_meta], [inode_addrs]), verbatim otherwise *)
  Definition ic_loaded_ghost (γfs : fs_names) (γi : gname) (cov : gset Z)
      (logstart : Z) (inum : mword 32) (dn : dinode) (bm : blkmap) : iProp Σ :=
    (∃ (data : nat -> list (bv 8)),
       ⌜inode_ok cov logstart dn bm data⌝ ∗
       ⌜dir_ok icfg_nib dn data⌝ ∗
       ⌜dir_dots_ix (bv_unsigned inum) dn data⌝ ∗
       ⌜dir_orphan_clean dn data⌝ ∗
       ⌜dir_uniq dn data⌝ ∗
       dlinks γfs (bv_unsigned inum) dn bm data ∗
       inode_owned_era γfs γi inum (era_node dn bm data) ∗
       dv_ride (bv_unsigned inum) (dv_of dn data) ∗
       fv_ride (bv_unsigned inum) (fv_of dn data))%I.

  (* the identity-keyed payload at a shape: today's [ic_payload_arm] with
     the cells removed.  An IDENTIFIED slot is never raw. *)
  Definition ic_pay (γfs : fs_names) (γi : gname) (cov : gset Z) (logstart : Z)
      (k : nat) (inum : mword 32) (x : ic_x) : iProp Σ :=
    match x with
    | IcRaw => False%I
    | IcUnloaded g =>
        ((ipool_shape_np γfs γi cov logstart inum ∗ ity_pending g ∗
          ifreeze_off (bv_unsigned inum) ∗ live_gen k (1/2) g)
         ∨ (frzown (bv_unsigned inum) ∗ frzsel k ((1/2)/2)%Qp true))%I
    | IcLoaded g dn bm =>
        ((ic_loaded_ghost γfs γi cov logstart inum dn bm ∗ ity_shot g (di_type dn) ∗
          ifreeze_off (bv_unsigned inum) ∗ live_gen k (1/2) g)
         ∨ (frzown (bv_unsigned inum) ∗ frzsel k ((1/2)/2)%Qp true))%I
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
  Definition ic_hdr_amb (γfs : fs_names) (γi : gname) (cov : gset Z) (logstart : Z)
      (k : nat) (i : ic_bid) (x : ic_x) : iProp Σ :=
    match i with
    | None =>
        (⌜x = IcRaw⌝ ∗
         (∃ v : mword 32, i_valid (ientry k) ↦₄ v) ∗
         (∃ dev inum : mword 32, inode_ident k (DfracOwn (1/2)) dev inum) ∗
         (∃ n : bv 16, i_nlink (ientry k) ↦₂ n))%I
    | Some (dev, inum) =>
        (i_valid (ientry k) ↦₄ valid_word (ic_x_loaded x) ∗
         inode_ident k (DfracOwn (1/2)) dev inum ∗
         (match x with
          | IcLoaded _ dn _ => i_nlink (ientry k) ↦₂ di_nlink dn
          | _ => ∃ n : bv 16, i_nlink (ientry k) ↦₂ n
          end) ∗
         ic_pay γfs γi cov logstart k inum x)%I
    end.

  (* M-1': the dead header's shape is known *)
  Lemma ic_hdr_dead_raw γfs γi cov logstart k x :
    ic_hdr_amb γfs γi cov logstart k None x -∗ ⌜x = IcRaw⌝.
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
  Global Instance ic_hdr_amb_timeless γfs γi cov logstart k i x :
    Timeless (ic_hdr_amb γfs γi cov logstart k i x).
  Proof.
    rewrite /ic_hdr_amb /inode_ident. destruct i as [[dev inum]|]; [destruct x|]; tl_struct.
  Qed.

  Lemma ic_bundle_loaded_intro γfs γi cov logstart k dev inum g dn bm :
    length (bm_cells bm) = 13%nat ->
    inode_ident k (DfracOwn (1/2)) dev inum -∗
    i_valid (ientry k) ↦₄ valid_word true -∗
    ic_loaded γfs γi cov logstart k inum dn bm -∗
    ity_shot g (di_type dn) -∗ ifreeze_off (bv_unsigned inum) -∗ live_gen k (1/2) g -∗
    ic_hdr_amb γfs γi cov logstart k (Some (dev, inum)) (IcLoaded g dn bm) ∗
    ic_rest_amb k (IcLoaded g dn bm).
  Proof.
    iIntros (Hlen) "Hid Hv Hl Hty Hoff Hlg".
    rewrite /ic_loaded. iDestruct "Hl" as (data) "(%H1 & %H2 & %H3 & %H4 & %H5 & Hdl & Hera & Hmeta & Haddr & Hdv & Hfv)".
    rewrite /inode_meta. iDestruct "Hmeta" as "(Hty2 & Hmaj & Hmin & Hnl & Hsz)".
    iSplitR "Hty2 Hmaj Hmin Hsz Haddr".
    - rewrite /ic_hdr_amb. iFrame "Hv Hid Hnl". rewrite /ic_pay. iLeft.
      iFrame "Hty Hoff Hlg". rewrite /ic_loaded_ghost. iExists data. iFrame "Hdl Hera Hdv Hfv". done.
    - rewrite /ic_rest_amb /ic_meta_rest. iFrame "Hty2 Hmaj Hmin Hsz Haddr". done.
  Qed.
  Lemma ic_bundle_loaded_elim γfs γi cov logstart k dev inum g dn bm :
    ic_hdr_amb γfs γi cov logstart k (Some (dev, inum)) (IcLoaded g dn bm) -∗
    ic_rest_amb k (IcLoaded g dn bm) -∗
    inode_ident k (DfracOwn (1/2)) dev inum ∗
    i_valid (ientry k) ↦₄ valid_word true ∗
    ((ic_loaded γfs γi cov logstart k inum dn bm ∗ ity_shot g (di_type dn) ∗
      ifreeze_off (bv_unsigned inum) ∗ live_gen k (1/2) g)
     ∨ (frzown (bv_unsigned inum) ∗ frzsel k ((1/2)/2)%Qp true ∗
        inode_meta (ientry k) dn ∗ inode_addrs (ientry k) (bm_cells bm))).
  Proof.
    rewrite /ic_hdr_amb /ic_rest_amb /ic_meta_rest.
    iIntros "(Hv & Hid & Hnl & Hpay) (%Hlen & (Hty2 & Hmaj & Hmin & Hsz) & Haddr)".
    iFrame "Hid Hv". rewrite /ic_pay.
    iDestruct "Hpay" as "[(Hg & Hty & Hoff & Hlg) | [Hfo Hfs]]".
    - iLeft. iFrame "Hty Hoff Hlg". rewrite /ic_loaded /ic_loaded_ghost.
      iDestruct "Hg" as (data) "(%H1 & %H2 & %H3 & %H4 & %H5 & Hdl & Hera & Hdv & Hfv)".
      iExists data. rewrite /inode_meta. iFrame "Hdl Hera Hdv Hfv Haddr Hty2 Hmaj Hmin Hnl Hsz". done.
    - iRight. iFrame "Hfo Hfs Haddr". rewrite /inode_meta. iFrame "Hty2 Hmaj Hmin Hnl Hsz".
  Qed.
  Lemma ic_bundle_unloaded_intro γfs γi cov logstart k dev inum g :
    inode_ident k (DfracOwn (1/2)) dev inum -∗
    i_valid (ientry k) ↦₄ valid_word false -∗
    (∃ n : bv 16, i_nlink (ientry k) ↦₂ n) -∗
    (∃ d : dinode, ic_meta_rest (ientry k) d) -∗
    (∃ l : list (bv 32), ⌜length l = 13%nat⌝ ∗ inode_addrs (ientry k) l) -∗
    ipool_shape_np γfs γi cov logstart inum -∗
    ity_pending g -∗ ifreeze_off (bv_unsigned inum) -∗ live_gen k (1/2) g -∗
    ic_hdr_amb γfs γi cov logstart k (Some (dev, inum)) (IcUnloaded g) ∗
    ic_rest_amb k (IcUnloaded g).
  Proof.
    iIntros "Hid Hv Hnl Hm Ha Hpool Hty Hoff Hlg".
    rewrite /ic_hdr_amb /ic_rest_amb. iFrame "Hv Hid Hnl Hm Ha".
    rewrite /ic_pay. iLeft. iFrame "Hpool Hty Hoff Hlg".
  Qed.
  Lemma ic_bundle_unloaded_elim γfs γi cov logstart k dev inum g :
    ic_hdr_amb γfs γi cov logstart k (Some (dev, inum)) (IcUnloaded g) -∗
    ic_rest_amb k (IcUnloaded g) -∗
    inode_ident k (DfracOwn (1/2)) dev inum ∗
    i_valid (ientry k) ↦₄ valid_word false ∗
    (∃ n : bv 16, i_nlink (ientry k) ↦₂ n) ∗
    (∃ d : dinode, ic_meta_rest (ientry k) d) ∗
    (∃ l : list (bv 32), ⌜length l = 13%nat⌝ ∗ inode_addrs (ientry k) l) ∗
    ((ipool_shape_np γfs γi cov logstart inum ∗ ity_pending g ∗
      ifreeze_off (bv_unsigned inum) ∗ live_gen k (1/2) g)
     ∨ (frzown (bv_unsigned inum) ∗ frzsel k ((1/2)/2)%Qp true)).
  Proof.
    rewrite /ic_hdr_amb /ic_rest_amb. iIntros "(Hv & Hid & Hnl & Hpay) (Hm & Ha)".
    iFrame "Hid Hv Hnl Hm Ha". iExact "Hpay".
  Qed.
  (* the dead header from raw cells *)
  Lemma ic_hdr_dead_intro γfs γi cov logstart k :
    (∃ v : mword 32, i_valid (ientry k) ↦₄ v) -∗
    (∃ dev inum : mword 32, inode_ident k (DfracOwn (1/2)) dev inum) -∗
    (∃ n : bv 16, i_nlink (ientry k) ↦₂ n) -∗
    ic_hdr_amb γfs γi cov logstart k None IcRaw.
  Proof. iIntros "Hv Hid Hnl". rewrite /ic_hdr_amb. iFrame "Hv Hid Hnl". done. Qed.
  (* the LOADED bundle's ghost side goes back to the free pool as the
     pool's [np] shape -- the eviction's re-pack (today's
     ic_close_to_empty_core, minus the cells the box keeps) *)
  Lemma ic_loaded_ghost_to_np γfs γi cov logstart (inum : mword 32) (dn : dinode) (bm : blkmap) :
    ic_loaded_ghost γfs γi cov logstart inum dn bm -∗
    ipool_shape_np γfs γi cov logstart inum.
  Proof.
    rewrite /ic_loaded_ghost.
    iIntros "(%data & %Hok & %Hdok & %Hddix & %Hdoc & %Hduq & Hdlk & Hera & Hdv & Hfv)".
    rewrite /ipool_shape_np /ipool_alloc. iLeft. iExists dn, bm, data.
    iSplitR; [iPureIntro; exact Hok |].
    iSplitR; [iPureIntro; exact Hdok |].
    iSplitR; [iPureIntro; exact Hddix |].
    iSplitR; [iPureIntro; exact Hdoc |].
    iSplitR; [iPureIntro; exact Hduq |].
    iSplitL "Hdlk"; [iExact "Hdlk" |]. iFrame.
  Qed.

  (* the identified header's identity halves and (loaded) nlink cell,
     borrowed and returned unchanged -- iput's guard reads them off the
     header in hand *)
  Lemma ic_hdr_ident_acc γfs γi cov logstart k dev inum x :
    ic_hdr_amb γfs γi cov logstart k (Some (dev, inum)) x -∗
    inode_ident k (DfracOwn (1/2)) dev inum ∗
    (inode_ident k (DfracOwn (1/2)) dev inum -∗
     ic_hdr_amb γfs γi cov logstart k (Some (dev, inum)) x).
  Proof.
    rewrite /ic_hdr_amb. iIntros "(Hv & Hid & Hnl & Hpay)". iFrame "Hid".
    iIntros "Hid". iFrame "Hv Hid Hnl Hpay".
  Qed.
  Lemma ic_hdr_nlink_acc γfs γi cov logstart k dev inum g dn bm :
    ic_hdr_amb γfs γi cov logstart k (Some (dev, inum)) (IcLoaded g dn bm) -∗
    i_nlink (ientry k) ↦₂ di_nlink dn ∗
    (i_nlink (ientry k) ↦₂ di_nlink dn -∗
     ic_hdr_amb γfs γi cov logstart k (Some (dev, inum)) (IcLoaded g dn bm)).
  Proof.
    rewrite /ic_hdr_amb. iIntros "(Hv & Hid & Hnl & Hpay)". iFrame "Hnl".
    iIntros "Hnl". iFrame "Hv Hid Hnl Hpay".
  Qed.

  (* the identified header's valid cell, borrowed and returned unchanged:
     ilock reads it before it knows the shape *)
  Lemma ic_hdr_valid_acc γfs γi cov logstart k dev inum x :
    ic_hdr_amb γfs γi cov logstart k (Some (dev, inum)) x -∗
    i_valid (ientry k) ↦₄ valid_word (ic_x_loaded x) ∗
    (i_valid (ientry k) ↦₄ valid_word (ic_x_loaded x) -∗
     ic_hdr_amb γfs γi cov logstart k (Some (dev, inum)) x).
  Proof.
    rewrite /ic_hdr_amb. iIntros "(Hv & Hid & Hnl & Hpay)". iFrame "Hv".
    iIntros "Hv". iFrame "Hv Hid Hnl Hpay".
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
       ⌜inode_rec_local dn⌝ ∗
       ⌜dir_ok icfg_nib dn data⌝ ∗
       ⌜dir_dots_ix (bv_unsigned inum) dn data⌝ ∗
       ⌜dir_orphan_clean dn data⌝ ∗
       ⌜dir_uniq dn data⌝ ∗
       dlinks γfs (bv_unsigned inum) dn bm data ∗
       dinode_at γi inum dn ∗
       ind_res γfs bm ∗
       inode_blocks γfs bm data ∗
       dv_ride (bv_unsigned inum) (dv_of dn data) ∗
       fv_ride (bv_unsigned inum) (fv_of dn data) ∗
       top_frag (fs_gamma_L γfs) (bv_unsigned inum) (era_node dn bm data).
  Proof.
    iIntros "H". rewrite /ic_loaded_ghost.
    iDestruct "H" as (data) "(%Hok & %Hdok & %Hddix & %Hdoc & %Hduq & Hl & Hn & Hv & Hw)".
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
    iFrame "Hl Hd Hr Hb Hv Hw Ht".
  Qed.
  Lemma ic_mk_loaded_ghost γfs γi cov logstart (inum : mword 32)
      (dn : dinode) (bm : blkmap) (data : nat -> list (bv 8)) :
    inode_ok cov logstart dn bm data ->
    inode_rec_local dn ->
    dir_ok icfg_nib dn data ->
    dir_dots_ix (bv_unsigned inum) dn data ->
    dir_orphan_clean dn data ->
    dir_uniq dn data ->
    dlinks γfs (bv_unsigned inum) dn bm data -∗
    dinode_at γi inum dn -∗
    ind_res γfs bm -∗
    inode_blocks γfs bm data -∗
    dv_ride (bv_unsigned inum) (dv_of dn data) -∗
    fv_ride (bv_unsigned inum) (fv_of dn data) -∗
    top_frag (fs_gamma_L γfs) (bv_unsigned inum) (era_node dn bm data) -∗
    ic_loaded_ghost γfs γi cov logstart inum dn bm.
  Proof.
    intros Hok Hrl Hdok Hddix Hdoc Hduq.
    iIntros "Hl Hd Hr Hb Hv Hw Ht".
    pose proof (node_shape_ok_of_inode_ok cov logstart dn bm data Hok) as Hsh.
    pose proof (inode_local_of_ok_rec (bv_unsigned inum) cov logstart dn bm
                  data Hok Hrl Hduq Hddix) as Hloc.
    rewrite /ic_loaded_ghost.
    iExists data. iSplitR; [done |]. iSplitR; [done |]. iSplitR; [done |].
    iSplitR; [done |]. iSplitR; [done |].
    iSplitL "Hl"; [iExact "Hl" |].
    iSplitR "Hv Hw".
    { iApply (inode_owned_era_era_node_of γfs γi inum dn bm data Hsh Hloc
                with "Hd Hr Hb Ht"). }
    iSplitL "Hv"; [iExact "Hv" | iExact "Hw"].
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
    - iIntros "(%data & %H1 & %H2 & %H3 & %H4 & %H5 & Hdl & Hera & Hmeta & Haddr & Hdv & Hfv)".
      iFrame "Hmeta Haddr". iExists data. iFrame "Hdl Hera Hdv Hfv". done.
    - iIntros "[(%data & %H1 & %H2 & %H3 & %H4 & %H5 & Hdl & Hera & Hdv & Hfv) [Hmeta Haddr]]".
      iExists data. iFrame "Hdl Hera Hmeta Haddr Hdv Hfv". done.
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
  Definition ic_hdr (γfs : fs_names) (γi : gname) (cov : gset Z) (logstart : Z)
      (k : nat) (i : ic_bid) (x : ic_x) (ξ : CtxId) : iProp Σ :=
    ic_hdr_amb (XI := ξ) γfs γi cov logstart k i x.
  Definition ic_rest (k : nat) (x : ic_x) (ξ : CtxId) : iProp Σ :=
    ic_rest_amb (XI := ξ) k x.

  (* ---- the client obligations (CtxBox's section Context) ------------ *)
  Global Instance ic_hdr_morph γfs γi cov logstart k i x : CtxMorph (ic_hdr γfs γi cov logstart k i x).
  Proof.
    rewrite /ic_hdr /ic_hdr_amb /inode_ident.
    destruct i as [[dev inum]|].
    - apply ctx_morph_sep; [apply ctx_morph_word4|].
      apply ctx_morph_sep; [apply ctx_morph_sep; apply ctx_morph_word4|].
      apply ctx_morph_sep; [| apply ctx_morph_const].
      destruct x; [apply ctx_morph_exist => n; apply ctx_morph_word2
                  | apply ctx_morph_exist => n; apply ctx_morph_word2
                  | apply ctx_morph_word2].
    - apply ctx_morph_sep; [apply ctx_morph_const|].
      apply ctx_morph_sep; [apply ctx_morph_exist => v; apply ctx_morph_word4|].
      apply ctx_morph_sep.
      + apply ctx_morph_exist => d. apply ctx_morph_exist => n. apply ctx_morph_sep; apply ctx_morph_word4.
      + apply ctx_morph_exist => n. apply ctx_morph_word2.
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
  Global Instance ic_hdr_timeless γfs γi cov logstart k i x ξ : Timeless (ic_hdr γfs γi cov logstart k i x ξ).
  Proof. rewrite /ic_hdr. apply ic_hdr_amb_timeless. Qed.
  Global Instance ic_rest_timeless k x ξ : Timeless (ic_rest k x ξ).
  Proof. rewrite /ic_rest. apply ic_rest_amb_timeless. Qed.
  Lemma ic_hdr_excl γfs γi cov logstart k : forall (i i' : ic_bid) (x x' : ic_x) (ξ ξ' : CtxId),
    ic_hdr γfs γi cov logstart k i x ξ -∗ ic_hdr γfs γi cov logstart k i' x' ξ' -∗ False.
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

  (* THE BOX, per slot: tok := ic_tok (ghost, R-4), Q := emp *)
  Definition ic_box cn (γfs : fs_names) (γi : gname) (cov : gset Z) (logstart : Z)
      (k : nat) : iProp Σ :=
    is_box (ic_hdr γfs γi cov logstart k) (ic_rest k) emp%I (ic_tok cn k) icBoxN (icfg_box k).
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
    | DepShr s dev inum g lo =>
        (inode_ident k (DfracOwn s) dev inum ∗ live_genlo k s g lo)%I
    | DepRef q dev inum g lo =>
        (inode_ident k (DfracOwn q) dev inum ∗ live_genlo k q g lo ∗ iref_frag k q)%I
    | _ => False%I
    end.
  (* the stamps mass the descriptor's holder parked: a share its fraction
     (M-5), a whole reference 1 *)
  Definition ic_dep_mass (d : ic_dep) : Qp :=
    match d with DepShr s _ _ _ _ => s | _ => 1%Qp end.
  Definition ic_dep_id (d : ic_dep) : ic_bid :=
    match d with
    | DepShr _ dev inum _ _ | DepRef _ dev inum _ _ => Some (dev, inum)
    | _ => None
    end.
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
    match d with DepShr _ _ _ g _ => live_gen k (1/2) g | _ => emp%I end.
  Definition ic_deposit (cn : ic_names) (k : nat) (d : ic_dep) : iProp Σ :=
    (ic_deposit2 k d ∗ ic_pay_live k d)%I.

  (* ---- the two payload rows (M-6) ------------------------------------ *)
  (* L2: the inode sleeplock's λ payload -- CtxBox.l2_row at ic_tok *)
  Definition ic_slp cn k : CtxId -> iProp Σ :=
    fun ξ => (∃ s : l2_reg ic_bid,
      CtxBox.l2_row (X := ic_x) (ic_tok cn k) (icfg_box k) s ξ)%I.
  Global Instance ic_slp_morph cn k : CtxMorph (ic_slp cn k).
  Proof. rewrite /ic_slp. apply ctx_morph_exist => s. apply _. Qed.
  (* the releaser's UNFLOORED row at a known park stamp (R2's Rdep, the
     bcache's bslp_dep): what (f) leaves in hand; the _in release re-floors
     it at the parked context through the fold *)
  Definition ic_slp_dep cn k (T' : nat) : iProp Σ :=
    (ic_tok cn k ∗ ic_regp k (L2Reg T' None))%I.
  Lemma ic_slp_fold cn k T' (ξ : CtxId) :
    ic_slp_dep cn k T' ∗ ctx_floor ξ T' ⊢ ic_slp cn k ξ.
  Proof.
    iIntros "[[Ht Hrp] #Hfl]". rewrite /ic_slp. iExists (L2Reg T' None).
    rewrite /CtxBox.l2_row /ic_regp. iFrame "Ht Hrp". iSplitR; [done |]. iExact "Hfl".
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
    ic_regd k r -∗ ic_cnt k 0 ={E}=∗
    own_context ξ ∗ ic_cnt k 0 ∗
    ∃ T0 : nat, ⌜(T0 <= Kd)%nat⌝ ∗
      ic_regd k (SlotReg (sr_td r) true None (Some (IcRaw, T0))) ∗
      ic_hdr γfs γi cov logstart k None IcRaw ξ.
  Proof.
    iIntros (HE Hw Hid HKd) "#Hbox Hrun #Hfl Hrd Hc".
    iMod (own_unit (authUR (gmapUR (ic_bid * nat) ufracR)) (bx_stamps (icfg_box k))) as "Hf0".
    assert (Hq0 : qsum (∅ : gmap (ic_bid * nat) ufrac) = nat_Qc 0).
    { rewrite /qsum map_fold_empty /nat_Qc /=. symmetry. apply Z2Qc_inj_0. }
    assert (Hm0 : (max_stamp (∅ : gmap (ic_bid * nat) ufrac) <= 0)%nat).
    { rewrite /max_stamp map_fold_empty. lia. }
    iMod (CtxBox.box_withdraw_L1 (ic_hdr γfs γi cov logstart k) (ic_rest k) emp%I (ic_tok cn k)
            icBoxN (icfg_box k) ξ r 0 ∅ Kd 0 E HE Hw Hq0 HKd Hm0
            with "Hbox Hrun Hfl [] [] Hrd Hc [Hf0]") as "(Hrun & Hc & Hout)".
    { iApply ctx_floor_0. }
    { rewrite /max_stamp map_fold_empty. iApply TsoGhost.llb_0. }
    { rewrite /stamps_frag. iExact "Hf0". }
    iDestruct "Hout" as (x0 T0) "(%HT0 & Hrd & Hhdr)". rewrite Hid.
    iDestruct (ic_hdr_dead_raw (XI := ξ) γfs γi cov logstart k x0 with "Hhdr") as %Hx0. subst x0.
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
    ic_hdr γfs γi cov logstart k (Some (dev, inum)) (IcUnloaded g) ξ ={E}=∗
    own_context ξ ∗
    ∃ T' : nat,
      ic_regd k (SlotReg T' false (Some (dev, inum)) None) ∗
      ic_cnt k 1 ∗
      ic_ref_stamps k dev inum 1%Qp ∗
      llb loglen_name T'.
  Proof.
    iIntros (HE Hw Hx) "#Hbox Hrun Hrd Hc Hhdr".
    iMod (CtxBox.box_deposit_L1_shape (ic_hdr γfs γi cov logstart k) (ic_rest k) emp%I (ic_tok cn k)
            icBoxN (icfg_box k) ξ r 0 (Some (dev, inum)) IcRaw (IcUnloaded g) T0 E HE Hw Hx
            ltac:(intros ξb; rewrite /ic_rest; simpl; reflexivity)
            with "Hbox Hrun Hrd Hc Hhdr") as "(Hrun & %T' & Hrd & Hc & Href & #Hllb)".
    iModIntro. iFrame "Hrun". iExists T'. iFrame "Hrd Hllb".
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
    iMod (CtxBox.box_ref_incr (ic_hdr γfs γi cov logstart k) (ic_rest k) emp%I (ic_tok cn k)
            icBoxN (icfg_box k) r (S c) E HE Hw with "Hbox Hrd Hc") as "(Hrd & Hc & %T & Href)".
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
    assert (Hq : qsum m = nat_Qc 1) by (rewrite Hm Qp_to_Qc_1 nat_Qc_1; reflexivity).
    iMod (CtxBox.box_ref_decr (ic_hdr γfs γi cov logstart k) (ic_rest k) emp%I (ic_tok cn k)
            icBoxN (icfg_box k) r c i m E HE Hw Hq with "Hbox Hrd Hllb Hc Href") as "(Hrd & Hc & #Hllb')".
    iModIntro. iExists (Nat.max (sr_td r) (max_stamp m)). iSplitR; [iPureIntro; lia|].
    iFrame "Hrd Hc Hllb'".
  Qed.

  (* ilock's and iput's CHECKOUT -- (e) with the descriptor's holder body
     (F15: the share minus slh_tok; F16: iput's whole unit at DepRef).  R1
     at the genl_llb acquiresleep presents the fragment's stamp; the L2
     row's pieces come from the payload.  Out: the bundle at the identity
     (one binder over the shape), and the handle row [ic_deposit2 k d]. *)
  Lemma ic_checkout `{CID : RiscvLang.CpuId} cn γfs γi cov logstart (k : nat)
      (ξ : CtxId) (d : ic_dep) (dev inum : mword 32)
      (s0 : l2_reg ic_bid) (Kt Kp : nat) (E : coPset) :
    ↑icBoxN ⊆ E ->
    ic_dep_id d = Some (dev, inum) ->
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
    ic_tok cn k -∗ ic_regp k s0 ={E}=∗
    own_context ξ ∗
    (∃ x : ic_x, ic_hdr γfs γi cov logstart k (Some (dev, inum)) x ξ ∗ ic_rest k x ξ) ∗
    ic_deposit2 k d.
  Proof.
    iIntros (HE Hid Hs0 HKp) "#Hbox Hrun #Hflt #Hflp Hbody Href Htok Hrp".
    iDestruct "Href" as (m) "(%Hm & %Hmt & Href)".
    iMod (CtxBox.box_checkout (ic_hdr γfs γi cov logstart k) (ic_rest k) emp%I (ic_tok cn k)
            (ic_tok_excl cn k) icBoxN (icfg_box k) ξ (Some (dev, inum)) m s0 Kt Kp E HE Hs0 Hmt HKp
            with "Hbox Hrun Hflt Hflp Href [] Htok Hrp") as "(Hrun & Hbun & Hhold)".
    { done. }
    iModIntro. iFrame "Hrun". iSplitL "Hbun"; [iExact "Hbun"|].
    rewrite /ic_deposit2 Hid. iFrame "Hbody". rewrite /ic_hold. iExists m. iFrame "Hhold". done.
  Qed.

  (* iunlock's and iput's PARK -- (f): the bundle back at the identity the
     handle names (the register agrees, (I) ties it), the fragment re-minted
     at the park stamp at the descriptor's mass, the holder's body back, the
     L2 row's pieces for the genin releasesleep (the client re-forms
     inode_shr2 / the reference once releasesleep returns slh_tok) *)
  Lemma ic_park `{CID : RiscvLang.CpuId} cn γfs γi cov logstart (k : nat)
      (ξ : CtxId) (d : ic_dep) (dev inum : mword 32) (E : coPset) :
    ↑icBoxN ⊆ E ->
    ic_dep_id d = Some (dev, inum) ->
    ic_box cn γfs γi cov logstart k -∗
    own_context ξ -∗
    (∃ x : ic_x, ic_hdr γfs γi cov logstart k (Some (dev, inum)) x ξ ∗ ic_rest k x ξ) -∗
    ic_deposit2 k d ={E}=∗
    own_context ξ ∗ ic_tok cn k ∗ ic_body k d ∗
    ∃ T' : nat,
      ic_regp k (L2Reg T' None) ∗
      CtxBox.reference (X := ic_x) (icfg_box k) (Some (dev, inum))
        {[ (Some (dev, inum), T') := ic_dep_mass d ]} ∗
      llb loglen_name T'.
  Proof.
    iIntros (HE Hid) "#Hbox Hrun Hbun Hdep".
    rewrite /ic_deposit2 Hid. iDestruct "Hdep" as "[Hhold Hbody]".
    iDestruct "Hhold" as (m) "[%Hm Hhold]".
    iMod (CtxBox.box_park (ic_hdr γfs γi cov logstart k) (ic_rest k) emp%I (ic_tok cn k)
            (ic_hdr_excl γfs γi cov logstart k) (ic_rest_excl k) icBoxN (icfg_box k) ξ (Some (dev, inum)) m E HE
            with "Hbox Hrun Hbun Hhold") as "(Hrun & _ & Htok & %T' & %q & %Hq & Hrp & Href & #Hllb)".
    assert (q = ic_dep_mass d) as ->. { apply Qp.to_Qc_inj_iff. by rewrite Hq Hm. }
    iModIntro. iFrame "Hrun Htok Hbody". iExists T'. iFrame "Hrp Href Hllb".
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
       CtxBox.reference (X := ic_x) (icfg_box k) (Some (dev, inum)) m) ={E}=∗
    own_context ξ ∗ ic_cnt k 1 ∗
    ∃ (x0 : ic_x) (T0 : nat), ⌜x0 ≠ IcRaw⌝ ∗ ⌜(T0 <= Nat.max Kd Kt)%nat⌝ ∗
      ic_regd k (SlotReg (sr_td r) true (Some (dev, inum)) (Some (x0, T0))) ∗
      ic_hdr γfs γi cov logstart k (Some (dev, inum)) x0 ξ.
  Proof.
    iIntros (HE Hw Hid HKd) "#Hbox Hrun #Hfld #Hflt Hrd Hc Href".
    iDestruct "Href" as (m) "(%Hm & %Hmt & Href)".
    iDestruct "Href" as "(%Hne & %Hk & Hf & #Hl)".
    assert (Hq : qsum m = nat_Qc 1) by (rewrite Hm Qp_to_Qc_1 nat_Qc_1; reflexivity).
    iMod (CtxBox.box_withdraw_L1 (ic_hdr γfs γi cov logstart k) (ic_rest k) emp%I (ic_tok cn k)
            icBoxN (icfg_box k) ξ r 1 m Kd Kt E HE Hw Hq HKd Hmt
            with "Hbox Hrun Hfld Hflt Hl Hrd Hc Hf") as "(Hrun & Hc & Hout)".
    iDestruct "Hout" as (x0 T0) "(%HT0 & Hrd & Hhdr)". rewrite Hid.
    destruct x0 as [|g|g dn bm].
    { rewrite /ic_hdr /ic_hdr_amb. iDestruct "Hhdr" as "(_ & _ & _ & Hpay)".
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
    ic_hdr γfs γi cov logstart k (Some (dev, inum)) x0 ξ ={E}=∗
    own_context ξ ∗
    ∃ T' : nat,
      ic_regd k (SlotReg T' false (Some (dev, inum)) None) ∗
      ic_cnt k 1 ∗
      ic_ref_stamps k dev inum 1%Qp ∗
      llb loglen_name T'.
  Proof.
    iIntros (HE Hw Hx Hid) "#Hbox Hrun Hrd Hc Hhdr".
    iMod (CtxBox.box_deposit_L1 (ic_hdr γfs γi cov logstart k) (ic_rest k) emp%I (ic_tok cn k)
            icBoxN (icfg_box k) ξ r 1 (Some (dev, inum)) x0 T0 E HE Hw Hx
            with "Hbox Hrun Hrd Hc Hhdr") as "(Hrun & %T' & Hrd & Hc & Href & #Hllb)".
    iModIntro. iFrame "Hrun". iExists T'. iFrame "Hrd Hllb". iSplitL "Hc"; [iExact "Hc"|].
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
    ic_hdr γfs γi cov logstart k (Some (dev, inum)) (IcLoaded g' dn bm) ξ ={E}=∗
    own_context ξ ∗
    ∃ T' : nat,
      ic_regd k (SlotReg T' false (Some (dev, inum)) None) ∗
      ic_cnt k 1 ∗
      ic_ref_stamps k dev inum 1%Qp ∗
      llb loglen_name T'.
  Proof.
    iIntros (HE Hw Hx Hid) "#Hbox Hrun Hrd Hc Hhdr".
    iMod (CtxBox.box_deposit_L1_shape (ic_hdr γfs γi cov logstart k) (ic_rest k) emp%I (ic_tok cn k)
            icBoxN (icfg_box k) ξ r 1 (Some (dev, inum)) (IcLoaded g dn bm) (IcLoaded g' dn bm) T0 E HE Hw Hx
            ltac:(intros ξb; rewrite /ic_rest; simpl; reflexivity)
            with "Hbox Hrun Hrd Hc Hhdr") as "(Hrun & %T' & Hrd & Hc & Href & #Hllb)".
    iModIntro. iFrame "Hrun". iExists T'. iFrame "Hrd Hllb". iSplitL "Hc"; [iExact "Hc"|].
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
    ic_hdr γfs γi cov logstart k None IcRaw ξ ={E}=∗
    own_context ξ ∗
    ∃ T' : nat,
      ic_regd k (SlotReg T' false None None) ∗
      ic_cnt k 1 ∗
      (∃ m : gmap (ic_bid * nat) ufrac, ⌜qsum m = Qp_to_Qc 1⌝ ∗
         CtxBox.reference (X := ic_x) (icfg_box k) None m) ∗
      llb loglen_name T'.
  Proof.
    iIntros (HE Hw Hx) "#Hbox Hrun Hrd Hc Hhdr".
    iMod (CtxBox.box_deposit_L1_shape (ic_hdr γfs γi cov logstart k) (ic_rest k) emp%I (ic_tok cn k)
            icBoxN (icfg_box k) ξ r 1 None x0 IcRaw T0 E HE Hw Hx
            ltac:(intros ξb; apply ic_rest_to_raw)
            with "Hbox Hrun Hrd Hc Hhdr") as "(Hrun & %T' & Hrd & Hc & Href & #Hllb)".
    iModIntro. iFrame "Hrun". iExists T'. iFrame "Hrd Hllb". iSplitL "Hc"; [iExact "Hc"|].
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
    ic_regd k r -∗ ic_cnt k 1 -∗ ic_tok cn k -∗ ic_regp k s0 ={E}=∗
    own_context ξ ∗
    ic_rest k x0 ξ ∗
    ic_regd k (SlotReg (sr_td r) false (Some (dev, inum)) None) ∗
    ic_cnt k 1 ∗
    ic_hold k dev inum 1%Qp.
  Proof.
    iIntros (HE Hw Hx Hid HTK Hs0) "#Hbox Hrun #Hfl Hrd Hc Htok Hrp".
    iMod (CtxBox.box_l1_to_l2 (ic_hdr γfs γi cov logstart k) (ic_rest k) emp%I (ic_tok cn k)
            icBoxN (icfg_box k) ξ r x0 T0 K s0 E HE Hw Hx HTK Hs0
            with "Hbox Hrun Hfl Hrd Hc [] Htok Hrp")
      as "(Hrun & Hrest & Hrd & Hc & %m & %Hm & Hhold)".
    { done. }
    iModIntro. iFrame "Hrun Hrest Hc". rewrite Hid. iFrame "Hrd".
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
       ic_hdr γfs γi cov logstart k None IcRaw ξ ∗ ic_rest k IcRaw ξ) ={E}=∗
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
                ic_hdr γfs γi cov logstart k None IcRaw ξ ∗ ic_rest k IcRaw ξ) ={E}=∗
               own_context ξ ∗
               (ic_box cn γfs γi cov logstart k ∗
                ∃ T_boot : nat,
                  ic_regd k (SlotReg T_boot false None None) ∗ llb loglen_name T_boot ∗
                  ic_cnt k 0 ∗ ic_regp k (L2Reg 0 None)))%I as "Hstep".
    { iApply big_sepL_intro. iIntros "!>" (i k _) "Hrun (Hst & Hc & Hd & Hp & Hhdr & Hrest)".
      iEval (rewrite -Qp.half_half) in "Hc". iDestruct (ghost_var_split with "Hc") as "[Hc1 Hc2]".
      iMod (ghost_var_update (L2Reg 0 None) with "Hp") as "Hp".
      iEval (rewrite -Qp.half_half) in "Hp". iDestruct (ghost_var_split with "Hp") as "[Hp1 Hp2]".
      iMod (CtxBox.box_alloc_at (ic_hdr γfs γi cov logstart k) (ic_rest k) emp%I (ic_tok cn k)
              icBoxN (icfg_box k) ξ None E with "Hrun Hst Hc1 [Hd] Hp1 [Hhdr Hrest]")
        as "(Hrun & %Tb & #Hbx & Hrd & #Hllb)".
      { iExists _. iExact "Hd". }
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
    (∃ dev inum : mword 32, islot_free_at k dev inum)%I.

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
       ipool γfs γi cov logstart (region_inums nib ∖ ci_inums ci))%I.

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
       ipool γfs γi cov logstart (region_inums nib ∖ ci_inums ci))%I.

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
       ipool γfs γi cov logstart (region_inums nib ∖ ci_inums ci))%I.

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
     ic_escrows cn γfs γi cov logstart)%I.

  Lemma is_itable2_lock (γl : gname) (cn : ic_names) (γfs : fs_names)
      (γi : gname) (cov : gset Z) (logstart : Z) (nib : nat)
      (dv : mword 32) :
    is_itable2 γl cn γfs γi cov logstart nib dv -∗
    is_lock γl itable_lock "itable"%string
      (fun ξ => itable_res2 ξ cn γfs γi cov logstart nib dv).
  Proof. iIntros "[$ _]". Qed.

  Lemma is_itable2_claims (γl : gname) (cn : ic_names) (γfs : fs_names)
      (γi : gname) (cov : gset Z) (logstart : Z) (nib : nat)
      (dv : mword 32) :
    is_itable2 γl cn γfs γi cov logstart nib dv -∗ iref_claims.
  Proof. iIntros "(_ & $ & _)". Qed.

  Lemma is_itable2_escrows (γl : gname) (cn : ic_names) (γfs : fs_names)
      (γi : gname) (cov : gset Z) (logstart : Z) (nib : nat)
      (dv : mword 32) :
    is_itable2 γl cn γfs γi cov logstart nib dv -∗ ic_escrows cn γfs γi cov logstart.
  Proof. iIntros "(_ & _ & $)". Qed.

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
         is_sleeplock_genl γil γisl (i_lock (ientry k)) "inode"%string
                           (ic_slp cn k) (slh_tok (icfg_isl k)))%I.

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
      ([∗ list] k ∈ seq 0 NINODE, ic_tok cn k).
  Proof.
    (* R3: [icn_mid] / [icn_id] are DEAD fields (the recycle token and the
       LIVE/EMPTY agreement retired with the arms); they are still minted so
       the record keeps its shape at its six construction sites. *)
    iMod (ic_dep_fun_alloc NINODE 0) as (fesc) "Hesc".
    iMod (ic_tok_fun_alloc NINODE 0) as (fmid) "_".
    iMod (ic_id_fun_alloc dvs NINODE 0) as (fid) "_".
    iModIntro. iExists (MkIcNames fesc fmid fid).
    rewrite /ic_tok. cbn [icn_esc]. iFrame "Hesc".
  Qed.

End IcacheEscrowAlloc.
