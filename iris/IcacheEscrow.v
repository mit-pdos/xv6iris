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

   ---- THE THREE ARMS (§13.1c) -----------------------------------------

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
     OUT    : checked out by a sleeplock chain -- the chain's own reference
              (count fragment AND identity fraction), the checkout token and
              the recycle token wait here until [iunlock] brings the content
              back.
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

   Refutations, and which opener uses which (§10.3, §13.1c):

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
       [ic_mid], which both of them hold and it is carrying.

   The ½-versus-FULL split of the inum cell IS the parked/mid
   discriminator, which is why §13.1b's identity re-budget in
   [IcacheInv.islot_rest] is not bookkeeping.

   ---- ONE DEVIATION FROM THE C3a BRIEF, RECORDED HERE ------------------

   The brief described [ic_swap_checkout] as splitting the winner's
   reference in half -- q/2 deposited into OUT, q/2 kept.  THAT IS NOT AN
   ENTAILMENT: [iref_tok γ k q] is [own γ (◯ {[k := (q,1)]})] and two
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
Require Import DiskPtsto.
Require Import FsBlocks.
Require Import DinodeEnc.
Require Import LogInv.
Require Import FsCrash.
Require Import InodeInv.
Require Import InodeLock.
Require Import InodeRegion.
Require Import IrefSlots.
Require Import IcacheInv.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.

Local Open Scope Z_scope.

(* ===================================================================== *)
(*  0.  GHOST NAMES                                                       *)
(* ===================================================================== *)

(* the escrow layer's names, as one record (BioInv.bio_names' shape): the
   reference authority IcacheInv's lemmas take, and per slot the checkout
   token's gname and the recycle token's gname.  The itable spinlock's own
   gname stays a separate argument, exactly as [is_itable] takes it. *)
Record ic_names := MkIcNames {
  icn_ref : gname;          (* the count authority (IcacheInv's γ)       *)
  icn_esc : nat -> gname;   (* entry k's CHECKOUT token                  *)
  icn_mid : nat -> gname;   (* entry k's RECYCLE token                   *)
  icn_id  : nat -> gname;   (* entry k's LIVE / EMPTY agreement          *)
}.

Section IcacheEscrow.
  Context `{!riscvGS Σ, !lockG Σ, !icacheG Σ, !irefslotG Σ,
            !diskGhostG Σ, !fsLogG Σ, !iregG Σ}.
  Context `{GEN : GenId}.

  (* ------------------------------------------------------------------ *)
  (*  Timeless instances the arms are built out of                       *)
  (* ------------------------------------------------------------------ *)

  (* Every opener below is inside a store's or a load's atomic update, with
     no step left to absorb a ▷, so the WHOLE body must be timeless (bio's
     [bv_clean_tl]/[bv_dirty_tl] exist for exactly this reason).  The
     components are points-tos, ghost_map elements and pure facts -- all
     timeless -- but several are guarded by a [decide], so the instances
     have to be discharged by hand rather than found. *)

  Global Instance word2_pointsto_timeless (a : Arch.pa) (dq : dfrac) (w : bv 16) :
    Timeless (word2_pointsto a dq w).
  Proof. rewrite /word2_pointsto. apply _. Qed.

  Global Instance inode_meta_timeless (ip : mword 64) (d : dinode) :
    Timeless (inode_meta ip d).
  Proof. rewrite /inode_meta. apply _. Qed.

  Global Instance inode_addrs_timeless (ip : mword 64) (l : list (bv 32)) :
    Timeless (inode_addrs ip l).
  Proof. rewrite /inode_addrs. apply _. Qed.

  Global Instance inode_raw_timeless (ip : mword 64) : Timeless (inode_raw ip).
  Proof. rewrite /inode_raw. apply _. Qed.

  Global Instance ind_blk_timeless γfs bm : Timeless (ind_blk γfs bm).
  Proof. rewrite /ind_blk /fsblock. case_decide; apply _. Qed.

  Global Instance ind_tok_timeless γfs bm : Timeless (ind_tok γfs bm).
  Proof. rewrite /ind_tok. case_decide; apply _. Qed.

  Global Instance ind_res_timeless γfs bm : Timeless (ind_res γfs bm).
  Proof. rewrite /ind_res. apply _. Qed.

  Global Instance blk_res_timeless γfs w bs : Timeless (blk_res γfs w bs).
  Proof. rewrite /blk_res /fsblock. case_decide; apply _. Qed.

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

  (* the entry sleeplock's WHOLE resource (BioInv.bown): holding it is what
     lets a winner refute the checked-out arm, and the checkout deposits it
     so that the arm records "somebody is inside the critical section". *)
  Definition ic_tok (cn : ic_names) (k : nat) : iProp Σ :=
    lock_tok_excl (icn_esc cn k).

  (* the recycle token (BioInv.bmid): parked in PARKED and OUT, in the
     recycler's hand during the MID window. *)
  Definition ic_mid (cn : ic_names) (k : nat) : iProp Σ :=
    lock_tok_excl (icn_mid cn k).

  Lemma ic_tok_exclusive cn k : ic_tok cn k -∗ ic_tok cn k -∗ False.
  Proof. apply lock_tok_excl_exclusive. Qed.

  Lemma ic_mid_exclusive cn k : ic_mid cn k -∗ ic_mid cn k -∗ False.
  Proof. apply lock_tok_excl_exclusive. Qed.

  Global Instance ic_tok_timeless cn k : Timeless (ic_tok cn k).
  Proof. rewrite /ic_tok. apply _. Qed.
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
  Definition ic_id (cn : ic_names) (k : nat) (q : Qp) (v : bool) : iProp Σ :=
    ghost_var (icn_id cn k) q v.

  Global Instance ic_id_timeless cn k q v : Timeless (ic_id cn k q v).
  Proof. rewrite /ic_id. apply _. Qed.

  Lemma ic_id_agree cn k q1 q2 v1 v2 :
    ic_id cn k q1 v1 -∗ ic_id cn k q2 v2 -∗ ⌜v1 = v2⌝.
  Proof.
    rewrite /ic_id. iIntros "H1 H2".
    by iDestruct (ghost_var_agree with "H1 H2") as %->.
  Qed.

  (* the two halves in one hand -- iget's recycle and iput's last close *)
  Lemma ic_id_flip cn k (v v' : bool) :
    ic_id cn k (1/2) v -∗ ic_id cn k (1/2) v ==∗
    ic_id cn k (1/2) v' ∗ ic_id cn k (1/2) v'.
  Proof.
    rewrite /ic_id. iIntros "H1 H2".
    iApply (ghost_var_update_halves v' with "H1 H2").
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  2.  THE PAYLOADS                                                   *)
  (* ------------------------------------------------------------------ *)

  (* ONE UNCACHED INUM'S POOL BUNDLE (§13.3).  Two shapes, because free
     inodes exist: [inode_ok] demands a nonzero type, and a type-0 inode
     owns no blocks (itrunc returned them), so it carries only its record.
     [ialloc] (future) is what flips an entry free -> allocated. *)
  Definition ipool_shape (γfs : fs_names) (γi : gname) (cov : gset Z)
      (logstart : Z) (inum : mword 32) : iProp Σ :=
    ((∃ (dn0 : dinode) (bm0 : blkmap) (data0 : nat -> list (bv 8)),
        ⌜inode_ok cov logstart dn0 bm0 data0⌝ ∗
        dinode_at γi inum dn0 ∗
        ind_res γfs bm0 ∗
        inode_blocks γfs bm0 data0)
     ∨ (∃ dn0 : dinode,
          ⌜bv_unsigned (di_type dn0) = 0⌝ ∗
          dinode_at γi inum dn0))%I.

  Global Instance ipool_shape_timeless γfs γi cov logstart inum :
    Timeless (ipool_shape γfs γi cov logstart inum).
  Proof. rewrite /ipool_shape. apply _. Qed.

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
     retags it.  Design: fs-icache.md §13 (parked-clean). *)
  Definition ic_loaded (γfs : fs_names) (γi : gname) (cov : gset Z)
      (logstart : Z) (k : nat) (inum : mword 32)
      (dn : dinode) (bm : blkmap) : iProp Σ :=
    (∃ (data : nat -> list (bv 8)),
       ⌜inode_ok cov logstart dn bm data⌝ ∗
       dinode_at γi inum dn ∗
       inode_meta (ientry k) dn ∗
       inode_addrs (ientry k) (bm_cells bm) ∗
       ind_res γfs bm ∗
       inode_blocks γfs bm data)%I.

  (* An UNLOADED entry's parked content: the cells at no particular value
     (iget minted the entry and nobody has read the dinode yet) plus the
     inum's pool bundle, parked here on its way past the recycler so that
     WHOEVER wins the sleeplock race finds what the fill needs. *)
  Definition ic_unloaded (γfs : fs_names) (γi : gname) (cov : gset Z)
      (logstart : Z) (k : nat) (inum : mword 32) : iProp Σ :=
    (inode_raw (ientry k) ∗ ipool_shape γfs γi cov logstart inum)%I.

  Global Instance ic_loaded_timeless γfs γi cov logstart k inum dn bm :
    Timeless (ic_loaded γfs γi cov logstart k inum dn bm).
  Proof. rewrite /ic_loaded. apply _. Qed.

  Global Instance ic_unloaded_timeless γfs γi cov logstart k inum :
    Timeless (ic_unloaded γfs γi cov logstart k inum).
  Proof. rewrite /ic_unloaded. apply _. Qed.

  (* the payload the valid word keys.  Named, because every swap lemma
     hands exactly this across. *)
  Definition ic_payload (γfs : fs_names) (γi : gname) (cov : gset Z)
      (logstart : Z) (k : nat) (inum : mword 32) (v : bool) : iProp Σ :=
    (if v
     then ∃ (dn : dinode) (bm : blkmap), ic_loaded γfs γi cov logstart k inum dn bm
     else ic_unloaded γfs γi cov logstart k inum)%I.

  Global Instance ic_payload_timeless γfs γi cov logstart k inum v :
    Timeless (ic_payload γfs γi cov logstart k inum v).
  Proof. rewrite /ic_payload. destruct v; apply _. Qed.

  (* ------------------------------------------------------------------ *)
  (*  3.  THE THREE ARMS                                                 *)
  (* ------------------------------------------------------------------ *)

  Definition ic_parked (cn : ic_names) (γfs : fs_names) (γi : gname)
      (cov : gset Z) (logstart : Z) (k : nat) : iProp Σ :=
    (∃ (dev inum : mword 32) (v : bool),
       i_dev (ientry k) ↦₄{DfracOwn (1/2)} dev ∗
       i_inum (ientry k) ↦₄{DfracOwn (1/2)} inum ∗
       i_valid (ientry k) ↦₄ valid_word v ∗
       ic_payload γfs γi cov logstart k inum v ∗
       ic_mid cn k ∗
       ic_id cn k (1/2) true)%I.

  Definition ic_out (cn : ic_names) (k : nat) : iProp Σ :=
    (∃ (q : Qp) (dev inum : mword 32),
       ic_tok cn k ∗
       inode_ref (icn_ref cn) k q dev inum ∗
       ic_mid cn k ∗
       ic_id cn k (1/2) true)%I.

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
       ic_id cn k (1/2) true)%I.

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
       ic_id cn k (1/2) false)%I.

  Definition ic_escrow_body (cn : ic_names) (γfs : fs_names) (γi : gname)
      (cov : gset Z) (logstart : Z) (k : nat) : iProp Σ :=
    (ic_parked cn γfs γi cov logstart k
     ∨ ic_out cn k
     ∨ ic_mid_arm cn γfs γi cov logstart k
     ∨ ic_empty_arm cn k)%I.

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

  Global Instance ic_parked_timeless cn γfs γi cov logstart k :
    Timeless (ic_parked cn γfs γi cov logstart k).
  Proof. rewrite /ic_parked. apply _. Qed.

  Global Instance ic_out_timeless cn k : Timeless (ic_out cn k).
  Proof. rewrite /ic_out /inode_ref /inode_ident. apply _. Qed.

  Global Instance ic_mid_arm_timeless cn γfs γi cov logstart k :
    Timeless (ic_mid_arm cn γfs γi cov logstart k).
  Proof. rewrite /ic_mid_arm. apply _. Qed.

  Global Instance ic_empty_arm_timeless cn k : Timeless (ic_empty_arm cn k).
  Proof. rewrite /ic_empty_arm /inode_raw. apply _. Qed.

  Global Instance ic_escrow_body_timeless cn γfs γi cov logstart k :
    Timeless (ic_escrow_body cn γfs γi cov logstart k).
  Proof. rewrite /ic_escrow_body. apply _. Qed.

  (* ------------------------------------------------------------------ *)
  (*  4.  THE SWAPS AND THE OPENINGS                                     *)
  (* ------------------------------------------------------------------ *)

  (* (a) CHECKOUT, post-[acquiresleep] (BioInv.escrow_swap_checkout).

     The opener's [ic_tok] refutes OUT; its reference's inum-cell FRACTION
     refutes MID (whose inum cell is FULL) and AGREES with PARKED's half,
     which is what pins the withdrawn payload to the winner's own inode --
     §13.1b's tie, doing its one job.  The dev half comes out at the
     opener's OWN dev by the same agreement, which is what lets the winner
     read [ip->dev] after it has deposited its whole reference (§13.1e).
     The deposited OUT absorbs the parked arm's recycle token, so the
     critical section need not carry it. *)
  Lemma ic_swap_checkout cn γfs γi cov logstart k (q : Qp) (dev inum : mword 32) :
    ic_escrow_body cn γfs γi cov logstart k -∗
    ic_tok cn k -∗
    inode_ref (icn_ref cn) k q dev inum -∗
    ic_escrow_body cn γfs γi cov logstart k ∗
    (∃ v : bool,
       i_dev (ientry k) ↦₄{DfracOwn (1/2)} dev ∗
       i_inum (ientry k) ↦₄{DfracOwn (1/2)} inum ∗
       i_valid (ientry k) ↦₄ valid_word v ∗
       ic_payload γfs γi cov logstart k inum v).
  Proof.
    iIntros "Hbody Htok Href".
    iDestruct "Hbody" as "[Hpk | [Hout | [Hmid | Hvg]]]".
    - iDestruct "Hpk" as (dev' inum' v) "(Hid & Hin & Hvld & Hpay & Hmid & Hgid)".
      iDestruct "Href" as "[Hrt [Hrd Hrn]]".
      iDestruct (word4_pointsto_agree with "Hrd Hid") as %<-.
      iDestruct (word4_pointsto_agree with "Hrn Hin") as %<-.
      iSplitR "Hid Hin Hvld Hpay".
      { iRight; iLeft. rewrite /ic_out. iExists q, dev, inum. iFrame. }
      iExists v. iFrame.
    - iDestruct "Hout" as (q' dev' inum') "(Htok' & _ & _ & _)".
      iExFalso. iApply (ic_tok_exclusive with "Htok Htok'").
    - iDestruct "Hmid" as (dev' inum' w) "(_ & Hin & _ & _ & _)".
      iDestruct "Href" as "[_ [_ Hq]]".
      iExFalso. iApply (ic_word4_excl with "Hin Hq").
    - (* EMPTY (§13.8): the arm owns the WHOLE dev cell and the winner
         brought a fraction of it inside its reference. *)
      iDestruct "Hvg" as (dev' inum' w) "(Hidv & _ & _ & _ & _ & _)".
      iDestruct "Href" as "[_ [Hqd _]]".
      iExFalso. iApply (ic_word4_excl with "Hidv Hqd").
  Qed.

  (* (b) PARK, [iunlock]'s release (BioInv.escrow_swap_park).

     The opener's FULL valid cell refutes PARKED and MID -- both hold that
     cell full -- so the body is OUT, and the reference it parked comes back
     out.  The returned reference is at the SAME dev AND inum: the arm's two
     identity fractions agree with the halves the opener is handing back
     (§13.1e -- without the dev half, iunlock could only promise a reference
     at SOME device, and no caller could ever ilock the same inode twice).
     Only the FRACTION is existential, exactly as in
     [BioInv.escrow_swap_park].  The deposited PARKED re-absorbs the recycle
     token OUT was keeping. *)
  Lemma ic_swap_park cn γfs γi cov logstart k (v : bool) (dev inum : mword 32) :
    ic_escrow_body cn γfs γi cov logstart k -∗
    i_dev (ientry k) ↦₄{DfracOwn (1/2)} dev -∗
    i_inum (ientry k) ↦₄{DfracOwn (1/2)} inum -∗
    i_valid (ientry k) ↦₄ valid_word v -∗
    ic_payload γfs γi cov logstart k inum v -∗
    ic_escrow_body cn γfs γi cov logstart k ∗
    ic_tok cn k ∗
    (∃ q : Qp, inode_ref (icn_ref cn) k q dev inum).
  Proof.
    iIntros "Hbody Hid Hin Hvld Hpay".
    iDestruct "Hbody" as "[Hpk | [Hout | [Hmid | Hvg]]]".
    - iDestruct "Hpk" as (dev' inum' v') "(_ & _ & Hvld' & _ & _ & _)".
      iExFalso. iApply (ic_word4_excl with "Hvld Hvld'").
    - iDestruct "Hout" as (q dev' inum') "(Htok & [Hrt [Hrd Hrn]] & Hmid & Hgid)".
      iDestruct (word4_pointsto_agree with "Hrd Hid") as %->.
      iDestruct (word4_pointsto_agree with "Hrn Hin") as %->.
      iSplitR "Htok Hrt Hrd Hrn".
      { iLeft. rewrite /ic_parked. iExists dev, inum, v. iFrame. }
      iFrame "Htok". iExists q. iFrame.
    - iDestruct "Hmid" as (dev' inum' w) "(_ & _ & Hvld' & _ & _)".
      iExFalso. iApply (ic_word4_excl with "Hvld Hvld'").
    - (* EMPTY: it holds the valid cell too, and the parker is carrying it *)
      iDestruct "Hvg" as (dev' inum' w) "(_ & _ & Hvld' & _ & _ & _)".
      iExFalso. iApply (ic_word4_excl with "Hvld Hvld'").
  Qed.

  (* (c) THE AUTHORITY-SIDE OPENING AT REF-1 (iput's two lock-free reads).

     [iput] holds the table's authority half showing [M !! k = Some (q',1)]
     -- REF-1, established by the caller with [iref_lookup] -- plus its own
     reference.  OUT is impossible: the arm's fragment and the opener's
     would make the outstanding count at least two ([iref_tok_two_lookup])
     against a count of one.  MID is impossible: its inum cell is FULL and
     the opener holds a fraction of it.  So the body IS the parked bundle,
     at the opener's OWN inum, and everything the opener brought comes back.

     The rebuild wand takes a WHOLE [ic_parked], so the same lemma serves a
     read-only opening (put the pieces straight back) and one that changes
     the cells -- which is why §13's read-only variant is not a separate
     lemma. *)
  Lemma ic_open_auth_ref cn γfs γi cov logstart k
      (M : gmap nat (Qp * positive)) (q qt qi : Qp) (dev inum : mword 32) :
    M !! k = Some (qt, 1%positive) ->
    ic_escrow_body cn γfs γi cov logstart k -∗
    itable_half (icn_ref cn) M -∗
    iref_tok (icn_ref cn) k q -∗
    inode_ident k (DfracOwn qi) dev inum -∗
    itable_half (icn_ref cn) M ∗
    iref_tok (icn_ref cn) k q ∗
    inode_ident k (DfracOwn qi) dev inum ∗
    (∃ v : bool,
       i_dev (ientry k) ↦₄{DfracOwn (1/2)} dev ∗
       i_inum (ientry k) ↦₄{DfracOwn (1/2)} inum ∗
       i_valid (ientry k) ↦₄ valid_word v ∗
       ic_payload γfs γi cov logstart k inum v ∗
       ic_mid cn k ∗
       ic_id cn k (1/2) true) ∗
    (ic_parked cn γfs γi cov logstart k -∗
     ic_escrow_body cn γfs γi cov logstart k).
  Proof.
    iIntros (HMk) "Hbody Hhalf Htok Hid".
    iDestruct "Hbody" as "[Hpk | [Hout | [Hmid | Hvg]]]".
    - iDestruct "Hpk" as (dev' inum' v) "(Hidv & Hin & Hvld & Hpay & Hmidt & Hgid)".
      iDestruct "Hid" as "[Hidd Hidn]".
      iDestruct (word4_pointsto_agree with "Hidd Hidv") as %<-.
      iDestruct (word4_pointsto_agree with "Hidn Hin") as %<-.
      iFrame "Hhalf Htok Hidd Hidn".
      iSplitR "".
      { iExists v. iFrame. }
      iIntros "Hp". by iLeft.
    - iDestruct "Hout" as (q' dev' inum') "(_ & [Htok' _] & _ & _)".
      iDestruct (iref_tok_two_lookup with "Hhalf Htok Htok'")
        as %(qt' & n & HMk' & Hn).
      rewrite HMk in HMk'. injection HMk' as _ Hn1. subst n.
      iExFalso. iPureIntro. cbn in Hn. lia.
    - iDestruct "Hmid" as (dev' inum' w) "(_ & Hin & _ & _ & _)".
      iDestruct "Hid" as "[_ Hqi]".
      iExFalso. iApply (ic_word4_excl with "Hin Hqi").
    - (* EMPTY: the opener's own dev fraction against the arm's full cell *)
      iDestruct "Hvg" as (dev' inum' w) "(Hidv & _ & _ & _ & _ & _)".
      iDestruct "Hid" as "[Hqd _]".
      iExFalso. iApply (ic_word4_excl with "Hidv Hqd").
  Qed.

  (* (d1) THE RECYCLER'S OPENING (iget, the [sw] at +0x72).  Under §13.9
     there is only ONE of these: a slot iget recycles is not live, so its arm
     is EMPTY, so there is NO payload to evict -- the eviction argument is
     iput's, at the last close, where the flush semantics hold.  The table's
     share at such a slot carries no dev fraction (the arm owns that cell
     whole), so the ONLY thing that tells this arm from an ordinary parked
     one is the identification ghost.  This is also where the FLIP happens:
     past this opening the entry is live, and both halves are in the
     recycler's hand exactly here. *)
  Lemma ic_open_empty_free cn γfs γi cov logstart k (inumT : mword 32) :
    ic_escrow_body cn γfs γi cov logstart k -∗
    ic_id cn k (1/2) false -∗
    i_inum (ientry k) ↦₄{DfracOwn (1/2)} inumT -∗
    |==> i_inum (ientry k) ↦₄ inumT ∗
      (∃ devA w : mword 32,
         i_dev (ientry k) ↦₄ devA ∗
         i_valid (ientry k) ↦₄ w ∗
         inode_raw (ientry k)) ∗
      ic_mid cn k ∗
      ic_id cn k (1/2) true ∗
      ic_id cn k (1/2) true.
  Proof.
    iIntros "Hbody Hgf HinT".
    iDestruct "Hbody" as "[Hpk | [Hout | [Hmid | Hvg]]]".
    - iDestruct "Hpk" as (dev' inum' v) "(_ & _ & _ & _ & _ & Hgt)".
      iDestruct (ic_id_agree with "Hgf Hgt") as %Hc. discriminate.
    - iDestruct "Hout" as (q dev' inum') "(_ & _ & _ & Hgt)".
      iDestruct (ic_id_agree with "Hgf Hgt") as %Hc. discriminate.
    - iDestruct "Hmid" as (dev' inum' w) "(_ & _ & _ & _ & Hgt)".
      iDestruct (ic_id_agree with "Hgf Hgt") as %Hc. discriminate.
    - iDestruct "Hvg" as (devA inum' w) "(Hidv & Hin & Hvld & Hraw & Hmidt & Hgf')".
      iDestruct (word4_pointsto_agree with "HinT Hin") as %<-.
      iDestruct (word4_pointsto_half_join with "HinT Hin") as "Hin".
      iMod (ic_id_flip cn k false true with "Hgf Hgf'") as "[Hg1 Hg2]".
      iModIntro. iFrame "Hin Hmidt Hg1 Hg2".
      iExists devA, w. iFrame.
  Qed.

  (* (d0) THE RECYCLER'S DEV STORE (iget, the [sw] at +0x6e).  The empty arm
     already owns the WHOLE dev cell -- the table has no share to join in --
     so the recycler borrows it, stores, and hands it straight back, leaving
     the arm empty at its new (still meaningless) device.  Nothing about the
     empty arm couples dev to anything, which is why this is a plain
     open/close pair, and why the recycler keeps NO dev fraction across the
     gap to +0x72: the arm must still hold the cell whole, or
     [ic_swap_checkout] would lose its refutation. *)
  Lemma ic_open_empty_dev cn γfs γi cov logstart k :
    ic_escrow_body cn γfs γi cov logstart k -∗
    ic_id cn k (1/2) false -∗
    ic_id cn k (1/2) false ∗
    (∃ devA : mword 32, i_dev (ientry k) ↦₄ devA) ∗
    (∀ dev' : mword 32,
       i_dev (ientry k) ↦₄ dev' -∗
       ic_escrow_body cn γfs γi cov logstart k).
  Proof.
    iIntros "Hbody Hgf".
    iDestruct "Hbody" as "[Hpk | [Hout | [Hmid | Hvg]]]".
    - iDestruct "Hpk" as (dev' inum' v) "(_ & _ & _ & _ & _ & Hgt)".
      iDestruct (ic_id_agree with "Hgf Hgt") as %Hc. discriminate.
    - iDestruct "Hout" as (q dev' inum') "(_ & _ & _ & Hgt)".
      iDestruct (ic_id_agree with "Hgf Hgt") as %Hc. discriminate.
    - iDestruct "Hmid" as (dev' inum' w) "(_ & _ & _ & _ & Hgt)".
      iDestruct (ic_id_agree with "Hgf Hgt") as %Hc. discriminate.
    - iDestruct "Hvg" as (devA inum' w) "(Hidv & Hin & Hvld & Hraw & Hmidt & Hgf')".
      iFrame "Hgf".
      iSplitL "Hidv"; [iExists devA; iExact "Hidv" |].
      iIntros (dev2) "Hd".
      iRight; iRight; iRight. rewrite /ic_empty_arm.
      iExists dev2, inum', w. iFrame.
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
  Proof. iIntros "H". iRight; iRight; iRight. iExact "H". Qed.

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
     from [blkmap_wf], which [inode_ok] carries. *)
  Lemma ic_close_to_empty cn γfs γi cov logstart k (v : bool) (dev inum : mword 32) :
    ic_id cn k (1/2) true -∗
    ic_id cn k (1/2) true -∗
    i_dev (ientry k) ↦₄{DfracOwn (1/2)} dev -∗
    i_dev (ientry k) ↦₄{DfracOwn (1/2)} dev -∗
    i_inum (ientry k) ↦₄{DfracOwn (1/2)} inum -∗
    i_valid (ientry k) ↦₄ valid_word v -∗
    ic_payload γfs γi cov logstart k inum v -∗
    ic_mid cn k -∗
    |==> ic_escrow_body cn γfs γi cov logstart k ∗
         ic_id cn k (1/2) false ∗
         ipool_shape γfs γi cov logstart inum.
  Proof.
    iIntros "Hg1 Hg2 Hd1 Hd2 Hin Hvld Hpay Hmt".
    iMod (ic_id_flip cn k true false with "Hg1 Hg2") as "[Hgf1 Hgf2]".
    iDestruct (word4_pointsto_half_join with "Hd1 Hd2") as "Hd".
    (* the payload splits into the cells the empty arm keeps and the bundle
       the pool takes back *)
    iAssert (inode_raw (ientry k) ∗ ipool_shape γfs γi cov logstart inum)%I
      with "[Hpay]" as "[Hraw Hpool]".
    { destruct v; [| iExact "Hpay" ].
      iDestruct "Hpay" as (dn bm) "Hlk".
      iDestruct "Hlk" as (data) "(%Hok & Hdat & Hmeta & Haddrs & Hind & Hblks)".
      pose proof Hok as Hok'.
      destruct Hok' as (Hwf & _ & Hda & _ & _ & _).
      assert (Hcelllen : length (bm_cells bm) = 13%nat).
      { rewrite /bm_cells length_app (blkmap_wf_dir_len _ _ _ Hwf). reflexivity. }
      iSplitL "Hmeta Haddrs".
      { rewrite /inode_raw. iSplitL "Hmeta"; [by iExists dn |].
        iExists (bm_cells bm). iSplitR; [iPureIntro; exact Hcelllen |].
        iExact "Haddrs". }
      rewrite /ipool_shape. iLeft. iExists dn, bm, data. iFrame.
      iPureIntro; exact Hok. }
    iModIntro. iFrame "Hgf2 Hpool".
    iApply ic_close_empty. rewrite /ic_empty_arm.
    iExists dev, inum, (valid_word v). iFrame.
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
    iDestruct "Hbody" as "[Hpk | [Hout | [Hmid | Hvg]]]".
    - iDestruct "Hpk" as (dev inum v) "(_ & _ & _ & _ & Hmt' & _)".
      iExFalso. iApply (ic_mid_exclusive with "Hmt Hmt'").
    - iDestruct "Hout" as (q dev inum) "(_ & _ & Hmt' & _)".
      iExFalso. iApply (ic_mid_exclusive with "Hmt Hmt'").
    - iFrame.
    - iDestruct "Hvg" as (dev inum w) "(_ & _ & _ & _ & Hmt' & _)".
      iExFalso. iApply (ic_mid_exclusive with "Hmt Hmt'").
  Qed.

  (* the reclose after the valid store: the window's FULL inum cell splits
     back into the arm's permanent half and the half the table retains, and
     the parked arm is deposited at v = false (the recycled entry is
     unloaded by construction).  Stating the split HERE is what keeps
     iget's proof from having to know the budget. *)
  Lemma ic_close_mid_to_parked cn γfs γi cov logstart k (dev inum : mword 32) :
    ic_mid cn k -∗
    ic_id cn k (1/2) true -∗
    i_dev (ientry k) ↦₄{DfracOwn (1/2)} dev -∗
    i_inum (ientry k) ↦₄ inum -∗
    i_valid (ientry k) ↦₄ valid_word false -∗
    ic_unloaded γfs γi cov logstart k inum -∗
    ic_escrow_body cn γfs γi cov logstart k ∗
    i_inum (ientry k) ↦₄{DfracOwn (1/2)} inum.
  Proof.
    iIntros "Hmt Hgid Hid Hin Hvld Hpay".
    iDestruct (word4_pointsto_half_split with "Hin") as "[Hin1 Hin2]".
    iSplitR "Hin2"; [| iExact "Hin2"].
    iLeft. rewrite /ic_parked.
    iExists dev, inum, false. iFrame.
  Qed.

  (* (f) BORROWING THE ARM'S REFERENCE, for a lock-free read INSIDE the
     critical section (iunlock's [ip->ref] panic guard).

     A thread that has checked the entry out holds the payload and no
     reference at all -- the deviation note in the header -- but it does
     hold the FULL valid cell, which refutes PARKED and MID.  So it can open
     the escrow, borrow OUT's reference for the duration of one atomic
     update, and hand it straight back. *)
  Lemma ic_open_out cn γfs γi cov logstart k (v : bool) :
    ic_escrow_body cn γfs γi cov logstart k -∗
    i_valid (ientry k) ↦₄ valid_word v -∗
    i_valid (ientry k) ↦₄ valid_word v ∗
    (∃ (q : Qp) (dev inum : mword 32),
       inode_ref (icn_ref cn) k q dev inum ∗
       (inode_ref (icn_ref cn) k q dev inum -∗
        ic_escrow_body cn γfs γi cov logstart k)).
  Proof.
    iIntros "Hbody Hvld".
    iDestruct "Hbody" as "[Hpk | [Hout | [Hmid | Hvg]]]".
    - iDestruct "Hpk" as (dev' inum v') "(_ & _ & Hvld' & _ & _ & _)".
      iExFalso. iApply (ic_word4_excl with "Hvld Hvld'").
    - iDestruct "Hout" as (q dev inum) "(Htok & Href & Hmt & Hgid)".
      iFrame "Hvld". iExists q, dev, inum. iFrame "Href".
      iIntros "Href". iRight; iLeft. rewrite /ic_out.
      iExists q, dev, inum. iFrame.
    - iDestruct "Hmid" as (dev' inum w) "(_ & _ & Hvld' & _ & _)".
      iExFalso. iApply (ic_word4_excl with "Hvld Hvld'").
    - iDestruct "Hvg" as (dev' inum w) "(_ & _ & Hvld' & _ & _ & _)".
      iExFalso. iApply (ic_word4_excl with "Hvld Hvld'").
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

  (* THE THREE WF CLAUSES (§13.2, and §13.9 on why the first one is an
     EQUALITY after all): [ci] records exactly the LIVE slots.

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
     [mword_of_int] faithful on the pool's keys. *)
  Definition ic_ci_wf (M : gmap nat (Qp * positive))
      (ci : gmap nat (mword 32 * mword 32)) (nib : nat) : Prop :=
    dom ci = dom M
    /\ (forall (k1 k2 : nat) (p1 p2 : mword 32 * mword 32),
          ci !! k1 = Some p1 -> ci !! k2 = Some p2 ->
          bv_unsigned (snd p1) = bv_unsigned (snd p2) -> k1 = k2)
    /\ (forall (k : nat) (p : mword 32 * mword 32),
          ci !! k = Some p -> bv_unsigned (snd p) < 16 * Z.of_nat nib).

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
    iIntros "H1 H2". iFrame.
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

  Global Instance ipool_timeless γfs γi cov logstart P :
    Timeless (ipool γfs γi cov logstart P).
  Proof. rewrite /ipool. apply _. Qed.

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
    ((∃ inum : mword 32, i_inum (ientry k) ↦₄{DfracOwn (1/2)} inum) ∗
     ic_id cn k (1/2) false)%I.

  Definition islot2 (cn : ic_names) (M : gmap nat (Qp * positive))
      (ci : gmap nat (mword 32 * mword 32)) (k : nat) : iProp Σ :=
    match M !! k, ci !! k with
    | None, None => islot_empty cn k
    | Some (q, n), Some (dev, inum) =>
        (islot_rest_at k q dev inum ∗ iref_slots (Pos.to_nat n) ∗
         ic_id cn k (1/2) true)%I
    | _, _ => False%I
    end.

  Definition itable_res2 (cn : ic_names) (γfs : fs_names) (γi : gname)
      (cov : gset Z) (logstart : Z) (nib : nat) : iProp Σ :=
    (∃ (M : gmap nat (Qp * positive)) (ci : gmap nat (mword 32 * mword 32)),
       itable_half (icn_ref cn) M ∗
       ⌜icM_wf M⌝ ∗ ⌜ic_ci_wf M ci nib⌝ ∗
       iref_slots_auth ∗
       ([∗ list] k ∈ seq 0 NINODE, islot2 cn M ci k) ∗
       ipool γfs γi cov logstart (region_inums nib ∖ ci_inums ci))%I.

  Definition is_itable2 (γl : gname) (cn : ic_names) (γfs : fs_names)
      (γi : gname) (cov : gset Z) (logstart : Z) (nib : nat) : iProp Σ :=
    is_lock γl itable_lock "itable"%string
      (itable_res2 cn γfs γi cov logstart nib).

  Global Instance is_itable2_persistent γl cn γfs γi cov logstart nib :
    Persistent (is_itable2 γl cn γfs γi cov logstart nib).
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

End IcacheEscrow.

(* ===================================================================== *)
(*  7.  ALLOCATION OF THE TOKEN FAMILIES                                  *)
(* ===================================================================== *)

Section IcacheEscrowAlloc.
  Context `{!riscvGS Σ, !lockG Σ, !icacheG Σ}.

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

  (* the IDENTIFICATION ghost's family (§13.8), allocated the same way and at
     [false]: at boot every entry is empty.  Each slot's variable comes out
     WHOLE, so the caller splits it into the escrow's half and the table's. *)
  Lemma ic_id_fun_alloc (n j : nat) :
    ⊢ |==> ∃ f : nat -> gname, [∗ list] k ∈ seq j n, ghost_var (f k) 1 false.
  Proof.
    iInduction n as [|n IH] forall (j).
    { iModIntro. iExists (fun _ => inhabitant). cbn [seq]. done. }
    iMod (ghost_var_alloc false) as (γ) "Hg".
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
  Lemma ic_names_alloc (γref : gname) :
    ⊢ |==> ∃ cn : ic_names,
      ⌜icn_ref cn = γref⌝ ∗
      ([∗ list] k ∈ seq 0 NINODE, ic_tok cn k) ∗
      ([∗ list] k ∈ seq 0 NINODE, ic_mid cn k) ∗
      ([∗ list] k ∈ seq 0 NINODE, ic_id cn k 1 false).
  Proof.
    iMod (ic_tok_fun_alloc NINODE 0) as (fesc) "Hesc".
    iMod (ic_tok_fun_alloc NINODE 0) as (fmid) "Hmid".
    iMod (ic_id_fun_alloc NINODE 0) as (fid) "Hid".
    iModIntro. iExists (MkIcNames γref fesc fmid fid).
    iSplitR; [done |]. rewrite /ic_tok /ic_mid /ic_id.
    cbn [icn_esc icn_mid icn_id].
    iFrame.
  Qed.

End IcacheEscrowAlloc.
