(* ======================================================================= *)
(*  IgetLic.v -- THE iget LICENCE ENUMERATION (increment C'-lite)           *)
(*                                                                         *)
(*  design of record: claude-notes/design/fs-fragments.md §7.1, ratified    *)
(*  as R13(i) and amended by R14.                                          *)
(* ======================================================================= *)

(*  WHAT THIS FILE IS FOR.

    [SpecIget] hands back a REFERENCE to an inode the caller names only by
    its inum, and the number came off a disk block: nothing in iget's own
    contract says the inum is allocated, and nothing in iget's own proof
    could.  §20.17.5 answered that with a PARAGRAPH -- an enumeration of the
    six reasons a caller of iget has to believe its inum names a live
    record, checked by reading the tree.  This file makes the paragraph a
    TYPE.

    The user's invariant -- "the kernel will never invoke iget on inode
    numbers in directories in a disconnected subtree" -- is not statable as
    a property of the machine's traces anywhere inside [ProofCreate] or
    [ProofIput] (§20.17.7 option (ii)).  It IS statable as a resource
    premise at the point of DELIVERY, and that is what [iname] is: every
    [iget] in the tree presents one licence out of a closed list, and the
    orphan-[".."] door (TRACE G, §7.5.4) is closed by contract, at exactly
    the [fs.c:693] [nlink] guard where [ProofNamex] earns its own.

    AN INDEX, NOT AN EXISTENTIAL (§7.1.1).  [ilic] is an inductive with one
    constructor per licence and [iname] is a [match] on it.  Three things
    the index buys that a disjunction does not: [destruct l] is exhaustive
    by construction; every call site names its licence in its own [iApply]
    line, so the audit is a [grep]; and §20.17.5's box becomes a
    mechanically checkable proposition -- *no site in the tree instantiates
    [GreyL]* -- which under the paragraph was a claim about reachability.

    HOME.  This is a NEW LEAF and it stays one.  The definitions belong
    beside [InodeRegion.v]'s ledger, but that file carries ~350 dependents
    and an additive definition inside it costs that cone on every iteration
    (durable-notes, "the rebuild cone is the dev-loop cost") -- the same
    reason [IregLinkNz.v] exists.  Fold back at a milestone.

    WHAT THIS FILE DOES NOT DO.  It does not discharge the free-side wall.
    §7.1.6's death certificate stands verbatim: the licence is BORROWED at
    the iget and RETURNED before the call ends, so [iput] holds none, and
    "the reference that outlives its licence" (§20.7) is untouched.
    The fresh-type span stands (see [ProofCreateFreshTy.v]).  This increment retires §20.17.5's PARAGRAPH,
    not §20.7's WALL.                                                      *)

From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import auth gmap frac excl.
From iris.algebra.lib Require Import dfrac_agree.
From iris.base_logic.lib Require Import invariants ghost_map.
Require Import SailStdpp.Values.
Require Import RiscvPtsto.
Require Import FsBlocks.
Require Import LogInv.
Require Import DinodeEnc.
Require Import DirView.
Require Import IcacheRef.
Require Import DirLinks.
Require Import InodeRegion.
Require Import FsStateLink.    (* [fsLinkG] -- capacity class, must be IMPORTed *)
Require Import FsBytesGamma.   (* [fs_gamma_L]                                  *)
Require Import Xv6G.   (* the ghost-state bundle; see its header *)

Local Open Scope Z_scope.

(* ----------------------------------------------------------------------- *)
(*  THE ENUMERATION                                                         *)
(* ----------------------------------------------------------------------- *)

(*  §20.4's six licences, in §20.4's order, plus R14's transitional seventh.

      [LinkedL]  (a)  a directory record names the inum and PAYS for it: the
                      caller lends the ENTRY's counting unit
                      ([FsStateLink.link_tok] at that inum, borrowed out of
                      the home's [FsStateInode.ent_toks] by
                      [FsStateEra.ent_toks_borrow]), the RA's own law
                      [link_auth_toks_le] read at the TARGET's authority in
                      [InodeRegion.ireg_lnk] bounds the count below, and
                      (L3) turns that into a nonzero type.  This is the
                      allocatedness witness §20 exists for, and it is the
                      licence every [dirlookup] delivers at a record that is
                      not the home's own.
                      THE CONSTRUCTOR CARRIES NO DATA any more (2b-inode-5,
                      step 3): a counting unit has no flavour, so the
                      [option (option Z)] index that used to pin WHICH of
                      [ilink] / [ilinkd] / [ilinkdp] the caller was lending
                      dies with the three-column ledger it indexed.
      [GreyL]    (b)  DELETED -- see the tombstone below.
      [HeldL]    (c)  the caller already holds the record, exclusively.  A
                      lookup of ["."] is the worked instance: it returns the
                      inum of the directory the caller has locked, whose own
                      [dinode_at] with a nonzero type is a strictly BETTER
                      witness than any fragment.
      [ClaimL]   (d)  the detached fragment of a claim box.  NOTHING MINTS
                      AN [iclaim] TODAY and nothing may: §7.1.5's theorem
                      says any region clause strong enough to found (d) is a
                      clause [EscrowDeposit.ireg_free_deposit_au] must re-establish, so (d) and
                      the walled increment F1.5c/F1.5d are ONE increment.
                      The constructor is R11's honesty marker, kept visible
                      in the source and never instantiated.
      [BufL]     (e)  the caller holds the inode BLOCK's client half at
                      bytes that decode to a record with a nonzero type.
                      §7.1.3's improvement on §20.4: the resource is
                      [FsBlocks.fs_chalf], one level below [bio_locked], and
                      it is STRONGER -- the element sits at ½+½, so a client
                      holding one half means no [ireg_write_au] /
                      [ireg_claim_au] / [EscrowDeposit.ireg_free_deposit_au] at ANY inum of that
                      block can fire while it is held.  That is §16.2's
                      serialiser as a resource fact.
      [RootL]    (f)  the inum is the root's.  The region's ROOT KEEP-ALIVE
                      TOKEN ([InodeRegion.ireg_keep], read by
                      [ireg_lnk_root_alive]) is what makes this a licence
                      rather than an assumption: root's [".."] is a SELF
                      record and therefore tokenless, so root's [nlink = 1]
                      is unaccounted for and the region parks the one unit
                      that nothing spends.
      (the two deleted licences, [GreyL] and [SpanL], are tombstoned
      below.)                                                             *)

(*  THREE CONSTRUCTORS CARRY DATA, AND THAT IS FORCED BY "THE SAME [l]".
    §7.1.1 wrote (a), (c) and (e) with the licence's content hidden behind a
    [∃] -- [∃ d, dinode_at …], [∃ ds, fs_chalf …].  A post that returns the
    licence "at the same [l]" then returns a DIFFERENT resource: the caller
    lends [dinode_at γi inum dn] and gets back [∃ d, dinode_at γi inum d],
    which no walk can put back into its payload.  The borrow is only a
    borrow if the index pins the content, so the record, the record LIST and
    the payment FLAVOUR are constructor arguments.  The enumeration is still
    closed and still seven constructors, [destruct l] is still exhaustive,
    and the two standing greps are unaffected. *)
Inductive ilic :=
  | LinkedL
  | HeldL (d : dinode)
  | ClaimL (ty : bv 16) (t : nat) (q : Qp)
  | BufL (bno : Z) (ds : list dinode)
  | RootL.

(*  ===================================================================== *)
(*  TWO TOMBSTONES: [SpanL] and [GreyL] ARE DELETED                        *)
(*  ===================================================================== *)
(*
    [SpanL] IS GONE, DELETED PER ITS OWN SCHEDULE.  The R14 header that
    stood here said in as many words: "IT DELETES.  [SpanL] goes away when
    F1.5c mints an [iclaim] (the site becomes [ClaimL], no signature moves
    -- that is why (d) is kept)".  F1.5c is
    claude-notes/projects/iclaim-ledger.md, whose §2.4 executes exactly that
    -- [InodeRegion.ireg_claim_au] now mints [iclaim] -- so the one
    permitted site ([ProofIalloc.v]'s iget, §7.1.7's window) becomes a
    [ClaimL] site and the transitional [⌜True⌝] licence has nothing left to
    license.  The standing audit [grep -n "SpanL" iris/Proof*.v] is
    satisfied by construction from here: the constructor does not exist.

    [GreyL] IS GONE TOO, AND ITS DELETION IS REQUIRED RATHER THAN
    HOUSEKEEPING (iclaim-ledger.md §2.6's licence table).  Its audit
    ("[grep -n "GreyL" iris/Proof*.v] must be empty") had held on the lane
    since R14, so no site moves.  What forces the deletion is the free-side
    wall: at an in-transition box (f = Some or c = Some) EVERY licence must
    be refutable, and [GreyL] is not -- a grave-[".."] grey legitimately
    survives the free ([IcacheRef.igrey]'s charter: "it carries no
    allocatedness, and that is the point").  With the new mint obligation an
    undeletable [GreyL] would make iget's own proof unclosable.  The [g]
    column and the [igrey] FRAGMENT both stay: the ledger's grave-[".."]
    state is untouched, only the LICENCE dies.                             *)

Section IgetLic.
  Context `{!riscvGS Σ, !xv6G Σ}.
  Context `{ICFG : icfg}.

  (* ------------------------------------------------------------------ *)
  (*  LICENCE (a)'s CARRIER: ONE COUNTING UNIT                            *)
  (* ------------------------------------------------------------------ *)

  (*  §7.1.1 spelt licence (a) as [ilink z], V5' split it by FLAVOUR into
      [DirLinks.dlc_tick self k (F k) z], and 2b-inode-5 collapses the whole
      family back to ONE proposition: [FsStateLink.link_tok Γ z], the
      counting RA's unit at the TARGET inum.  There is no flavour left to
      index -- a unit is a unit -- so [LinkedL] carries no argument, and the
      lending is not "the payload's ticket at record k" but "one of the
      home's entry units", peeled by [FsStateEra.ent_toks_borrow] and put
      back by its wand.

      WHY THE BORROW IS NOT HERE.  [ent_toks] is keyed by NAME, so the peel
      needs [FsTree.dir_view_lookup] at the record the scan WON on; that is
      an era-side fact and it lives beside the other per-move lemmas in
      [FsStateEra].  What is left here is the licence itself.

      WHY (L1) IS NOT READ HERE EITHER.  The bound the licence needs is
      [1 <= #tokens ⟹ 1 <= nlink], and the RA proves it OUTRIGHT
      ([FsStateLink.link_auth_toks_le]) against the authority the region
      parks at the target's own slot ([InodeRegion.ireg_lnk]).  So the
      reading below opens [iregN] once and applies
      [InodeRegion.ireg_lnk_tok_nz]; there is no ledger column to consult
      and no invariant to maintain. *)

  (* THE FLAVOUR OF THE UNIT A LICENCE MINTS (§5'.2): the [ClaimL] iget --
     ialloc's own, into its own claim box -- mints [runit_claim]; every other
     licence mints [runit_plain].  One function, so the mint sites, the
     contracts and the pin's side condition all read the same index. *)
  Definition is_claim (l : ilic) : bool :=
    match l with ClaimL _ _ _ => true | _ => false end.

  (* ------------------------------------------------------------------ *)
  (*  THE LICENCE ITSELF                                                  *)
  (* ------------------------------------------------------------------ *)

  Definition iname (γi : gname) (γfs : fs_names) (inodestart : Z)
                   (inum : bv 32) (l : ilic)
    : iProp Σ :=
    match l with
    | LinkedL => FsStateLink.link_tok (FsBytesGamma.fs_gamma_L γfs)
                   (bv_unsigned inum)                                (* a *)
    (* (c) STRENGTHENED BY iclaim-ledger.md §2.6: the held record's link
       count is NONZERO.  That is what makes [HeldL] refutable at an
       in-transition box -- both pins carry [di_nlink = 0], and
       fragment-auth agreement pins [d] to the arm's record.  VERIFY(2.6a)
       audited on the lane: the one worked instance is the ["."] lookup at a
       caller-locked LIVE directory ([ProofDirlookup.v:2074]), which is at
       [1 <= nlink] already; no site presents a torn-down dir. *)
    | HeldL d => (dinode_at γi inum d ∗
                  ⌜bv_unsigned (di_type d) <> 0⌝ ∗
                  ⌜bv_unsigned (di_nlink d) <> 0⌝)                   (* c *)
    | ClaimL ty t q => iclaim (bv_unsigned inum) ty t q             (* d *)
    (* (e) BOOT-GATED BY §2.6: the presenter also LENDS [ireg_boot].
       Runtime: nobody has it after the seal fires, so licence (e) is
       unpresentable at all and the free-side table has nothing to refute.
       Boot: the presenter's pending token doubles against the freeze arm's
       parked pending ([ity_pending_excl]) or meets a runtime claim's
       [ireg_open] ([ireg_boot_open_excl]).  BORROWED, like the rest of the
       licence -- it is simply part of the [iname] resource the caller
       lends, and [ProofIreclaim.v:1302] (the only site in the tree) is a
       boot-thread proof that holds one; it re-proves in a later
       increment. *)
    (* THE BLOCK TIE IS THE LICENCE'S OWN (SIMP-1).  It used to be a
       standalone premise on [SpecIget] -- and hence a [discriminate] at
       every one of the tree's non-[BufL] iget sites -- but it is a fact
       ABOUT THIS CONSTRUCTOR and nothing else: the half a [BufL] presenter
       holds must be the block that CONTAINS the inum it is licensing, or
       [iname_mint_ok] cannot meet it against the region's own half.  Stated
       here it is discharged once, by the one presenter in the tree
       ([ProofIreclaim]'s boot walk), and no other caller ever sees it. *)
    | BufL bno ds =>
                 (fs_chalf γfs bno (diblk_bytes ds) ∗                  (* e *)
                  ⌜bno = IBLOCK inum inodestart⌝ ∗
                  ⌜diblk_wf ds⌝ ∗
                  ⌜bv_unsigned (di_type (ds !!! islot inum)) <> 0⌝ ∗
                  ireg_boot)
    | RootL   => ⌜bv_unsigned inum = ireg_root⌝                      (* f *)
    end%I.

  (* Timeless throughout -- which is what lets [SpecIget]'s premise sit
     beside the itable spinlock's resource without a later. *)
  Global Instance iname_timeless γi γfs ist inum l :
    Timeless (iname γi γfs ist inum l).
  Proof. destruct l; rewrite /iname; apply _. Qed.

  (* ------------------------------------------------------------------ *)
  (*  THE READINGS, AND THE SHAPE THEY MUST TAKE                          *)
  (* ------------------------------------------------------------------ *)

  (*  STANDING CONSTRAINT (§7.1.4, the [ProofCreateFreshTy.v] header's test).
      Every reading below is an ACCESSOR OVER [ireg_inv], in
      [IregLinkNz.ireg_link_nz]'s shape: it opens the region, reads the
      ledger's own clauses at the slot the caller's [dinode_at] names, and
      hands everything back.  A free-standing entailment

          iname γi γfs inodestart inum l -∗ ⌜bv_unsigned (di_type dn) <> 0⌝

      with [dn] FREE is the inconsistent form the axiom's own header warns
      about, verbatim -- it says something about a record nobody has tied to
      the licence.  Write it in the accessor shape or not at all.

      [ClaimL] has no reading yet; F1.5c's payout increment (§2.8 item 7) is
      what gives it one, at create's fill.                                 *)

  (* ---- (a) [LinkedL] ⇒ allocated ------------------------------------- *)

  (*  [link_tok Γ z] ⇒ [1 <= nlink] ([InodeRegion.ireg_lnk_tok_nz], which is
      the RA's law [link_auth_toks_le] read at the authority the region
      parks at THIS inum's slot) ⇒ (L3)'s contrapositive [di_type <> 0].
      Everything is borrowed and returned, exactly as [ireg_link_nz] borrows
      it; the opening is mask-preserving.  The (L3) step is why this is not
      simply the RA law plus a corollary: (L3) is a clause of [ireg_slot]
      and can only be read INSIDE the opening -- and so, now, is the
      authority the law is read against, which is the whole reason
      2b-inode-4 put it there. *)
  Lemma iname_linked_alloc (E : coPset) (γi : gname) (γfs : fs_names)
      (inodestart : Z) (nib : nat) (inum : bv 32) (dn : dinode) :
    ↑iregN ⊆ E ->
    bv_unsigned inum < 16 * Z.of_nat nib ->
    ireg_inv γi γfs inodestart nib -∗
    dinode_at γi inum dn -∗
    iname γi γfs inodestart inum LinkedL ={E}=∗
    ⌜bv_unsigned (di_type dn) <> 0⌝ ∗
    dinode_at γi inum dn ∗ iname γi γfs inodestart inum LinkedL.
  Proof.
    iIntros (HE Hin) "#Hinv Hdn Hfrag". rewrite /iname.
    pose proof (islot_lt inum) as Hsl.
    assert (Hkey : (16 * Z.of_nat (ireg_bi inum) + Z.of_nat (islot inum))%Z
                   = bv_unsigned inum) by (symmetry; apply ireg_key_split).
    iDestruct "Hinv" as "[#Hiinv [#Hrb #Hftopi]]".
    iMod (inv_acc E iregN with "Hiinv") as "[Hbody Hclose]"; [exact HE |].
    iDestruct "Hbody" as (m) "(>Ha & Hblks & >Hreg)".
    pose proof (ireg_bi_lt inum nib Hin) as Hbi.
    iDestruct (ireg_blks_acc_upd γi γfs inodestart m nib (ireg_bi inum) Hbi
                with "Hblks") as "[Hblk Hback]".
    iDestruct "Hblk" as (ds) "(>%Hwf & >%Hcp & >Hfsb & >Hsls)".
    assert (Hlen16 : length ds = 16%nat) by (destruct Hwf as [Hl _]; exact Hl).
    iDestruct (ireg_slots_acc_upd γfs γi (ireg_bi inum) ds (islot inum) Hsl Hlen16
                with "Hsls") as "[Hslot Hslback]".
    iEval (rewrite Hkey) in "Hslot".
    iDestruct "Hslot" as "[(%wl & %wdu & %wdt & %gl & %rl & %cl & %pl & %fz & %cn & Hla & %Hlok & %Hdir & %Hwl0 & %Hpar & #Hdisj & Hcnt & %Hclm & %Hfrz & Hfdisj & Hfrcp & Harm) [Hep Hlnk]]".
    iDestruct (ireg_lnk_tok_nz with "Hlnk Hfrag") as %Hnl1.
    rewrite /dinode_at.
    iDestruct (ghost_map_lookup with "Ha Hdn") as %Hm.
    assert (Hdeq : ds !!! islot inum = dn).
    { specialize (Hcp (islot inum) Hsl).
      rewrite -ireg_key_split in Hcp. congruence. }
    (* the RA's law, then (L3), both read at the caller's own record *)
    assert (Hnz : bv_unsigned (di_type dn) <> 0).
    { rewrite -Hdeq. destruct Hlok as [_ [Hl3 _]]. intro Hty.
      exact (Hnl1 (Hl3 Hty)). }
    assert (Hins : <[islot inum := ds !!! islot inum]> ds = ds).
    { apply list_insert_id, list_lookup_lookup_total_lt. lia. }
    iMod ("Hclose" with "[Ha Hreg Hfsb Harm Hla Hep Hlnk Hslback Hback Hcnt Hfdisj Hfrcp]") as "_".
    { iNext. iExists m. iFrame "Ha Hreg".
      iApply ("Hback" $! m with "[%] [Hfsb Harm Hla Hep Hlnk Hslback Hcnt Hfdisj Hfrcp]"); [done |].
      iExists ds. iSplitR; [done |]. iSplitR; [done |].
      iSplitL "Hfsb"; [iExact "Hfsb" |].
      iEval (rewrite -Hins).
      iApply ("Hslback" $! (ds !!! islot inum) with "[Harm Hla Hep Hlnk Hcnt Hfdisj Hfrcp]").
      rewrite Hkey.
      iApply (ireg_slot_intro γfs γi (bv_unsigned inum) (ds !!! islot inum)
                wl wdu wdt gl cl rl pl fz cn Hlok Hdir Hwl0 Hpar Hclm Hfrz
                with "Hla Hep Hlnk Hdisj Hcnt Hfdisj Hfrcp Harm"). }
    iModIntro. iFrame "Hdn Hfrag". iPureIntro. exact Hnz.
  Qed.

  (* ---- (c) [HeldL] ⇒ allocated, definitional ------------------------- *)

  (*  THE ONE READING THAT MAY NOT TAKE A CALLER'S [dinode_at], AND THE
      REASON IS THE STANDING CONSTRAINT ITSELF.  [dinode_at] is a
      FULL-fraction ghost_map element ([InodeRegion.dinode_at_excl]), so a
      lemma of the accessor family's shape --

          ireg_inv -∗ dinode_at γi inum dn -∗ iname γi γfs inodestart inum HeldL
            ={E}=∗ ⌜bv_unsigned (di_type dn) <> 0⌝ ∗ …

      -- has an UNSATISFIABLE premise set: the licence carries a second
      element at the same key, so the two fragments prove [False] and the
      lemma says nothing about anything.  That is precisely the
      twice-instantiate failure of §4.1, one tier up, and writing it would
      have been green.  The honest statement is the unpack: the licence IS
      the record, so it hands the record out and takes it back. *)
  Lemma iname_held_alloc (γi : gname) (γfs : fs_names) (inodestart : Z)
      (inum : bv 32) (d : dinode) :
    iname γi γfs inodestart inum (HeldL d) -∗
    ⌜bv_unsigned (di_type d) <> 0⌝ ∗ ⌜bv_unsigned (di_nlink d) <> 0⌝
    ∗ dinode_at γi inum d.
  Proof.
    rewrite /iname. iIntros "(Hd & %Hnz & %Hnl)". by iFrame "Hd".
  Qed.

  (* ...and back in, which is all the round trip costs at the ["."] site.
     The [nlink] premise is §2.6's strengthening: the ["."] site holds a
     LIVE directory, so it is discharged where the licence is built. *)
  Lemma iname_held_intro (γi : gname) (γfs : fs_names) (inodestart : Z)
      (inum : bv 32) (d : dinode) :
    bv_unsigned (di_type d) <> 0 ->
    bv_unsigned (di_nlink d) <> 0 ->
    dinode_at γi inum d -∗ iname γi γfs inodestart inum (HeldL d).
  Proof. intros Hnz Hnl. rewrite /iname. iIntros "Hd". by iFrame "Hd". Qed.

  (* ---- (f) [RootL] ⇒ allocated --------------------------------------- *)

  (*  THE ROOT KEEP-ALIVE TOKEN'S FIRST CONSUMER.  [InodeRegion.ireg_keep]
      parks one [link_tok] at [ireg_root] and nothing spends it; its
      chartered reading [ireg_lnk_root_alive] gives [1 <= di_nlink] at the
      root outright, and (L3)'s contrapositive turns that into the nonzero
      type.  Note the shape is the accessor's, not a
      free-standing entailment: [RootL]'s own proposition is PURE, so
      without the opening it would conclude something about a [dn] nothing
      had tied to the root's slot. *)
  Lemma iname_root_alloc (E : coPset) (γi : gname) (γfs : fs_names)
      (inodestart : Z) (nib : nat) (inum : bv 32) (dn : dinode) :
    ↑iregN ⊆ E ->
    bv_unsigned inum < 16 * Z.of_nat nib ->
    ireg_inv γi γfs inodestart nib -∗
    dinode_at γi inum dn -∗
    iname γi γfs inodestart inum RootL ={E}=∗
    ⌜bv_unsigned (di_type dn) <> 0⌝ ∗
    dinode_at γi inum dn ∗ iname γi γfs inodestart inum RootL.
  Proof.
    iIntros (HE Hin) "#Hinv Hdn %Hroot". rewrite /iname.
    pose proof (islot_lt inum) as Hsl.
    assert (Hkey : (16 * Z.of_nat (ireg_bi inum) + Z.of_nat (islot inum))%Z
                   = bv_unsigned inum) by (symmetry; apply ireg_key_split).
    iDestruct "Hinv" as "[#Hiinv [#Hrb #Hftopi]]".
    iMod (inv_acc E iregN with "Hiinv") as "[Hbody Hclose]"; [exact HE |].
    iDestruct "Hbody" as (m) "(>Ha & Hblks & >Hreg)".
    pose proof (ireg_bi_lt inum nib Hin) as Hbi.
    iDestruct (ireg_blks_acc_upd γi γfs inodestart m nib (ireg_bi inum) Hbi
                with "Hblks") as "[Hblk Hback]".
    iDestruct "Hblk" as (ds) "(>%Hwf & >%Hcp & >Hfsb & >Hsls)".
    assert (Hlen16 : length ds = 16%nat) by (destruct Hwf as [Hl _]; exact Hl).
    iDestruct (ireg_slots_acc_upd γfs γi (ireg_bi inum) ds (islot inum) Hsl Hlen16
                with "Hsls") as "[Hslot Hslback]".
    iEval (rewrite Hkey) in "Hslot".
    iDestruct "Hslot" as "[(%wl & %wdu & %wdt & %gl & %rl & %cl & %pl & %fz & %cn & Hla & %Hlok & %Hdir & %Hwl0 & %Hpar & #Hdisj & Hcnt & %Hclm & %Hfrz & Hfdisj & Hfrcp & Harm) [Hep Hlnk]]".
    rewrite /dinode_at.
    iDestruct (ghost_map_lookup with "Ha Hdn") as %Hm.
    assert (Hdeq : ds !!! islot inum = dn).
    { specialize (Hcp (islot inum) Hsl).
      rewrite -ireg_key_split in Hcp. congruence. }
    iEval (rewrite Hroot) in "Hlnk".
    iDestruct (ireg_lnk_root_alive γfs (ds !!! islot inum) with "Hlnk")
      as %Halive.
    iEval (rewrite -Hroot) in "Hlnk".
    assert (Hnz : bv_unsigned (di_type dn) <> 0).
    { rewrite -Hdeq. destruct Hlok as [_ [Hl3 _]]. intro Hty.
      rewrite (Hl3 Hty) in Halive. lia. }
    assert (Hins : <[islot inum := ds !!! islot inum]> ds = ds).
    { apply list_insert_id, list_lookup_lookup_total_lt. lia. }
    iMod ("Hclose" with "[Ha Hreg Hfsb Harm Hla Hep Hlnk Hslback Hback Hcnt Hfdisj Hfrcp]") as "_".
    { iNext. iExists m. iFrame "Ha Hreg".
      iApply ("Hback" $! m with "[%] [Hfsb Harm Hla Hep Hlnk Hslback Hcnt Hfdisj Hfrcp]"); [done |].
      iExists ds. iSplitR; [done |]. iSplitR; [done |].
      iSplitL "Hfsb"; [iExact "Hfsb" |].
      iEval (rewrite -Hins).
      iApply ("Hslback" $! (ds !!! islot inum) with "[Harm Hla Hep Hlnk Hcnt Hfdisj Hfrcp]").
      rewrite Hkey.
      iApply (ireg_slot_intro γfs γi (bv_unsigned inum) (ds !!! islot inum)
                wl wdu wdt gl cl rl pl fz cn Hlok Hdir Hwl0 Hpar Hclm Hfrz
                with "Hla Hep Hlnk Hdisj Hcnt Hfdisj Hfrcp Harm"). }
    iModIntro. iFrame "Hdn". iSplitR; [iPureIntro; exact Hnz | done].
  Qed.

  (* ---- (e) [BufL] ⇒ allocated ---------------------------------------- *)

  (*  [InodeRegion.ireg_read]'s pattern plus [diblk_bytes_inj].  The licence
      carries the block's CLIENT half at bytes it claims decode to [ds];
      [ireg_read] pins those bytes against the region's parked list and
      names the caller's slot in it, and injectivity of the encoding turns
      the two decodings into one.

      THE BLOCK NUMBER IS CARRIED BY THE CONSTRUCTOR, and so is its tie to
      the inum -- [ireg_read]'s [Hb] comes straight out of the licence
      (SIMP-1), so this reading takes no block premise at all. *)
  Lemma iname_buf_alloc (E : coPset) (γi : gname) (γfs : fs_names)
      (inodestart : Z) (nib : nat) (inum : bv 32) (dn : dinode)
      (bno : Z) (ds : list dinode) :
    ↑iregN ⊆ E ->
    (* [ireg_read]'s, inherited (durable-disk 1c-flip step 3) *)
    ↑logN ⊆ E ->
    bv_unsigned inum < 16 * Z.of_nat nib ->
    ireg_inv γi γfs inodestart nib -∗
    dinode_at γi inum dn -∗
    iname γi γfs inodestart inum (BufL bno ds) ={E}=∗
    ⌜bv_unsigned (di_type dn) <> 0⌝ ∗
    dinode_at γi inum dn ∗ iname γi γfs inodestart inum (BufL bno ds).
  Proof.
    iIntros (HE HEl Hin) "#Hinv Hdn Hbuf". rewrite /iname.
    iDestruct "Hbuf" as "(Hhalf & %Hb & %Hwf & %Hnz & Hboot)".
    rewrite /fs_chalf.
    iMod (ireg_read E γi γfs inodestart nib inum dn
            bno (diblk_bytes ds) HE HEl Hin Hb
            with "Hinv Hdn Hhalf") as "(%Hex & Hdn & Hhalf)".
    destruct Hex as (ds' & Hwf' & Hbytes & Hslot).
    assert (Hdseq : ds' = ds)
      by (apply (diblk_bytes_inj ds' ds Hwf' Hwf); symmetry; exact Hbytes).
    subst ds'.
    iModIntro. iSplitR.
    { iPureIntro. rewrite -Hslot. exact Hnz. }
    iFrame "Hdn Hhalf Hboot".
    iPureIntro. split; [exact Hb | split; [exact Hwf | exact Hnz]].
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  THE LICENCE TABLE AT AN IN-TRANSITION BOX                           *)
  (*  (iclaim-ledger.md §2.6, executed as §3.1's RULING A)                 *)
  (* ------------------------------------------------------------------ *)

  (*  WHAT THIS IS.  §2.6 wrote a five-row table -- "at a box the free path
      has frozen, EVERY runtime licence is refutable" -- and increment IIIb
      proved it unimplementable against the count-only pin: four of the five
      rows contradict a frozen box through its LINK COUNT, and the pin did
      not mention one.  RULING A put [di_nlink d = 0 /\ di_type d <> 0] back
      into [InodeRegion.ireg_frz_ok] at both phases, and this lemma is the
      table.

      WHY IT IS NOT AN ACCESSOR, unlike every other reading in this file.
      Its two consumers -- [IcacheInv]'s up-count movers and
      [IcacheEscrow]'s pool peel -- call it with [^iregN] ALREADY OPEN (the
      count coupling's region half is what they came for), and an invariant
      cannot be opened twice.  So the lemma takes the SLOT's own components
      as arguments, in the order [InodeRegion.ireg_slot] hands them out, and
      concludes about the f column that came with them.  The standing
      constraint (§7.1.4) is met a different way: every fact is about the
      record [d] the authority itself is carrying, tied to the caller by
      [Hmd], so nothing here says anything about a record nobody named.

      EVERYTHING IS BORROWED.  The conclusion is PURE, so the proofmode
      shares the arguments rather than consuming them and the caller's slot
      pieces are all still in hand afterwards.

      THE FIVE ROWS.

        [LinkedL]     one counting unit bounds the target's OWN authority
                      below ([InodeRegion.ireg_lnk_tok_nz], the RA's law),
                      hence [1 <= di_nlink d]; the pin says a frozen
                      record's is zero.  This is the row the whole table
                      exists for -- it is what a [dirlookup]-licenced iget
                      presents.
        [HeldL d']    the licence IS a [dinode_at], so ghost-map agreement
                      pins [d' = d], and §2.6's strengthening of the arm
                      carries [di_nlink d' <> 0] into the same collision.
        [ClaimL]      the c column, not the record: [link_claim_agree] reads
                      [c = Some] off the token and [ireg_claim_ok]'s new
                      conjunct (RULING A) says a claimed box's f column is
                      [FrzOff].  It has to go this way round -- a claim box
                      has [di_nlink = 0] too ([fresh_shape]), so the record
                      cannot tell the two generations apart, which is
                      exactly the B1/B2 debt §0 names.
        [BufL bno ds] not the record and not the count but the BOOT
                      one-shot: the licence lends [ireg_boot], and the
                      freeze's own boot-shelter disjunct is then refuted arm
                      by arm ([ity_pending_excl] against a parked pending,
                      [ireg_boot_open_excl] against a runtime seal), leaving
                      its LEFT disjunct.  This is the one row that was
                      already provable under the count-only pin (IIIb's
                      finding), and it is unchanged.
        [RootL]       the root clause is (L1) MADE STRICT, so it delivers
                      [1 <= di_nlink d] outright and the collision is the
                      first row's.                                        *)
  Lemma iname_not_frozen (γi : gname) (γfs : fs_names) (inodestart : Z)
      (inum : bv 32) (l : ilic) (d : dinode) (mm : gmap Z dinode)
      (wl wdu wdt g r : nat) (c : ctyUR)
      (p : option (dfrac_agreeR (leibnizO Z))) (f : frzUR) (n : nat) :
    ireg_link_ok d (wl + wdu + wdt) ->
    ireg_claim_ok c f d ->
    ireg_frz_ok f n d ->
    mm !! bv_unsigned inum = Some d ->
    ghost_map_auth γi 1 mm -∗
    ireg_rcol (bv_unsigned inum) wl wdu wdt g c r p f n d -∗
    ireg_lnk γfs (bv_unsigned inum) d -∗
    (* the slot's shelter conjunct, whole (durable-disk C-5): the c side is
       the claim window's parked share and rides straight back out, so a
       caller hands this row over exactly as the slot gave it. *)
    ireg_shp c f -∗
    iname γi γfs inodestart inum l -∗
    ⌜f = Some (Excl FrzOff)⌝.
  Proof.
    intros Hlok Hclm Hfrz Hmd.
    (* the shared step of rows (a), (c) and (f): a NAMED record is not
       mid-transition *)
    iAssert (⌜bv_unsigned (di_nlink d) <> 0⌝ -∗ ⌜f = Some (Excl FrzOff)⌝)%I
      as "Hnz".
    { iIntros (Hnl). iPureIntro. exact (ireg_frz_ok_nz f n d Hnl Hfrz). }
    iIntros "Ha Hla Hlnk Hshp Hl".
    iDestruct (ireg_shp_split with "Hshp") as "[Hsh _]".
    rewrite /iname.
    destruct l as [| d' | tyc tc qc | bno ds |].
    - (* (a) LinkedL -- the RA's law at the target's own authority *)
      iDestruct (ireg_lnk_tok_nz with "Hlnk Hl") as %Hnl1.
      iApply "Hnz". iPureIntro. exact Hnl1.
    - (* (c) HeldL *)
      iDestruct "Hl" as "(Hd & %Hty' & %Hnl')".
      rewrite /dinode_at.
      iDestruct (ghost_map_lookup with "Ha Hd") as %Hm'.
      assert (Hdd : d' = d) by congruence.
      iApply "Hnz". iPureIntro. rewrite -Hdd. exact Hnl'.
    - (* (d) ClaimL -- the c column, not the record *)
      iDestruct (ireg_rcol_claim_agree with "Hla Hl") as %Hc.
      iPureIntro.
      exact (ireg_claim_ok_off c f d ltac:(rewrite Hc; discriminate) Hclm).
    - (* (e) BufL -- the boot one-shot against the freeze's own shelter *)
      iDestruct "Hl" as "(_ & _ & _ & _ & Hboot)".
      iApply (ireg_fsh_boot_off f with "Hsh Hboot").
    - (* (f) RootL -- the region's own keep-alive token *)
      iDestruct "Hl" as %Hroot.
      iEval (rewrite Hroot) in "Hlnk".
      iDestruct (ireg_lnk_root_alive γfs d with "Hlnk") as %Halive.
      iApply "Hnz". iPureIntro. lia.
  Qed.

  (* ===================================================================== *)
  (*  THE MINT's TABLE (iclaim-ledger.md §5', RULING R)                     *)
  (* ===================================================================== *)

  (*  [iname_not_claimed] AND ITS ALLOCATEDNESS TWIN, FUSED.  §5'.2 asks for
      "[iname_not_claimed] -- the §2.6-pattern table lemma, twin of the landed
      [iname_not_frozen]"; the mint needs TWO facts from the same five rows
      and by the same three bridges, so they are ONE lemma:

        (i)  the box is ALLOCATED -- [di_type <> 0] -- which is what
             [InodeRegion.ireg_ref_ok]'s (R2) owes at every up-count;
        (ii) a NON-[ClaimL] licence's box is UNCLAIMED -- [c = None] -- which
             is (R3), THE PIN: "no plainly-licenced reference exists to a
             claim box".

      THE THREE BRIDGES, and two of them are [iname_not_frozen]'s verbatim.
      (a) a NAMED record has [di_nlink <> 0], which gives (i) by (L3)'s
      contrapositive and (ii) because a claim box is [fresh_shape] and its
      count is ZERO; (b) the ledger's sum bounds that count from below, which
      is rows [LinkedL] and [RootL]; (c) [HeldL] carries the count outright.
      The two rows that do NOT go through the count are the same two as in the
      freeze table: [ClaimL] reads the c column itself (and owes only (i),
      through the claim pin's [fresh_shape]), and [BufL] reads the BOOT
      one-shot against the c column's own shelter clause -- [ireg_boot] versus
      [ireg_open], [ireg_boot_open_excl], exactly as it plays the freeze's.

      WHY [BufL] TAKES THE BLOCK.  Its (i) is the buffer's own decoded type
      fact, and transporting it to the REGION's record needs the two block
      halves to meet -- which is [iname_buf_alloc]'s [ireg_read] step, except
      that this lemma's consumers ([IcacheInv]'s up-count movers) already hold
      [^iregN] open and cannot re-open it.  So the region's half comes IN as
      an argument, and the constructor's [bno] tie comes out of the LICENCE
      itself (SIMP-1).  Everything is borrowed: the conclusion is pure. *)
  (* THE BufL ROW'S BLOCK TRANSPORT, ON ITS OWN (durable-disk 1c-flip
     step 3).  [iname_mint_ok] below used to meet the licence's machinery
     half against the region's parked CACHE half by an auth-free
     agreement; the region now owns the block's EXCLUSIVE byte run, so the
     two maps meet only inside [FsBlocks.fs_bytes_inv].  That is a fupd,
     and [iname_mint_ok]'s conclusion is pure -- so the crossing is split
     off here and [iname_mint_ok] takes its result as a PURE premise, which
     keeps the five-row table an entailment and its one consumer's
     [iDestruct ... as %] shape.  Only the [BufL] row does any work. *)
  Lemma iname_buf_list (E : coPset) (home : gset Z)
      (γi : gname) (γfs : fs_names) (inodestart : Z)
      (inum : bv 32) (l : ilic) (ds : list dinode) :
    ↑logN ⊆ E ->
    diblk_wf ds ->
    fs_bytes_inv (fs_bytes γfs) (fs_cache γfs) home -∗
    fsblock (fs_bytes γfs) (IBLOCK inum inodestart) (diblk_bytes ds) -∗
    iname γi γfs inodestart inum l ={E}=∗
    ⌜forall (bno : Z) (ds0 : list dinode), l = BufL bno ds0 -> ds0 = ds⌝ ∗
    fsblock (fs_bytes γfs) (IBLOCK inum inodestart) (diblk_bytes ds) ∗
    iname γi γfs inodestart inum l.
  Proof.
    iIntros (HE Hwf) "#Hbinv Hfsb Hl".
    destruct l as [| d' | tyc tc qc | bno ds0 |];
      [ iModIntro; iFrame "Hfsb Hl"; iPureIntro; intros ? ? Hc; discriminate
      | iModIntro; iFrame "Hfsb Hl"; iPureIntro; intros ? ? Hc; discriminate
      | iModIntro; iFrame "Hfsb Hl"; iPureIntro; intros ? ? Hc; discriminate
      |
      | iModIntro; iFrame "Hfsb Hl"; iPureIntro; intros ? ? Hc; discriminate ].
    iEval (rewrite /iname) in "Hl".
    iDestruct "Hl" as "(Hhalf & %Hbno & %Hwf0 & %Hnz0 & Hboot)".
    iEval (rewrite Hbno /fs_chalf) in "Hhalf".
    iMod (fs_bytes_agree E (fs_bytes γfs) (fs_cache γfs) home
            (IBLOCK inum inodestart) (diblk_bytes ds) (diblk_bytes ds0)
            HE with "Hbinv Hfsb Hhalf") as "(%Hbytes & Hfsb & Hhalf)".
    assert (Hdseq : ds0 = ds)
      by exact (diblk_bytes_inj ds0 ds Hwf0 Hwf Hbytes).
    iModIntro. iFrame "Hfsb".
    iSplitR.
    { iPureIntro. intros bno' ds1 Heq. injection Heq as _ <-. exact Hdseq. }
    rewrite /iname /fs_chalf.
    iEval (rewrite -Hbno) in "Hhalf".
    iFrame "Hhalf Hboot". iPureIntro.
    split; [exact Hbno | split; [exact Hwf0 | exact Hnz0]].
  Qed.

  Lemma iname_mint_ok (γi : gname) (γfs : fs_names) (inodestart : Z)
      (inum : bv 32) (l : ilic) (ds : list dinode) (mm : gmap Z dinode)
      (wl wdu wdt g r : nat) (c : ctyUR)
      (p : option (dfrac_agreeR (leibnizO Z))) (f : frzUR) (n : nat) :
    diblk_wf ds ->
    ireg_link_ok (ds !!! islot inum) (wl + wdu + wdt) ->
    ireg_claim_ok c f (ds !!! islot inum) ->
    mm !! bv_unsigned inum = Some (ds !!! islot inum) ->
    (* the [BufL] row's block transport, from [iname_buf_list] above *)
    (forall (bno : Z) (ds0 : list dinode), l = BufL bno ds0 -> ds0 = ds) ->
    ghost_map_auth γi 1 mm -∗
    ireg_rcol (bv_unsigned inum) wl wdu wdt g c r p f n (ds !!! islot inum) -∗
    ireg_lnk γfs (bv_unsigned inum) (ds !!! islot inum) -∗
    (⌜c = None⌝ ∨ ireg_open) -∗
    iname γi γfs inodestart inum l -∗
    ⌜bv_unsigned (di_type (ds !!! islot inum)) <> 0
     /\ (is_claim l = false -> c = None)⌝.
  Proof.
    intros Hwf Hlok Hclm Hmd Hbuf.
    (* bridge (a): a named record is neither free nor a claim box *)
    assert (Hnzb : bv_unsigned (di_nlink (ds !!! islot inum)) <> 0 ->
                   bv_unsigned (di_type (ds !!! islot inum)) <> 0 /\ c = None).
    { intros Hnl. split.
      - intros H0. exact (Hnl (proj1 (proj2 Hlok) H0)).
      - destruct c as [x |]; [| reflexivity]. exfalso. apply Hnl.
        exact (fresh_shape_nlink _
                 (ireg_claim_ok_shape (Some x) f (ds !!! islot inum)
                    ltac:(discriminate) Hclm)). }
    iIntros "Ha Hla Hlnk Hsh Hl". rewrite /iname /is_claim.
    destruct l as [| d' | tyc tc qc | bno ds0 |].
    - (* (a) LinkedL -- the RA's law at the target's own authority *)
      iDestruct (ireg_lnk_tok_nz with "Hlnk Hl") as %Hnl1.
      destruct (Hnzb Hnl1) as [H1 H2].
      iPureIntro. split; [exact H1 | intros _; exact H2].
    - (* (c) HeldL -- the licence IS the record *)
      iDestruct "Hl" as "(Hd & %Hty' & %Hnl')".
      rewrite /dinode_at.
      iDestruct (ghost_map_lookup with "Ha Hd") as %Hm'.
      assert (Hdd : d' = ds !!! islot inum) by congruence.
      destruct (Hnzb ltac:(rewrite -Hdd; exact Hnl')) as [H1 H2].
      iPureIntro. split; [exact H1 | intros _; exact H2].
    - (* (d) ClaimL -- the claimant's OWN box; only (i) is owed, and the
         claim pin's [fresh_shape] is exactly it *)
      iDestruct (ireg_rcol_claim_agree with "Hla Hl") as %Hc.
      iPureIntro. split; [| discriminate].
      exact (proj1 (ireg_claim_ok_shape c f (ds !!! islot inum)
                      ltac:(rewrite Hc; discriminate) Hclm)).
    - (* (e) BufL -- the buffer's type fact, transported; the boot one-shot
         against the c column's shelter *)
      iDestruct "Hl" as "(Hhalf & %Hbno & %Hwf0 & %Hnz0 & Hboot)".
      assert (Hdseq : ds0 = ds) by exact (Hbuf bno ds0 eq_refl).
      subst ds0.
      iAssert (⌜c = None⌝)%I as %Hc0.
      { iDestruct "Hsh" as "[%Hn | Hopen]"; [by iPureIntro |].
        iExFalso. iApply (ireg_boot_open_excl with "Hboot Hopen"). }
      iPureIntro. split; [exact Hnz0 | intros _; exact Hc0].
    - (* (f) RootL -- the region's own keep-alive token *)
      iDestruct "Hl" as %Hroot.
      iEval (rewrite Hroot) in "Hlnk".
      iDestruct (ireg_lnk_root_alive γfs (ds !!! islot inum) with "Hlnk")
        as %Halive.
      assert (Hw1 : bv_unsigned (di_nlink (ds !!! islot inum)) <> 0) by lia.
      destruct (Hnzb Hw1) as [H1 H2].
      iPureIntro. split; [exact H1 | intros _; exact H2].
  Qed.

  (* THE TABLE AS AN ACCESSOR, for the consumer that does NOT already have
     the region open: [IcacheEscrow.ipool_shape_to_np]'s AWAIT arm
     (iclaim-ledger.md §3.1, A-refuter).

     WHAT IT REPLACES.  Increment IIIa spelled §1.3's refutation as a bare
     wand [ipool_await_refuter z = ifreeze_post z -* False], and IIIb proved
     that shape unbuildable: opening [ireg_inv] is a fupd, and
     [(|={E}=> False)] does not entail [False], so no amount of region
     reasoning can produce a wand into [False].  The ruling was to change
     the SHAPE of the premise, not its discharge -- so the refutation
     becomes a FUPD, the caller lends its licence, and the region opens
     INSIDE.

     WHAT IT SAYS.  A licence-holder's inum is not mid-transition, so any
     freeze token standing at it is the UNFROZEN one.  The await arm holds
     [ifreeze_post], and [FrzPost <> FrzOff] closes the arm outright.
     Everything is borrowed: the licence and the token both come back. *)
  Lemma iname_freeze_off (E : coPset) (γi : gname) (γfs : fs_names)
      (inodestart : Z) (nib : nat) (inum : bv 32) (l : ilic) (ph : frz) :
    ↑iregN ⊆ E ->
    bv_unsigned inum < 16 * Z.of_nat nib ->
    ireg_inv γi γfs inodestart nib -∗
    iname γi γfs inodestart inum l -∗
    ifreeze ph (bv_unsigned inum) ={E}=∗
    ⌜ph = FrzOff⌝ ∗ iname γi γfs inodestart inum l ∗ ifreeze ph (bv_unsigned inum).
  Proof.
    iIntros (HE Hin) "#Hinv Hl Hfz".
    pose proof (islot_lt inum) as Hsl.
    assert (Hkey : (16 * Z.of_nat (ireg_bi inum) + Z.of_nat (islot inum))%Z
                   = bv_unsigned inum) by (symmetry; apply ireg_key_split).
    iDestruct "Hinv" as "[#Hiinv [#Hrb #Hftopi]]".
    iMod (inv_acc E iregN with "Hiinv") as "[Hbody Hclose]"; [exact HE |].
    iDestruct "Hbody" as (m) "(>Ha & Hblks & >Hreg)".
    pose proof (ireg_bi_lt inum nib Hin) as Hbi.
    iDestruct (ireg_blks_acc_upd γi γfs inodestart m nib (ireg_bi inum) Hbi
                with "Hblks") as "[Hblk Hback]".
    iDestruct "Hblk" as (ds) "(>%Hwf & >%Hcp & >Hfsb & >Hsls)".
    assert (Hlen16 : length ds = 16%nat) by (destruct Hwf as [Hl _]; exact Hl).
    iDestruct (ireg_slots_acc_upd γfs γi (ireg_bi inum) ds (islot inum) Hsl Hlen16
                with "Hsls") as "[Hslot Hslback]".
    iEval (rewrite Hkey) in "Hslot".
    iDestruct "Hslot" as "[(%wl & %wdu & %wdt & %gl & %rl & %cl & %pl & %fz & %cn & Hla & %Hlok & %Hdir & %Hwl0 & %Hpar & #Hdisj & Hcnt & %Hclm & %Hfrz & Hfdisj & Hfrcp & Harm) [Hep Hlnk]]".
    (* the caller's token pins the column; the table says which phase *)
    iDestruct (ireg_rcol_freeze_agree with "Hla Hfz") as %Hfeq.
    pose proof (Hcp (islot inum) Hsl) as Hmd.
    rewrite -ireg_key_split in Hmd.
    iDestruct (iname_not_frozen γi γfs inodestart inum l (ds !!! islot inum) m
                 wl wdu wdt gl rl cl pl fz cn Hlok Hclm Hfrz Hmd
                 with "Ha Hla Hlnk Hfdisj Hl") as %Hfz0.
    assert (Hph : ph = FrzOff).
    { rewrite Hfeq in Hfz0. by simplify_eq. }
    assert (Hins : <[islot inum := ds !!! islot inum]> ds = ds).
    { apply list_insert_id, list_lookup_lookup_total_lt. lia. }
    iMod ("Hclose" with "[Ha Hreg Hfsb Harm Hla Hep Hlnk Hslback Hback Hcnt Hfdisj Hfrcp]")
      as "_".
    { iNext. iExists m. iFrame "Ha Hreg".
      iApply ("Hback" $! m with "[%] [Hfsb Harm Hla Hep Hlnk Hslback Hcnt Hfdisj Hfrcp]");
        [done |].
      iExists ds. iSplitR; [done |]. iSplitR; [done |].
      iSplitL "Hfsb"; [iExact "Hfsb" |].
      iEval (rewrite -Hins).
      iApply ("Hslback" $! (ds !!! islot inum) with "[Harm Hla Hep Hlnk Hcnt Hfdisj Hfrcp]").
      rewrite Hkey.
      iApply (ireg_slot_intro γfs γi (bv_unsigned inum) (ds !!! islot inum)
                wl wdu wdt gl cl rl pl fz cn Hlok Hdir Hwl0 Hpar Hclm Hfrz
                with "Hla Hep Hlnk Hdisj Hcnt Hfdisj Hfrcp Harm"). }
    iModIntro. iFrame "Hl Hfz". iPureIntro. exact Hph.
  Qed.

End IgetLic.
