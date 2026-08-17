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
    [create_fresh_ty] stands.  This increment retires §20.17.5's PARAGRAPH,
    not §20.7's WALL.                                                      *)

From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import auth gmap frac excl.
From iris.algebra.lib Require Import dfrac_agree.
From iris.base_logic.lib Require Import invariants ghost_map.
Require Import SailStdpp.Values.
Require Import RiscvPtsto.
Require Import DiskPtsto.
Require Import FsBlocks.
Require Import LogInv.
Require Import DinodeEnc.
Require Import DirView.
Require Import IcacheRef.
Require Import DirLinks.
Require Import InodeRegion.

Local Open Scope Z_scope.

(* ----------------------------------------------------------------------- *)
(*  THE ENUMERATION                                                         *)
(* ----------------------------------------------------------------------- *)

(*  §20.4's six licences, in §20.4's order, plus R14's transitional seventh.

      [LinkedL]  (a)  a directory record names the inum and PAYS for it: the
                      caller lends its ticket ([ipaid], below), (L1) bounds
                      the count below and (L3) turns that into a nonzero
                      type.  This is the allocatedness witness §20 exists
                      for, and it is the licence every [dirlookup] delivers
                      at a record that is not the home's own.
      [GreyL]    (b)  §20.8's orphaned [".."] -- the one record in xv6 whose
                      target's link count does not account for it.  It
                      concludes NOTHING, by construction (§20.18 ruling 2),
                      and THE STANDING AUDIT IS THAT NO SITE INSTANTIATES
                      IT: [grep -n "GreyL" iris/Proof*.v] must be empty.
                      Kept as a constructor so the enumeration is §20.4's
                      and the box is a grep rather than a paragraph.
      [HeldL]    (c)  the caller already holds the record, exclusively.  A
                      lookup of ["."] is the worked instance: it returns the
                      inum of the directory the caller has locked, whose own
                      [dinode_at] with a nonzero type is a strictly BETTER
                      witness than any fragment.
      [ClaimL]   (d)  the detached fragment of a claim box.  NOTHING MINTS
                      AN [iclaim] TODAY and nothing may: §7.1.5's theorem
                      says any region clause strong enough to found (d) is a
                      clause [ireg_free_au] must re-establish, so (d) and
                      the walled increment F1.5c/F1.5d are ONE increment.
                      The constructor is R11's honesty marker, kept visible
                      in the source and never instantiated.
      [BufL]     (e)  the caller holds the inode BLOCK's client half at
                      bytes that decode to a record with a nonzero type.
                      §7.1.3's improvement on §20.4: the resource is
                      [FsBlocks.fsblock], one level below [bio_locked], and
                      it is STRONGER -- the element sits at ½+½, so a client
                      holding one half means no [ireg_write_au] /
                      [ireg_claim_au] / [ireg_free_au] at ANY inum of that
                      block can fire while it is held.  That is §16.2's
                      serialiser as a resource fact.
      [RootL]    (f)  the inum is the root's.  The landed root clause
                      ([InodeRegion.ireg_root_ok], (L1) MADE STRICT at
                      [ireg_root]) is what makes this a licence rather than
                      an assumption, and this is its first consumer.
      [SpanL]         see the R14 header below.                            *)

(*  THREE CONSTRUCTORS CARRY DATA, AND THAT IS FORCED BY "THE SAME [l]".
    §7.1.1 wrote (a), (c) and (e) with the licence's content hidden behind a
    [∃] -- [∃ d, dinode_at …], [∃ ds, fsblock …].  A post that returns the
    licence "at the same [l]" then returns a DIFFERENT resource: the caller
    lends [dinode_at γi inum dn] and gets back [∃ d, dinode_at γi inum d],
    which no walk can put back into its payload.  The borrow is only a
    borrow if the index pins the content, so the record, the record LIST and
    the payment FLAVOUR are constructor arguments.  The enumeration is still
    closed and still seven constructors, [destruct l] is still exhaustive,
    and the two standing greps are unaffected. *)
Inductive ilic :=
  | LinkedL (fl : option (option Z))
  | GreyL
  | HeldL (d : dinode)
  | ClaimL
  | BufL (bno : Z) (ds : list dinode)
  | RootL
  | SpanL.

(*  ===================================================================== *)
(*  R14: [SpanL] -- THE create_fresh_ty SPAN LICENCE, ONE PERMITTED SITE   *)
(*  ===================================================================== *)
(*
    [SpanL]'s [iname] is [⌜True⌝].  It is a licence that licenses nothing,
    and that is deliberate: it is the ONE place in the tree where an [iget]
    presents no evidence, and naming it is what turns "the axiom's
    delivery-side perimeter" from a paragraph into a grep line.

    THE SITE IS [ProofIalloc.v]'s [iget], AND ONLY THAT ONE.  ialloc's
    [iget] runs in the window §7.1.7 describes: [ialloc] has claimed the
    inum, written [dip->type = ty], logged it and BRELSE'd, so at the [iget]
    it holds nothing revocable at all -- no buffer half (that is why licence
    (e) is not available here, and §7.2's CURRENCY GAP is why no epoch
    repair recovers it), no reference, no fragment.  Licence (d) is what
    the record deserves and licence (d) is foreclosed by §7.1.5's theorem.
    The span is exactly the gap [create_fresh_ty] axiomatizes.

    THE STANDING AUDIT: [grep -n "SpanL" iris/Proof*.v] must name EXACTLY
    [ProofIalloc.v]'s iget and nothing else.  A second site would be a
    silent widening of the axiom's perimeter, which is the thing this
    constructor exists to make impossible to do quietly.

    IT DELETES.  [SpanL] goes away when F1.5c mints an [iclaim] (the site
    becomes [ClaimL], no signature moves -- that is why (d) is kept) or when
    [create_fresh_ty] retires.  It is a transitional constructor and it is
    the only permitted [⌜True⌝] in this enumeration.                       *)

Section IgetLic.
  Context `{!riscvGS Σ, !diskGhostG Σ, !fsLogG Σ, !iregG Σ, !icacheG Σ,
            !logG Σ}.
  Context `{ICFG : icfg}.

  (* ------------------------------------------------------------------ *)
  (*  LICENCE (a)'s CARRIER: ONE UNIT OF PAYMENT, AT ANY FLAVOUR          *)
  (* ------------------------------------------------------------------ *)

  (*  §7.1.1 spells licence (a) as [ilink z], and that was right when it was
      written: [DirLinks.dir_link_at]'s ticket was the plain unit.  V5' split
      the payment unit by FLAVOUR -- a record's ticket is
      [DirLinks.dlc_tick self k (F k) z], which is [ilink z] at a plain
      record, [ilinkd z] at the [".."] slot of a directory, and [ilinkdp z
      self] at a NAME record whose target is a directory.  Those are three
      fragments in three components of one authority and there is no
      weakening between them ([IcacheRef.ilinkd]'s header says why, and it
      is deliberate).

      So licence (a) is INDEXED BY THE FLAVOUR, at the tree's own index type
      [option (option Z)] -- and nothing is lost: (L1) bounds the ledger's
      SUM [wl + wdu + wdt] below [di_nlink], so any ONE unit is the
      allocatedness witness, which is what [link_paid_ge] below says in one
      line.  Spelling licence (a) as the plain [ilink] instead would have
      made it unsuppliable at the commonest [iget] in the kernel -- namex's
      walk into a SUBDIRECTORY, whose record's ticket is tagged.

      NOTE THE ONE DIFFERENCE FROM [IcacheRef.ilink_fl]: at the tagged
      flavour this is the PAYMENT half alone ([ilinkdp]), not the pair.
      That is deliberate and it is what the payload holds -- the [iparent]
      half is the CHILD's, and it lives in the child's own [dir_par_tie]
      (DirLinks' header, V5' increment P). *)
  Definition ipaid (fl : option (option Z)) (z : Z) : iProp Σ :=
    match fl with
    | None           => ilink z
    | Some None      => ilinkd z
    | Some (Some pv) => ilinkdp z pv
    end%I.

  Global Instance ipaid_timeless fl z : Timeless (ipaid fl z).
  Proof. destruct fl as [[pv |] |]; rewrite /ipaid; apply _. Qed.

  (* the flavour index of the ticket the payload files at record [k] of the
     directory [self] -- [DirLinks.dlc_tick]'s own case analysis, read as an
     index so that the licence a walk lends and the ticket it must put back
     are the SAME PROPOSITION and not merely equi-derivable. *)
  Definition ipaid_fl (self : Z) (k : nat) (b : bool) : option (option Z) :=
    if b then (if decide (2 <= k)%nat then Some (Some self) else Some None)
         else None.

  Lemma ipaid_tick (self : Z) (k : nat) (b : bool) (z : Z) :
    dlc_tick self k b z = ipaid (ipaid_fl self k b) z.
  Proof.
    rewrite /dlc_tick /ipaid /ipaid_fl.
    destruct b; [destruct (decide (2 <= k)%nat) |]; reflexivity.
  Qed.

  (* the two directions as WANDS -- an [=]-equation between [iProp]s does not
     reliably [rewrite] inside the proofmode (durable-notes), and every use
     of this pair is at a call site *)
  Lemma ipaid_of_tick (self : Z) (k : nat) (b : bool) (z : Z) :
    dlc_tick self k b z -∗ ipaid (ipaid_fl self k b) z.
  Proof. rewrite ipaid_tick. iIntros "H". iExact "H". Qed.

  Lemma tick_of_ipaid (self : Z) (k : nat) (b : bool) (z : Z) :
    ipaid (ipaid_fl self k b) z -∗ dlc_tick self k b z.
  Proof. rewrite ipaid_tick. iIntros "H". iExact "H". Qed.

  (* ------------------------------------------------------------------ *)
  (*  THE BORROW AT A MATCHED RECORD -- where licence (a) comes from      *)
  (* ------------------------------------------------------------------ *)

  (*  [ProofDirlookup]'s found arm holds the home directory's whole ticket
      list and needs the ONE ticket at the record the scan stopped on.  This
      is [DirLinks.dir_links_dotdot_out]'s shape at an arbitrary index: open
      the payload under a LIVE home (which is what refutes the grey disjunct
      where it stands -- [dir_link_at]'s grey carries [di_nlink dn = 0]),
      take the ticket out with a [big_sepL_lookup_acc], and hand back a wand
      that re-seals at the SAME flavour.  The parent tie is untouched.

      HOME: here rather than in [DirLinks.v], which the increment must leave
      byte-identical, and which in any case may not mention [ipaid].

      The [dir_inum <> self] premise is the self-record exclusion: at the
      [\".\"] record there IS no ticket ([dir_link_at]'s guard is false, xv6
      deliberately does not count it) and the caller uses licence (c)
      instead.  That case split is not an accident of the proof -- it is
      §20.4's (a)-vs-(c) boundary, drawn where the kernel draws it.        *)
  Lemma dir_links_borrow (self : Z) (dn : dinode)
      (data : nat -> list (bv 8)) (k : nat) :
    bv_unsigned (di_type dn) = T_DIR_z ->
    bv_unsigned (di_nlink dn) <> 0 ->
    (k < dir_nrec (bv_unsigned (di_size dn)))%nat ->
    dir_live data k ->
    bv_unsigned (dir_inum data k) <> self ->
    dir_links self dn data -∗
      ∃ fl : option (option Z),
        ipaid fl (bv_unsigned (dir_inum data k))
        ∗ (ipaid fl (bv_unsigned (dir_inum data k)) -∗ dir_links self dn data).
  Proof.
    intros Hty Hnl Hk Hlive Hself.
    rewrite /dir_links decide_True; [| exact Hty].
    iIntros "H". iDestruct "H" as (F) "(%Hbnd & %Hlow & Htie & H)".
    iDestruct (big_sepL_lookup_acc _
                 (seq 0 (dir_nrec (bv_unsigned (di_size dn)))) k k
                 with "H") as "[H1 Hback]".
    { apply lookup_seq. lia. }
    iExists (ipaid_fl self k (F k)).
    iAssert (dlc_tick self k (F k) (bv_unsigned (dir_inum data k)))
      with "[H1]" as "Ht".
    { rewrite /dir_link_at_f.
      rewrite (proj2 (dir_liveb_true data k) Hlive).
      rewrite (bool_decide_eq_false_2
                 (bv_unsigned (dir_inum data k) = self) Hself).
      cbn [negb andb].
      iDestruct "H1" as "[Ht | [_ %Hz]]";
        [iExact "Ht" | exfalso; exact (Hnl Hz)]. }
    iSplitL "Ht".
    { iApply (ipaid_of_tick self k (F k) (bv_unsigned (dir_inum data k))
                with "Ht"). }
    iIntros "Hp". iExists F.
    iSplitR; [iPureIntro; exact Hbnd |].
    iSplitR; [iPureIntro; exact Hlow |].
    iSplitL "Htie"; [iExact "Htie" |].
    iApply "Hback". rewrite /dir_link_at_f.
    rewrite (proj2 (dir_liveb_true data k) Hlive).
    rewrite (bool_decide_eq_false_2
               (bv_unsigned (dir_inum data k) = self) Hself).
    cbn [negb andb]. iLeft.
    iApply (tick_of_ipaid self k (F k) (bv_unsigned (dir_inum data k))
              with "Hp").
  Qed.

  (* ...and (L1) reads off it: one unit at ANY flavour bounds the sum *)
  Lemma link_paid_ge (z : Z) (wl wdu wdt g : nat) (c : option (excl unit))
      (r : nat) (p : option (dfrac_agreeR (leibnizO Z)))
      (fl : option (option Z)) :
    link_auth z wl wdu wdt g c r p -∗ ipaid fl z -∗
    ⌜(1 <= wl + wdu + wdt)%nat⌝.
  Proof.
    iIntros "Ha Hb". rewrite /ipaid. destruct fl as [[pv |] |].
    - iDestruct (link_wdt_ge with "Ha Hb") as %[Hw _]. iPureIntro. lia.
    - iDestruct (link_wsum_ge _ _ _ _ _ _ _ _ (Some None) with "Ha Hb") as %Hw.
      iPureIntro. lia.
    - iDestruct (link_w_ge with "Ha Hb") as %Hw. iPureIntro. lia.
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  THE LICENCE ITSELF                                                  *)
  (* ------------------------------------------------------------------ *)

  Definition iname (γi : gname) (γfs : fs_names) (inum : bv 32) (l : ilic)
    : iProp Σ :=
    match l with
    | LinkedL fl => ipaid fl (bv_unsigned inum)                      (* a *)
    | GreyL   => igrey (bv_unsigned inum)                            (* b *)
    | HeldL d => (dinode_at γi inum d ∗
                  ⌜bv_unsigned (di_type d) <> 0⌝)                    (* c *)
    | ClaimL  => iclaim (bv_unsigned inum)                           (* d *)
    | BufL bno ds =>
                 (fsblock γfs bno (diblk_bytes ds) ∗                  (* e *)
                  ⌜diblk_wf ds⌝ ∗
                  ⌜bv_unsigned (di_type (ds !!! islot inum)) <> 0⌝)
    | RootL   => ⌜bv_unsigned inum = ireg_root⌝                      (* f *)
    | SpanL   => ⌜True⌝                                       (* R14, above *)
    end%I.

  (* Timeless throughout -- which is what lets [SpecIget]'s premise sit
     beside the itable spinlock's resource without a later. *)
  Global Instance iname_timeless γi γfs inum l : Timeless (iname γi γfs inum l).
  Proof. destruct l; rewrite /iname; apply _. Qed.

  (* ------------------------------------------------------------------ *)
  (*  THE READINGS, AND THE SHAPE THEY MUST TAKE                          *)
  (* ------------------------------------------------------------------ *)

  (*  STANDING CONSTRAINT (§7.1.4, the [SpecCreateFreshTy.v:34-45] test).
      Every reading below is an ACCESSOR OVER [ireg_inv], in
      [IregLinkNz.ireg_link_nz]'s shape: it opens the region, reads the
      ledger's own clauses at the slot the caller's [dinode_at] names, and
      hands everything back.  A free-standing entailment

          iname γi γfs inum l -∗ ⌜bv_unsigned (di_type dn) <> 0⌝

      with [dn] FREE is the inconsistent form the axiom's own header warns
      about, verbatim -- it says something about a record nobody has tied to
      the licence.  Write it in the accessor shape or not at all.

      NONE OF THESE HAS A CONSUMER IN THIS INCREMENT.  They are the payoff
      the enumeration exists to make available, and stating them now is what
      proves the constructors are not vacuous.  [ClaimL] has no reading and
      may not get one before F1.5c ((L5) is what it would need); [GreyL] has
      none by construction.                                                *)

  (* ---- (a) [LinkedL] ⇒ allocated ------------------------------------- *)

  (*  [ilink z] ⇒ [1 <= wl] ([IcacheRef.link_w_ge]) ⇒ (L1) [1 <= nlink] ⇒
      (L3)'s contrapositive [di_type <> 0].  Everything is borrowed and
      returned, exactly as [ireg_link_nz] borrows it; the opening is
      mask-preserving.  The (L3) step is why this is not simply
      [ireg_link_nz] plus a corollary: (L3) is a clause of [ireg_slot] and
      can only be read INSIDE the opening. *)
  Lemma iname_linked_alloc (E : coPset) (γi : gname) (γfs : fs_names)
      (inodestart : Z) (nib : nat) (inum : bv 32) (dn : dinode)
      (fl : option (option Z)) :
    ↑iregN ⊆ E ->
    bv_unsigned inum < 16 * Z.of_nat nib ->
    ireg_inv γi γfs inodestart nib -∗
    dinode_at γi inum dn -∗
    iname γi γfs inum (LinkedL fl) ={E}=∗
    ⌜bv_unsigned (di_type dn) <> 0⌝ ∗
    dinode_at γi inum dn ∗ iname γi γfs inum (LinkedL fl).
  Proof.
    iIntros (HE Hin) "#Hinv Hdn Hfrag". rewrite /iname.
    pose proof (islot_lt inum) as Hsl.
    assert (Hkey : (16 * Z.of_nat (ireg_bi inum) + Z.of_nat (islot inum))%Z
                   = bv_unsigned inum) by (symmetry; apply ireg_key_split).
    iMod (inv_acc E iregN with "Hinv") as "[Hbody Hclose]"; [exact HE |].
    iDestruct "Hbody" as (m) "(>Ha & Hblks & >Hreg)".
    pose proof (ireg_bi_lt inum nib Hin) as Hbi.
    iDestruct (ireg_blks_acc_upd γi γfs inodestart m nib (ireg_bi inum) Hbi
                with "Hblks") as "[Hblk Hback]".
    iDestruct "Hblk" as (ds) "(>%Hwf & >%Hcp & >Hfsb & >Hsls)".
    assert (Hlen16 : length ds = 16%nat) by (destruct Hwf as [Hl _]; exact Hl).
    iDestruct (ireg_slots_acc_upd γi (ireg_bi inum) ds (islot inum) Hsl Hlen16
                with "Hsls") as "[Hslot Hslback]".
    iEval (rewrite Hkey) in "Hslot".
    iDestruct "Hslot" as "[(%wl & %wdu & %wdt & %gl & %rl & %cl & %pl & Hla & %Hlok & %Hrt & %Hdir & %Hwl0 & %Hpar & #Hdisj) [Hep Harm]]".
    iDestruct (link_paid_ge with "Hla Hfrag") as %Hw1.
    rewrite /dinode_at.
    iDestruct (ghost_map_lookup with "Ha Hdn") as %Hm.
    assert (Hdeq : ds !!! islot inum = dn).
    { specialize (Hcp (islot inum) Hsl).
      rewrite -ireg_key_split in Hcp. congruence. }
    (* (L1) then (L3), both read at the caller's own record *)
    assert (Hnz : bv_unsigned (di_type dn) <> 0).
    { rewrite -Hdeq. destruct Hlok as [Hle [Hl3 _]]. intro Hty.
      specialize (Hl3 Hty).
      assert (Hz0 : Z.to_nat (bv_unsigned (di_nlink (ds !!! islot inum)))
                    = 0%nat) by (rewrite Hl3; reflexivity).
      rewrite Hz0 in Hle. lia. }
    assert (Hins : <[islot inum := ds !!! islot inum]> ds = ds).
    { apply list_insert_id, list_lookup_lookup_total_lt. lia. }
    iMod ("Hclose" with "[Ha Hreg Hfsb Harm Hla Hep Hslback Hback]") as "_".
    { iNext. iExists m. iFrame "Ha Hreg".
      iApply ("Hback" $! m with "[%] [Hfsb Harm Hla Hep Hslback]"); [done |].
      iExists ds. iSplitR; [done |]. iSplitR; [done |].
      iSplitL "Hfsb"; [iExact "Hfsb" |].
      iEval (rewrite -Hins).
      iApply ("Hslback" $! (ds !!! islot inum) with "[Harm Hla Hep]").
      rewrite Hkey.
      iApply (ireg_slot_intro γi (bv_unsigned inum) (ds !!! islot inum)
                wl wdu wdt gl cl rl pl Hlok Hrt Hdir Hwl0 Hpar
                with "Hla Hep Hdisj"). iExact "Harm". }
    iModIntro. iFrame "Hdn Hfrag". iPureIntro. exact Hnz.
  Qed.

  (* ---- (c) [HeldL] ⇒ allocated, definitional ------------------------- *)

  (*  THE ONE READING THAT MAY NOT TAKE A CALLER'S [dinode_at], AND THE
      REASON IS THE STANDING CONSTRAINT ITSELF.  [dinode_at] is a
      FULL-fraction ghost_map element ([InodeRegion.dinode_at_excl]), so a
      lemma of the accessor family's shape --

          ireg_inv -∗ dinode_at γi inum dn -∗ iname γi γfs inum HeldL
            ={E}=∗ ⌜bv_unsigned (di_type dn) <> 0⌝ ∗ …

      -- has an UNSATISFIABLE premise set: the licence carries a second
      element at the same key, so the two fragments prove [False] and the
      lemma says nothing about anything.  That is precisely the
      twice-instantiate failure of §4.1, one tier up, and writing it would
      have been green.  The honest statement is the unpack: the licence IS
      the record, so it hands the record out and takes it back. *)
  Lemma iname_held_alloc (γi : gname) (γfs : fs_names) (inum : bv 32)
      (d : dinode) :
    iname γi γfs inum (HeldL d) -∗
    ⌜bv_unsigned (di_type d) <> 0⌝ ∗ dinode_at γi inum d.
  Proof. rewrite /iname. iIntros "[Hd %Hnz]". by iFrame "Hd". Qed.

  (* ...and back in, which is all the round trip costs at the ["."] site *)
  Lemma iname_held_intro (γi : gname) (γfs : fs_names) (inum : bv 32)
      (d : dinode) :
    bv_unsigned (di_type d) <> 0 ->
    dinode_at γi inum d -∗ iname γi γfs inum (HeldL d).
  Proof. intros Hnz. rewrite /iname. iIntros "Hd". by iFrame "Hd". Qed.

  (* ---- (f) [RootL] ⇒ allocated --------------------------------------- *)

  (*  THE ROOT CLAUSE'S FIRST CONSUMER.  [ireg_root_ok] is (L1) MADE STRICT
      at [ireg_root]; its chartered projection [ireg_root_ok_alive] gives
      [1 <= di_nlink] at the root outright, and (L3)'s contrapositive turns
      that into the nonzero type.  Note the shape is the accessor's, not a
      free-standing entailment: [RootL]'s own proposition is PURE, so
      without the opening it would conclude something about a [dn] nothing
      had tied to the root's slot. *)
  Lemma iname_root_alloc (E : coPset) (γi : gname) (γfs : fs_names)
      (inodestart : Z) (nib : nat) (inum : bv 32) (dn : dinode) :
    ↑iregN ⊆ E ->
    bv_unsigned inum < 16 * Z.of_nat nib ->
    ireg_inv γi γfs inodestart nib -∗
    dinode_at γi inum dn -∗
    iname γi γfs inum RootL ={E}=∗
    ⌜bv_unsigned (di_type dn) <> 0⌝ ∗
    dinode_at γi inum dn ∗ iname γi γfs inum RootL.
  Proof.
    iIntros (HE Hin) "#Hinv Hdn %Hroot". rewrite /iname.
    pose proof (islot_lt inum) as Hsl.
    assert (Hkey : (16 * Z.of_nat (ireg_bi inum) + Z.of_nat (islot inum))%Z
                   = bv_unsigned inum) by (symmetry; apply ireg_key_split).
    iMod (inv_acc E iregN with "Hinv") as "[Hbody Hclose]"; [exact HE |].
    iDestruct "Hbody" as (m) "(>Ha & Hblks & >Hreg)".
    pose proof (ireg_bi_lt inum nib Hin) as Hbi.
    iDestruct (ireg_blks_acc_upd γi γfs inodestart m nib (ireg_bi inum) Hbi
                with "Hblks") as "[Hblk Hback]".
    iDestruct "Hblk" as (ds) "(>%Hwf & >%Hcp & >Hfsb & >Hsls)".
    assert (Hlen16 : length ds = 16%nat) by (destruct Hwf as [Hl _]; exact Hl).
    iDestruct (ireg_slots_acc_upd γi (ireg_bi inum) ds (islot inum) Hsl Hlen16
                with "Hsls") as "[Hslot Hslback]".
    iEval (rewrite Hkey) in "Hslot".
    iDestruct "Hslot" as "[(%wl & %wdu & %wdt & %gl & %rl & %cl & %pl & Hla & %Hlok & %Hrt & %Hdir & %Hwl0 & %Hpar & #Hdisj) [Hep Harm]]".
    rewrite /dinode_at.
    iDestruct (ghost_map_lookup with "Ha Hdn") as %Hm.
    assert (Hdeq : ds !!! islot inum = dn).
    { specialize (Hcp (islot inum) Hsl).
      rewrite -ireg_key_split in Hcp. congruence. }
    assert (Hnz : bv_unsigned (di_type dn) <> 0).
    { rewrite -Hdeq.
      pose proof (ireg_root_ok_alive (bv_unsigned inum) (ds !!! islot inum)
                    (wl + wdu + wdt)%nat Hrt Hroot) as Halive.
      destruct Hlok as [_ [Hl3 _]]. intro Hty.
      rewrite (Hl3 Hty) in Halive. lia. }
    assert (Hins : <[islot inum := ds !!! islot inum]> ds = ds).
    { apply list_insert_id, list_lookup_lookup_total_lt. lia. }
    iMod ("Hclose" with "[Ha Hreg Hfsb Harm Hla Hep Hslback Hback]") as "_".
    { iNext. iExists m. iFrame "Ha Hreg".
      iApply ("Hback" $! m with "[%] [Hfsb Harm Hla Hep Hslback]"); [done |].
      iExists ds. iSplitR; [done |]. iSplitR; [done |].
      iSplitL "Hfsb"; [iExact "Hfsb" |].
      iEval (rewrite -Hins).
      iApply ("Hslback" $! (ds !!! islot inum) with "[Harm Hla Hep]").
      rewrite Hkey.
      iApply (ireg_slot_intro γi (bv_unsigned inum) (ds !!! islot inum)
                wl wdu wdt gl cl rl pl Hlok Hrt Hdir Hwl0 Hpar
                with "Hla Hep Hdisj"). iExact "Harm". }
    iModIntro. iFrame "Hdn". iSplitR; [iPureIntro; exact Hnz | done].
  Qed.

  (* ---- (e) [BufL] ⇒ allocated ---------------------------------------- *)

  (*  [InodeRegion.ireg_read]'s pattern plus [diblk_bytes_inj].  The licence
      carries the block's CLIENT half at bytes it claims decode to [ds];
      [ireg_read] pins those bytes against the region's parked list and
      names the caller's slot in it, and injectivity of the encoding turns
      the two decodings into one.

      THE BLOCK NUMBER IS CARRIED BY THE CONSTRUCTOR, and the tie to the
      inum is this reading's own premise -- [ireg_read]'s [Hb], verbatim.
      Spelling it as [iblk_of] instead would pin the licence to the
      region's AMBIENT start [icfg_ist] (a receipt key, §G.17) while every
      holder of a buffer half has it at the THREADED [inodestart]; the two
      are equal at every real caller and the equation is exactly what this
      lemma should be asking for rather than assuming. *)
  Lemma iname_buf_alloc (E : coPset) (γi : gname) (γfs : fs_names)
      (inodestart : Z) (nib : nat) (inum : bv 32) (dn : dinode)
      (bno : Z) (ds : list dinode) :
    ↑iregN ⊆ E ->
    bv_unsigned inum < 16 * Z.of_nat nib ->
    bno = IBLOCK inum inodestart ->
    ireg_inv γi γfs inodestart nib -∗
    dinode_at γi inum dn -∗
    iname γi γfs inum (BufL bno ds) ={E}=∗
    ⌜bv_unsigned (di_type dn) <> 0⌝ ∗
    dinode_at γi inum dn ∗ iname γi γfs inum (BufL bno ds).
  Proof.
    iIntros (HE Hin Hb) "#Hinv Hdn Hbuf". rewrite /iname.
    iDestruct "Hbuf" as "(Hhalf & %Hwf & %Hnz)".
    rewrite /fsblock.
    iMod (ireg_read E γi γfs inodestart nib inum dn
            bno (diblk_bytes ds) HE Hin Hb
            with "Hinv Hdn Hhalf") as "(%Hex & Hdn & Hhalf)".
    destruct Hex as (ds' & Hwf' & Hbytes & Hslot).
    assert (Hdseq : ds' = ds)
      by (apply (diblk_bytes_inj ds' ds Hwf' Hwf); symmetry; exact Hbytes).
    subst ds'.
    iModIntro. iSplitR.
    { iPureIntro. rewrite -Hslot. exact Hnz. }
    iFrame "Hdn Hhalf".
    iPureIntro. split; [exact Hwf | exact Hnz].
  Qed.

End IgetLic.
