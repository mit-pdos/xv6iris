(* ======================================================================= *)
(*  DirLinks.v -- THE RESOURCE TWIN OF [DirView.dir_ok]                     *)
(*  design: claude-notes/design/fs-icache.md §20.3, stage B                 *)
(* ======================================================================= *)

(*  WHY THIS FILE EXISTS, AND WHY IT IS NOT IN [DirView.v] (fs-sysfile S5h).

    §20.3 charters [dir_links] as "five short lemmas mirroring the pure
    ones", which reads as a DirView addition.  It is not one: [dir_links] is
    an [iProp] over [IcacheRef.icfg_link], and [DirView.v] is a PURE record
    view that requires neither [IcacheRef] nor the proofmode.  Three homes
    were on the table and this is the one that survives:

      * DirView itself.  Nothing forbids it importing [IcacheRef] (there is
        no cycle -- [IcacheRef] requires no fs file), but DirView would stop
        being a pure record view, and every consumer of the pure vocabulary
        -- [SpecDirlookup], [ProofNamex], [ProofCreateParts] -- would start
        pulling the icache's algebra in behind it.  §S5g's sizing note.
      * [IcacheEscrow.v], which already imports both.  It splits the twins
        from the pure lemmas they mirror by ~400 lines of unrelated escrow
        machinery, and it puts DirView-shaped reasoning inside the file that
        is supposed to be about ARMS.
      * HERE: a thin file above both, requiring exactly [DirView] (the pure
        record vocabulary) and [IcacheRef] (the ledger's fragments), and
        required by [IcacheEscrow] alongside [DirView].

    THE RULE THIS INSTANTIATES: the pure vocabulary stays where the pure
    consumers are; the RESOURCE twin quantifies over it from one level up.
    Nothing in [DirView.v] moved, and [dir_ok]'s text is untouched -- the
    twin RIDES BESIDE it in the two escrow payloads, it does not replace it.

    ---- THE COUNT CLAUSE (V2) --------------------------------------------

    [dir_links] carries one more thing since the count-fact carrier:
    a FLAVOUR MAP [F : nat -> bool], existentially quantified, saying of
    each record whether its ticket is [IcacheRef.ilinkd] (the target is a
    directory) or plain [ilink] -- together with [DirView.dlc_bound F],
    which bounds the home's OWN link count by one plus the number of live,
    non-dot, d-flavoured records.  That is the fact S7-unlink's T_DIR
    re-park could not get anywhere else (fs-sysfile.md FINDING 3): at an
    empty directory the count is zero and the clause reads [nlink <= 1].

    THE FLAVOUR AND THE BOUND ARE ONE PACKAGE, and neither works alone.
    A bound over a free-floating [∃ F] would be unprovable at the zeroing
    (nothing would refute [F k0 = true] and the count could fall under the
    home's), and a flavour map with no bound would say nothing anyone
    wants.  Read the two writers together: [dir_links_dirlink] deposits a
    PLAIN ticket and cannot raise [nlink]; [dir_links_dirlink_d] deposits a
    d-flavoured one and raises it by exactly one; [dir_links_unlink] hands
    the removed record's ticket back AT ITS OWN FLAVOUR and charges the
    caller for the count it takes away.
*)

From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.algebra Require Import auth gmap frac numbers excl.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap invariants own ghost_var.
Require Import SailStdpp.Values SailStdpp.Operators_mwords SailStdpp.MachineWord.
Require Import RiscvExtras.            (* [add_vec_unsigned], for the [++] *)
Require Import DinodeEnc.
Require Import DirentEnc.
Require Import InodeDefs.
Require Import DirView.
Require Import IcacheRef.

Local Open Scope Z_scope.

(* ---------------------------------------------------------------------- *)
(*  THE ROOT INUM, AT THIS FILE'S KEY TYPE (V5' increment P)               *)
(* ---------------------------------------------------------------------- *)

(*  The parent tie below is owed by every LIVE directory EXCEPT the root:
    root's [".."] is a self-record, root has no create-episode, and nothing
    ever mints a parent register for it.  So the clause's guard names the
    root inum, and this file needs a spelling for it.

    IT IS RESTATED RATHER THAN IMPORTED, exactly as [InodeRegion.ireg_root]
    is and for the same reason its own comment gives: a file with hundreds
    of dependents does not acquire the in-core inode geometry for one
    constant.  DirLinks sits BELOW [InodeRegion] and cannot import it at
    all, and below [InodeInv], where [ROOTINO] lives.  The bridges live
    where two of the three spellings are in scope --
    [IregLinkNz.ireg_root_ROOTINO] ([ROOTINO] vs [ireg_root]) and
    [IregLinkNz.dl_root_ireg_root] ([dl_root] vs [ireg_root]) -- and both
    are one [vm_compute]. *)
Definition dl_root : Z := 1.

Section DirLinks.
  Context `{!icacheG Σ} `{ICFG : icfg}.

  (* ------------------------------------------------------------------ *)
  (*  THE PER-RECORD FRAGMENT                                            *)
  (* ------------------------------------------------------------------ *)

  (* ONE DIRECTORY RECORD'S TICKET.  A live record naming [z] carries one
     ledger fragment for [z], in one of TWO colours:

       [ilink z]  -- [z]'s own [di_nlink] pays for this record, so (L1)
                     forces [di_nlink z >= 1] and (L3) then forces a nonzero
                     TYPE.  This is the ALLOCATEDNESS witness §20 exists for.
       [igrey z]  -- nothing pays for it.  §20.8's orphaned [".."], the one
                     record in xv6 whose target's link count does not account
                     for it.  It carries no allocatedness, which is honest:
                     on that trace the target genuinely is not allocated.

     THE SELF-RECORD EXEMPTION IS FORCED, NOT CHOSEN (§20.3).  mkdir writes
     [dirlink(ip, ".", ip->inum)] and xv6 deliberately does NOT bump
     [ip->nlink] for it -- the source comment is "No ip->nlink++ for '.':
     avoid cyclic ref count".  A self-record therefore has no [nlink] to pay
     for it and (L1) would be violated the instant the dot went in.  It
     costs the consumer nothing: a lookup of ["."] returns the inum of the
     directory the caller is already holding, and that payload's own
     [dinode_at] with [inode_ok]'s nonzero type is a strictly BETTER
     allocatedness witness than any fragment -- §20.4's licence (c).

     A FREE record (inum 0) carries nothing: [dir_liveb] is exactly the
     predicate [dirlookup]'s scan skips on. *)
  Definition dir_link_at (self : Z) (dn : dinode)
      (data : nat -> list (bv 8)) (k : nat)
    : iProp Σ :=
    (if dir_liveb data k
        && negb (bool_decide (bv_unsigned (dir_inum data k) = self))
     then (ilink (bv_unsigned (dir_inum data k))
           ∨ (igrey (bv_unsigned (dir_inum data k))
              ∗ ⌜bv_unsigned (di_nlink dn) = 0⌝))
     else emp)%I.

  (* THE GREY DISJUNCT CARRIES ITS OWN HOME CONDITION (§20.17.7, option
     (iii)).  Grey is §20.8's orphaned [".."], and the ONLY way a record can
     be grey is that its HOME's link count has already reached zero -- that
     is §20.17.4's theorem, at exactly the placement §20.17.4(a) forces: a
     payload conjunct, obligated at the park, where [nlink] is already 0.
     Carrying it here rather than at the caller is what makes "a fragment
     consumed under a LIVE home is [ilink]" a lemma ([dir_link_at_live]
     below) instead of a paragraph.

     [dn] IS A PARAMETER ITS ONLY CALLER ALREADY HAS.  [dir_links] takes
     [dn] for the type test and for [dir_nrec (di_size dn)], so this new
     argument costs no arity anywhere above -- §17.6.3's move, one level
     down.  Both disjuncts stay timeless, so [ic_loaded_timeless] /
     [ipool_alloc_timeless] survive verbatim. *)
  Global Instance dir_link_at_timeless self dn data k :
    Timeless (dir_link_at self dn data k).
  Proof.
    rewrite /dir_link_at.
    destruct (dir_liveb data k
              && negb (bool_decide (bv_unsigned (dir_inum data k) = self)));
      apply _.
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  ...AND ITS FLAVOURED FORM (V2's count clause; V1's [ilinkd])        *)
  (* ------------------------------------------------------------------ *)

  (* THE SAME TICKET AT A CHOSEN FLAVOUR.  [DirView.dlc_bound] bounds a
     directory's [nlink] ABOVE by the number of its records whose target is
     KNOWN to be a directory, and V1's [IcacheRef.ilinkd] is what knows it:
     one unit of payment, filed in the ledger component that carries (T1).
     So the payload's big-op is indexed by a FLAVOUR MAP [F : nat -> bool]
     -- record [k]'s ticket is [ilinkd] when [F k] and [ilink] otherwise --
     and the clause counts exactly the records where [F] is set.

     [dlc_fl] is spelled at the contracts' own index type rather than at
     [bool] because that is what [SpecIupdate.wp_iupdate_link] / [_unlink]
     take: a walk that extracts a ticket out of this big-op feeds it
     STRAIGHT to the spending contract, with no conversion (V3's shape). *)
  (* WIDENED BY V5' along with [IcacheRef.ilink_fl]: the payload's own
     tickets are plain or UNTAGGED-d ([Some None]); the TAGGED form
     ([Some (Some pv)]) enters the payload only through the successor
     increment's index-aware ticket split (V5' increment P). *)
  Definition dlc_fl (b : bool) : option (option Z) :=
    if b then Some None else None.

  (* ------------------------------------------------------------------ *)
  (*  ...AND THE TICKET ITSELF, WHICH IS INDEX-AWARE (V5' increment P)    *)
  (* ------------------------------------------------------------------ *)

  (*  A d-flavoured record names a DIRECTORY, and there are exactly two
      kinds of such record in xv6.  They pay for different things, so they
      are different ledger units:

        * INDEX 1 is the [".."] entry.  What it accounts for is the
          PARENT's link count -- the parent's own record of this directory
          is a different record, in a different directory -- so its unit is
          the UNTAGGED d-unit [IcacheRef.ilinkd], which carries a [wdu] and
          nothing else.
        * INDEX >= 2 is a NAME record.  The only way a record naming a
          directory ever enters a directory in xv6 is create's mkdir:
          [sys_link] refuses [T_DIR] outright and there is no rename.  So
          every such record was minted by the mkdir whose PARENT is this
          very directory, and its unit is the TAGGED parent-record unit
          [IcacheRef.ilinkdp z self] -- **the tag is literally the payload's
          own [self] parameter**.  That is what lets ONE payload state a
          two-inode relation without naming the other inode: the relation
          hides behind the register's agreement.
        * INDEX 0 is the ["."] entry, which is the self record and carries
          no ticket at all (the guard in [dir_link_at_f] is false there).
          It is grouped with index 1 so the two dot slots have one shape.

      THE TAGGED FORM IS ONE HALF, NOT THE PAIR.  [IcacheRef.ilink_fl] at
      [Some (Some pv)] is [ilinkdp ∗ iparent] -- the MINT's payout and the
      SPEND's input, one slot so that every contract keeps one shape.  The
      payload holds only the [ilinkdp] half; the [iparent] half is the
      CHILD's, and it lives in the child's own tie ([dir_par_tie] below).
      Half plus half is the full register, which is exactly why no third
      copy can exist. *)
  Definition dlc_tick (self : Z) (k : nat) (b : bool) (z : Z) : iProp Σ :=
    (if b then (if decide (2 <= k)%nat then ilinkdp z self else ilinkd z)
     else ilink z)%I.

  Global Instance dlc_tick_timeless self k b z : Timeless (dlc_tick self k b z).
  Proof.
    rewrite /dlc_tick. destruct b; [destruct (decide (2 <= k)%nat) |];
      apply _.
  Qed.

  (* the two dot slots carry the UNTAGGED unit, which is exactly
     [ilink_fl (dlc_fl b)] -- so every landed statement at index 1 (the
     [".."] extraction, and the contract it feeds) keeps its shape. *)
  Lemma dlc_tick_dot (self : Z) (k : nat) (b : bool) (z : Z) :
    (k < 2)%nat -> dlc_tick self k b z = ilink_fl (dlc_fl b) z.
  Proof.
    intro Hk. rewrite /dlc_tick /dlc_fl.
    destruct b; [rewrite decide_False; [reflexivity | lia] | reflexivity].
  Qed.

  (* ...and a name record carries the TAGGED unit, at the tag [self] *)
  Lemma dlc_tick_name (self : Z) (k : nat) (b : bool) (z : Z) :
    (2 <= k)%nat ->
    dlc_tick self k b z = (if b then ilinkdp z self else ilink z)%I.
  Proof.
    intro Hk. rewrite /dlc_tick.
    destruct b; [rewrite decide_True; [reflexivity | lia] | reflexivity].
  Qed.

  Lemma dlc_tick_false (self : Z) (k : nat) (z : Z) :
    dlc_tick self k false z = ilink z.
  Proof. reflexivity. Qed.

  (* THE FOUR MOVERS, AS WANDS RATHER THAN EQUATIONS.  The equations above
     are the reading; a `rewrite` of one inside the proofmode has to match a
     term that the surrounding `∃`/`∗` structure has already elaborated, and
     it does not always -- so every USE goes through these. *)
  Lemma dlc_tick_dot_out (self : Z) (k : nat) (b : bool) (z : Z) :
    (k < 2)%nat -> dlc_tick self k b z -∗ ilink_fl (dlc_fl b) z.
  Proof.
    intro Hk. rewrite /dlc_tick /dlc_fl.
    destruct b; [rewrite decide_False; [| lia] |];
      iIntros "H"; iExact "H".
  Qed.

  Lemma dlc_tick_dot_in (self : Z) (k : nat) (b : bool) (z : Z) :
    (k < 2)%nat -> ilink_fl (dlc_fl b) z -∗ dlc_tick self k b z.
  Proof.
    intro Hk. rewrite /dlc_tick /dlc_fl.
    destruct b; [rewrite decide_False; [| lia] |];
      iIntros "H"; iExact "H".
  Qed.

  Lemma dlc_tick_name_out (self : Z) (k : nat) (b : bool) (z : Z) :
    (2 <= k)%nat ->
    dlc_tick self k b z -∗ (if b then ilinkdp z self else ilink z).
  Proof.
    intro Hk. rewrite /dlc_tick.
    destruct b; [rewrite decide_True; [| lia] |];
      iIntros "H"; iExact "H".
  Qed.

  Lemma dlc_tick_name_in (self : Z) (k : nat) (b : bool) (z : Z) :
    (2 <= k)%nat ->
    (if b then ilinkdp z self else ilink z) -∗ dlc_tick self k b z.
  Proof.
    intro Hk. rewrite /dlc_tick.
    destruct b; [rewrite decide_True; [| lia] |];
      iIntros "H"; iExact "H".
  Qed.

  (* THE MACHINE'S [++], CROSSED WITH NO GUARD AT ALL.  [DirView.dlc_bound]
     is an INEQUALITY, so create's [dp->nlink++] needs only that a
     sixteen-bit increment raises the value by at most one -- true even at
     the wrap, which lands at zero.  An equality would have needed (L4) at
     a record the walk cannot name (fs-sysfile.md's twelfth stop); this is
     what buying the weaker clause bought.  It lives in this file because
     [DirView.v] has no [add_vec] in scope. *)
  Lemma dlc_bv_add1_le (h : mword 16) :
    bv_unsigned (add_vec h (mword_of_int 1 : mword 16))
    <= bv_unsigned h + 1.
  Proof.
    rewrite add_vec_unsigned.
    assert (H1 : bv_unsigned (mword_of_int 1 : mword 16) = 1)
      by (vm_compute; reflexivity).
    rewrite H1.
    pose proof (bv_unsigned_in_range _ h) as Hr.
    unfold bv_wrap. unfold bv_modulus in Hr |- *.
    change (2 ^ Z.of_N (MachineWord.MachineWord.Z_idx 16))%Z with 65536%Z
      in Hr |- *.
    apply Z.mod_le; lia.
  Qed.

  (* ...AND ITS EXACT FORM UNDER A NONZERO READ-BACK (V4's [dlc_lower]).
     A sixteen-bit [++] wraps only at 65535, where it lands at ZERO -- so
     an increment whose result is known nonzero did not wrap, and the
     lower clause's EXACT [+1] is free.  The nonzero fact is the flush's
     own read-back ([IregLinkNz.ireg_link_nz] at the bumped record). *)
  Lemma dlc_bv_add1_nz_eq (h : mword 16) :
    bv_unsigned (add_vec h (mword_of_int 1 : mword 16)) <> 0 ->
    bv_unsigned (add_vec h (mword_of_int 1 : mword 16))
    = bv_unsigned h + 1.
  Proof.
    rewrite add_vec_unsigned.
    assert (H1 : bv_unsigned (mword_of_int 1 : mword 16) = 1)
      by (vm_compute; reflexivity).
    rewrite H1.
    pose proof (bv_unsigned_in_range _ h) as Hr.
    unfold bv_wrap. unfold bv_modulus in Hr |- *.
    change (2 ^ Z.of_N (MachineWord.MachineWord.Z_idx 16))%Z with 65536%Z
      in Hr |- *.
    intro Hnz.
    destruct (Z.eq_dec (bv_unsigned h) 65535) as [He | Hne].
    - exfalso. apply Hnz. rewrite He. vm_compute. reflexivity.
    - rewrite Z.mod_small; lia.
  Qed.

  Definition dir_link_at_f (F : nat -> bool) (self : Z) (dn : dinode)
      (data : nat -> list (bv 8)) (k : nat)
    : iProp Σ :=
    (if dir_liveb data k
        && negb (bool_decide (bv_unsigned (dir_inum data k) = self))
     then (dlc_tick self k (F k) (bv_unsigned (dir_inum data k))
           ∨ (igrey (bv_unsigned (dir_inum data k))
              ∗ ⌜bv_unsigned (di_nlink dn) = 0⌝))
     else emp)%I.

  Global Instance dir_link_at_f_timeless F self dn data k :
    Timeless (dir_link_at_f F self dn data k).
  Proof.
    rewrite /dir_link_at_f.
    destruct (dir_liveb data k
              && negb (bool_decide (bv_unsigned (dir_inum data k) = self)));
      apply _.
  Qed.

  (* [dir_link_at] IS THE UNFLAVOURED INSTANCE, and it is stated in
     expanded form rather than as [dir_link_at_f (fun _ => false)] on
     purpose: every landed consumer of the plain ticket
     ([IregLinkNz.dir_link_at_nlink_drop], [FsRep.fedges_acc],
     [ProofCreate.cr_grey_links], [ProofSysUnlinkParts]'s two record
     lemmas) opens it with [rewrite /dir_link_at] and then [destruct]s the
     guard, which only fires on the literal [if].  The two are convertible
     ([ilink_fl None] IS [ilink], by iota), which is what this lemma
     says. *)
  Lemma dir_link_at_f_plain (F : nat -> bool) (self : Z) (dn : dinode)
      (data : nat -> list (bv 8)) (k : nat) :
    F k = false ->
    dir_link_at_f F self dn data k ⊣⊢ dir_link_at self dn data k.
  Proof.
    intro HF. rewrite /dir_link_at_f /dir_link_at HF /dlc_tick. reflexivity.
  Qed.

  (* the congruence, at the flavour: a record whose two inum bytes did not
     move and whose flavour did not change carries the same ticket. *)
  Lemma dir_link_at_f_agree (F G : nat -> bool) (self : Z) (dn dn' : dinode)
      (data data' : nat -> list (bv 8)) (k : nat) :
    di_nlink dn' = di_nlink dn ->
    dir_inum data' k = dir_inum data k ->
    G k = F k ->
    dir_link_at_f F self dn data k -∗ dir_link_at_f G self dn' data' k.
  Proof.
    intros Hnl Heq HF.
    rewrite /dir_link_at_f /dir_liveb /dir_freeb Heq Hnl HF.
    iIntros "H". iExact "H".
  Qed.

  (* ...AND THE SAME CONGRUENCE ACROSS A COUNT CHANGE, which the writers
     that MOVE [nlink] need ([IregLinkNz.dir_link_at_nlink_drop]'s twin).
     A live home refutes the grey disjunct where it stands, and an
     [ilink_fl] says nothing about the home at all. *)
  Lemma dir_link_at_f_live_agree (F G : nat -> bool) (self : Z)
      (dn dn' : dinode) (data data' : nat -> list (bv 8)) (k : nat) :
    bv_unsigned (di_nlink dn) <> 0 ->
    dir_inum data' k = dir_inum data k ->
    G k = F k ->
    dir_link_at_f F self dn data k -∗ dir_link_at_f G self dn' data' k.
  Proof.
    intros Hnz Heq HF.
    rewrite /dir_link_at_f /dir_liveb /dir_freeb Heq HF.
    destruct (negb (bool_decide (dir_inum data k = bv_0 16))
              && negb (bool_decide (bv_unsigned (dir_inum data k) = self)));
      [| iIntros "_"; done].
    iIntros "[H | [_ %Hz]]"; [iLeft; iExact "H" |].
    exfalso. exact (Hnz Hz).
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  THE PAYLOAD CONJUNCT                                               *)
  (* ------------------------------------------------------------------ *)

  (* THE TWIN OF [DirView.dir_ok], RIDING IN THE SAME TWO PAYLOADS
     ([IcacheEscrow.ipool_alloc] and [ic_loaded]) FOR THE SAME REASON.
     TYPE-CONDITIONAL, exactly as [dir_ok] is: only a directory's bytes are
     records, a file's data is arbitrary, and a free inode has no data.

     NO ARITY CHANGES ANYWHERE.  The colour disjunction lives inside
     [dir_link_at], exactly as §17.6.3 put [ity_shot]/[ity_pending] inside
     [ic_payload] without moving [ic_loaded]; [self] is the inum both
     payloads already carry as a parameter.  Both fragments are timeless, so
     [ic_loaded_timeless] / [ipool_alloc_timeless] survive verbatim. *)
  (* THE COUNT CLAUSE RIDES INSIDE, AND THE FLAVOUR MAP IS EXISTENTIAL
     (V2).  [DirView.dlc_bound] is the fact FINDING 3 needs -- an empty
     directory's [nlink] is one -- and it is stated about the SAME [F] the
     big-op's tickets are flavoured by, because that is what makes it
     PRESERVABLE: a walk that zeroes a record and shrinks the count must
     show the record's ticket was not d-flavoured, and the only evidence is
     the ticket itself ([IregDirBit.ireg_dirbit_ty] reads the target's type
     off an [ilinkd]).  A free-floating [⌜∃ F, dlc_bound F dn data⌝] beside
     the big-op would be unprovable at exactly that step.

     THE EXISTENTIAL IS INSIDE THE [if], so a non-directory's payload is
     still literally [emp] and every landed discharge that opens this
     definition on a refuted type is unchanged.  Arity does not move. *)
  (* THE LOWER CLAUSE RIDES BESIDE THE BOUND (V4, S7-unlink (D2)'s
     carrier).  [DirView.dlc_lower] is the mirror inequality -- a LIVE
     directory's count is at least one plus its d-flavoured record count
     -- and at the same [F] the two clauses pin [nlink = 1 + count].  A
     SEPARATE conjunct, not a strengthening of [dlc_bound]: every
     discharge below reads them by position and half the parks pay for
     exactly one of the two. *)
  (* ------------------------------------------------------------------ *)
  (*  THE PARENT TIE (V5' increment P; S7-unlink's (D1))                  *)
  (* ------------------------------------------------------------------ *)

  (*  THE HALF OF THE PARENT REGISTER THAT SAYS WHAT THIS DIRECTORY'S
      [".."] MUST HOLD.  [IcacheRef.iparent self pv] is a claim about the
      LEDGER -- "[self]'s parent register reads [pv]" -- and the pure
      conjunct beside it ties that register to the BYTES of record 1.  The
      relation "ip's parent is dp" is therefore stated by ONE payload, which
      is what §20.17.4's sharpening (b) said a payload cannot do: the second
      inode is not named here at all, it is named by the OTHER half of the
      register, which lives in dp's own name record ([dlc_tick] at index
      >= 2).  [IcacheRef.iparent_agree] joins them, with no region open.

      THE GUARD'S FIRST TWO CONJUNCTS COPY [DirView.dir_dots_ix]'s
      ANTECEDENT, so every discharge co-fires with the dots clause the same
      payload already carries: a directory owes the tie exactly when it is
      LIVE and has grown its two dot records.  A directory that is dead
      (the orphan re-park, iput's free path) or has not got its [".."] yet
      (ilock's claim box, create's child between the two dot writes) owes
      nothing, and the momentary falseness in between is covered by the
      checked-out payload under the sleeplock -- §20.17.4(a)'s chartered
      placement.

      THE ROOT IS EXCLUDED because it has no create-episode: nothing ever
      mints its register, its [".."] is a self-record, and the fact would be
      false rather than merely unavailable.  Boot's image obligation is
      exactly this exclusion (see [dir_links_of_plain]).

      IT IS A SEPARATE CONJUNCT of [dir_links]' T_DIR branch, beside the
      [∃ F] and the two count clauses -- NOT a new argument and not a new
      payload.  That is what keeps the ~30 transfer parks (namex, chdir,
      kexec, fileread/stat, iput's peels) blind to it: they move [dir_links]
      whole and never open it. *)
  Definition dir_par_tie (self : Z) (dn : dinode)
      (data : nat -> list (bv 8)) : iProp Σ :=
    (if decide (bv_unsigned (di_nlink dn) <> 0
                /\ (2 <= dir_nrec (bv_unsigned (di_size dn)))%nat
                /\ self <> dl_root)
     then ∃ pv : Z, iparent self pv ∗ ⌜bv_unsigned (dir_inum data 1) = pv⌝
     else emp)%I.

  Global Instance dir_par_tie_timeless self dn data :
    Timeless (dir_par_tie self dn data).
  Proof.
    rewrite /dir_par_tie.
    destruct (decide (bv_unsigned (di_nlink dn) <> 0
                      /\ (2 <= dir_nrec (bv_unsigned (di_size dn)))%nat
                      /\ self <> dl_root)); apply _.
  Qed.

  (* the guard is false at a DEAD home -- the orphan re-park, iput's free
     path, and create's [fail:] arms all land here *)
  Lemma dir_par_tie_nl0 (self : Z) (dn : dinode)
      (data : nat -> list (bv 8)) :
    bv_unsigned (di_nlink dn) = 0 -> ⊢ dir_par_tie self dn data.
  Proof.
    intro Hnl. rewrite /dir_par_tie decide_False; [done |].
    intros (Hc & _ & _). exact (Hc Hnl).
  Qed.

  (* ...and at a home with no [".."] yet: ilock's claim box (size 0) and
     create's child between its two dot writes *)
  Lemma dir_par_tie_small (self : Z) (dn : dinode)
      (data : nat -> list (bv 8)) :
    (dir_nrec (bv_unsigned (di_size dn)) < 2)%nat ->
    ⊢ dir_par_tie self dn data.
  Proof.
    intro Hsz. rewrite /dir_par_tie decide_False; [done |].
    intros (_ & Hc & _). lia.
  Qed.

  (* ...and at the ROOT, which owes no parent edge at all *)
  Lemma dir_par_tie_root (self : Z) (dn : dinode)
      (data : nat -> list (bv 8)) :
    self = dl_root -> ⊢ dir_par_tie self dn data.
  Proof.
    intro Hr. rewrite /dir_par_tie decide_False; [done |].
    intros (_ & _ & Hc). exact (Hc Hr).
  Qed.

  (* the guard's positive side: a LIVE, non-root directory that has its two
     dot records OWES the tie, and this is how a reader takes it *)
  Lemma dir_par_tie_open (self : Z) (dn : dinode)
      (data : nat -> list (bv 8)) :
    bv_unsigned (di_nlink dn) <> 0 ->
    (2 <= dir_nrec (bv_unsigned (di_size dn)))%nat ->
    self <> dl_root ->
    dir_par_tie self dn data -∗
      ∃ pv : Z, iparent self pv ∗ ⌜bv_unsigned (dir_inum data 1) = pv⌝.
  Proof.
    intros H1 H2 H3. rewrite /dir_par_tie decide_True;
      [| split; [exact H1 | split; [exact H2 | exact H3]]].
    iIntros "H". iExact "H".
  Qed.

  (* ...and how a writer puts it back, at ANY record: where the guard is
     false the half is simply dropped (affine) *)
  Lemma dir_par_tie_close (self : Z) (dn : dinode)
      (data : nat -> list (bv 8)) (pv : Z) :
    bv_unsigned (dir_inum data 1) = pv ->
    iparent self pv -∗ dir_par_tie self dn data.
  Proof.
    intros Hpv. rewrite /dir_par_tie.
    destruct (decide (bv_unsigned (di_nlink dn) <> 0
                      /\ (2 <= dir_nrec (bv_unsigned (di_size dn)))%nat
                      /\ self <> dl_root)) as [_ | _];
      [| iIntros "_"; done].
    iIntros "H". iExists pv. iSplitL "H"; [iExact "H" |].
    iPureIntro. exact Hpv.
  Qed.

  (* THE CONGRUENCE EVERY RIDING PARK USES.  The tie names exactly three
     things about the record -- the count (only whether it is zero), the
     record count, and record 1's two inum bytes -- so any write that
     leaves those alone carries it across, whatever else it moved. *)
  Lemma dir_par_tie_cong (self : Z) (dn dn' : dinode)
      (data data' : nat -> list (bv 8)) :
    (bv_unsigned (di_nlink dn') <> 0 -> bv_unsigned (di_nlink dn) <> 0) ->
    ((2 <= dir_nrec (bv_unsigned (di_size dn')))%nat ->
     (2 <= dir_nrec (bv_unsigned (di_size dn)))%nat) ->
    dir_inum data' 1 = dir_inum data 1 ->
    dir_par_tie self dn data -∗ dir_par_tie self dn' data'.
  Proof.
    intros Hnl Hsz Heq. rewrite /dir_par_tie.
    destruct (decide (bv_unsigned (di_nlink dn') <> 0
                      /\ (2 <= dir_nrec (bv_unsigned (di_size dn')))%nat
                      /\ self <> dl_root)) as [(H1 & H2 & H3) | _];
      [| iIntros "_"; done].
    rewrite decide_True; [| split; [exact (Hnl H1) |
                                    split; [exact (Hsz H2) | exact H3]]].
    rewrite Heq. iIntros "H". iExact "H".
  Qed.

  (* THE LOWER CLAUSE RIDES BESIDE THE BOUND (V4, S7-unlink (D2)'s
     carrier) and the PARENT TIE beside both (V5', (D1)'s). *)
  Definition dir_links (self : Z) (dn : dinode) (data : nat -> list (bv 8))
    : iProp Σ :=
    (if decide (bv_unsigned (di_type dn) = T_DIR_z)
     then ∃ F : nat -> bool,
            ⌜dlc_bound F dn data⌝ ∗ ⌜dlc_lower F dn data⌝ ∗
            dir_par_tie self dn data ∗
            ([∗ list] k ∈ seq 0 (dir_nrec (bv_unsigned (di_size dn))),
               dir_link_at_f F self dn data k)
     else emp)%I.

  Global Instance dir_links_timeless self dn data :
    Timeless (dir_links self dn data).
  Proof.
    rewrite /dir_links.
    destruct (decide (bv_unsigned (di_type dn) = T_DIR_z)); apply _.
  Qed.

  (* the plain stock: an all-[ilink] big-op with the bound in hand.  Every
     builder that has no directory records to speak of goes through this. *)
  (* ITS ONE IMAGE OBLIGATION (V5' increment P).  The all-plain stock is
     what BOOT builds every directory from, and the parent tie is owed by
     every LIVE directory that has a [".."] -- except the root.  So the
     builder owes exactly the exclusion, and for the stock image it is a
     COMPUTATIONAL fact rather than a resource one: mkfs lays down exactly
     one directory, the root, so every live image directory IS root.  Same
     precedent class as V2's [nlink <= 1] image fact.  (A rich, post-crash
     image would break it, and a crash model would then mint the registers
     computationally off record 1 at boot; noted for that effort, not this
     one.) *)
  Lemma dir_links_of_plain (self : Z) (dn : dinode)
      (data : nat -> list (bv 8)) :
    bv_unsigned (di_type dn) = T_DIR_z ->
    dlc_bound (fun _ => false) dn data ->
    (bv_unsigned (di_nlink dn) <> 0 ->
     (2 <= dir_nrec (bv_unsigned (di_size dn)))%nat -> self = dl_root) ->
    ([∗ list] k ∈ seq 0 (dir_nrec (bv_unsigned (di_size dn))),
       dir_link_at self dn data k) -∗
    dir_links self dn data.
  Proof.
    intros Hty Hb Hroot.
    iIntros "H". rewrite /dir_links decide_True; [| exact Hty].
    iExists (fun _ => false). iSplitR; [iPureIntro; exact Hb |].
    (* V4: the LOWER clause is free at the all-plain stock -- [nlink <> 0
       -> 1 <= nlink] is true of any bitvector, so boot owes nothing *)
    iSplitR; [iPureIntro; exact (dlc_lower_false dn data) |].
    iSplitR.
    { rewrite /dir_par_tie.
      destruct (decide (bv_unsigned (di_nlink dn) <> 0
                        /\ (2 <= dir_nrec (bv_unsigned (di_size dn)))%nat
                        /\ self <> dl_root)) as [(H1 & H2 & H3) | _];
        [| done].
      exfalso. exact (H3 (Hroot H1 H2)). }
    iApply (big_sepL_mono with "H"). intros i k Hik. iIntros "Hx".
    rewrite (dir_link_at_f_plain (fun _ => false) self dn data k eq_refl).
    iExact "Hx".
  Qed.

  (* ---- the four ways a holder discharges it, mirroring DirView ------- *)

  (* (i) it is not a directory -- [DirView.dir_ok_not_dir]'s twin *)
  Lemma dir_links_not_dir (self : Z) (dn : dinode)
      (data : nat -> list (bv 8)) :
    bv_unsigned (di_type dn) <> T_DIR_z ->
    ⊢ dir_links self dn data.
  Proof.
    intros H. rewrite /dir_links decide_False; [| exact H]. done.
  Qed.

  (* (ii) it is FREE -- [ipool_shape]'s free arm, and iput's post-itrunc
     park.  [dir_ok_free]'s twin. *)
  Lemma dir_links_free (self : Z) (dn : dinode)
      (data : nat -> list (bv 8)) :
    bv_unsigned (di_type dn) = 0 ->
    ⊢ dir_links self dn data.
  Proof.
    intros H. apply dir_links_not_dir. rewrite H. unfold T_DIR_z. lia.
  Qed.

  (* (iii) it holds no whole record -- itrunc's zeroed directory, whose size
     is 0.  [dir_ok_size_zero]'s twin, and the one that makes iput's free
     path shed whatever the directory held: the big-op is over
     [seq 0 (dir_nrec 0)] = [] and collapses to [emp]. *)
  (* THE COUNT PREMISE IS NEW (V2) AND IT IS FREE AT EVERY CALLER.  A
     record with no records at all counts ZERO subdirectories, so the
     clause reads [nlink <= 1] -- true of both sites: ilock's claim box has
     [InodeRegion.fresh_shape]'s [nlink = 0], and iput's post-itrunc park
     runs behind [ip->nlink == 0]. *)
  Lemma dir_links_size_zero (self : Z) (dn : dinode)
      (data : nat -> list (bv 8)) :
    bv_unsigned (di_size dn) = 0 ->
    bv_unsigned (di_nlink dn) <= 1 ->
    ⊢ dir_links self dn data.
  Proof.
    intros Hsz Hnl. rewrite /dir_links.
    destruct (decide (bv_unsigned (di_type dn) = T_DIR_z)) as [_ | _];
      [| done].
    iExists (fun _ => false).
    iSplitR; [iPureIntro; exact (dlc_bound_le1 _ dn data Hnl) |].
    iSplitR; [iPureIntro; exact (dlc_lower_false dn data) |].
    assert (Hz : dir_nrec (bv_unsigned (di_size dn)) = 0%nat)
      by (rewrite Hsz /dir_nrec; vm_compute; reflexivity).
    (* V5': no records at all means no [".."], so the tie's guard is false *)
    iSplitR; [iApply (dir_par_tie_small self dn data ltac:(rewrite Hz; lia)) |].
    rewrite Hz /=. done.
  Qed.

  (* (iv) the DATA is unchanged and so is the record -- the "rides" case
     every re-park in the cache is (ilock's fill, iget's eviction, iunlock's
     park).  [dir_ok_eq]'s twin, and the reason stage B is threading-shaped:
     no writer in the landed tree changes a DIRECTORY's bytes. *)
  Lemma dir_links_eq (self : Z) (dn dn' : dinode)
      (data data' : nat -> list (bv 8)) :
    dn = dn' -> data = data' ->
    dir_links self dn data -∗ dir_links self dn' data'.
  Proof. intros -> ->. iIntros "H". iExact "H". Qed.

  (* ---- the congruence the writer twin will be built on --------------- *)

  (* A record whose two inum bytes did not move carries the same ticket.
     This is [DirView.dir_liveb_agree]'s resource consequence and it is what
     [dir_links_dirlink] (stage D, §20.6's dirlink row) will iterate over:
     dirlink touches exactly one slot, so every OTHER index rides by this
     lemma and only the written one moves a fragment. *)
  Lemma dir_link_at_agree (self : Z) (dn dn' : dinode)
      (data data' : nat -> list (bv 8)) (k : nat) :
    di_nlink dn' = di_nlink dn ->
    dir_inum data' k = dir_inum data k ->
    dir_link_at self dn data k -∗ dir_link_at self dn' data' k.
  Proof.
    intros Hnl Heq. rewrite /dir_link_at /dir_liveb /dir_freeb Heq Hnl.
    iIntros "H". iExact "H".
  Qed.

  (* THE SLOT dirlink APPENDS AT IS NEVER A DOT SLOT.  [DirView.dir_dots_ix]
     says records 0 and 1 are LIVE, and [dir_slot] returns either a FREE
     record below the count or the count itself -- which the same clause
     puts at 2 or above.  Packaged here because [dir_links_dirlink]'s
     [k0 <> 1] premise (V5': record 1 is what the parent tie names) and
     [dir_links_dirlink_d]'s internal [2 <= k0] are the same three lines,
     and because every caller of the former has exactly these hypotheses in
     hand at the deposit. *)
  Lemma dir_slot_dots_ge2 (self : Z) (dn : dinode)
      (data : nat -> list (bv 8)) (nrec : nat) :
    bv_unsigned (di_type dn) = T_DIR_z ->
    bv_unsigned (di_nlink dn) <> 0 ->
    dir_dots_ix self dn data ->
    nrec = dir_nrec (bv_unsigned (di_size dn)) ->
    (2 <= dir_slot data nrec)%nat.
  Proof.
    intros Hty Hnl Hdd Hnrec.
    destruct (Hdd Hty Hnl) as (Hnr2 & Hlv0 & _ & _ & Hlv1 & _).
    rewrite <- Hnrec in Hnr2.
    destruct (Nat.lt_ge_cases (dir_slot data nrec) 2) as [Hlt | Hge];
      [| exact Hge].
    exfalso.
    assert (Hfree : dir_inum data (dir_slot data nrec) = bv_0 16)
      by (apply dir_slot_free; lia).
    assert (Hc : dir_slot data nrec = 0%nat \/ dir_slot data nrec = 1%nat)
      by lia.
    destruct Hc as [Hc | Hc]; rewrite Hc in Hfree;
      [exact (Hlv0 Hfree) | exact (Hlv1 Hfree)].
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  (v) THE WRITER'S CASE -- [DirView.dir_ok_dirlink]'s twin           *)
  (*      design: fs-icache.md §20.3 / §20.6's dirlink row               *)
  (* ------------------------------------------------------------------ *)

  (* THE SHAPE DEVIATES FROM §20.3, AND THE REASON IS A REAL GAP (fs-sysfile
     S5i).  §20.3 charters this lemma as "the same hypothesis list, one
     [ilink inum] in, the new big-op out ... the resource moves only in the
     third case ([tot >= 2])".  That is wrong at [tot = 1], and the pure
     sibling is what shows it: [DirView.dir_ok_dirlink]'s middle case proves
     the stored halfword is [inum mod 256] (only the LOW byte is new, and the
     slot's old high byte is zero because the slot was free).  The PURE
     clause survives that -- [inum mod 256 <= inum] is still in range -- but
     the RESOURCE clause does not: the record at [k0] becomes LIVE at the
     inum [inum mod 256], and no [ilink] for that key exists anywhere.  An
     [ilink inum] is a fragment for a DIFFERENT key and cannot be bent.

     [tot = 1] is UNREACHABLE in the kernel -- dirlink's window is sixteen
     bytes at a 16-aligned offset and 1024 = 64*16, so writei's loop takes
     exactly one chunk of sixteen and either bmap fails before it (leaving
     [tot = 0]) or the whole record goes in ([either_copyin] cannot fail on
     the kernel arm) -- but [SpecWritei]'s postcondition offers only
     [tot <= n], so [SpecDirlink]'s offers only [tot < 16], and the fact is
     not available to a caller.  See the S5i ledger.

     So the twin is stated in the form that is TRUE WITHOUT A SIDE
     CONDITION: the caller hands in the ticket for the slot that was
     written, whatever landed in it.  [dir_link_at_dirlink] below is the
     constructor for the case create actually takes on its success arms
     ([tot >= 2], hence [tot = 16]), and [dir_links_dirlink_nop] is the
     no-write arm, which needs no ticket at all. *)
  Lemma dir_links_dirlink (self : Z) (dn dn' : dinode)
      (data data' : nat -> list (bv 8))
      (inum : bv 16) (s : list (bv 8)) (nrec k0 tot : nat) :
    nrec = dir_nrec (bv_unsigned (di_size dn)) ->
    k0 = dir_slot data nrec ->
    (tot <= 16)%nat ->
    (* V5' increment P: THE SLOT IS NOT THE [".."].  The parent tie names
       record 1's two inum bytes, so a plain deposit INTO record 1 would
       have to re-establish it -- and a plain deposit has no register half
       to do it with.  It is not a restriction on anything real: every
       caller appends into a directory whose two dots are already there
       ([DirView.dir_dots_ix]), and [dir_slot] never returns a live record
       below the count, so the slot is at 2 or past the end
       ([dir_slot_dots_ge2] is the packaged argument). *)
    k0 <> 1%nat ->
    (* writei preserves the type and installs [max(size, off+tot)] *)
    di_type dn' = di_type dn ->
    (* the nlink half of "writei moved neither" -- [wi_dinode] touches only
       size and addrs, so every caller closes this by [reflexivity] *)
    di_nlink dn' = di_nlink dn ->
    bv_unsigned (di_size dn')
      = Z.max (bv_unsigned (di_size dn)) (Z.of_nat (16 * k0 + tot)) ->
    (* dirlink's TIGHTENED range clause: no disturbed region *)
    (forall x : nat,
       file_byte data' x
       = if decide ((16 * k0 <= x)%nat /\ (x < 16 * k0 + tot)%nat)
         then dirent_bytes (de_of_name inum s) !!! (x - 16 * k0)%nat
         else file_byte data x) ->
    dir_link_at self dn' data' k0 -∗
    dir_links self dn data -∗ dir_links self dn' data'.
  Proof.
    intros Hnrec Hk0 Htot Hk01 Hty Hnl Hsz Hrng.
    (* the type is unmoved, so the two big-ops are both live or both [emp] *)
    rewrite /dir_links Hty.
    destruct (decide (bv_unsigned (di_type dn) = T_DIR_z)) as [_ | _];
      [| iIntros "_ _"; done].
    (* THE COUNT CLAUSE RIDES (V2), and it needs nothing new from the
       caller: the deposited ticket is PLAIN, so the written slot is not
       counted, every other record keeps its halfword and its flavour, and
       the record count only grows.  [di_nlink] is unmoved by hypothesis --
       the mkdir arm, which moves it, is [dir_links_dirlink_d] below. *)
    (* ---- the count arithmetic, verbatim from [dir_ok_dirlink] ---- *)
    assert (Hsznn : 0 <= bv_unsigned (di_size dn))
      by exact (proj1 (bv_unsigned_in_range _ (di_size dn))).
    assert (Hsznn' : 0 <= bv_unsigned (di_size dn'))
      by exact (proj1 (bv_unsigned_in_range _ (di_size dn'))).
    destruct (dir_nrec_range (bv_unsigned (di_size dn)) Hsznn) as [Hnr1 Hnr2].
    destruct (dir_nrec_range (bv_unsigned (di_size dn')) Hsznn')
      as [Hnr1' Hnr2'].
    rewrite <- Hnrec in Hnr1, Hnr2.
    assert (Hk0le : (k0 <= nrec)%nat) by (rewrite Hk0; apply dir_slot_le).
    assert (Hcalt : dir_nrec (bv_unsigned (di_size dn')) = nrec
                    \/ (dir_nrec (bv_unsigned (di_size dn')) = S nrec
                        /\ k0 = nrec /\ tot = 16%nat)) by lia.
    (* every record BUT [k0] keeps its two inum bytes *)
    assert (Hagree : forall q : nat, q <> k0 ->
                       dir_inum data' q = dir_inum data q).
    { intros q Hq. unfold dir_inum.
      rewrite (Hrng (16 * q)%nat). rewrite (Hrng (16 * q + 1)%nat).
      rewrite decide_False; [| lia]. rewrite decide_False; [| lia].
      reflexivity. }
    rewrite <- Hnrec.
    iIntros "Hk0 H". iDestruct "H" as (F) "(%Hbnd & %Hlow & Htie & H)".
    destruct (dlc_upd_map F k0 false) as (G & HGk0 & HGoff).
    (* the written slot was FREE below the record count and out of range at
       it -- [dir_slot]'s own two readings, and what makes the count
       monotone either way *)
    assert (Hslot : (k0 < nrec)%nat -> dir_inum data k0 = bv_0 16).
    { intro Hlt. rewrite Hk0. apply dir_slot_free. rewrite <- Hk0. exact Hlt. }
    assert (Hcalt2 : dir_nrec (bv_unsigned (di_size dn')) = nrec
                     \/ (dir_nrec (bv_unsigned (di_size dn')) = S nrec
                         /\ k0 = nrec))
      by (destruct Hcalt as [H1 | (H1 & H2 & _)]; [left; exact H1
                                                  | right; split; assumption]).
    iExists G. iSplitR.
    { iPureIntro.
      apply (dlc_bound_le F G dn dn' data data'); [rewrite Hnl; lia | | exact Hbnd].
      rewrite <- Hnrec.
      apply (dlc_count_slot_ge F G data data' nrec _ k0); [| exact Hagree
                                                           | exact HGoff
                                                           | exact Hslot].
      pose proof Hcalt as Hc2. destruct Hc2 as [Hn' | (Hn' & _ & _)]; lia. }
    (* V4: THE LOWER CLAUSE RIDES TOO -- the deposited ticket is PLAIN, so
       the written slot stays uncounted and the count cannot RISE either *)
    iSplitR.
    { iPureIntro.
      apply (dlc_lower_eq F G dn dn' data data');
        [rewrite Hnl; reflexivity | | exact Hlow].
      rewrite <- Hnrec.
      apply (dlc_count_ctb_le F G data data' nrec _ k0 Hcalt2 Hagree HGoff
               (dlc_ctb_flav G data' k0 HGk0)). }
    (* V5': THE PARENT TIE RIDES.  The count did not move, record 1's bytes
       did not move ([k0 <> 1]), and the record count can only have grown --
       and it cannot have grown ACROSS 2, because the only growth is an
       append at [k0 = nrec] and [k0 <> 1]. *)
    iSplitL "Htie".
    { assert (Htnl : bv_unsigned (di_nlink dn') <> 0 ->
                     bv_unsigned (di_nlink dn) <> 0)
        by (rewrite Hnl; exact (fun H => H)).
      assert (Htnr : (2 <= dir_nrec (bv_unsigned (di_size dn')))%nat ->
                     (2 <= dir_nrec (bv_unsigned (di_size dn)))%nat).
      { intro Hx. rewrite <- Hnrec.
        destruct Hcalt2 as [He | (He & Hke)]; lia. }
      assert (Ht1 : dir_inum data' 1 = dir_inum data 1)
        by (apply Hagree; intro Hc; exact (Hk01 (eq_sym Hc))).
      iApply (dir_par_tie_cong self dn dn' data data' Htnl Htnr Ht1
                with "Htie"). }
    destruct Hcalt as [Hn' | (Hn' & Hkn & Ht16)]; rewrite Hn'.
    - (* ======== the record COUNT did not move ======== *)
      destruct (Nat.lt_ge_cases k0 nrec) as [Hlt | Hge].
      + (* the written slot is one of the goal's indices: swap it *)
        rewrite (big_sepL_delete
                   (fun _ k => dir_link_at_f G self dn' data' k)
                   (seq 0 nrec) k0 k0).
        2:{ apply lookup_seq; lia. }
        iSplitL "Hk0".
        { rewrite (dir_link_at_f_plain G self dn' data' k0 HGk0).
          iExact "Hk0". }
        iApply (big_sepL_mono with "H"). intros i k Hik.
        apply lookup_seq in Hik. destruct Hik as [Hk Hi].
        destruct (decide (i = k0)) as [_ | Hne]; [by iIntros "_" |].
        assert (Heq : dir_inum data' k = dir_inum data k)
          by (apply Hagree; lia).
        iIntros "Hx".
        iApply (dir_link_at_f_agree F G self dn dn' data data' k Hnl Heq
                  ltac:(apply HGoff; lia) with "Hx").
      + (* the written slot is at or past the end: nothing in range moved *)
        iApply (big_sepL_mono with "H"). intros i k Hik.
        apply lookup_seq in Hik. destruct Hik as [Hk Hi].
        assert (Heq : dir_inum data' k = dir_inum data k)
          by (apply Hagree; lia).
        iIntros "Hx".
        iApply (dir_link_at_f_agree F G self dn dn' data data' k Hnl Heq
                  ltac:(apply HGoff; lia) with "Hx").
    - (* ======== ONE record was appended, at [k0 = nrec] ======== *)
      rewrite seq_S big_sepL_app. iSplitL "H".
      + iApply (big_sepL_mono with "H"). intros i k Hik.
        apply lookup_seq in Hik. destruct Hik as [Hk Hi].
        assert (Heq : dir_inum data' k = dir_inum data k)
          by (apply Hagree; lia).
        iIntros "Hx".
        iApply (dir_link_at_f_agree F G self dn dn' data data' k Hnl Heq
                  ltac:(apply HGoff; lia) with "Hx").
      + simpl. iSplitL "Hk0"; [| done].
        rewrite <- Hkn.
        rewrite (dir_link_at_f_plain G self dn' data' k0 HGk0).
        iExact "Hk0".
  Qed.

  (* THE CONSTRUCTOR create USES ON ITS SUCCESS ARMS.  Two bytes are enough:
     [dir_inum] reads exactly the record's first two, and [de_of_name inum s]
     puts [inum] there.  If the linked inum is the directory's OWN (mkdir's
     ["."]) or is zero, the ticket is [emp] and the fragment is simply
     dropped -- affine, and the self-record exemption is the whole point. *)
  Lemma dir_link_at_dirlink (self : Z) (dn : dinode)
      (data data' : nat -> list (bv 8))
      (inum : bv 16) (s : list (bv 8)) (k0 tot : nat) :
    (2 <= tot)%nat ->
    (forall x : nat,
       file_byte data' x
       = if decide ((16 * k0 <= x)%nat /\ (x < 16 * k0 + tot)%nat)
         then dirent_bytes (de_of_name inum s) !!! (x - 16 * k0)%nat
         else file_byte data x) ->
    ilink (bv_unsigned inum) -∗ dir_link_at self dn data' k0.
  Proof.
    intros Htot Hrng.
    assert (Hrec : dir_inum data' k0 = inum).
    { rewrite (dir_inum_of_two data' k0 (de_of_name inum s)); [reflexivity |].
      intros jj Hjj. rewrite (Hrng (16 * k0 + jj)%nat).
      rewrite decide_True; [| lia].
      replace (16 * k0 + jj - 16 * k0)%nat with jj by lia. reflexivity. }
    (* S5h trap 3: [dir_liveb] is [negb (dir_freeb ..)] -- unfold BOTH, or
       the rewrite under [Hrec] does not fire. *)
    rewrite /dir_link_at /dir_liveb /dir_freeb Hrec.
    destruct (negb (bool_decide (inum = bv_0 16))
              && negb (bool_decide (bv_unsigned inum = self)));
      [| by iIntros "_"].
    iIntros "H". iLeft. iExact "H".
  Qed.

  (* ...AND AT THE FLAVOUR THE SLOT IS ABOUT TO CARRY (V2).  The same two
     bytes; the ticket that goes in is whatever [F] says the record's
     target is, which for create's [mkdir] is the [ilinkd] its child's
     [ip->nlink = 1] mint paid out.  [dir_link_at_dirlink] above is its
     [F k0 = false] instance, stated separately because its landed callers
     hand in a bare [ilink]. *)
  Lemma dir_link_at_f_dirlink (F : nat -> bool) (self : Z) (dn : dinode)
      (data data' : nat -> list (bv 8))
      (inum : bv 16) (s : list (bv 8)) (k0 tot : nat) :
    (2 <= tot)%nat ->
    (forall x : nat,
       file_byte data' x
       = if decide ((16 * k0 <= x)%nat /\ (x < 16 * k0 + tot)%nat)
         then dirent_bytes (de_of_name inum s) !!! (x - 16 * k0)%nat
         else file_byte data x) ->
    dlc_tick self k0 (F k0) (bv_unsigned inum) -∗
    dir_link_at_f F self dn data' k0.
  Proof.
    intros Htot Hrng.
    assert (Hrec : dir_inum data' k0 = inum).
    { rewrite (dir_inum_of_two data' k0 (de_of_name inum s)); [reflexivity |].
      intros jj Hjj. rewrite (Hrng (16 * k0 + jj)%nat).
      rewrite decide_True; [| lia].
      replace (16 * k0 + jj - 16 * k0)%nat with jj by lia. reflexivity. }
    rewrite /dir_link_at_f /dir_liveb /dir_freeb Hrec.
    destruct (negb (bool_decide (inum = bv_0 16))
              && negb (bool_decide (bv_unsigned inum = self)));
      [| by iIntros "_"].
    iIntros "H". iLeft. iExact "H".
  Qed.

  (* ...AND THE SELF-RECORD, WHICH NEEDS NO TICKET AT ALL (design §20.3's
     forced exemption, landed as its own constructor for §20.18's C1).
     mkdir's [dirlink(ip, ".", ip->inum)] writes a record naming the
     directory ITSELF, and xv6 deliberately does not bump [ip->nlink] for it
     ("No ip->nlink++ for '.': avoid cyclic ref count") -- so there is no
     [ilink] to hand in, and none is wanted: the guard's second half is
     false at [inum = self] and the ticket is [emp].

     [dir_link_at_dirlink] above already DROPS a fragment offered at a
     self-record (it is affine), but create cannot use it for the dot: it
     has no fragment to offer.  This is the same two bytes, with the premise
     that makes the ticket free instead of dropped. *)
  Lemma dir_link_at_dirlink_self (self : Z) (dn : dinode)
      (data data' : nat -> list (bv 8))
      (inum : bv 16) (s : list (bv 8)) (k0 tot : nat) :
    (2 <= tot)%nat ->
    bv_unsigned inum = self ->
    (forall x : nat,
       file_byte data' x
       = if decide ((16 * k0 <= x)%nat /\ (x < 16 * k0 + tot)%nat)
         then dirent_bytes (de_of_name inum s) !!! (x - 16 * k0)%nat
         else file_byte data x) ->
    ⊢ dir_link_at self dn data' k0.
  Proof.
    intros Htot Hself Hrng.
    assert (Hrec : dir_inum data' k0 = inum).
    { rewrite (dir_inum_of_two data' k0 (de_of_name inum s)); [reflexivity |].
      intros jj Hjj. rewrite (Hrng (16 * k0 + jj)%nat).
      rewrite decide_True; [| lia].
      replace (16 * k0 + jj - 16 * k0)%nat with jj by lia. reflexivity. }
    rewrite /dir_link_at Hrec.
    rewrite (bool_decide_eq_true_2 (bv_unsigned inum = self) Hself).
    rewrite andb_false_r. done.
  Qed.

  (* ...AND THE NO-WRITE ARM.  writei's short-write break at [tot = 0] moves
     no byte and no size, so the whole big-op rides -- and this is the arm
     create's [fail:] takes when a dirlink could not allocate. *)
  Lemma dir_links_dirlink_nop (self : Z) (dn dn' : dinode)
      (data data' : nat -> list (bv 8))
      (inum : bv 16) (s : list (bv 8)) (nrec k0 : nat) :
    nrec = dir_nrec (bv_unsigned (di_size dn)) ->
    k0 = dir_slot data nrec ->
    di_type dn' = di_type dn ->
    di_nlink dn' = di_nlink dn ->
    bv_unsigned (di_size dn')
      = Z.max (bv_unsigned (di_size dn)) (Z.of_nat (16 * k0 + 0)) ->
    (forall x : nat,
       file_byte data' x
       = if decide ((16 * k0 <= x)%nat /\ (x < 16 * k0 + 0)%nat)
         then dirent_bytes (de_of_name inum s) !!! (x - 16 * k0)%nat
         else file_byte data x) ->
    dir_links self dn data -∗ dir_links self dn' data'.
  Proof.
    intros Hnrec Hk0 Hty Hnl Hsz Hrng.
    (* the range clause degenerates: EVERY byte agrees *)
    assert (Hall : forall x : nat, file_byte data' x = file_byte data x).
    { intros x. rewrite (Hrng x). rewrite decide_False; [reflexivity | lia]. }
    assert (Hagree : forall q : nat, dir_inum data' q = dir_inum data q).
    { intros q. unfold dir_inum. rewrite (Hall (16 * q)%nat).
      rewrite (Hall (16 * q + 1)%nat). reflexivity. }
    (* ...and so does the size: the slot is at or below the record count *)
    assert (Hsznn : 0 <= bv_unsigned (di_size dn))
      by exact (proj1 (bv_unsigned_in_range _ (di_size dn))).
    destruct (dir_nrec_range (bv_unsigned (di_size dn)) Hsznn) as [Hnr1 _].
    rewrite <- Hnrec in Hnr1.
    assert (Hk0le : (k0 <= nrec)%nat) by (rewrite Hk0; apply dir_slot_le).
    assert (Hszeq : bv_unsigned (di_size dn') = bv_unsigned (di_size dn))
      by lia.
    rewrite /dir_links Hty Hszeq.
    destruct (decide (bv_unsigned (di_type dn) = T_DIR_z)) as [_ | _];
      [| by iIntros "_"].
    iIntros "H". iDestruct "H" as (F) "(%Hbnd & %Hlow & Htie & H)".
    iExists F. iSplitR.
    { iPureIntro.
      apply (dlc_bound_le F F dn dn' data data'); [rewrite Hnl; lia | | exact Hbnd].
      rewrite Hszeq.
      rewrite (dlc_count_agree F F data data' _ Hagree ltac:(intro k; reflexivity)).
      lia. }
    iSplitR.
    { iPureIntro.
      apply (dlc_lower_eq F F dn dn' data data');
        [rewrite Hnl; reflexivity | | exact Hlow].
      rewrite Hszeq.
      rewrite (dlc_count_agree F F data data' _ Hagree ltac:(intro k; reflexivity)).
      lia. }
    (* V5': nothing the tie names moved at all -- the no-write arm writes
       no byte, no size and no count *)
    iSplitL "Htie".
    { iApply (dir_par_tie_cong self dn dn' data data'
                ltac:(rewrite Hnl; exact (fun H => H))
                ltac:(rewrite Hszeq; exact (fun H => H))
                (Hagree 1%nat) with "Htie"). }
    iApply (big_sepL_mono with "H"). intros i k Hik.
    iIntros "Hx".
    iApply (dir_link_at_f_agree F F self dn dn' data data' k Hnl (Hagree k)
              eq_refl with "Hx").
  Qed.

  (* ==================================================================== *)
  (*  (v') THE MKDIR DEPOSIT -- the one write that RAISES a directory's    *)
  (*       count, and the only producer of a d-flavoured record           *)
  (*       design: fs-fragments-campaign.md, V2                           *)
  (* ==================================================================== *)

  (* WHY IT IS ONE LEMMA AND NOT [dir_links_dirlink] THEN A COUNT MOVE.
     create's mkdir arm appends the child's record to the parent
     ([dirlink(dp, name, ip->inum)], +0x12c) and THEN raises the parent's
     count ([dp->nlink++], +0x134) -- and the clause's slack between the
     two steps is exactly one, held by the record just written.  Sealing
     the payload in between would existentially quantify the flavour map
     away and lose it: what comes back out of [dir_links] is "SOME [F] with
     the bound", which is a strictly weaker fact than "THIS [F], and the
     record at [k0] is set".  So the deposit and the [++] are crossed
     together, and the caller applies this where it holds both.

     ITS [nlink] PREMISE IS AN EQUALITY SINCE V4: [dlc_bound] alone needed
     only [<=] (the wrap lands at zero, below any bound), but [dlc_lower]
     needs the exact [+1] -- an [<=] would let the wrap under the clause.
     The caller derives it from the machine's [++] plus the flush's own
     nonzero read-back ([dlc_bv_add1_nz_eq]; the read-back is
     [IregLinkNz.ireg_link_nz] at the bumped record, which create's site
     already fires for [dir_orphan_clean]) -- still no (L4) and no kernel
     guard.

     [2 <= k0] IS NOT A PREMISE: [dir_dots_ix] says records 0 and 1 are
     live, and [dir_slot] never returns a live record below the count, so
     the slot the append landed on is at 2 or past the end.  That argument
     is made HERE rather than at the caller because both facts are already
     in this lemma's hypothesis list. *)
  Lemma dir_links_dirlink_d (self : Z) (dn dn' : dinode)
      (data data' : nat -> list (bv 8))
      (inum : bv 16) (s : list (bv 8)) (nrec k0 tot : nat) :
    nrec = dir_nrec (bv_unsigned (di_size dn)) ->
    k0 = dir_slot data nrec ->
    (* THE WHOLE RECORD, and unlike [dir_links_dirlink] this one cannot take
       [tot < 16]: at a SHORT write the appended record falls outside the
       new [dir_nrec] and is not counted, while [dp->nlink] rises anyway.
       create's ARM C-OK-DIR is the [tot = 16] arm by construction (it is
       the arm the [bltz] fell through on), so the premise costs its one
       caller nothing. *)
    tot = 16%nat ->
    bv_unsigned (di_type dn) = T_DIR_z ->
    bv_unsigned (di_nlink dn) <> 0 ->
    dir_dots_ix self dn data ->
    (* the child is a real inode, and it is not the parent itself *)
    inum <> bv_0 16 ->
    bv_unsigned inum <> self ->
    di_type dn' = di_type dn ->
    bv_unsigned (di_nlink dn') = bv_unsigned (di_nlink dn) + 1 ->
    bv_unsigned (di_size dn')
      = Z.max (bv_unsigned (di_size dn)) (Z.of_nat (16 * k0 + tot)) ->
    (forall x : nat,
       file_byte data' x
       = if decide ((16 * k0 <= x)%nat /\ (x < 16 * k0 + tot)%nat)
         then dirent_bytes (de_of_name inum s) !!! (x - 16 * k0)%nat
         else file_byte data x) ->
    (* V5' increment P: THE DEPOSITED TICKET IS THE **TAGGED** UNIT, AND ITS
       TAG IS THIS DIRECTORY.  The slot is at 2 or past the end (proved
       below off [dir_dots_ix]), so it is a NAME record, and a name record
       naming a directory is create's mkdir output: the child's parent IS
       [self].  The caller pays with the [ilinkdp] half of the mint at
       [ip->nlink = 1]; the other half ([iparent]) goes to the child's own
       tie through [dir_links_dirlink_dot]. *)
    ilinkdp (bv_unsigned inum) self -∗
    dir_links self dn data -∗ dir_links self dn' data'.
  Proof.
    intros Hnrec Hk0 Ht16 Hty Hnlnz Hddix Hinz Hself Hty' Hnl Hsz Hrng.
    assert (Htot2 : (2 <= tot)%nat) by lia.
    (* ---- the record the write installed ---- *)
    assert (Hrec : dir_inum data' k0 = inum).
    { rewrite (dir_inum_of_two data' k0 (de_of_name inum s)); [reflexivity |].
      intros jj Hjj. rewrite (Hrng (16 * k0 + jj)%nat).
      rewrite decide_True; [| lia].
      replace (16 * k0 + jj - 16 * k0)%nat with jj by lia. reflexivity. }
    (* ---- the slot is at 2 or past the end (see the banner) ---- *)
    destruct (Hddix Hty Hnlnz) as (Hnr2 & Hlv0 & _ & _ & Hlv1 & _).
    rewrite <- Hnrec in Hnr2.
    assert (Hk2 : (2 <= k0)%nat).
    { destruct (Nat.lt_ge_cases k0 2) as [Hlt | Hge]; [| exact Hge]. exfalso.
      assert (Hfree : dir_inum data k0 = bv_0 16)
        by (rewrite Hk0; apply dir_slot_free; rewrite <- Hk0; lia).
      destruct k0 as [| k1]; [exact (Hlv0 Hfree) |].
      destruct k1 as [| k2]; [exact (Hlv1 Hfree) | lia]. }
    (* ---- the count arithmetic, [dir_links_dirlink]'s verbatim ---- *)
    assert (Hsznn : 0 <= bv_unsigned (di_size dn))
      by exact (proj1 (bv_unsigned_in_range _ (di_size dn))).
    assert (Hsznn' : 0 <= bv_unsigned (di_size dn'))
      by exact (proj1 (bv_unsigned_in_range _ (di_size dn'))).
    destruct (dir_nrec_range (bv_unsigned (di_size dn)) Hsznn) as [Hnr1 Hnr2'].
    destruct (dir_nrec_range (bv_unsigned (di_size dn')) Hsznn')
      as [Hnr1' Hnr2''].
    rewrite <- Hnrec in Hnr1, Hnr2'.
    assert (Hk0le : (k0 <= nrec)%nat) by (rewrite Hk0; apply dir_slot_le).
    assert (Hcalt : dir_nrec (bv_unsigned (di_size dn')) = nrec
                    \/ (dir_nrec (bv_unsigned (di_size dn')) = S nrec
                        /\ k0 = nrec /\ tot = 16%nat)) by lia.
    (* the appended record IS in range: a WHOLE record at [k0] pushes the
       size to at least [16*(k0+1)] *)
    assert (Hk0lt : (k0 < dir_nrec (bv_unsigned (di_size dn')))%nat).
    { pose proof Hnr2'' as Hx. rewrite Hsz in Hx. lia. }
    assert (Hagree : forall q : nat, q <> k0 ->
                       dir_inum data' q = dir_inum data q).
    { intros q Hq. unfold dir_inum.
      rewrite (Hrng (16 * q)%nat). rewrite (Hrng (16 * q + 1)%nat).
      rewrite decide_False; [| lia]. rewrite decide_False; [| lia].
      reflexivity. }
    assert (Hslot : (k0 < nrec)%nat -> dir_inum data k0 = bv_0 16).
    { intro Hlt. rewrite Hk0. apply dir_slot_free. rewrite <- Hk0. exact Hlt. }
    (* ---- and the payload ---- *)
    rewrite /dir_links Hty' decide_True; [| exact Hty].
    rewrite decide_True; [| exact Hty].
    rewrite <- Hnrec.
    iIntros "Hd H". iDestruct "H" as (F) "(%Hbnd & %Hlow & Htie & H)".
    destruct (dlc_upd_map F k0 true) as (G & HGk0 & HGoff).
    assert (Hcalt2 : dir_nrec (bv_unsigned (di_size dn')) = nrec
                     \/ (dir_nrec (bv_unsigned (di_size dn')) = S nrec
                         /\ k0 = nrec))
      by (destruct Hcalt as [H1 | (H1 & H2 & _)]; [left; exact H1
                                                  | right; split; assumption]).
    iExists G. iSplitR.
    { iPureIntro.
      apply (dlc_bound_bump F G dn dn' data data');
        [rewrite Hnl; lia | | exact Hbnd].
      rewrite <- Hnrec.
      apply (dlc_count_set_ge F G data data' nrec _ k0);
        [ destruct Hcalt as [H | (H & _ & _)]; lia
        | exact Hk2 | exact Hk0lt | exact Hagree | exact HGoff | exact Hslot
        | rewrite /dir_live Hrec; exact Hinz
        | exact HGk0 ]. }
    (* V4: THE LOWER CLAUSE -- both sides rise by EXACTLY one: the count
       by the flipped-on slot (at most one, [dlc_count_set_le]) and the
       home by the exact increment premise *)
    iSplitR.
    { iPureIntro.
      apply (dlc_lower_bump F G dn dn' data data' Hnlnz Hnl); [| exact Hlow].
      rewrite <- Hnrec.
      apply (dlc_count_set_le F G data data' nrec _ k0 Hcalt2 Hagree HGoff). }
    (* V5': THE PARENT TIE RIDES.  Record 1's bytes did not move ([2 <= k0]),
       the record count only grew and was already at least 2 (the dots
       clause), and the home's count rose from nonzero. *)
    iSplitL "Htie".
    { assert (Htnl : bv_unsigned (di_nlink dn') <> 0 ->
                     bv_unsigned (di_nlink dn) <> 0)
        by (intros _; exact Hnlnz).
      assert (Htnr : (2 <= dir_nrec (bv_unsigned (di_size dn')))%nat ->
                     (2 <= dir_nrec (bv_unsigned (di_size dn)))%nat)
        by (intros _; rewrite <- Hnrec; exact Hnr2).
      assert (Ht1 : dir_inum data' 1 = dir_inum data 1)
        by (apply Hagree; lia).
      iApply (dir_par_tie_cong self dn dn' data data' Htnl Htnr Ht1
                with "Htie"). }
    (* the deposited ticket, at its own flavour -- TAGGED, since [2 <= k0] *)
    iAssert (dir_link_at_f G self dn' data' k0) with "[Hd]" as "Hk0".
    { iApply (dir_link_at_f_dirlink G self dn' data data' inum s k0 tot
                Htot2 Hrng with "[Hd]").
      rewrite HGk0.
      iApply (dlc_tick_name_in self k0 true (bv_unsigned inum) Hk2
                with "Hd"). }
    destruct Hcalt as [Hn' | (Hn' & Hkn & _)]; rewrite Hn'.
    - destruct (Nat.lt_ge_cases k0 nrec) as [Hlt | Hge].
      + rewrite (big_sepL_delete
                   (fun _ k => dir_link_at_f G self dn' data' k)
                   (seq 0 nrec) k0 k0).
        2:{ apply lookup_seq; lia. }
        iSplitL "Hk0"; [iExact "Hk0" |].
        iApply (big_sepL_mono with "H"). intros i k Hik.
        apply lookup_seq in Hik. destruct Hik as [Hk Hi].
        destruct (decide (i = k0)) as [_ | Hne]; [by iIntros "_" |].
        iIntros "Hx".
        iApply (dir_link_at_f_live_agree F G self dn dn' data data' k Hnlnz
                  ltac:(apply Hagree; lia) ltac:(apply HGoff; lia) with "Hx").
      + exfalso. lia.
    - rewrite seq_S big_sepL_app. iSplitL "H".
      + iApply (big_sepL_mono with "H"). intros i k Hik.
        apply lookup_seq in Hik. destruct Hik as [Hk Hi].
        iIntros "Hx".
        iApply (dir_link_at_f_live_agree F G self dn dn' data data' k Hnlnz
                  ltac:(apply Hagree; lia) ltac:(apply HGoff; lia) with "Hx").
      + simpl. iSplitL "Hk0"; [| done]. rewrite <- Hkn. iExact "Hk0".
  Qed.

  (* ==================================================================== *)
  (*  (v'') THE DOT DEPOSIT -- a d-flavoured ticket at a DOT slot, and     *)
  (*        the count does not move (V4; V5''s fusion point)              *)
  (* ==================================================================== *)

  (* create's mkdir writes the child's [".."] at index 1, and since V4's
     flip the ticket it deposits is the [ilinkd dp] the [dp->nlink++]
     minted -- d-flavoured, because [dp] IS a directory.  [DirView.dlc_ctb]
     refuses the two dot indices whatever the flavour map says, so the
     deposit is COUNT-NEUTRAL on both clauses and the home's [nlink] does
     not move.  The V5' successor extends this same lemma with the
     [".."]-tie's establishment (the [iparent] half plus the bytes just
     written); it is the one place both halves of the tagged mint meet
     the payload.

     V5' LANDED THAT FUSION, and with it the lemma is pinned to [k0 = 1]:
     the [".."] is the ONLY dot record that carries a ticket at all (index
     0 is the self record, whose ticket is [emp] and whose constructor is
     [dir_link_at_dirlink_self]), and it is index 1 that the tie names.  So
     this lemma takes BOTH halves the mint at [ip->nlink = 1] paid out --
     the [ilinkd] for the record and the [iparent] for the tie -- and the
     tie's guard turns true at exactly this write, because it is this write
     that pushes the child's record count to 2. *)
  Lemma dir_links_dirlink_dot (self : Z) (dn dn' : dinode)
      (data data' : nat -> list (bv 8))
      (inum : bv 16) (s : list (bv 8)) (nrec k0 tot : nat) :
    nrec = dir_nrec (bv_unsigned (di_size dn)) ->
    k0 = dir_slot data nrec ->
    k0 = 1%nat ->
    (2 <= tot)%nat -> (tot <= 16)%nat ->
    di_type dn' = di_type dn ->
    di_nlink dn' = di_nlink dn ->
    bv_unsigned (di_size dn')
      = Z.max (bv_unsigned (di_size dn)) (Z.of_nat (16 * k0 + tot)) ->
    (forall x : nat,
       file_byte data' x
       = if decide ((16 * k0 <= x)%nat /\ (x < 16 * k0 + tot)%nat)
         then dirent_bytes (de_of_name inum s) !!! (x - 16 * k0)%nat
         else file_byte data x) ->
    ilinkd (bv_unsigned inum) -∗
    iparent self (bv_unsigned inum) -∗
    dir_links self dn data -∗ dir_links self dn' data'.
  Proof.
    intros Hnrec Hk0 Hk02 Htot2 Htot16 Hty Hnl Hsz Hrng.
    (* the record the write installed -- this is what the tie is about *)
    assert (Hrec : dir_inum data' k0 = inum).
    { rewrite (dir_inum_of_two data' k0 (de_of_name inum s)); [reflexivity |].
      intros jj Hjj. rewrite (Hrng (16 * k0 + jj)%nat).
      rewrite decide_True; [| lia].
      replace (16 * k0 + jj - 16 * k0)%nat with jj by lia. reflexivity. }
    assert (Hrec1 : dir_inum data' 1%nat = inum)
      by (rewrite <- Hk02; exact Hrec).
    (* the type is unmoved, so the two big-ops are both live or both [emp] *)
    rewrite /dir_links Hty.
    destruct (decide (bv_unsigned (di_type dn) = T_DIR_z)) as [_ | _];
      [| iIntros "_ _ _"; done].
    (* ---- the count arithmetic, [dir_links_dirlink]'s verbatim ---- *)
    assert (Hsznn : 0 <= bv_unsigned (di_size dn))
      by exact (proj1 (bv_unsigned_in_range _ (di_size dn))).
    assert (Hsznn' : 0 <= bv_unsigned (di_size dn'))
      by exact (proj1 (bv_unsigned_in_range _ (di_size dn'))).
    destruct (dir_nrec_range (bv_unsigned (di_size dn)) Hsznn) as [Hnr1 Hnr2].
    destruct (dir_nrec_range (bv_unsigned (di_size dn')) Hsznn')
      as [Hnr1' Hnr2'].
    rewrite <- Hnrec in Hnr1, Hnr2.
    assert (Hk0le : (k0 <= nrec)%nat) by (rewrite Hk0; apply dir_slot_le).
    assert (Hcalt : dir_nrec (bv_unsigned (di_size dn')) = nrec
                    \/ (dir_nrec (bv_unsigned (di_size dn')) = S nrec
                        /\ k0 = nrec /\ tot = 16%nat)) by lia.
    assert (Hagree : forall q : nat, q <> k0 ->
                       dir_inum data' q = dir_inum data q).
    { intros q Hq. unfold dir_inum.
      rewrite (Hrng (16 * q)%nat). rewrite (Hrng (16 * q + 1)%nat).
      rewrite decide_False; [| lia]. rewrite decide_False; [| lia].
      reflexivity. }
    assert (Hslot : (k0 < nrec)%nat -> dir_inum data k0 = bv_0 16).
    { intro Hlt. rewrite Hk0. apply dir_slot_free. rewrite <- Hk0. exact Hlt. }
    assert (Hcalt2 : dir_nrec (bv_unsigned (di_size dn')) = nrec
                     \/ (dir_nrec (bv_unsigned (di_size dn')) = S nrec
                         /\ k0 = nrec))
      by (destruct Hcalt as [H1 | (H1 & H2 & _)]; [left; exact H1
                                                  | right; split; assumption]).
    rewrite <- Hnrec.
    iIntros "Hd Hpar H". iDestruct "H" as (F) "(%Hbnd & %Hlow & Htie & H)".
    (* THE INPUT TIE IS DROPPED, NOT CARRIED.  Before this write the child
       has one record (the ["."]), so the input guard is false and the
       conjunct is [emp]; and even where it is not, the record the tie names
       is the one being written.  The OUTPUT tie is built from the half the
       caller hands in. *)
    iClear "Htie".
    destruct (dlc_upd_map F k0 true) as (G & HGk0 & HGoff).
    (* the DOT index is refused by the counter at any flavour *)
    assert (Hctb : dlc_ctb G data' k0 = false)
      by exact (dlc_ctb_dot G data' k0 ltac:(lia)).
    iExists G. iSplitR.
    { iPureIntro.
      apply (dlc_bound_le F G dn dn' data data'); [rewrite Hnl; lia | | exact Hbnd].
      rewrite <- Hnrec.
      apply (dlc_count_slot_ge F G data data' nrec _ k0); [| exact Hagree
                                                           | exact HGoff
                                                           | exact Hslot].
      destruct Hcalt as [Hn' | (Hn' & _ & _)]; lia. }
    iSplitR.
    { iPureIntro.
      apply (dlc_lower_eq F G dn dn' data data');
        [rewrite Hnl; reflexivity | | exact Hlow].
      rewrite <- Hnrec.
      apply (dlc_count_ctb_le F G data data' nrec _ k0 Hcalt2 Hagree HGoff
               Hctb). }
    (* V5': **THE TIE IS ESTABLISHED HERE**, and this is the only site in
       the tree that establishes it.  [pv] is the inum just written into
       record 1, the half is the one the child's own mint paid out, and the
       pure conjunct is the bytes read back off the write. *)
    iSplitL "Hpar".
    { rewrite /dir_par_tie.
      destruct (decide (bv_unsigned (di_nlink dn') <> 0
                        /\ (2 <= dir_nrec (bv_unsigned (di_size dn')))%nat
                        /\ self <> dl_root)) as [_ | _];
        [| iClear "Hpar"; done].
      iExists (bv_unsigned inum). iSplitL "Hpar"; [iExact "Hpar" |].
      iPureIntro. rewrite Hrec1. reflexivity. }
    (* the deposited ticket, at its own flavour -- UNTAGGED, since the
       [".."] pays for the PARENT's count, never for this directory's *)
    iAssert (dir_link_at_f G self dn' data' k0) with "[Hd]" as "Hk0".
    { iApply (dir_link_at_f_dirlink G self dn' data data' inum s k0 tot
                Htot2 Hrng with "[Hd]").
      rewrite HGk0.
      iApply (dlc_tick_dot_in self k0 true (bv_unsigned inum) ltac:(lia)
                with "Hd"). }
    destruct Hcalt as [Hn' | (Hn' & Hkn & _)]; rewrite Hn'.
    - destruct (Nat.lt_ge_cases k0 nrec) as [Hlt | Hge].
      + rewrite (big_sepL_delete
                   (fun _ k => dir_link_at_f G self dn' data' k)
                   (seq 0 nrec) k0 k0).
        2:{ apply lookup_seq; lia. }
        iSplitL "Hk0"; [iExact "Hk0" |].
        iApply (big_sepL_mono with "H"). intros i k Hik.
        apply lookup_seq in Hik. destruct Hik as [Hk Hi].
        destruct (decide (i = k0)) as [_ | Hne]; [by iIntros "_" |].
        iIntros "Hx".
        iApply (dir_link_at_f_agree F G self dn dn' data data' k Hnl
                  ltac:(apply Hagree; lia) ltac:(apply HGoff; lia) with "Hx").
      + (* the written slot is at or past the end: nothing in range moved,
           and the ticket is dropped (affine) *)
        iClear "Hk0".
        iApply (big_sepL_mono with "H"). intros i k Hik.
        apply lookup_seq in Hik. destruct Hik as [Hk Hi].
        iIntros "Hx".
        iApply (dir_link_at_f_agree F G self dn dn' data data' k Hnl
                  ltac:(apply Hagree; lia) ltac:(apply HGoff; lia) with "Hx").
    - rewrite seq_S big_sepL_app. iSplitL "H".
      + iApply (big_sepL_mono with "H"). intros i k Hik.
        apply lookup_seq in Hik. destruct Hik as [Hk Hi].
        iIntros "Hx".
        iApply (dir_link_at_f_agree F G self dn dn' data data' k Hnl
                  ltac:(apply Hagree; lia) ltac:(apply HGoff; lia) with "Hx").
      + simpl. iSplitL "Hk0"; [| done]. rewrite <- Hkn. iExact "Hk0".
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  (vi) THE THEOREM: A LIVE HOME HAS NO GREY RECORDS                   *)
  (*       design: fs-icache.md §20.17.7, option (iii)                    *)
  (* ------------------------------------------------------------------ *)

  (* the ticket with the grey disjunct GONE.  Named so the consumer's
     statement is two lines rather than an [if] inside a big-op inside an
     [if]. *)
  Definition dir_ilink_at (F : nat -> bool) (self : Z)
      (data : nat -> list (bv 8)) (k : nat) : iProp Σ :=
    (if dir_liveb data k
        && negb (bool_decide (bv_unsigned (dir_inum data k) = self))
     then dlc_tick self k (F k) (bv_unsigned (dir_inum data k))
     else emp)%I.

  (* the payload with the grey colour gone, named so the round trip
     [dir_links_live] ; <the write> ; [dir_links_of_ilink] is two lines at
     the caller.  IT CARRIES THE FLAVOUR MAP: the count clause is stated
     about it, so an opener that means to re-seal must keep [F] rather than
     collapse the tickets to a colourless form (V2). *)
  Definition dir_ilinks (F : nat -> bool) (self : Z) (dn : dinode)
      (data : nat -> list (bv 8)) : iProp Σ :=
    (if decide (bv_unsigned (di_type dn) = T_DIR_z)
     then dir_par_tie self dn data ∗
          ([∗ list] k ∈ seq 0 (dir_nrec (bv_unsigned (di_size dn))),
             dir_ilink_at F self data k)
     else emp)%I.

  (* THIS IS D2's FIX, FORMALISED.  Grey now carries [di_nlink dn = 0]
     (see [dir_link_at]'s header), so under a LIVE home the right disjunct
     is refuted where it stands and every record's ticket collapses to the
     allocatedness witness.  The guard the caller supplies is exactly the
     [c.beqz] it just fell through. *)
  Lemma dir_link_at_live (F : nat -> bool) (self : Z) (dn : dinode)
      (data : nat -> list (bv 8)) (k : nat) :
    bv_unsigned (di_nlink dn) <> 0 ->
    dir_link_at_f F self dn data k -∗ dir_ilink_at F self data k.
  Proof.
    intros Hnz. rewrite /dir_link_at_f /dir_ilink_at.
    destruct (dir_liveb data k
              && negb (bool_decide (bv_unsigned (dir_inum data k) = self)));
      [| by iIntros "_"].
    iIntros "[H | [_ %Hz]]"; [iExact "H" | destruct (Hnz Hz)].
  Qed.

  (* ...and the payload-level lift, which is what a walk holding
     [ic_loaded]'s [dir_links] applies.  IT HANDS THE FLAVOUR MAP AND THE
     BOUND OUT (V2): a caller that re-seals with [dir_links_of_ilink] owes
     the clause at its OWN record, and the only way to owe it is to know
     which [F] the tickets are at. *)
  Lemma dir_links_live (self : Z) (dn : dinode)
      (data : nat -> list (bv 8)) :
    bv_unsigned (di_nlink dn) <> 0 ->
    dir_links self dn data -∗
      ∃ F : nat -> bool,
        ⌜bv_unsigned (di_type dn) = T_DIR_z -> dlc_bound F dn data⌝
        ∗ ⌜bv_unsigned (di_type dn) = T_DIR_z -> dlc_lower F dn data⌝
        ∗ dir_ilinks F self dn data.
  Proof.
    intros Hnz. rewrite /dir_links /dir_ilinks.
    destruct (decide (bv_unsigned (di_type dn) = T_DIR_z)) as [Hd | Hd];
      [| iIntros "_"; iExists (fun _ => false); iSplitR;
         [iPureIntro; intro Hc; exfalso; exact (Hd Hc) |
          iSplitR; [iPureIntro; intro Hc; exfalso; exact (Hd Hc) | done]]].
    iIntros "H". iDestruct "H" as (F) "(%Hbnd & %Hlow & Htie & H)".
    iExists F. iSplitR; [iPureIntro; intros _; exact Hbnd |].
    iSplitR; [iPureIntro; intros _; exact Hlow |].
    iSplitL "Htie"; [iExact "Htie" |].
    iApply (big_sepL_mono with "H"). intros i k Hik.
    iIntros "Hx". iApply (dir_link_at_live F self dn data k Hnz with "Hx").
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  ...AND BACK.  THE WRITE-BACK HALF OF THE SAME THEOREM              *)
  (*     design: fs-icache.md §20.18's C1 layer                          *)
  (* ------------------------------------------------------------------ *)

  (* [dir_links_live] takes a payload's tickets apart under a LIVE home and
     hands back the colourless [dir_ilink_at] form; a walk that then WRITES
     the directory has to put them back, and B' landed only the outbound
     half.  The return trip needs no hypothesis at all, because the ticket's
     LEFT disjunct is [dn]-free: an [ilink] is a claim about the record's
     TARGET and says nothing about the home, so it re-enters the two-colour
     ticket at ANY [dn'] -- including the one create's [dp->nlink++] has
     just moved.  That is what makes the round trip
     [dir_links_live] ; <the write> ; [dir_links_of_ilink] type-check
     across an nlink change, which is exactly create's shape. *)
  Lemma dir_link_at_of_ilink (F : nat -> bool) (self : Z) (dn' : dinode)
      (data : nat -> list (bv 8)) (k : nat) :
    dir_ilink_at F self data k -∗ dir_link_at_f F self dn' data k.
  Proof.
    rewrite /dir_link_at_f /dir_ilink_at.
    destruct (dir_liveb data k
              && negb (bool_decide (bv_unsigned (dir_inum data k) = self)));
      [| by iIntros "_"].
    iIntros "H". iLeft. iExact "H".
  Qed.

  (* ...and the payload-level lift, [dir_links_live]'s exact inverse.  ITS
     RETURN LEG TAKES THE COUNT CLAUSE (V2), at the record it re-seals at
     and at the flavour map it was opened with: the tickets are unmoved, so
     the only thing that can have changed is the home's own [nlink], which
     is exactly what the clause bounds. *)
  Lemma dir_links_of_ilink (F : nat -> bool) (self : Z) (dn' : dinode)
      (data : nat -> list (bv 8)) :
    dlc_bound F dn' data ->
    dlc_lower F dn' data ->
    dir_ilinks F self dn' data -∗ dir_links self dn' data.
  Proof.
    intros Hbnd Hlow. rewrite /dir_links /dir_ilinks.
    destruct (decide (bv_unsigned (di_type dn') = T_DIR_z)) as [_ | _];
      [| by iIntros "_"].
    iIntros "[Htie H]". iExists F. iSplitR; [iPureIntro; exact Hbnd |].
    iSplitR; [iPureIntro; exact Hlow |].
    iSplitL "Htie"; [iExact "Htie" |].
    iApply (big_sepL_mono with "H"). intros i k Hik.
    iIntros "Hx". iApply (dir_link_at_of_ilink F self dn' data k with "Hx").
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  (vii) THE ALGEBRA'S INVERSE: THE EDGE-DELETE CONSTRUCTOR            *)
  (*        design: claude-notes/design/fs-fragments.md R9 / §6           *)
  (*                fs-icache.md §20.6's sys_unlink row                   *)
  (* ------------------------------------------------------------------ *)

  (* WHY THIS IS OWED, AND WHY IT LANDS AHEAD OF ITS CALLER.  Insert has a
     full resource story here ([dir_link_at_dirlink] and its two siblings)
     and delete has only the REFCOUNT half: [InodeRegion.ireg_write_unlink]
     is the kernel's one nlink-LOWERING region write and it CONSUMES an
     [ilink] as it lowers -- and it has no caller.  Nothing on THIS side
     ever released the ticket out of a zeroed record, so the fragment the
     region write demands could not be produced.  That asymmetry is the
     single clearest statement of why the constructor is owed; these three
     lemmas close it.

     ITS CONSUMER IS S7-unlink's walk (V3), which is being written against
     the shape below; the fragment layer above ([FsRep.v]) is the other
     future one. *)

  (* THE EMPTIED SLOT CARRIES NOTHING.  A record whose inum halfword is zero
     is exactly what [dir_liveb] -- and hence [dirlookup]'s scan -- skips,
     so its ticket is [emp] and is free.  This is the delete-side twin of
     [dir_links_size_zero]: the resource does not have to be found, it has
     to be shown absent. *)
  Lemma dir_link_at_zeroed (self : Z) (dn' : dinode)
      (data' : nat -> list (bv 8)) (k0 : nat) :
    dir_inum data' k0 = bv_0 16 ->
    ⊢ dir_link_at self dn' data' k0.
  Proof.
    intros Hz. rewrite /dir_link_at /dir_liveb /dir_freeb Hz.
    rewrite (bool_decide_eq_true_2 (bv_0 16 = bv_0 16) eq_refl).
    cbn [negb andb]. done.
  Qed.

  (* ...at any flavour, since a dead record's ticket is [emp] whatever [F]
     says about it *)
  Lemma dir_link_at_f_zeroed (F : nat -> bool) (self : Z) (dn' : dinode)
      (data' : nat -> list (bv 8)) (k0 : nat) :
    dir_inum data' k0 = bv_0 16 ->
    ⊢ dir_link_at_f F self dn' data' k0.
  Proof.
    intros Hz. rewrite /dir_link_at_f /dir_liveb /dir_freeb Hz.
    rewrite (bool_decide_eq_true_2 (bv_0 16 = bv_0 16) eq_refl).
    cbn [negb andb]. done.
  Qed.

  (* ...AND THE SELF RECORD, which is [ "." ] and is ticket-free by the
     exemption at the top of this file.  ([ProofSysUnlinkParts.su_link_self]
     is its plain twin; this is the form [dir_links_orphan] needs.) *)
  Lemma dir_link_at_f_self (F : nat -> bool) (self : Z) (dn' : dinode)
      (data' : nat -> list (bv 8)) (k0 : nat) :
    bv_unsigned (dir_inum data' k0) = self ->
    ⊢ dir_link_at_f F self dn' data' k0.
  Proof.
    intros Hs. rewrite /dir_link_at_f.
    rewrite (bool_decide_eq_true_2
               (bv_unsigned (dir_inum data' k0) = self) Hs).
    rewrite andb_false_r. done.
  Qed.

  (* **THE HALF [dir_links_unlink] IS BUILT ON, AND THE INVERSE OF
     [dir_link_at_dirlink].**  A live non-self record under a LIVE home
     carries its own [ilink_fl] and nothing else -- the grey disjunct is refuted
     where it stands, exactly as in [dir_link_at_live] -- so removing the
     record RELEASES that [ilink], which is precisely the fragment
     [ireg_write_unlink] consumes as it lowers the target's [nlink].

     The home-live premise is not a convenience: a GREY record's target has
     [di_nlink = 0] already and there is no count to lower, so the
     conversion S7 performs there is a different move (§20.17.4) and not
     this one. *)
  Lemma dir_link_at_unlink (F : nat -> bool) (self : Z) (dn : dinode)
      (data : nat -> list (bv 8)) (k0 : nat) :
    bv_unsigned (di_nlink dn) <> 0 ->
    dir_live data k0 ->
    bv_unsigned (dir_inum data k0) <> self ->
    dir_link_at_f F self dn data k0 -∗
      dlc_tick self k0 (F k0) (bv_unsigned (dir_inum data k0)).
  Proof.
    intros Hnl Hlv Hself. iIntros "H".
    iDestruct (dir_link_at_live F self dn data k0 Hnl with "H") as "H".
    rewrite /dir_ilink_at.
    rewrite (proj2 (dir_liveb_true data k0) Hlv).
    rewrite (bool_decide_eq_false_2
               (bv_unsigned (dir_inum data k0) = self) Hself).
    cbn [negb andb]. iExact "H".
  Qed.

  (* **THE PAYLOAD-LEVEL DELETE, [dir_links_dirlink]'s exact inverse.**
     sys_unlink's [memset(&de,0,sizeof(de)); writei(dp,0,&de,off,sizeof(de))]
     writes a ZERO-INUM record over slot [k0]; the record count does not
     move (the write is inside the existing size), every other slot's inum
     halfword rides by [dir_link_at_f_live_agree], the written slot's
     ticket becomes free by [dir_link_at_f_zeroed], and the ticket the old
     record held falls out for the caller to spend at
     [ireg_write_unlink_fl].

     The premises are the same shape as [dir_links_dirlink]'s -- the range
     clause writei's kernel arm actually delivers -- plus the three that
     make the released fragment an [ilink_fl] rather than a colour
     disjunction: the home is live, the record is live, and it is not the
     directory's own ["."].

     WHAT V2 CHANGED, AND IT IS THE WHOLE CONSUMER INTERFACE.  The released
     ticket comes out AT THE RECORD'S OWN FLAVOUR, existentially -- the
     caller cannot choose it, because the payload's flavour map is
     existential -- and the re-park is a WAND whose premise prices exactly
     what the zeroing costs the count clause:

       * at [b = false] the count does not move and the caller's [nlink]
         must not move either.  sys_unlink's FILE arm gets there by
         REFUTING [b = true]: it holds [ilinkd] of a record whose type it
         has just tested at the [beq] on +0xb4, and
         [IregDirBit.ireg_dirbit_ty] reads the type off the fragment.
         The T_DIR arm refutes [b = false] through the MIRROR,
         [IregDirBit.ireg_link_not_dir] off (T1') -- V4's whole point.
       * at [b = true] the count falls by one and the caller owes one unit
         of [nlink] -- which is exactly the [dp->nlink--] the T_DIR arm
         performs, so the arm pays with the instruction it was going to
         execute anyway.

     THE WAND'S PREMISE IS AN EQUALITY SINCE V4 ([dlc_lower] rides in the
     payload, so the zeroing must account for the count EXACTLY): at
     [b = false] the home did not move, at [b = true] it fell by exactly
     one.  Both landed consumers have it -- the FILE arm re-parks the
     SAME record, the T_DIR arm decrements by exactly one -- and the
     T_DIR arm's [b = false] case, where the equality would be false, is
     the case (T1') refutes.

     [k0 <> 0] IS NEW WITH V4 for the same clause: at [b = true] the
     count falls only if the killed slot was COUNTED, and index 0 is a
     dot index.  Both consumers derive [kk ∉ {0,1}] off [dir_dots_ix]'s
     two name clauses already (VERDICT #3's move).

     The [di_nlink dn' = di_nlink dn] premise is GONE for the same reason
     as before: the tickets that ride across say nothing about the home
     (the grey disjunct is refuted by the live-home premise), so the only
     constraint left on the two counts is the wand's. *)
  Lemma dir_links_unlink (self : Z) (dn dn' : dinode)
      (data data' : nat -> list (bv 8))
      (d : dirent) (nrec k0 tot : nat) :
    bv_unsigned (di_type dn) = T_DIR_z ->
    nrec = dir_nrec (bv_unsigned (di_size dn)) ->
    (k0 < nrec)%nat ->
    (2 <= tot)%nat -> (tot <= 16)%nat ->
    de_inum d = bv_0 16 ->
    bv_unsigned (di_nlink dn) <> 0 ->
    dir_live data k0 ->
    bv_unsigned (dir_inum data k0) <> self ->
    (* ...AND IT IS NOT THE [".."] SLOT.  [DirView.dir_dots_ix] pins index
       1 as the parent entry, and S7 never zeroes it -- [namecmp] refuses
       [".."], so the record [sys_unlink] clears is always the one
       [dirlookup] matched on a caller-supplied name.  Additive: this lemma
       has no consumers yet, and the premise is what keeps the index bridge
       alive across the delete. *)
    k0 <> 0%nat ->
    k0 <> 1%nat ->
    di_type dn' = di_type dn ->
    di_size dn' = di_size dn ->
    (forall x : nat,
       file_byte data' x
       = if decide ((16 * k0 <= x)%nat /\ (x < 16 * k0 + tot)%nat)
         then dirent_bytes d !!! (x - 16 * k0)%nat
         else file_byte data x) ->
    (* V5': THE RELEASED TICKET COMES OUT **TAGGED** at [b = true].  The
       killed record is at index >= 2 (the two premises above), so it is a
       NAME record, and a name record naming a directory is create's mkdir
       output -- its unit is the parent-record unit and its tag is [self],
       spelled off this payload's own parameter.  That identity IS
       S7-unlink's (D1): joined against the child's own [iparent] half
       through [IcacheRef.iparent_agree], it says the child's [".."] names
       THIS directory. *)
    dir_links self dn data -∗
      ∃ b : bool,
        (if b then ilinkdp (bv_unsigned (dir_inum data k0)) self
         else ilink (bv_unsigned (dir_inum data k0)))
        ∗ (⌜(bv_unsigned (di_nlink dn') + (if b then 1 else 0)
             = bv_unsigned (di_nlink dn))%Z⌝ -∗ dir_links self dn' data').
  Proof.
    intros Hty Hnrec Hk0 Htot2 Htot16 Hde Hnl Hlv Hself Hk00 Hdd Hty' Hsz'
           Hrng.
    (* the written slot is dead: its two inum bytes came out of [d] *)
    assert (Hz : dir_inum data' k0 = bv_0 16).
    { rewrite (dir_inum_of_two data' k0 d); [exact Hde |].
      intros j Hj. rewrite (Hrng (16 * k0 + j)%nat).
      rewrite decide_True; [| lia].
      replace (16 * k0 + j - 16 * k0)%nat with j by lia. reflexivity. }
    (* ...and every other record keeps its two inum bytes *)
    assert (Hagree : forall q : nat, q <> k0 ->
                       dir_inum data' q = dir_inum data q).
    { intros q Hq. unfold dir_inum.
      rewrite (Hrng (16 * q)%nat). rewrite (Hrng (16 * q + 1)%nat).
      rewrite decide_False; [| lia]. rewrite decide_False; [| lia].
      reflexivity. }
    (* the type and the size are unmoved, so the two big-ops run over the
       same index range *)
    rewrite /dir_links Hty' Hsz'.
    destruct (decide (bv_unsigned (di_type dn) = T_DIR_z)) as [_ | Hnd];
      [| destruct (Hnd Hty)].
    rewrite <- Hnrec.
    iIntros "H". iDestruct "H" as (F) "(%Hbnd & %Hlow & Htie & H)".
    rewrite (big_sepL_delete (fun _ k => dir_link_at_f F self dn data k)
               (seq 0 nrec) k0 k0).
    2:{ apply lookup_seq. lia. }
    iDestruct "H" as "[Hk0 Hrest]".
    iExists (F k0). iSplitL "Hk0".
    { iDestruct (dir_link_at_unlink F self dn data k0 Hnl Hlv Hself
                   with "Hk0") as "Hk0".
      assert (Hk2 : (2 <= k0)%nat) by lia.
      iApply (dlc_tick_name_out self k0 (F k0)
                (bv_unsigned (dir_inum data k0)) Hk2 with "Hk0"). }
    iIntros "%Hcnt".
    (* the killed slot is DEAD on the new side, at any flavour *)
    assert (Hz'lb : dir_liveb data' k0 = false)
      by exact (proj2 (dir_liveb_false data' k0) Hz).
    iExists F. iSplitR.
    { (* THE COUNT CLAUSE ACROSS THE ZEROING.  The record at [k0] dies, so
         the right-hand side falls by at most one -- and by NOTHING unless
         [k0]'s ticket was d-flavoured, which is what the caller's premise
         pays for.  That is the whole asymmetry between sys_unlink's two
         arms: the file arm refutes the flavour and owes nothing, the T_DIR
         arm lowers [dp->nlink] by the one it owes. *)
      iPureIntro. unfold dlc_bound. rewrite Hsz'.
      pose proof (dlc_count_kill F data data'
                    (dir_nrec (bv_unsigned (di_size dn))) k0 Hagree) as Hk.
      unfold dlc_bound in Hbnd. destruct (F k0); lia. }
    (* V4: THE LOWER CLAUSE ACROSS THE ZEROING, priced by the same wand
       premise -- now an equality, so both arms balance exactly *)
    iSplitR.
    { iPureIntro. destruct (F k0) eqn:EFk0.
      - (* d-flavoured: the slot WAS counted (it is live, non-dot), so the
           count falls by exactly the one unit the home just paid *)
        assert (Hct : dlc_ctb F data k0 = true)
          by (apply dlc_ctb_true; [lia | exact Hlv | exact EFk0]).
        pose proof (dlc_count_kill_counted F data data'
                      (dir_nrec (bv_unsigned (di_size dn))) k0
                      ltac:(lia) Hagree Hct Hz'lb) as Hkc.
        unfold dlc_lower in Hlow |- *. rewrite Hsz'.
        intro Hnz'. pose proof (Hlow Hnl). cbn in Hcnt. lia.
      - (* plain: the slot was never counted, and the home did not move *)
        apply (dlc_lower_eq F F dn dn' data data');
          [cbn in Hcnt; lia | | exact Hlow].
        rewrite Hsz'.
        apply (dlc_count_ctb_le F F data data'
                 (dir_nrec (bv_unsigned (di_size dn))) _ k0
                 ltac:(left; reflexivity) Hagree
                 ltac:(intros k _; reflexivity)
                 (dlc_ctb_dead F data' k0 Hz'lb)). }
    (* V5': THE PARENT TIE RIDES.  The zeroing is at index >= 2, so record
       1's bytes are untouched; the size does not move, so neither does the
       record count; and the home's count only falls -- if it fell to zero
       the tie is not owed at all. *)
    iSplitL "Htie".
    { assert (Ht1 : dir_inum data' 1 = dir_inum data 1)
        by (apply Hagree; lia).
      iApply (dir_par_tie_cong self dn dn' data data'
                ltac:(intros _; exact Hnl)
                ltac:(rewrite Hsz'; exact (fun H => H)) Ht1 with "Htie"). }
    rewrite (big_sepL_delete (fun _ k => dir_link_at_f F self dn' data' k)
               (seq 0 nrec) k0 k0).
    2:{ apply lookup_seq. lia. }
    iSplitR "Hrest".
    - iApply (dir_link_at_f_zeroed F self dn' data' k0 Hz).
    - iApply (big_sepL_mono with "Hrest"). intros i k Hik.
      apply lookup_seq in Hik. destruct Hik as [Hk Hi].
      destruct (decide (i = k0)) as [_ | Hne]; [by iIntros "_" |].
      assert (Heq : dir_inum data' k = dir_inum data k)
        by (apply Hagree; lia).
      iIntros "Hx".
      iApply (dir_link_at_f_live_agree F F self dn dn' data data' k Hnl Heq
                eq_refl with "Hx").
  Qed.

  (* ==================================================================== *)
  (*  THE ".." EXTRACTION (fs-icache §20.17.4's owed fact, consumer side). *)
  (*                                                                      *)
  (*  S7's [dp->nlink--] must consume one [ilink dp].  This hands out the  *)
  (*  fragment at index 1 and takes the payload back, borrowing rather     *)
  (*  than destroying -- which is what the caller needs, since the record  *)
  (*  itself is NOT zeroed (namecmp refuses [".."]); only its colour       *)
  (*  changes, and that is §20.17.4's own conversion.                      *)
  (*                                                                      *)
  (*  IT DOES NOT NAME THE PARENT.  [dir_inum data 1] is whatever the      *)
  (*  child's [".."] holds; the tree layer supplies                        *)
  (*  [ents ip !! ".." = Some dp] and [DirView.dir_dots_ix] says that      *)
  (*  entry is at index 1 -- under [dir_names_unique] (FsRep, R2's         *)
  (*  amendment) any-match is first-match, so the two compose to           *)
  (*  [dir_inum data 1 = dp].  That last step is the tree layer's, not     *)
  (*  this file's.                                                        *)
  (*                                                                      *)
  (*  IT TAKES NO RECORD-COUNT PREMISE.  [dir_dots_ix] carries             *)
  (*  [2 <= dir_nrec] itself, under the SAME two guards this lemma already *)
  (*  needs for the ticket ([T_DIR] to open the big-op, [nlink <> 0] to    *)
  (*  make index 1's ticket an [ilink_fl] rather than a colour             *)
  (*  disjunction),                                                        *)
  (*  so the bound the [big_sepL_lookup_acc] wants is a projection rather  *)
  (*  than an obligation.  S7 supplies both guards from the kernel: the    *)
  (*  type test it branched on, and [if(ip->nlink < 1) panic].            *)
  (* ==================================================================== *)
  (*  ...AND SINCE V5' IT DOES NAME THE PARENT -- through the register, not *)
  (*  through the tree.  The payload's own tie hands out the [iparent]      *)
  (*  half beside the ticket, together with the pure fact that record 1's   *)
  (*  inum IS what that half reads.  The caller joins it against the        *)
  (*  [ilinkdp] half it holds from the PARENT's name record                 *)
  (*  ([dir_links_unlink]'s tagged release) with                            *)
  (*  [IcacheRef.iparent_agree], and (D1) falls with no region open and no  *)
  (*  tree fragment anywhere.  The comment above describes the route that   *)
  (*  DIED (fs-fragments-campaign V5' death certificate 1); it is kept      *)
  (*  because the circularity it names is the reason the register exists.   *)
  (*                                                                        *)
  (*  THE SELF-DISEQUALITY MOVED BEHIND THE TIE, and that ordering is the   *)
  (*  whole point.  A caller cannot know that record 1 does not name THIS    *)
  (*  directory until it knows WHO record 1 names -- which is (D1), which is *)
  (*  what the tie supplies.  So the tie comes out first, unconditionally,   *)
  (*  and the TICKET is behind a wand taking the disequality the caller then *)
  (*  derives.  Stating both under one premise list was circular.            *)
  (*                                                                        *)
  (*  THE TIE IS HANDED BACK BY THE RETURN LEG, so this stays an ACCESSOR:   *)
  (*  S7's T_DIR arm never uses that leg (its next park is the orphan,      *)
  (*  which owes no tie and whose [iparent] half has been SPENT at the      *)
  (*  child's own decrement), but a borrower that means to re-park the      *)
  (*  same record must have it.                                            *)
  Lemma dir_links_dotdot_out (self : Z) (dn : dinode)
      (data : nat -> list (bv 8)) :
    bv_unsigned (di_type dn) = T_DIR_z ->
    bv_unsigned (di_nlink dn) <> 0 ->
    dir_dots_ix self dn data ->
    self <> dl_root ->
    dir_links self dn data -∗
      ∃ pv : Z,
        iparent self pv
        ∗ ⌜bv_unsigned (dir_inum data 1) = pv⌝
        ∗ (⌜bv_unsigned (dir_inum data 1) <> self⌝ -∗
             ∃ b : bool,
               ilink_fl (dlc_fl b) (bv_unsigned (dir_inum data 1))
               ∗ (ilink_fl (dlc_fl b) (bv_unsigned (dir_inum data 1))
                  -∗ iparent self pv -∗ dir_links self dn data)).
  Proof.
    intros Hty Hnl Hdd Hroot.
    destruct (Hdd Hty Hnl) as (Hnrec & _ & _ & _ & Hlive & _).
    rewrite /dir_links decide_True; [| exact Hty].
    iIntros "H". iDestruct "H" as (F) "(%Hbnd & %Hlow & Htie & H)".
    iDestruct (dir_par_tie_open self dn data Hnl Hnrec Hroot with "Htie")
      as (pv) "[Hpar %Hpv]".
    iExists pv. iSplitL "Hpar"; [iExact "Hpar" |].
    iSplitR; [iPureIntro; exact Hpv |].
    iIntros "%Hself".
    iDestruct (big_sepL_lookup_acc _
                 (seq 0 (dir_nrec (bv_unsigned (di_size dn)))) 1%nat 1%nat
                 with "H") as "[H1 Hback]".
    { apply lookup_seq. lia. }
    (* THE BORROW IS AT THE RECORD'S OWN FLAVOUR, and it is the [".."]
       slot -- index 1, which [DirView.dlc_ctb] refuses whatever [F] says
       of it.  So neither count clause moves and the return leg needs
       no premise: a [".."] pays for the PARENT's count, never for this
       directory's.  At index 1 the ticket is the UNTAGGED d-unit, i.e.
       [ilink_fl (dlc_fl b)] -- the shape [SpecIupdate.wp_iupdate_unlink]
       takes, unchanged since V2. *)
    iExists (F 1%nat). iSplitL "H1".
    { iDestruct (dir_link_at_unlink F self dn data 1 Hnl Hlive Hself
                   with "H1") as "H1".
      iApply (dlc_tick_dot_out self 1%nat (F 1%nat)
                (bv_unsigned (dir_inum data 1)) ltac:(lia) with "H1"). }
    iIntros "Ht Hpar". iExists F. iSplitR; [iPureIntro; exact Hbnd |].
    iSplitR; [iPureIntro; exact Hlow |].
    iSplitL "Hpar".
    { iApply (dir_par_tie_close self dn data pv Hpv with "Hpar"). }
    iApply "Hback". rewrite /dir_link_at_f.
    rewrite (proj2 (dir_liveb_true data 1) Hlive).
    rewrite (bool_decide_eq_false_2
               (bv_unsigned (dir_inum data 1) = self) Hself).
    cbn [negb andb]. iLeft.
    iApply (dlc_tick_dot_in self 1%nat (F 1%nat)
              (bv_unsigned (dir_inum data 1)) ltac:(lia) with "Ht").
  Qed.

  (* ==================================================================== *)
  (*  **THE PAYOFF (S7-unlink FINDING 3).  AN EMPTY DIRECTORY'S COUNT IS   *)
  (*  AT MOST ONE, READ STRAIGHT OFF THE PAYLOAD.**                        *)
  (*                                                                      *)
  (*  This is what the whole carrier exists for.  The premise is exactly   *)
  (*  what sys_unlink's isdirempty loop concludes -- every record past the *)
  (*  two dots is free -- and the conclusion is the fact its T_DIR arm     *)
  (*  needs before the [ip->nlink--]: with the walk's own [blez]           *)
  (*  fall-through ([1 <= nlink]) it is [di_nlink ip = 1], which is        *)
  (*  [ProofSysUnlinkParts.su_dir_links_orphan]'s one unsupplied premise.  *)
  (*                                                                      *)
  (*  IT CONSUMES NOTHING.  The conclusion is pure, so a walk reads it off *)
  (*  its [ic_loaded] payload with [iDestruct … as %H] and still holds the *)
  (*  payload afterwards -- which matters, because the arm has to re-park  *)
  (*  that very payload two instructions later.                            *)
  (*                                                                      *)
  (*  GUARDED BY THE TYPE, like every other reading of this payload: at a  *)
  (*  non-directory the conjunct is [emp] and says nothing about [nlink]   *)
  (*  (a FILE's link count is not bounded by anything here).               *)
  (* ==================================================================== *)
  Lemma dir_links_empty_nlink (self : Z) (dn : dinode)
      (data : nat -> list (bv 8)) :
    (forall k : nat, (2 <= k)%nat ->
       (k < dir_nrec (bv_unsigned (di_size dn)))%nat ->
       dir_inum data k = bv_0 16) ->
    dir_links self dn data -∗
      ⌜bv_unsigned (di_type dn) = T_DIR_z ->
       bv_unsigned (di_nlink dn) <= 1⌝.
  Proof.
    intros Hdead. rewrite /dir_links.
    destruct (decide (bv_unsigned (di_type dn) = T_DIR_z)) as [Hd | Hd];
      [| iIntros "_"; iPureIntro; intro Hc; exfalso; exact (Hd Hc)].
    iIntros "H". iDestruct "H" as (F) "(%Hbnd & _ & _ & _)".
    iPureIntro. intros _. exact (dlc_bound_empty F dn data Hdead Hbnd).
  Qed.

  (* ==================================================================== *)
  (*  THE ORPHAN'S RE-PARK (fs-icache §20.17.4, S7-unlink's T_DIR arm)     *)
  (*                                                                      *)
  (*  A directory whose count has just reached ZERO and whose records are  *)
  (*  its two dots and nothing else: record 0 is the self record and is    *)
  (*  ticket-free, records 2.. are dead (the [isdirempty] loop's own       *)
  (*  conclusion), and record 1 -- the [".."] whose [ilink] the            *)
  (*  [dp->nlink--] has just SPENT -- goes back GREY, which is free from   *)
  (*  [InodeRegion.ireg_link_grey] and whose home condition is exactly the *)
  (*  premise.                                                            *)
  (*                                                                      *)
  (*  THE COUNT CLAUSE IS FREE HERE: at [nlink = 0] the bound reads        *)
  (*  [0 <= 1 + _].  It lives in THIS file rather than in the walk's parts *)
  (*  file because it is a [dir_links] constructor and the flavour map is  *)
  (*  this file's business.                                               *)
  (* ==================================================================== *)
  Lemma dir_links_orphan (self : Z) (dn' : dinode)
      (data : nat -> list (bv 8)) :
    bv_unsigned (di_nlink dn') = 0 ->
    bv_unsigned (dir_inum data 0) = self ->
    (forall k : nat, (2 <= k)%nat ->
       (k < dir_nrec (bv_unsigned (di_size dn')))%nat ->
       dir_inum data k = bv_0 16) ->
    igrey (bv_unsigned (dir_inum data 1)) -∗ dir_links self dn' data.
  Proof.
    intros Hnl Hself Hdead. iIntros "Hg".
    assert (Hemp : forall k : nat, k <> 1%nat ->
              (k < dir_nrec (bv_unsigned (di_size dn')))%nat ->
              ⊢ (dir_link_at_f (fun _ => false) self dn' data k : iProp Σ)).
    { intros k Hk1 Hk.
      destruct k as [| k'];
        [ exact (dir_link_at_f_self (fun _ => false) self dn' data 0 Hself) |].
      destruct k' as [| k'']; [ congruence |].
      apply dir_link_at_f_zeroed. apply Hdead; lia. }
    rewrite /dir_links.
    destruct (decide (bv_unsigned (di_type dn') = T_DIR_z)) as [_ | _];
      [| iClear "Hg"; done].
    iExists (fun _ => false).
    iSplitR; [iPureIntro; apply dlc_bound_le1; lia |].
    iSplitR; [iPureIntro; exact (dlc_lower_nl0 _ dn' data Hnl) |].
    (* V5': a DEAD home owes no tie -- the orphan's own [iparent] half was
       spent at the [ip->nlink--] one instruction earlier *)
    iSplitR; [iApply (dir_par_tie_nl0 self dn' data Hnl) |].
    destruct (decide (1 < dir_nrec (bv_unsigned (di_size dn')))%nat)
      as [Hlt | Hge].
    - rewrite (big_sepL_delete
                 (fun _ k => dir_link_at_f (fun _ => false) self dn' data k)
                 (seq 0 (dir_nrec (bv_unsigned (di_size dn')))) 1%nat 1%nat).
      2:{ apply lookup_seq. lia. }
      iSplitL "Hg".
      + rewrite /dir_link_at_f.
        destruct (dir_liveb data 1
                  && negb (bool_decide (bv_unsigned (dir_inum data 1) = self)));
          [| iClear "Hg"; done].
        iRight. iSplitL "Hg"; [iExact "Hg" | iPureIntro; exact Hnl].
      + iApply big_sepL_intro. iIntros "!>" (i k Hik).
        destruct (decide (i = 1%nat)) as [-> | Hne]; [done |].
        apply lookup_seq in Hik. destruct Hik as [Hke Hi]. subst k.
        rewrite Nat.add_0_l. iApply (Hemp i Hne Hi).
    - iClear "Hg". iApply big_sepL_intro. iIntros "!>" (i k Hik).
      apply lookup_seq in Hik. destruct Hik as [Hke Hi]. subst k.
      rewrite Nat.add_0_l.
      iApply (Hemp i ltac:(lia) Hi).
  Qed.

End DirLinks.
