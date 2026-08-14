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
*)

From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.algebra Require Import auth gmap frac numbers excl.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap invariants own ghost_var.
Require Import SailStdpp.Values.
Require Import RiscvModelBytes.
Require Import DinodeEnc.
Require Import DirentEnc.
Require Import InodeInv.
Require Import DirView.
Require Import IcacheRef.

Local Open Scope Z_scope.

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
  Definition dir_links (self : Z) (dn : dinode) (data : nat -> list (bv 8))
    : iProp Σ :=
    (if decide (bv_unsigned (di_type dn) = T_DIR_z)
     then ([∗ list] k ∈ seq 0 (dir_nrec (bv_unsigned (di_size dn))),
             dir_link_at self dn data k)
     else emp)%I.

  Global Instance dir_links_timeless self dn data :
    Timeless (dir_links self dn data).
  Proof.
    rewrite /dir_links.
    destruct (decide (bv_unsigned (di_type dn) = T_DIR_z)); apply _.
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
  Lemma dir_links_size_zero (self : Z) (dn : dinode)
      (data : nat -> list (bv 8)) :
    bv_unsigned (di_size dn) = 0 ->
    ⊢ dir_links self dn data.
  Proof.
    intros Hsz. rewrite /dir_links.
    destruct (decide (bv_unsigned (di_type dn) = T_DIR_z)) as [_ | _];
      [| done].
    rewrite Hsz /dir_nrec.
    assert (Hz : Z.to_nat (0 / 16) = 0%nat) by (vm_compute; reflexivity).
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
    intros Hnrec Hk0 Htot Hty Hnl Hsz Hrng.
    (* the type is unmoved, so the two big-ops are both live or both [emp] *)
    rewrite /dir_links Hty.
    destruct (decide (bv_unsigned (di_type dn) = T_DIR_z)) as [_ | _];
      [| iIntros "_ _"; done].
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
    iIntros "Hk0 H".
    destruct Hcalt as [Hn' | (Hn' & Hkn & Ht16)]; rewrite Hn'.
    - (* ======== the record COUNT did not move ======== *)
      destruct (Nat.lt_ge_cases k0 nrec) as [Hlt | Hge].
      + (* the written slot is one of the goal's indices: swap it *)
        rewrite (big_sepL_delete
                   (fun _ k => dir_link_at self dn' data' k) (seq 0 nrec) k0 k0).
        2:{ apply lookup_seq; lia. }
        iSplitL "Hk0"; [iExact "Hk0" |].
        iApply (big_sepL_mono with "H"). intros i k Hik.
        apply lookup_seq in Hik. destruct Hik as [Hk Hi].
        destruct (decide (i = k0)) as [_ | Hne]; [by iIntros "_" |].
        assert (Heq : dir_inum data' k = dir_inum data k)
          by (apply Hagree; lia).
        iIntros "Hx".
        iApply (dir_link_at_agree self dn dn' data data' k Hnl Heq with "Hx").
      + (* the written slot is at or past the end: nothing in range moved *)
        iApply (big_sepL_mono with "H"). intros i k Hik.
        apply lookup_seq in Hik. destruct Hik as [Hk Hi].
        assert (Heq : dir_inum data' k = dir_inum data k)
          by (apply Hagree; lia).
        iIntros "Hx".
        iApply (dir_link_at_agree self dn dn' data data' k Hnl Heq with "Hx").
    - (* ======== ONE record was appended, at [k0 = nrec] ======== *)
      rewrite seq_S big_sepL_app. iSplitL "H".
      + iApply (big_sepL_mono with "H"). intros i k Hik.
        apply lookup_seq in Hik. destruct Hik as [Hk Hi].
        assert (Heq : dir_inum data' k = dir_inum data k)
          by (apply Hagree; lia).
        iIntros "Hx".
        iApply (dir_link_at_agree self dn dn' data data' k Hnl Heq with "Hx").
      + simpl. iSplitL "Hk0"; [| done].
        rewrite <- Hkn. iExact "Hk0".
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
    iIntros "H". iApply (big_sepL_mono with "H"). intros i k Hik.
    iIntros "Hx".
    iApply (dir_link_at_agree self dn dn' data data' k Hnl (Hagree k) with "Hx").
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  (vi) THE THEOREM: A LIVE HOME HAS NO GREY RECORDS                   *)
  (*       design: fs-icache.md §20.17.7, option (iii)                    *)
  (* ------------------------------------------------------------------ *)

  (* the ticket with the grey disjunct GONE.  Named so the consumer's
     statement is two lines rather than an [if] inside a big-op inside an
     [if], and so [ProofCreate]'s guard arm has something to write down. *)
  Definition dir_ilink_at (self : Z) (data : nat -> list (bv 8)) (k : nat)
    : iProp Σ :=
    (if dir_liveb data k
        && negb (bool_decide (bv_unsigned (dir_inum data k) = self))
     then ilink (bv_unsigned (dir_inum data k))
     else emp)%I.

  (* THIS IS D2's FIX, FORMALISED.  Grey now carries [di_nlink dn = 0]
     (see [dir_link_at]'s header), so under a LIVE home the right disjunct
     is refuted where it stands and every record's ticket collapses to the
     allocatedness witness.  The guard the caller supplies is exactly the
     [c.beqz] it just fell through. *)
  Lemma dir_link_at_live (self : Z) (dn : dinode)
      (data : nat -> list (bv 8)) (k : nat) :
    bv_unsigned (di_nlink dn) <> 0 ->
    dir_link_at self dn data k -∗ dir_ilink_at self data k.
  Proof.
    intros Hnz. rewrite /dir_link_at /dir_ilink_at.
    destruct (dir_liveb data k
              && negb (bool_decide (bv_unsigned (dir_inum data k) = self)));
      [| by iIntros "_"].
    iIntros "[H | [_ %Hz]]"; [iExact "H" | destruct (Hnz Hz)].
  Qed.

  (* ...and the payload-level lift, which is what a walk holding
     [ic_loaded]'s [dir_links] applies. *)
  Lemma dir_links_live (self : Z) (dn : dinode)
      (data : nat -> list (bv 8)) :
    bv_unsigned (di_nlink dn) <> 0 ->
    dir_links self dn data -∗
      (if decide (bv_unsigned (di_type dn) = T_DIR_z)
       then ([∗ list] k ∈ seq 0 (dir_nrec (bv_unsigned (di_size dn))),
               dir_ilink_at self data k)
       else emp)%I.
  Proof.
    intros Hnz. rewrite /dir_links.
    destruct (decide (bv_unsigned (di_type dn) = T_DIR_z)) as [_ | _];
      [| by iIntros "_"].
    iIntros "H". iApply (big_sepL_mono with "H"). intros i k Hik.
    iIntros "Hx". iApply (dir_link_at_live self dn data k Hnz with "Hx").
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
  Lemma dir_link_at_of_ilink (self : Z) (dn' : dinode)
      (data : nat -> list (bv 8)) (k : nat) :
    dir_ilink_at self data k -∗ dir_link_at self dn' data k.
  Proof.
    rewrite /dir_link_at /dir_ilink_at.
    destruct (dir_liveb data k
              && negb (bool_decide (bv_unsigned (dir_inum data k) = self)));
      [| by iIntros "_"].
    iIntros "H". iLeft. iExact "H".
  Qed.

  (* ...and the payload-level lift, [dir_links_live]'s exact inverse. *)
  Lemma dir_links_of_ilink (self : Z) (dn' : dinode)
      (data : nat -> list (bv 8)) :
    (if decide (bv_unsigned (di_type dn') = T_DIR_z)
     then ([∗ list] k ∈ seq 0 (dir_nrec (bv_unsigned (di_size dn'))),
             dir_ilink_at self data k)
     else emp)%I -∗
    dir_links self dn' data.
  Proof.
    rewrite /dir_links.
    destruct (decide (bv_unsigned (di_type dn') = T_DIR_z)) as [_ | _];
      [| by iIntros "_"].
    iIntros "H". iApply (big_sepL_mono with "H"). intros i k Hik.
    iIntros "Hx". iApply (dir_link_at_of_ilink self dn' data k with "Hx").
  Qed.

End DirLinks.
