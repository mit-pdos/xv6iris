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
  Definition dir_link_at (self : Z) (data : nat -> list (bv 8)) (k : nat)
    : iProp Σ :=
    (if dir_liveb data k
        && negb (bool_decide (bv_unsigned (dir_inum data k) = self))
     then (ilink (bv_unsigned (dir_inum data k))
           ∨ igrey (bv_unsigned (dir_inum data k)))
     else emp)%I.

  Global Instance dir_link_at_timeless self data k :
    Timeless (dir_link_at self data k).
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
             dir_link_at self data k)
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
  Lemma dir_link_at_agree (self : Z) (data data' : nat -> list (bv 8))
      (k : nat) :
    dir_inum data' k = dir_inum data k ->
    dir_link_at self data k -∗ dir_link_at self data' k.
  Proof.
    intros Heq. rewrite /dir_link_at /dir_liveb /dir_freeb Heq.
    iIntros "H". iExact "H".
  Qed.

End DirLinks.
