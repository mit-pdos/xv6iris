(* ====================================================================== *)
(*  HISTORY -- OFF [_CoqProject] SINCE LANE G5.                            *)
(*                                                                        *)
(*  This file refutes shapes for the SEPARATE PARENT REGISTER of lanes     *)
(*  G2/G3 ([FsStateLink.par_auth] / [par_tok], camera [Xv6Cameras.fsParUR] *)
(*  -- an [auth] of [gmultiset (option Z)] beside an [auth nat] count).     *)
(*  fs-state.md section 6.5's ruling deleted that register outright: the   *)
(*  count and the type are ONE RA now (the TYPE REGISTER,                  *)
(*  [authUR (gmultisetUR ity)]), a directory's value CARRIES its parent,   *)
(*  and rmdir's (D1) is the RA's own agreement law read at the child's     *)
(*  ["."] fragment.  None of the propositions below still typecheck, so    *)
(*  the file is off the build; the finding it records -- a register half   *)
(*  whose statement has to know the TARGET's type cannot be written one    *)
(*  inode at a time -- is what made the type register the answer, and is   *)
(*  kept here in prose.                                                    *)
(* ====================================================================== *)

(* ====================================================================== *)
(*  FsParRefute.v -- WHY THE PARENT REGISTER IS AN auth-OF-MULTISET AT     *)
(*  THE CHILD'S KEY, AND NOT A PAIR OF dfrac_agree HALVES                  *)
(*  (durable-disk lane G2; design of record: fs-state.md section 6.5)      *)
(*                                                                        *)
(*  A DOCUMENTED REFUTATION, in the family of [FsDurRefute.v] /            *)
(*  [FsDurDefer.v] / [FsBootWall.v]: nothing above depends on it, and its  *)
(*  purpose is to stop the next lane from re-deriving a register that      *)
(*  cannot be defined one inode at a time.                                 *)
(*                                                                        *)
(*  THE TASK.  rmdir pays [dp->nlink--] with the CHILD's [".."] token, so  *)
(*  it needs "the child's [".."] names [dp]".  That is cross-inode as a    *)
(*  pure fact and is never stated as one, so it has to be a RESOURCE held  *)
(*  by both parties: something in the child's bundle, something in [dp]'s, *)
(*  and an RA law that collapses them.                                     *)
(*                                                                        *)
(*  THE SHAPE THAT DOES NOT WORK is "a half of [agree dp] at the CHILD's   *)
(*  key, one half in the child's bundle beside its [".."] entry and one in *)
(*  [dp]'s beside its entry FOR THE CHILD".  Its parent side is stated at  *)
(*  "an entry whose target is a DIRECTORY", and a directory entry does not *)
(*  record its target's type -- xv6's [dirent] is (inum, name).  So the    *)
(*  parent's per-entry resource is either                                  *)
(*                                                                        *)
(*    (a) CONDITIONAL ON THE TARGET'S TYPE, which makes a directory's      *)
(*        payload a function of the WHOLE inode map -- the arity of        *)
(*        [FsStateInode.ent_toks], hence of [inode_owned], hence of every  *)
(*        payload site -- and breaks fs-state.md section 0's local         *)
(*        reasoning rule outright; the runtime payload has no such map at  *)
(*        all, so there the condition can only be an EXISTENTIAL FLAVOUR   *)
(*        refuted against the region's per-inum type clause, which is      *)
(*        exactly the apparatus ([DirLinks.dir_link_at_f] + the ledger's   *)
(*        (T1)) that this lane exists to delete; or                        *)
(*    (b) UNCONDITIONAL -- every name record carries one -- and then the   *)
(*        two theorems below kill it.                                      *)
(*                                                                        *)
(*  Theorem [par_half_three_namers]: a FILE may be named three times       *)
(*  (xv6's [sys_link] has no link limit below [nlink <= 32767]), so an     *)
(*  unconditional half puts THREE halves at one key and the element is     *)
(*  invalid.  The only compositions that survive an unbounded number of    *)
(*  holders are the CORE-ID ones ([agree]-like).                           *)
(*                                                                        *)
(*  Theorem [nondir_marker_stuck]: a core-id "this inum is not a live      *)
(*  directory" marker can never be RETRACTED, so the inum can never become *)
(*  a directory again -- and [ialloc] hands out freed inums for any type,  *)
(*  so a file that is deleted and whose inum is then [mkdir]'d needs       *)
(*  exactly that step.  Unbounded sharing and retractability are           *)
(*  incompatible in a flat register at the child's key.                    *)
(*                                                                        *)
(*  WHAT IS BUILT INSTEAD ([FsStateLink], [Xv6Cameras.fsParUR]): an        *)
(*  [authUR (gmultisetUR (option Z))] column at the CHILD's key, holding   *)
(*  the multiset of namers -- [Some j] for a NAME record of [j], [None]    *)
(*  for an up-pointing one (which names nothing but still holds a link,    *)
(*  so it still holds a unit).                                             *)
(*                                                                        *)
(*    - the parent's side is the FRAGMENT [par_tok Gamma t v], one per     *)
(*      token-bearing record, UNCONDITIONAL: it never asks what the        *)
(*      target's type is, and fragments compose for any number of namers   *)
(*      ([par_frag_any] below);                                            *)
(*    - the child's side is the AUTHORITY [par_auth Gamma c P].  As built  *)
(*      it parks in the inode REGION's slot under the one clause a slot    *)
(*      can state ([size P <= nlink], [InodeRegion.ireg_par]); the clause  *)
(*      that gives the register its CONTENT -- "a LIVE DIRECTORY admits    *)
(*      only its own up-pointing target as a namer" -- reads the node's    *)
(*      DATA and so belongs in the checked-out payload, where it lands     *)
(*      when [IcacheEscrow.dlinks] loses [DirLinks.dir_links];             *)
(*    - the collapse is [auth]'s own law ([FsStateLink.par_auth_tok_eq]),  *)
(*      and [par_register_roundtrip] below is the non-vacuity witness at   *)
(*      the real instance: mkdir mints the pair from an EMPTY register,    *)
(*      every namer's fragment is then pinned to the [".."] target -- that *)
(*      is the fact rmdir's [dp->nlink--] needs -- and rmdir's retirement  *)
(*      leaves the register empty again, which is the reuse step           *)
(*      [nondir_marker_stuck] refutes for the core-id marker.              *)
(*                                                                        *)
(*  A FILE's authority is unconstrained (it has many namers), which is why *)
(*  the bundle binds it existentially under [size P <= nlink]: that bound  *)
(*  is what makes a FREED inum's register provably empty, so the mint      *)
(*  above always starts where [par_register_roundtrip] starts.             *)
(*                                                                        *)
(*  ==== AND THE AUTHORITY CANNOT FOLLOW THE PAYLOAD (lane G3) ==========  *)
(*                                                                        *)
(*  The bullet above says the DIRECTORY clause "lands in the checked-out   *)
(*  payload".  IT CANNOT, and the obstruction is this kernel's LOCK        *)
(*  DISCIPLINE rather than anything about the RA:                          *)
(*                                                                        *)
(*    sys_link runs  ilock(ip); ip->nlink++; iupdate(ip); iunlock(ip);     *)
(*                   nameiparent(new,name); ilock(dp); dirlink(dp,name,ip) *)
(*                                                                        *)
(*  so the unit is MINTED before the namer is known and RE-VALUED at the   *)
(*  deposit ([IregLinkNz.ireg_par_revalue]) -- at which point [ip] is      *)
(*  UNLOCKED.  The walk there holds [dp]'s payload and, for [ip], only     *)
(*  [IcacheRef.inode_ref] (its two identity cells); [ip]'s payload is in   *)
(*  the escrow behind a sleeplock the code never re-takes.  With the       *)
(*  authority in [IcacheEscrow.dlinks] that re-valuation has NO SOURCE.    *)
(*  Witnesses: ProofSysLink.v:1818 (the mint) and ProofSysLink.v:2961      *)
(*  (the re-valuation, which reaches the authority through [ireg_inv] at   *)
(*  [iregN] precisely because it is region-side).                          *)
(*                                                                        *)
(*  So the tie between a directory's [".."] DATA and its register is a     *)
(*  TWO-HOLDER fact and needs either the [p] column ([IcacheRef]'s         *)
(*  [option (dfrac_agree Z)] + [DirLinks.dir_par_tie], the shape that is   *)
(*  built) or a third kind of register VALUE -- a "self-up" unit at the    *)
(*  node's own key, not counted by the bound.  fs-state.md section 6.5     *)
(*  carries both and the choice.  What DOES come off the register with no  *)
(*  data at all is S7-unlink's other reading, (D2): [InodeRegion]'s        *)
(*  (U1)/(U2), which retired [IregDirBit.dir_links_subdir_nlink2].         *)
(* ====================================================================== *)

From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap gmultiset.
From iris.algebra Require Import auth agree csum dfrac frac gmap gmultiset
     numbers updates.
From iris.algebra.lib Require Import dfrac_agree.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import iprop own.
Require Import Xv6Cameras.
Require Import FsStateLink.

Local Open Scope Z_scope.

(* ---------------------------------------------------------------------- *)
(*  1.  AN UNCONDITIONAL HALF DIES AT THE THIRD HARD LINK                  *)
(* ---------------------------------------------------------------------- *)

Theorem par_half_three_namers (v : Z) :
  ~ ✓ (to_dfrac_agree (DfracOwn (1/2)) (v : leibnizO Z)
       ⋅ to_dfrac_agree (DfracOwn (1/2)) (v : leibnizO Z)
       ⋅ to_dfrac_agree (DfracOwn (1/2)) (v : leibnizO Z)).
Proof.
  rewrite -dfrac_agree_op dfrac_agree_op_valid.
  intros [Hv _]. revert Hv.
  rewrite dfrac_op_own dfrac_valid_own. compute. intros H. by apply H.
Qed.

(* ---------------------------------------------------------------------- *)
(*  2.  A CORE-ID MARKER IS NEVER RETRACTED                                *)
(* ---------------------------------------------------------------------- *)

(* [Cinl (to_agree ())] is the only shape an UNCONDITIONAL parent-side
   resource can take at a non-directory target (section 1 rules out every
   fractional one).  It is core-id, so it is its own frame: no update away
   from it is frame-preserving, and in particular the inum can never take
   on the directory register [Cinr x] that a later [mkdir] would install. *)
Theorem nondir_marker_stuck {A : cmra} `{!CmraDiscrete A} (x : A) :
  ~ ((Cinl (to_agree ()) : csumR (agreeR unitO) A) ~~> Cinr x).
Proof.
  intros Hup.
  assert (Hv : ✓ ((Cinl (to_agree ()) : csumR (agreeR unitO) A)
                  ⋅? Some (Cinl (to_agree ())))).
  { rewrite /= -Cinl_op agree_idemp. done. }
  pose proof (proj1 (cmra_discrete_update _ _) Hup
                (Some (Cinl (to_agree ()))) Hv) as Hbot.
  by rewrite /= in Hbot.
Qed.

(* ---------------------------------------------------------------------- *)
(*  3.  ...AND THE MULTISET REGISTER HAS NEITHER PROBLEM                   *)
(* ---------------------------------------------------------------------- *)

(* The parent side composes for ANY number of namers: a lone [auth]
   fragment is valid whatever the multiset. *)
Theorem par_frag_any (c : Z) (Q : gmultiset (option Z)) :
  ✓ ({[ c := ((ε : authUR natUR), (◯ Q : fsParUR)) ]} : fsLinkUR).
Proof.
  apply singleton_valid, pair_valid.
  split; [apply ucmra_unit_valid | by apply auth_frag_valid].
Qed.

(* ...and the law is read at a SATISFIABLE premise: the authority and the
   fragment a [mkdir] mints stand together. *)
Theorem par_pair_valid (c : Z) (p : option Z) :
  ✓ (par_auth_elem c {[+ p +]} ⋅ par_tok_elem c p).
Proof.
  rewrite /par_auth_elem /par_tok_elem singleton_op -pair_op.
  apply singleton_valid, pair_valid.
  split; [by rewrite left_id; apply ucmra_unit_valid |].
  apply auth_both_valid_discrete.
  split; [by apply gmultiset_included | done].
Qed.

Section Roundtrip.
  Context `{!fsLinkG Σ}.

  (* THE WHOLE MECHANISM IN ONE STATEMENT.  From an EMPTY register -- what
     [size P <= nlink] gives at a freed inum -- [mkdir] mints the pair; any
     namer's fragment is then pinned to the parent [dp], which is (D1);
     and rmdir's retirement returns the register to empty, so the inum is
     reusable as a directory again. *)
  Lemma par_register_mint (Γ : fs_view_names Σ) (c : Z) (dp : option Z) :
    par_auth Γ c ∅ ==∗ par_auth Γ c {[+ dp +]} ∗ par_tok Γ c dp.
  Proof.
    iIntros "Ha".
    iMod (par_alloc Γ c ∅ dp with "Ha") as "[Ha $]".
    assert (Hemp : (∅ : gmultiset (option Z)) ⊎ {[+ dp +]} = {[+ dp +]})
      by multiset_solver.
    rewrite Hemp. by iFrame.
  Qed.

  Lemma par_register_retire (Γ : fs_view_names Σ) (c : Z) (dp : option Z) :
    par_auth Γ c {[+ dp +]} -∗ par_tok Γ c dp ==∗ par_auth Γ c ∅.
  Proof.
    iIntros "Ha Ht".
    assert (Hemp : (∅ : gmultiset (option Z)) ⊎ {[+ dp +]} = {[+ dp +]})
      by multiset_solver.
    iApply (par_dealloc Γ c ∅ dp with "[Ha] Ht"). rewrite Hemp. iFrame "Ha".
  Qed.

  Theorem par_register_roundtrip (Γ : fs_view_names Σ) (c : Z)
      (dp : option Z) :
    par_auth Γ c ∅ ==∗ ∃ j : option Z, ⌜j = dp⌝ ∗ par_auth Γ c ∅.
  Proof.
    iIntros "Ha".
    iMod (par_register_mint with "Ha") as "[Ha Ht]".
    iDestruct (par_auth_tok_eq with "Ha Ht") as %Hj.
    iMod (par_register_retire with "Ha Ht") as "Ha".
    iModIntro. iExists dp. by iFrame.
  Qed.

End Roundtrip.
