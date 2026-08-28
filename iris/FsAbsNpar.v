(* FsAbsNpar.v -- THE NAMEIPARENT SIDE OF THE ERA WALK'S VOCABULARY: the
   hop family over the PARENT PREFIX, and the death arm a nameiparent walk
   can actually reach.

   Worklist: claude-notes/projects/fs-syscall-specs.md, lane A item (iii),
   REMAINING item ("the NAMEIPARENT walk").  Design of record:
   claude-notes/design/fs-syscall-specs.md v3, sections 2-3.

   WHY A LEAF AND NOT AN APPEND TO [FsAbsEra.v].  The same mechanical
   reason [FsAbsPins] is a leaf and not an append to [FsAbs.v]: the EC2
   build mirror forbids touching a tracked file.  Fuse the two when
   [FsAbsEra.v] is next edited.

   NOTHING HERE IS A NEW KIND OF HOP.  [ep_hop] is [FsAbs.ax_hop] at
   [FsAbsEra.elend], by [reflexivity] -- the very same hop [FsAbsEra.ex_hop]
   is.  What changes is the LIST it ranges over.

   THE ONE IDEA.  nameiparent walks one element LESS than namei: it
   dirlookups every element but the last, and returns the directory the
   last element would have been looked up IN.  So its trace family is the
   hop list over [removelast (path_elems pl)] -- which is, definitionally,
   [SpecSysMknodAU.mknod_parent_elems pl], the family lane W's
   [FsAbsEraMknod.mknod_walk_pre_era] already produces.  Stating the
   contract over the parent prefix is therefore not a design choice with
   alternatives: it is the only shape a create-side caller can supply.  (An
   earlier sketch had the walk take the FULL family and hand the last hop
   back unfired; that is unsuppliable, because producing the extra hop is a
   real fupd obligation and the caller has no directory to discharge it
   against.)

   THE DEATH ARM IS THE GENUINELY NEW STATEMENT.  The frozen namei shape
   ([SpecNameiTr] / [SpecNamexEra]) is

       exists k d, k < L /\ ((P k d * hops k) \/ (Pmiss k d * hops (S k)))

   and it cannot express two things a nameiparent walk really does.

     (1) THE PARENT'S OWN TYPE TEST.  namex runs [ip->type == T_DIR]
         (+0xbc) and its nlink guard (+0x7a) at EVERY level it reaches --
         including the LAST one, the level whose directory is the parent
         being returned.  A death there is at index [k = length ps], one
         past the last hop, which [k < length ps] refuses.

     (2) "nameiparent of /".  When the path has no elements at all the loop
         never runs: namex falls out at +0x140, iputs, and returns 0 with
         the cursor and the (empty) family untouched.  That is [k = 0] with
         [length ps = 0], which again [k < length ps] refuses.

   So the LEFT disjunct's bound is [k <= length ps] and both cases land in
   it.  The RIGHT disjunct -- hop [k] fired and MISSED -- keeps a STRICT
   bound, and honestly so: dirlookup is reached only after the walk has
   decided the element is not the last one, so a miss cannot happen at the
   parent level.  The two bounds differ by exactly the instruction order of
   namex's loop body, which is the point of stating them separately rather
   than weakening both.

   BINDERS: [FsAbsEra]'s, unchanged. *)

From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import gmap dfrac.
From iris.base_logic.lib Require Import iprop own ghost_map.
Require Import SailStdpp.Base SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvPtsto.
Require Import DinodeEnc.
Require Import DirView.
Require Import FsTree.          (* [fname] *)
Require Import PathElems.       (* [path_elems] *)
Require Import BioDefs.
Require Import InodeInv.
Require Import InodeLock.
Require Import IrefSlots.
Require Import FsBlocks.        (* [fs_names] *)
Require Import FsBytesGamma.    (* [fs_gamma_L] *)
Require Import FsStateEra.
Require Import IcacheRef.
Require Import DirViewLend.
Require Import IcacheEscrow.
Require Import Xv6G.
Require Import FsAbsSeam.
Require Import FsAbsPins.
Require Import FsAbsEra.        (* [elend], [ex_hop]: the LEND, unchanged *)
Require Import FsAbs.           (* LAST (FsAbs's own rule) *)

Local Open Scope Z_scope.

(* ===================================================================== *)
(*  0.  TWO PURE FACTS ABOUT [removelast]                                 *)
(*                                                                        *)
(*  Both are used by the walk's proof and by the discharge lemmas, and    *)
(*  neither is in stdpp under a name this import mix exposes.  Stated at  *)
(*  the top level, outside the ghost section, so they carry no binder.    *)
(* ===================================================================== *)

Lemma np_len_removelast {A} (l : list A) :
  length (removelast l) = (length l - 1)%nat.
Proof.
  induction l as [|x l IH]; [reflexivity |].
  destruct l as [|y l']; [reflexivity |].
  cbn [removelast] in *. cbn [length] in *. lia.
Qed.

Lemma np_removelast_app {A} (l l' : list A) :
  l' <> [] -> removelast (l ++ l') = l ++ removelast l'.
Proof.
  intros Hne. induction l as [|x l IH]; [reflexivity |].
  cbn [app]. rewrite -IH.
  destruct (l ++ l') as [|y r] eqn:Heq; [| reflexivity].
  exfalso. destruct l as [|z l0]; cbn [app] in Heq;
    [ exact (Hne Heq) | discriminate ].
Qed.

Lemma np_removelast_snoc {A} (l : list A) (x : A) :
  removelast (l ++ [x]) = l.
Proof. rewrite (np_removelast_app l [x] ltac:(discriminate)). by rewrite app_nil_r. Qed.

(* THE TWO INDEX BOUNDS THE WALK'S PROOF NEEDS, HOISTED.  They are here and
   not inline for [ProofNamex.v]'s own reason (its [nx_wi_*] family): inside
   that file's proofmode context [lia] on a goal with NAT SUBTRACTION fails
   with "Cannot find witness" -- measured, on the two-line goal
   [n <= n + S m - 1] -- while the same goal closes instantly at the top
   level.  Stated so the walk never has to subtract: the caller hands the
   decomposition it already has and gets the bound. *)

Lemma np_removelast_len_ge {A} (ps es rest : list A) :
  ps = es ++ rest -> rest <> [] ->
  (length es <= length (removelast ps))%nat.
Proof.
  intros -> Hne. rewrite (np_removelast_app es rest Hne) length_app. lia.
Qed.

Lemma np_removelast_len_gt {A} (ps es : list A) (x : A) (rest : list A) :
  ps = (es ++ [x]) ++ rest -> rest <> [] ->
  (length es < length (removelast ps))%nat.
Proof.
  intros -> Hne.
  rewrite (np_removelast_app (es ++ [x]) rest Hne) !length_app.
  cbn [length]. lia.
Qed.

Section FsAbsNpar.
  Context `{!riscvGS Σ, !xv6G Σ}.
  Implicit Types Γ : fs_view_names Σ.

  (* =================================================================== *)
  (*  1.  THE PARENT PREFIX AND ITS HOP FAMILY                            *)
  (* =================================================================== *)

  Definition np_elems (pl : list (bv 8)) : list fname :=
    removelast (path_elems pl).

  Definition ep_hop (γfs : fs_names) (P : nat -> Z -> iProp Σ)
      (Pmiss : nat -> Z -> iProp Σ) (k : nat) (s : fname) : iProp Σ :=
    ax_hop (elend (fs_gamma_L γfs)) P Pmiss k s.

  Definition ep_hops_from (γfs : fs_names) (P : nat -> Z -> iProp Σ)
      (Pmiss : nat -> Z -> iProp Σ) (pl : list (bv 8)) (n : nat) : iProp Σ :=
    ax_hops_from (elend (fs_gamma_L γfs)) P Pmiss (np_elems pl) n.

  Lemma ep_hop_is_ax_hop (γfs : fs_names) P Pmiss k s :
    ep_hop γfs P Pmiss k s = ax_hop (elend (fs_gamma_L γfs)) P Pmiss k s.
  Proof. reflexivity. Qed.

  Lemma ep_hops_is_ax_hops (γfs : fs_names) P Pmiss pl n :
    ep_hops_from γfs P Pmiss pl n
    = ax_hops_from (elend (fs_gamma_L γfs)) P Pmiss (np_elems pl) n.
  Proof. reflexivity. Qed.

  (* the head hop peels off exactly as [FsAbsEra.ex_hops_cons] peels it,
     at the shorter list *)
  Lemma ep_hops_cons (γfs : fs_names) (P Pmiss : nat -> Z -> iProp Σ)
      (pl : list (bv 8)) (k : nat) (s : fname) (rest : list fname) :
    drop k (np_elems pl) = s :: rest ->
    ep_hops_from γfs P Pmiss pl k -∗
    ep_hop γfs P Pmiss k s ∗ ep_hops_from γfs P Pmiss pl (S k).
  Proof.
    iIntros (Hd) "H". rewrite /ep_hops_from /ax_hops_from.
    assert (HdS : drop (S k) (np_elems pl) = rest).
    { replace (S k) with (k + 1)%nat by lia.
      rewrite -(drop_drop (np_elems pl) 1 k) Hd. reflexivity. }
    rewrite Hd HdS big_sepL_cons Nat.add_0_r.
    iDestruct "H" as "[$ H]".
    iApply (big_sepL_mono with "H"). intros i x _.
    replace (k + S i)%nat with (S k + i)%nat by lia. done.
  Qed.

  (* the family past its end is [emp] -- what the success exit and the
     "nameiparent of /" exit both hand back *)
  Lemma ep_hops_done (γfs : fs_names) (P Pmiss : nat -> Z -> iProp Σ)
      (pl : list (bv 8)) (k : nat) :
    (length (np_elems pl) <= k)%nat ->
    ⊢ ep_hops_from γfs P Pmiss pl k.
  Proof.
    intros Hk. rewrite /ep_hops_from /ax_hops_from.
    rewrite (drop_ge (np_elems pl) k Hk). by iApply big_sepL_nil.
  Qed.

  (* =================================================================== *)
  (*  2.  THE DEATH ARM                                                   *)
  (* =================================================================== *)

  (* See the header for why the two bounds differ.  LEFT: hop [k] never
     fired (the level's type test or nlink guard died, or the path had no
     elements at all), so the cursor comes back beside hops [k..] -- and
     [k] may BE [length ps], the parent's own level.  RIGHT: hop [k] fired
     and missed, which can only happen strictly inside the prefix. *)
  Definition np_dead (γfs : fs_names) (P Pmiss : nat -> Z -> iProp Σ)
      (pl : list (bv 8)) : iProp Σ :=
    ((∃ (k : nat) (d : Z),
        ⌜(k <= length (np_elems pl))%nat⌝ ∗ P k d
        ∗ ep_hops_from γfs P Pmiss pl k)
     ∨ (∃ (k : nat) (d : Z),
        ⌜(k < length (np_elems pl))%nat⌝ ∗ Pmiss k d
        ∗ ep_hops_from γfs P Pmiss pl (S k)))%I.

  (* the three introduction forms the walk's three failure exits use *)
  Lemma np_dead_unfired (γfs : fs_names) (P Pmiss : nat -> Z -> iProp Σ)
      (pl : list (bv 8)) (k : nat) (d : Z) :
    (k <= length (np_elems pl))%nat ->
    P k d -∗ ep_hops_from γfs P Pmiss pl k -∗ np_dead γfs P Pmiss pl.
  Proof.
    iIntros (Hk) "HP Hh". rewrite /np_dead. iLeft.
    iExists k, d. iSplitR; [by iPureIntro |]. iFrame.
  Qed.

  Lemma np_dead_missed (γfs : fs_names) (P Pmiss : nat -> Z -> iProp Σ)
      (pl : list (bv 8)) (k : nat) (d : Z) :
    (k < length (np_elems pl))%nat ->
    Pmiss k d -∗ ep_hops_from γfs P Pmiss pl (S k) -∗ np_dead γfs P Pmiss pl.
  Proof.
    iIntros (Hk) "HP Hh". rewrite /np_dead. iRight.
    iExists k, d. iSplitR; [by iPureIntro |]. iFrame.
  Qed.

  (* "nameiparent of /": the path has no elements, so the family is empty
     and the cursor at 0 IS the whole refund *)
  Lemma np_dead_noelems (γfs : fs_names) (P Pmiss : nat -> Z -> iProp Σ)
      (pl : list (bv 8)) (d : Z) :
    path_elems pl = [] ->
    P 0%nat d -∗ np_dead γfs P Pmiss pl.
  Proof.
    iIntros (Hnil) "HP".
    iApply (np_dead_unfired γfs P Pmiss pl 0%nat d with "HP").
    - lia.
    - iApply ep_hops_done. rewrite /np_elems Hnil. reflexivity.
  Qed.

End FsAbsNpar.
