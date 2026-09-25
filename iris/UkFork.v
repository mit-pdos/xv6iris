(* ===================================================================== *)
(* UkFork.v -- FORK, on [urun]: the ecall leaf whose contract returns      *)
(* TWICE, and the [Forkable] payload class that moves a caller's facts     *)
(* into the child.                                                         *)
(*                                                                         *)
(* THE PROBLEM.  [uexec_ret]'s fork arm (UexecRet.v) pays TWO slots at the *)
(* same key -- the parent's, at every r <> 0, and the child's, at r = 0 -- *)
(* both at the SAME image, permission map and break.  The parent resumes   *)
(* under the heap it already owns ([γt]/[γd]/[γs] untouched, like a quiet  *)
(* syscall).  The child's address space is a COPY, so its heap is a FRESH  *)
(* gname triple over the same image: [uheap_alloc]-style allocation, which *)
(* needs no ownership at all.  Duplicating a points-to across a fork is    *)
(* therefore sound for free -- it is allocation at a fresh name, never     *)
(* sharing -- and the whole design question is which of the parent's facts *)
(* the child INHERITS without the prover flattening them to a byte map.    *)
(*                                                                         *)
(* THE ANSWER is [Forkable P]: a payload [P : gname -> gname -> gname ->   *)
(* iProp] -- the caller's facts as a FAMILY over the heap names -- that    *)
(* factors through a footprint.  The class reveals the payload's text,     *)
(* read-only and exclusive byte maps, restores the payload to the parent,  *)
(* and rebuilds [P γt' γd' γs'] at any fresh names from mirrored           *)
(* fragments.  [wp_uk_ecall_fork] then says exactly what fork should:      *)
(*                                                                         *)
(*   { P γt γd γs }  fork  { parent: r <> 0, P γt γd γs   (same names)     *)
(*                         ; child:  r  = 0, P γt' γd' γs' (fresh names) } *)
(*                                                                         *)
(* with the free stack below sp crossing ALONGSIDE the payload -- [ustack] *)
(* is itself Forkable, and the leaf bundles [P ∗ ustack] into one payload  *)
(* internally, so the child resumes at the same [avail] -- and the break   *)
(* carried over ([usz γs' szv]).                                           *)
(*                                                                         *)
(* WHAT DOES NOT CROSS.  Resources that are not address-space state --     *)
(* protocol tokens, shared-file facts -- are NOT [Forkable] and must not   *)
(* be: both processes run the code that would use them, and the logic      *)
(* must refuse to duplicate an exclusive right.  The caller distributes    *)
(* them between the two continuations by ordinary separation ([iSplitL]   *)
(* at the leaf's [∗]).  Fractional data payloads (a [dq] that is neither   *)
(* full nor discarded) are also not covered yet: the class's three maps    *)
(* are full/discarded/text, which is every dq the user programs use.       *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Bool Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_map ghost_var invariants.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvModelBytes.
Require Import RegFile.
Require Import UserFrame.
Require Import UserExecFacts.
Require Import UserPerm.
Require Import UmodeAbi.   (* [ubyte0] *)
Require Import WpMmodeLeafBase.   (* [csp_rs1] *)
Require Import UsysMemOk UexecSlot UexecRet.
Require Import FdSlots.      (* [fdstate] -- the key's descriptor view *)
Require Import UkStep.
Require Import UserHeap.
Require Import UkRun.
Require Import UkRunSys.   (* [usysno] *)
Require Import CtxIdDefs.
Require Import ChildTok.     (* [child_tok] / [my_pay] -- fork's two pieces *)
Require Import ProcGeom.     (* [PIDMAX] -- the fork answer's pid range *)
Local Open Scope Z_scope.
Import Defs.

(* ===================================================================== *)
(* §0 PURE MAP HELPERS (no ghosts).                                       *)
(* ===================================================================== *)

Local Lemma map_union_sub (m1 m2 m3 : gmap Z (bv 8)) :
  m1 ⊆ m3 -> m2 ⊆ m3 -> m1 ∪ m2 ⊆ m3.
Proof.
  intros H1 H2. apply map_subseteq_spec. intros k v Hk.
  apply lookup_union_Some_raw in Hk.
  destruct Hk as [Hk | [_ Hk]];
    [ exact (proj1 (map_subseteq_spec _ _) H1 k v Hk)
    | exact (proj1 (map_subseteq_spec _ _) H2 k v Hk) ].
Qed.

Local Lemma map_insert_sub (m1 m2 : gmap Z (bv 8)) (i : Z) (x : bv 8) :
  m2 !! i = Some x -> m1 ⊆ m2 -> <[i := x]> m1 ⊆ m2.
Proof.
  intros Hi H. apply map_subseteq_spec. intros k v Hk.
  destruct (decide (i = k)) as [-> | Hne].
  - rewrite lookup_insert in Hk. injection Hk as <-. exact Hi.
  - rewrite lookup_insert_ne in Hk; [ | exact Hne ].
    exact (proj1 (map_subseteq_spec _ _) H k v Hk).
Qed.

(* the right injection of a union, valid when the two maps AGREE on the
   overlap (the left-bias then never changes a value m2 speaks for) *)
Local Lemma map_sub_union_r_agree (m1 m2 : gmap Z (bv 8)) :
  (forall (a : Z) (b1 b2 : bv 8),
     m1 !! a = Some b1 -> m2 !! a = Some b2 -> b1 = b2) ->
  m2 ⊆ m1 ∪ m2.
Proof.
  intros Hag. apply map_subseteq_spec. intros k v Hk.
  destruct (m1 !! k) as [b1 |] eqn:H1.
  - pose proof (Hag k b1 v H1 Hk) as Hbv. subst v.
    exact (lookup_union_Some_l m1 m2 k b1 H1).
  - apply lookup_union_Some_raw. right. exact (conj H1 Hk).
Qed.

(* ✓ (DfracOwn 1 ⋅ dq) is absurd: full ownership composes with nothing. *)
Local Lemma dfrac_full_absurd (dq : dfrac) : ✓ (DfracOwn 1 ⋅ dq) -> False.
Proof.
  intros Hv. apply dfrac_valid_own_l in Hv.
  exact (irreflexivity Qp.lt 1%Qp Hv).
Qed.

(* ===================================================================== *)
(* §0b A RUN AS A MAP.  [useq_map a n f] is the byte map of the run       *)
(* [f 0 .. f (n-1)] at [a .. a+n-1] -- the canonical footprint of every    *)
(* run-shaped payload, with the ONE conversion lemma every instance uses.  *)
(* ===================================================================== *)

Fixpoint useq_map (a : Z) (n : nat) (f : nat -> bv 8) : gmap Z (bv 8) :=
  match n with
  | O => ∅
  | S k => <[ (a + Z.of_nat k)%Z := f k ]> (useq_map a k f)
  end.

Local Lemma useq_map_lookup_Some (a : Z) (n : nat) (f : nat -> bv 8) (x : Z) (b : bv 8) :
  useq_map a n f !! x = Some b -> a <= x < a + Z.of_nat n.
Proof.
  revert x b. induction n as [| k IH]; intros x b Hx.
  - rewrite lookup_empty in Hx. discriminate Hx.
  - cbn in Hx. destruct (decide ((a + Z.of_nat k)%Z = x)) as [<- | Hne].
    + lia.
    + rewrite lookup_insert_ne in Hx; [ | exact Hne ].
      pose proof (IH x b Hx). lia.
Qed.

Local Lemma useq_map_fresh (a : Z) (n : nat) (f : nat -> bv 8) :
  useq_map a n f !! (a + Z.of_nat n)%Z = None.
Proof.
  destruct (useq_map a n f !! (a + Z.of_nat n)%Z) as [b |] eqn:Hb;
    [ | reflexivity ].
  pose proof (useq_map_lookup_Some a n f _ b Hb). lia.
Qed.

Require Import UserFd.   (* [ufd_auth] -- the PROGRAM's own view of
                            its descriptor table, the authority for
                            which rides inside [urun] *)
Require Import UserChildren. (* [uch] -- the child's own half of its (empty)
                                children set, minted here *)
Require Import UserCwd.  (* [ucwd] -- the parent's half of its working
                            directory, which the child is minted at *)
Require Import UexecSG.   (* [uexecSG] / [uprogSG]: the ARM deposit class *)

Section UkFork.
  Context `{!riscvGS Σ}.
  Context `{!ufdG Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  Context `{!ghost_varG Σ Z}.
  (* ...and the children set's ([Xv6Cameras.uchG]), which [UkRun.urun]
     carries beside the cwd's *)
  Context `{!ghost_varG Σ (gset gname)}.
  (* [ChildTok.ctokG]: this file names the generation's pieces and binds no
     whole-system bundle.  A file that binds [Xv6G.xv6G] gets the class
     through the bundle and must not bind it again. *)
  Context `{!ctokG Σ}.
  Context {SG : uexecSG Σ}.
  Context `{PS : uprogSG Σ}.

  (* the conversion: a big-op over the run's map IS the big-op over the run *)
  Local Lemma big_seq_map (Φ : Z -> bv 8 -> iProp Σ) (a : Z) (n : nat)
      (f : nat -> bv 8) :
    ([∗ map] k ↦ b ∈ useq_map a n f, Φ k b)
    ⊣⊢ ([∗ list] j ∈ seq 0 n, Φ (a + Z.of_nat j)%Z (f j)).
  Proof using .
    induction n as [| k IH].
    - cbn. rewrite big_sepM_empty. reflexivity.
    - cbn [useq_map].
      rewrite (big_sepM_insert _ _ _ _ (useq_map_fresh a k f)).
      rewrite seq_S big_sepL_app /= right_id IH.
      rewrite comm. reflexivity.
  Qed.

  (* ===================================================================== *)
  (* §1 PURE EXTRACTION: what a fragment map says against an authority,    *)
  (* and what the free stack excludes.  Every conclusion here is PURE, so   *)
  (* a caller's [iDestruct ... as %H] consumes nothing.                     *)
  (* ===================================================================== *)

  (* a uniform-dq fragment map is a submap of its authority *)
  Local Lemma ghost_frags_sub (γ : gname) (q : Qp) (Md T : gmap Z (bv 8))
      (dq : dfrac) :
    ghost_map_auth γ q Md -∗ ([∗ map] a ↦ b ∈ T, a ↪[γ]{dq} b) -∗ ⌜ T ⊆ Md ⌝.
  Proof using .
    induction T as [| a b T Ha IH] using map_ind.
    - iIntros "_ _". iPureIntro. apply map_empty_subseteq.
    - iIntros "Hauth HT".
      rewrite big_sepM_insert; [ | exact Ha ].
      iDestruct "HT" as "[Hb HT]".
      iDestruct (ghost_map_lookup with "Hauth Hb") as %Hb.
      iDestruct (IH with "Hauth HT") as %Hsub.
      iPureIntro. exact (map_insert_sub T Md a b Hb Hsub).
  Qed.

  (* a FULL fragment map is disjoint from any other fragment map: full
     ownership composes with nothing *)
  Local Lemma ghost_frags_full_disjoint (γ : gname) (F G : gmap Z (bv 8))
      (dq : dfrac) :
    ([∗ map] a ↦ b ∈ F, a ↪[γ] b) -∗
    ([∗ map] a ↦ b ∈ G, a ↪[γ]{dq} b) -∗ ⌜ F ##ₘ G ⌝.
  Proof using .
    induction F as [| a b F Ha IH] using map_ind.
    - iIntros "_ _". iPureIntro. apply map_disjoint_empty_l.
    - iIntros "HF HG".
      rewrite big_sepM_insert; [ | exact Ha ].
      iDestruct "HF" as "[Hb HF]".
      iDestruct (IH with "HF HG") as %Hd.
      destruct (G !! a) as [g |] eqn:HGa.
      + iDestruct (big_sepM_lookup_acc _ _ a g HGa with "HG") as "[Hg _]".
        iDestruct (ghost_map_elem_valid_2 with "Hb Hg") as %[Hv _].
        destruct (dfrac_full_absurd dq Hv).
      + iPureIntro. apply map_disjoint_insert_l_2; [ exact HGa | exact Hd ].
  Qed.

  (* two fragment maps agree wherever they overlap *)
  Local Lemma ghost_frags_agree (γ : gname) (dq1 dq2 : dfrac)
      (T1 T2 : gmap Z (bv 8)) :
    ([∗ map] a ↦ b ∈ T1, a ↪[γ]{dq1} b) -∗
    ([∗ map] a ↦ b ∈ T2, a ↪[γ]{dq2} b) -∗
    ⌜ forall (a : Z) (b1 b2 : bv 8),
        T1 !! a = Some b1 -> T2 !! a = Some b2 -> b1 = b2 ⌝.
  Proof using .
    induction T2 as [| a b T2 Ha IH] using map_ind.
    - iIntros "_ _". iPureIntro. intros a b1 b2 _ Hb2.
      rewrite lookup_empty in Hb2. discriminate Hb2.
    - iIntros "H1 H2".
      rewrite big_sepM_insert; [ | exact Ha ].
      iDestruct "H2" as "[Hb H2]".
      iDestruct (IH with "H1 H2") as %HIH.
      destruct (T1 !! a) as [b1 |] eqn:H1a.
      + iDestruct (big_sepM_lookup_acc _ _ a b1 H1a with "H1") as "[Hb1 _]".
        iDestruct (ghost_map_elem_agree with "Hb1 Hb") as %Heq.
        iPureIntro. intros a' b1' b2' Hl1 Hl2.
        destruct (decide (a = a')) as [<- | Hne].
        * rewrite lookup_insert in Hl2. injection Hl2 as <-.
          rewrite H1a in Hl1. injection Hl1 as <-. exact Heq.
        * rewrite lookup_insert_ne in Hl2; [ | exact Hne ].
          exact (HIH a' b1' b2' Hl1 Hl2).
      + iPureIntro. intros a' b1' b2' Hl1 Hl2.
        destruct (decide (a = a')) as [<- | Hne].
        * rewrite H1a in Hl1. discriminate Hl1.
        * rewrite lookup_insert_ne in Hl2; [ | exact Hne ].
          exact (HIH a' b1' b2' Hl1 Hl2).
  Qed.

  (* a union of persistent big-ops, no disjointness required *)
  Local Lemma pers_map_union (Φ : Z -> bv 8 -> iProp Σ)
      `{!forall a b, Persistent (Φ a b)} (T1 T2 : gmap Z (bv 8)) :
    ([∗ map] a ↦ b ∈ T1, Φ a b) -∗ ([∗ map] a ↦ b ∈ T2, Φ a b) -∗
    ([∗ map] a ↦ b ∈ T1 ∪ T2, Φ a b).
  Proof using .
    iIntros "#H1 #H2". iApply big_sepM_intro.
    iIntros "!>" (k x Hk).
    apply lookup_union_Some_raw in Hk.
    destruct Hk as [Hk | [_ Hk]].
    - iApply (big_sepM_lookup _ _ k x Hk with "H1").
    - iApply (big_sepM_lookup _ _ k x Hk with "H2").
  Qed.

  (* ===================================================================== *)
  (* §3 THE MINT: a SECOND heap over the same image.                       *)
  (*                                                                       *)
  (* The semantic heart of fork.  Given the parent's heap and a designated *)
  (* text/read-only/exclusive footprint of it, mint a fresh gname triple   *)
  (* over the SAME image whose fragments mirror exactly that footprint --  *)
  (* and hand the parent everything back untouched.  Sound because it is   *)
  (* allocation: the child's authorities are fresh, and their contents are *)
  (* submaps of the image the parent's own authorities already vouch for.  *)
  (*                                                                       *)
  (* The child's slack is EMPTY: its data authority holds exactly the      *)
  (* mirrored fragments, so a child that wants sbrk must be given slack    *)
  (* explicitly when the sbrk row exists.                                  *)
  (* ===================================================================== *)
  Lemma uheap_fork (γt γd γs : gname) (M : gmap Z (bv 8))
      (pm : gmap (mword 27) uperm) (szv : Z) (Ft Fp F : gmap Z (bv 8)) :
    uheap γt γd γs M pm szv -∗
    ([∗ map] a ↦ b ∈ Ft, utext γt a b) -∗
    ([∗ map] a ↦ b ∈ Fp, ubyteq γd DfracDiscarded a b) -∗
    ([∗ map] a ↦ b ∈ F, ubyte γd a b) -∗
    |==> uheap γt γd γs M pm szv ∗ ([∗ map] a ↦ b ∈ F, ubyte γd a b) ∗
         ∃ γt' γd' γs' : gname,
           uheap γt' γd' γs' M pm szv ∗ usz γs' szv ∗
           ([∗ map] a ↦ b ∈ Ft, utext γt' a b) ∗
           ([∗ map] a ↦ b ∈ Fp, ubyteq γd' DfracDiscarded a b) ∗
           ([∗ map] a ↦ b ∈ F, ubyte γd' a b).
  Proof using .
    iIntros "Hheap #Htf Hpf Hdf".
    iDestruct "Hheap" as (Mt Md Mslack)
      "(%Hst & %Hsd & %Hdisj & %Hcan & %Hx & %Hxw & %Hw & Ht & Hd & Hszg & %Hsl & %Hstop & Hslack)".
    (* ---- pure inventory, all non-consuming ---- *)
    iDestruct (ghost_frags_sub γt 1 Mt Ft DfracDiscarded with "Ht Htf") as %HFt.
    iDestruct (ghost_frags_sub γd 1 Md Fp DfracDiscarded with "Hd Hpf") as %HFp.
    iDestruct (ghost_frags_sub γd 1 Md F (DfracOwn 1) with "Hd Hdf") as %HF.
    iDestruct (ghost_frags_full_disjoint γd F Fp DfracDiscarded
                 with "Hdf Hpf") as %HFFp.
    set (Fd := F ∪ Fp).
    assert (HFdMd : Fd ⊆ Md)
      by (apply map_union_sub; [ exact HF | exact HFp ]).
    assert (HFdM : Fd ⊆ M) by (etransitivity; [ exact HFdMd | exact Hsd ]).
    (* THE CHILD'S FRAGMENTS ARE ALL BELOW THE BREAK, and the reason is the
       invariant's own boundary: a data byte at or above it is the SLACK's,
       which the invariant holds EXCLUSIVELY, so a fragment the process (or
       a persisted area) holds there would be a second claim on it. *)
    iAssert (⌜ forall a : Z, is_Some (Fd !! a) -> a < szv ⌝)%I
      with "[Hslack Hdf Hpf]" as %Hbelow.
    { rewrite bi.pure_forall. iIntros (a). rewrite bi.pure_impl. iIntros (Ha).
      destruct (decide (a < szv)) as [Hlt | Hge]; [ iPureIntro; exact Hlt | ].
      iExFalso.
      assert (HMd : is_Some (Md !! a))
        by (destruct Ha as [b Hb]; exists b;
            exact (proj1 (map_subseteq_spec Fd Md) HFdMd a b Hb)).
      assert (Hge' : szv <= a) by lia.
      destruct (proj2 (Hsl a) (conj HMd Hge')) as [b0 Hb0].
      iDestruct (big_sepM_lookup _ _ a b0 Hb0 with "Hslack") as "Hinv".
      destruct Ha as [b1 Hb1].
      destruct (proj1 (lookup_union_Some F Fp a b1 HFFp) Hb1) as [HF1 | HFp1].
      - iDestruct (big_sepM_lookup _ _ a b1 HF1 with "Hdf") as "Hf".
        iDestruct (ghost_map_elem_valid_2 with "Hinv Hf") as %[Hv _].
        done.
      - iDestruct (big_sepM_lookup _ _ a b1 HFp1 with "Hpf") as "Hf".
        iDestruct (ghost_map_elem_valid_2 with "Hinv Hf") as %[Hv _].
        done. }
    (* ---- the three fresh ghosts ---- *)
    iMod (ghost_map_alloc Mt) as (γt') "[Ht' Htfr]".
    iAssert (|==> [∗ map] a ↦ b ∈ Mt, utext γt' a b)%I
      with "[Htfr]" as ">#Htall'".
    { iApply big_sepM_bupd. iApply (big_sepM_impl with "Htfr").
      iIntros "!>" (a b _) "H". rewrite /utext.
      iApply (ghost_map_elem_persist with "H"). }
    iMod (ghost_map_alloc Fd) as (γd') "[Hd' Hdfr]".
    iMod (ghost_var_alloc szv) as (γs') "Hsz'".
    iEval (rewrite -Qp.half_half) in "Hsz'".
    iDestruct (ghost_var_split with "Hsz'") as "[HszA' HszF']".
    (* ---- route the child's fragments ---- *)
    iEval (rewrite /Fd (big_sepM_union _ _ _ HFFp)) in "Hdfr".
    iDestruct "Hdfr" as "[HdF' HdFp']".
    iMod (uarea_persist γd' Fp with "HdFp'") as "#HdFp'".
    iAssert ([∗ map] a ↦ b ∈ Ft, utext γt' a b)%I as "#Htf'".
    { iApply (big_sepM_subseteq
                (fun (a : Z) (b : bv 8) => utext γt' a b) Mt Ft HFt).
      iExact "Htall'". }
    (* ---- reassemble the parent, hand over the child ---- *)
    iModIntro.
    iSplitL "Ht Hd Hszg Hslack".
    { iExists Mt, Md, Mslack. iFrame "Ht Hd Hszg Hslack".
      iPureIntro. split_and!; assumption. }
    iFrame "Hdf".
    iExists γt', γd', γs'.
    iSplitL "Ht' Hd' HszA'".
    { (* the child's heap invariant, clause by clause *)
      iExists Mt, Fd, ∅.
      iSplitR; [ iPureIntro; exact Hst | ].
      iSplitR; [ iPureIntro; exact HFdM | ].
      iSplitR;
        [ iPureIntro; exact (map_disjoint_weaken_r Mt Fd Md Hdisj HFdMd) | ].
      iSplitR; [ iPureIntro; exact Hcan | ].
      iSplitR; [ iPureIntro; exact Hx | ].
      iSplitR; [ iPureIntro; exact Hxw | ].
      iSplitR.
      { iPureIntro. intros a Ha. apply Hw.
        destruct Ha as [b Hb].
        exists b. exact (proj1 (map_subseteq_spec Fd Md) HFdMd a b Hb). }
      iFrame "Ht' Hd' HszA'".
      iSplitR.
      { iPureIntro. intro a. split.
        - intros [b Hb]. rewrite lookup_empty in Hb. discriminate Hb.
        - intros [Ha Hge]. exfalso. pose proof (Hbelow a Ha). lia. }
      iSplitR; [ iPureIntro; exact Hstop | ].
      rewrite big_sepM_empty. done. }
    iFrame "HszF'".
    iSplitR; [ iExact "Htf'" | ].
    iSplitR; [ iExact "HdFp'" | ].
    iExact "HdF'".
  Qed.

  (* ===================================================================== *)
  (* §4 THE PAYLOAD CLASS.                                                 *)
  (*                                                                       *)
  (* [P : gname -> gname -> gname -> iProp] is the caller's facts AS A     *)
  (* FAMILY over the heap names -- in this tree every heap predicate is    *)
  (* already written that way, so a payload is an application, not an      *)
  (* encoding.  [Forkable P] says P factors through a footprint:           *)
  (*                                                                       *)
  (*   reveal   its text map (persistent), its read-only data map          *)
  (*            (persistent) and its exclusive data map,                   *)
  (*   restore  the payload from the exclusive map (the persistent maps    *)
  (*            were duplicated at the reveal),                            *)
  (*   rebuild  [P γt' γd' γs'] AT ANY NAMES from mirrored fragments at    *)
  (*            the same dfracs.                                           *)
  (*                                                                       *)
  (* The rebuild is a [□]: it captures only pure facts and persistent      *)
  (* views, which is what makes it usable inside the child's slot.  A      *)
  (* constant family that smuggles a non-heap resource (a protocol token)  *)
  (* has no instance, and that is the point -- see the header.             *)
  (* ===================================================================== *)
  Class Forkable (P : gname -> gname -> gname -> iProp Σ) : Prop :=
    forkable : forall γt γd γs : gname,
      P γt γd γs -∗
      ∃ Ft Fp F : gmap Z (bv 8),
        ([∗ map] a ↦ b ∈ Ft, utext γt a b) ∗
        ([∗ map] a ↦ b ∈ Fp, ubyteq γd DfracDiscarded a b) ∗
        ([∗ map] a ↦ b ∈ F, ubyte γd a b) ∗
        (([∗ map] a ↦ b ∈ F, ubyte γd a b) -∗ P γt γd γs) ∗
        □ (∀ γt' γd' γs' : gname,
             ([∗ map] a ↦ b ∈ Ft, utext γt' a b) -∗
             ([∗ map] a ↦ b ∈ Fp, ubyteq γd' DfracDiscarded a b) -∗
             ([∗ map] a ↦ b ∈ F, ubyte γd' a b) ==∗
             P γt' γd' γs').

  (* families with equivalent bodies are interchangeably Forkable; the
     workhorse for every instance that is a Definition over the primitives *)
  Lemma Forkable_ext (P Q : gname -> gname -> gname -> iProp Σ) :
    (forall γt γd γs, P γt γd γs ⊣⊢ Q γt γd γs) ->
    Forkable P -> Forkable Q.
  Proof using .
    intros Heq HP γt γd γs.
    iIntros "HQ".
    iAssert (P γt γd γs) with "[HQ]" as "HP".
    { rewrite Heq. iExact "HQ". }
    iDestruct (HP γt γd γs with "HP") as (Ft Fp F) "(#HT & #HD & HF & HR & #HB)".
    iExists Ft, Fp, F. iFrame "HT HD HF".
    iSplitL "HR".
    { iIntros "HF". rewrite -Heq. iApply ("HR" with "HF"). }
    iModIntro. iIntros (γt' γd' γs') "#HT' #HD' HF'".
    iMod ("HB" $! γt' γd' γs' with "HT' HD' HF'") as "HP'".
    iModIntro. rewrite -Heq. iExact "HP'".
  Qed.

  Global Instance forkable_emp : Forkable (fun _ _ _ => emp%I).
  Proof using .
    intros γt γd γs. iIntros "_".
    iExists ∅, ∅, ∅. rewrite !big_sepM_empty.
    iSplitR; [ done | ]. iSplitR; [ done | ]. iSplitR; [ done | ].
    iSplitR; [ iIntros "_"; done | ].
    iModIntro. iIntros (γt' γd' γs') "_ _ _". iModIntro. done.
  Qed.

  Global Instance forkable_pure (φ : Prop) : Forkable (fun _ _ _ => ⌜φ⌝%I).
  Proof using .
    intros γt γd γs. iIntros "%Hφ".
    iExists ∅, ∅, ∅. rewrite !big_sepM_empty.
    iSplitR; [ done | ]. iSplitR; [ done | ]. iSplitR; [ done | ].
    iSplitR; [ iIntros "_"; iPureIntro; exact Hφ | ].
    iModIntro. iIntros (γt' γd' γs') "_ _ _". iModIntro.
    iPureIntro. exact Hφ.
  Qed.

  Global Instance forkable_sep (P Q : gname -> gname -> gname -> iProp Σ) :
    Forkable P -> Forkable Q ->
    Forkable (fun γt γd γs => (P γt γd γs ∗ Q γt γd γs)%I).
  Proof using .
    intros HP HQ γt γd γs. iIntros "[HP HQ]".
    iDestruct (HP γt γd γs with "HP")
      as (Ft1 Fp1 F1) "(#HT1 & #HD1 & HF1 & HR1 & #HB1)".
    iDestruct (HQ γt γd γs with "HQ")
      as (Ft2 Fp2 F2) "(#HT2 & #HD2 & HF2 & HR2 & #HB2)".
    (* the exclusive maps are disjoint (full composes with nothing); the
       persistent maps agree on their overlaps *)
    iDestruct (ghost_frags_full_disjoint γd F1 F2 (DfracOwn 1)
                 with "HF1 HF2") as %HF12.
    iDestruct (ghost_frags_agree γt DfracDiscarded DfracDiscarded Ft1 Ft2
                 with "HT1 HT2") as %HTag.
    iDestruct (ghost_frags_agree γd DfracDiscarded DfracDiscarded Fp1 Fp2
                 with "HD1 HD2") as %HDag.
    assert (HT1s : Ft1 ⊆ Ft1 ∪ Ft2) by apply map_union_subseteq_l.
    assert (HT2s : Ft2 ⊆ Ft1 ∪ Ft2) by (apply map_sub_union_r_agree; exact HTag).
    assert (HD1s : Fp1 ⊆ Fp1 ∪ Fp2) by apply map_union_subseteq_l.
    assert (HD2s : Fp2 ⊆ Fp1 ∪ Fp2) by (apply map_sub_union_r_agree; exact HDag).
    iExists (Ft1 ∪ Ft2), (Fp1 ∪ Fp2), (F1 ∪ F2).
    iSplitR; [ iApply (pers_map_union with "HT1 HT2") | ].
    iSplitR; [ iApply (pers_map_union with "HD1 HD2") | ].
    iSplitL "HF1 HF2".
    { iEval (rewrite (big_sepM_union _ _ _ HF12)). iFrame "HF1 HF2". }
    iSplitL "HR1 HR2".
    { iIntros "HF".
      iEval (rewrite (big_sepM_union _ _ _ HF12)) in "HF".
      iDestruct "HF" as "[HF1 HF2]".
      iSplitL "HR1 HF1";
        [ iApply ("HR1" with "HF1") | iApply ("HR2" with "HF2") ]. }
    iModIntro. iIntros (γt' γd' γs') "#HT' #HD' HF'".
    iEval (rewrite (big_sepM_union _ _ _ HF12)) in "HF'".
    iDestruct "HF'" as "[HF1' HF2']".
    iDestruct (big_sepM_subseteq
                 (fun (a : Z) (b : bv 8) => utext γt' a b)
                 (Ft1 ∪ Ft2) Ft1 HT1s with "HT'") as "#HT1'".
    iDestruct (big_sepM_subseteq
                 (fun (a : Z) (b : bv 8) => utext γt' a b)
                 (Ft1 ∪ Ft2) Ft2 HT2s with "HT'") as "#HT2'".
    iDestruct (big_sepM_subseteq
                 (fun (a : Z) (b : bv 8) => ubyteq γd' DfracDiscarded a b)
                 (Fp1 ∪ Fp2) Fp1 HD1s with "HD'") as "#HD1'".
    iDestruct (big_sepM_subseteq
                 (fun (a : Z) (b : bv 8) => ubyteq γd' DfracDiscarded a b)
                 (Fp1 ∪ Fp2) Fp2 HD2s with "HD'") as "#HD2'".
    iMod ("HB1" $! γt' γd' γs' with "HT1' HD1' HF1'") as "HP'".
    iMod ("HB2" $! γt' γd' γs' with "HT2' HD2' HF2'") as "HQ'".
    iModIntro. iFrame "HP' HQ'".
  Qed.

  Global Instance forkable_exist {A : Type}
      (Φ : A -> gname -> gname -> gname -> iProp Σ) :
    (forall x : A, Forkable (Φ x)) ->
    Forkable (fun γt γd γs => (∃ x : A, Φ x γt γd γs)%I).
  Proof using .
    intros HΦ γt γd γs. iIntros "HP".
    iDestruct "HP" as (x) "HP".
    iDestruct (HΦ x γt γd γs with "HP")
      as (Ft Fp F) "(#HT & #HD & HF & HR & #HB)".
    iExists Ft, Fp, F. iFrame "HT HD HF".
    iSplitL "HR". { iIntros "HF". iExists x. iApply ("HR" with "HF"). }
    iModIntro. iIntros (γt' γd' γs') "#HT' #HD' HF'".
    iMod ("HB" $! γt' γd' γs' with "HT' HD' HF'") as "HP'".
    iModIntro. iExists x. iExact "HP'".
  Qed.

  Global Instance forkable_big_sepL {A : Type} (l : list A)
      (Φ : nat -> A -> gname -> gname -> gname -> iProp Σ) :
    (forall (i : nat) (x : A), Forkable (Φ i x)) ->
    Forkable (fun γt γd γs => ([∗ list] i ↦ x ∈ l, Φ i x γt γd γs)%I).
  Proof using .
    revert Φ. induction l as [| y l IH]; intros Φ HΦ.
    - eapply Forkable_ext; [ | exact forkable_emp ].
      intros γt γd γs. rewrite big_sepL_nil. reflexivity.
    - eapply Forkable_ext;
        [ | exact (forkable_sep _ _ (HΦ 0%nat y)
                     (IH (fun i x => Φ (S i) x) (fun i x => HΦ (S i) x))) ].
      intros γt γd γs. rewrite big_sepL_cons. reflexivity.
  Qed.

  (* ---- the primitives ------------------------------------------------- *)

  Global Instance forkable_ubyte (a : Z) (b : bv 8) :
    Forkable (fun _ γd _ => ubyte γd a b).
  Proof using .
    intros γt γd γs. iIntros "Hb".
    iExists ∅, ∅, {[ a := b ]}.
    rewrite !big_sepM_empty !big_sepM_singleton.
    iSplitR; [ done | ]. iSplitR; [ done | ].
    iFrame "Hb".
    iSplitR; [ iIntros "Hb"; iExact "Hb" | ].
    iModIntro. iIntros (γt' γd' γs') "_ _ Hb'". iModIntro.
    iEval (rewrite big_sepM_singleton) in "Hb'". iExact "Hb'".
  Qed.

  Global Instance forkable_ubyteq_disc (a : Z) (b : bv 8) :
    Forkable (fun _ γd _ => ubyteq γd DfracDiscarded a b).
  Proof using .
    intros γt γd γs. iIntros "#Hb".
    iExists ∅, {[ a := b ]}, ∅.
    rewrite !big_sepM_empty !big_sepM_singleton.
    iSplitR; [ done | ]. iSplitR; [ iExact "Hb" | ]. iSplitR; [ done | ].
    iSplitR; [ iIntros "_"; iExact "Hb" | ].
    iModIntro. iIntros (γt' γd' γs') "_ #Hb' _". iModIntro.
    iEval (rewrite big_sepM_singleton) in "Hb'". iExact "Hb'".
  Qed.

  Global Instance forkable_utext (a : Z) (b : bv 8) :
    Forkable (fun γt _ _ => utext γt a b).
  Proof using .
    intros γt γd γs. iIntros "#Hb".
    iExists {[ a := b ]}, ∅, ∅.
    rewrite !big_sepM_empty !big_sepM_singleton.
    iSplitR; [ iExact "Hb" | ]. iSplitR; [ done | ]. iSplitR; [ done | ].
    iSplitR; [ iIntros "_"; iExact "Hb" | ].
    iModIntro. iIntros (γt' γd' γs') "#Hb' _ _". iModIntro.
    iEval (rewrite big_sepM_singleton) in "Hb'". iExact "Hb'".
  Qed.

  (* a whole text map at once -- [utext_all]'s shape, and the payload that
     hands the child the parent's entire text vocabulary *)
  Global Instance forkable_utext_map (T : gmap Z (bv 8)) :
    Forkable (fun γt _ _ => ([∗ map] a ↦ b ∈ T, utext γt a b)%I).
  Proof using .
    intros γt γd γs. iIntros "#Hm".
    iExists T, ∅, ∅.
    rewrite !big_sepM_empty.
    iSplitR; [ iExact "Hm" | ]. iSplitR; [ done | ]. iSplitR; [ done | ].
    iSplitR; [ iIntros "_"; iExact "Hm" | ].
    iModIntro. iIntros (γt' γd' γs') "#Hm' _ _". iModIntro. iExact "Hm'".
  Qed.

  (* ...and a whole PERSISTED DATA map at once, [forkable_utext_map]'s twin
     on the other half of the heap.  init's argument vector is what needs
     it: sixteen read-only .data bytes the parent keeps and the child
     inherits. *)
  Global Instance forkable_ubyteq_map (D : gmap Z (bv 8)) :
    Forkable (fun _ γd _ => ([∗ map] a ↦ b ∈ D, ubyteq γd DfracDiscarded a b)%I).
  Proof using .
    intros γt γd γs. iIntros "#Hm".
    iExists ∅, D, ∅.
    rewrite !big_sepM_empty.
    iSplitR; [ done | ]. iSplitR; [ iExact "Hm" | ]. iSplitR; [ done | ].
    iSplitR; [ iIntros "_"; iExact "Hm" | ].
    iModIntro. iIntros (γt' γd' γs') "_ #Hm' _". iModIntro. iExact "Hm'".
  Qed.

  Global Instance forkable_utext_all (M : gmap Z (bv 8))
      (pm : gmap (mword 27) uperm) :
    Forkable (fun γt _ _ => utext_all γt M pm).
  Proof using .
    eapply Forkable_ext; [ | exact (forkable_utext_map (utext_part M pm)) ].
    intros γt γd γs. rewrite /utext_all. reflexivity.
  Qed.

  (* ---- runs ----------------------------------------------------------- *)

  Global Instance forkable_ubytes (a : Z) (n : nat) (f : nat -> bv 8) :
    Forkable (fun _ γd _ => ubytes γd a n f).
  Proof using .
    intros γt γd γs. iIntros "Hb".
    iExists ∅, ∅, (useq_map a n f).
    rewrite !big_sepM_empty.
    iSplitR; [ done | ]. iSplitR; [ done | ].
    iSplitL "Hb".
    { iEval (rewrite (big_seq_map (fun k b => ubyte γd k b) a n f)).
      iEval (rewrite /ubytes /ubytesq /ubyte) in "Hb". iExact "Hb". }
    iSplitR.
    { iIntros "Hb".
      iEval (rewrite (big_seq_map (fun k b => ubyte γd k b) a n f)) in "Hb".
      iEval (rewrite /ubytes /ubytesq /ubyte). iExact "Hb". }
    iModIntro. iIntros (γt' γd' γs') "_ _ Hb'". iModIntro.
    iEval (rewrite (big_seq_map (fun k b => ubyte γd' k b) a n f)) in "Hb'".
    iEval (rewrite /ubytes /ubytesq /ubyte). iExact "Hb'".
  Qed.

  Global Instance forkable_ubytesq_disc (a : Z) (n : nat) (f : nat -> bv 8) :
    Forkable (fun _ γd _ => ubytesq γd DfracDiscarded a n f).
  Proof using .
    intros γt γd γs. iIntros "#Hb".
    iExists ∅, (useq_map a n f), ∅.
    rewrite !big_sepM_empty.
    iSplitR; [ done | ].
    iSplitR.
    { iEval (rewrite (big_seq_map (fun k b => ubyteq γd DfracDiscarded k b) a n f)).
      iEval (rewrite /ubytesq) in "Hb". iExact "Hb". }
    iSplitR; [ done | ].
    iSplitR; [ iIntros "_"; iExact "Hb" | ].
    iModIntro. iIntros (γt' γd' γs') "_ #Hb' _". iModIntro.
    iEval (rewrite (big_seq_map (fun k b => ubyteq γd' DfracDiscarded k b) a n f))
      in "Hb'".
    iEval (rewrite /ubytesq). iExact "Hb'".
  Qed.

  Global Instance forkable_utext_run (a : Z) (n : nat) (f : nat -> bv 8) :
    Forkable (fun γt _ _ =>
                ([∗ list] j ∈ seq 0 n, utext γt (a + Z.of_nat j)%Z (f j))%I).
  Proof using .
    intros γt γd γs. iIntros "#Hb".
    iExists (useq_map a n f), ∅, ∅.
    rewrite !big_sepM_empty.
    iSplitR.
    { iEval (rewrite (big_seq_map (fun k b => utext γt k b) a n f)).
      iExact "Hb". }
    iSplitR; [ done | ]. iSplitR; [ done | ].
    iSplitR; [ iIntros "_"; iExact "Hb" | ].
    iModIntro. iIntros (γt' γd' γs') "#Hb' _ _". iModIntro.
    iEval (rewrite (big_seq_map (fun k b => utext γt' k b) a n f)) in "Hb'".
    iExact "Hb'".
  Qed.

  Global Instance forkable_uword (a : Z) (w : mword 64) :
    Forkable (fun _ γd _ => uword γd a w).
  Proof using .
    eapply Forkable_ext; [ | exact (forkable_ubytes a 8 (nth_byte w)) ].
    intros γt γd γs. rewrite /uword /uwordq. reflexivity.
  Qed.

  Global Instance forkable_uwordq_disc (a : Z) (w : mword 64) :
    Forkable (fun _ γd _ => uwordq γd DfracDiscarded a w).
  Proof using .
    eapply Forkable_ext; [ | exact (forkable_ubytesq_disc a 8 (nth_byte w)) ].
    intros γt γd γs. rewrite /uwordq. reflexivity.
  Qed.

  (* THE FREE STACK IS A PAYLOAD TOO: pure alignment over a list of
     existentially-valued words, every piece of which the class already
     covers.  This is what licenses the fork leaf's stack mirror -- the
     leaf bundles [P ∗ ustack] into one payload and never special-cases
     the stack. *)
  Global Instance forkable_ustack (sp : mword 64) (n : nat) :
    Forkable (fun _ γd _ => ustack γd sp n).
  Proof using .
    eapply Forkable_ext.
    2: {
      apply forkable_sep; [ apply forkable_pure | ].
      apply (forkable_big_sepL (seq 0 n)
               (fun (_ i : nat) (_ γd _ : gname) =>
                  (∃ w : mword 64,
                     uword γd (uint sp - 8 * (Z.of_nat i + 1)) w)%I)).
      intros _ i.
      apply forkable_exist. intros w. apply forkable_uword. }
    intros γt γd γs. rewrite /ustack /ustack_body. reflexivity.
  Qed.

  (* ---- strings and the argument vector -------------------------------- *)

  Global Instance forkable_ustr (a : Z) (len : nat) (f : nat -> bv 8) :
    Forkable (fun _ γd _ => ustr γd (DfracOwn 1) a len f).
  Proof using .
    eapply Forkable_ext.
    2: {
      apply forkable_sep; [ apply forkable_pure | ].
      apply forkable_sep; [ apply forkable_pure | ].
      apply (forkable_sep
               (fun _ γd _ => ubytesq γd (DfracOwn 1) a len f)
               (fun _ γd _ => ubyteq γd (DfracOwn 1) (a + Z.of_nat len)%Z ubyte0)).
      - eapply Forkable_ext; [ | exact (forkable_ubytes a len f) ].
        intros γt γd γs. rewrite /ubytes. reflexivity.
      - eapply Forkable_ext;
          [ | exact (forkable_ubyte (a + Z.of_nat len)%Z ubyte0) ].
        intros γt γd γs. rewrite /ubyte. reflexivity. }
    intros γt γd γs. rewrite /ustr. reflexivity.
  Qed.

  Global Instance forkable_ustr_disc (a : Z) (len : nat) (f : nat -> bv 8) :
    Forkable (fun _ γd _ => ustr γd DfracDiscarded a len f).
  Proof using .
    eapply Forkable_ext.
    2: {
      apply forkable_sep; [ apply forkable_pure | ].
      apply forkable_sep; [ apply forkable_pure | ].
      apply (forkable_sep
               (fun _ γd _ => ubytesq γd DfracDiscarded a len f)
               (fun _ γd _ => ubyteq γd DfracDiscarded (a + Z.of_nat len)%Z ubyte0)).
      - apply forkable_ubytesq_disc.
      - apply forkable_ubyteq_disc. }
    intros γt γd γs. rewrite /ustr. reflexivity.
  Qed.

  Global Instance forkable_uargv (av : Z) (args : list uarg) :
    Forkable (fun _ γd _ => uargv γd av args).
  Proof using .
    eapply Forkable_ext.
    2: {
      apply forkable_sep; [ apply forkable_pure | ].
      apply forkable_sep; [ apply forkable_pure | ].
      apply (forkable_big_sepL args
               (fun i g _ γd _ =>
                  (uwordq γd DfracDiscarded (av + 8 * Z.of_nat i)
                     (mword_of_int (ua_ptr g)) ∗
                   ustr γd DfracDiscarded (ua_ptr g) (ua_len g) (ua_bytes g))%I)).
      intros i g.
      apply (forkable_sep
               (fun _ γd _ => uwordq γd DfracDiscarded (av + 8 * Z.of_nat i)
                                (mword_of_int (ua_ptr g)))
               (fun _ γd _ => ustr γd DfracDiscarded (ua_ptr g) (ua_len g)
                                (ua_bytes g)));
        [ apply forkable_uwordq_disc | apply forkable_ustr_disc ]. }
    intros γt γd γs. rewrite /uargv. reflexivity.
  Qed.

  (* ===================================================================== *)
  (* §5 THE LEAF: ecall at fork.                                           *)
  (*                                                                       *)
  (* The contract returns twice.  The PARENT keeps its gnames, its payload *)
  (* and its free stack, learns r <> 0, and continues like a quiet         *)
  (* syscall.  The CHILD gets a FRESH gname triple: the same payload at    *)
  (* the new names, the same break, and a [urun] whose free stack mirrors  *)
  (* the parent's -- same registers but a0 = 0, same pc + 4, same [avail]. *)
  (*                                                                       *)
  (* Anything the caller holds that is NOT in [P] splits between the two   *)
  (* continuations by ordinary separation at the [∗] below -- that is      *)
  (* where shared, non-address-space resources (fds, protocol state) get   *)
  (* distributed, and the leaf neither knows nor cares.                    *)
  (* ===================================================================== *)
  (* [D] IS THE CALLER'S OWN DESCRIPTOR HANDLES, and fork hands them back
     TWICE -- once to each process, at that process's own ghost name.  That
     is what fork does to descriptors: the child's table is a copy, so every
     descriptor the parent held open the child holds open too, and each may
     close its own.
     STATED AT [D] RATHER THAN AT THE WHOLE TABLE because the table lives
     inside [UkRun.urun]'s existential and no caller can name it.
     [UserFd.ufd_sub] turns the caller's handles into the sub-map fact that
     licenses re-minting them at the child's name, so a caller says only
     what it actually holds; one holding nothing passes the empty map and
     the two extra premises are [emp]. *)
  Lemma wp_uk_ecall_fork (N : uk_names Σ) (h : CpuId) (m : regfile)
      (pc : mword 64) (avail : nat) (szv : Z) (l : list fdstate)
      (D : gmap nat fdstate) (c : Z)
      (* THE CALLER'S LIVE CHILDREN, and THE PAYLOAD ITS CHILD'S EXIT WILL
         OWE IT.  Both are the program's choice: [S] because the key's
         children reading grows by the child's generation and [urun] hides
         the set existentially (the parent's half is what pins it, exactly
         as its [ucwd] pins the working directory), and [Q] because the
         parent is the party that decides what it wants back -- a program
         that wants nothing passes [fun _ => True]. *)
      (Sc : gset gname) (Q : Z -> iProp Σ)
      (* ...AND WHATEVER ELSE THE PARENT LENDS THE CHILD.  The payload [Q]
         is what the child's EXIT owes back; [Rc] is what the child is
         handed to run WITH, and it cannot ride in [P]: [Forkable] is by
         construction a family of ADDRESS-SPACE views re-minted at the
         child's fresh ghost names (its header: "a constant family that
         smuggles a non-heap resource has no instance"), while what a
         parent lends here is a protocol token at a FIXED name -- init
         lends the shell its half of the console position pair
         ([UserConsole.upos], app-echo.md "SH-LINE RULING").  A caller
         that lends nothing passes [emp]. *)
      (Rc : iProp Σ)
      (* ...AND THE SET THE CHILD'S RECORD IS MINTED AT (lane OFF-HAND-4,
         S1).  The PARENT chooses it: the child's table IS the parent's, so
         any superset of the parent's own held set is honest, and a parent
         that means its child to hold an offset half -- sh's REDIR child
         opens [f] on slot 1 at a held offset (design/app-file.md SS3) --
         has no other place to say so.  A parent that means nothing by it
         passes [ukn_held N]. *)
      (P : gname -> gname -> gname -> iProp Σ) `{FP : !Forkable P} :
    usysno m = USYS_fork ->
    is_aligned_vaddr (Virtaddr (add_vec_int pc 4)) 2 = true ->
    uinstr_is (ukn_t N) pc false (ECALL tt) -∗
    (* ...AND THE CHILD'S PAYLOAD ITSELF, at the kill status.  The parent
       chose [Q]; the child's RUN carries [Q (-1)] from its first
       instruction, because the kernel may tear the child down at any trap
       and nothing its program does could pay then
       ([UexecRet.uexec_pay_dep]).  So the resource crosses HERE: a parent
       that lends its child a resource lends it at the fork.  At
       [fun _ => True] it costs nothing. *)
    (* ...and the lend itself, which crosses on the same terms *)
    Rc -∗
    P (ukn_t N) (ukn_d N) (ukn_s N) -∗
    usz (ukn_s N) szv -∗
    UserFd.ustd (ukn_fd N) l -∗
    ([∗ map] fd ↦ st ∈ D, UserFd.ufd (ukn_fd N) fd st) -∗
    (* THE CALLER'S OWN HALF OF ITS WORKING DIRECTORY.  fork keeps the cwd
       ([UexecRet]'s child arm resumes the child at the parent's
       [uvis_cwd]), and the child's half has to be minted at a value this
       statement can NAME -- [urun]'s [cw] is existentially bound and
       cannot be.  So the parent hands its half in, agreement pins the
       key's [cw] to it, and both processes come out holding [c]: exactly
       what fork does to the descriptor ledger one line up. *)
    UserCwd.ucwd (ukn_cwd N) c -∗
    (* ...AND ITS OWN HALF OF ITS CHILDREN SET, for the cwd's reason: the
       set MOVES here, and an update needs both halves. *)
    UserChildren.uch (ukn_ch N) Sc -∗
    (* ...AND HOW A KILLER PAYS FOR THE CHILD (lane SELF-KILL, §4b'): the
       child's killed row publishes a wand from the application's TAINT
       ([RiscvPtsto.app_taint]) to the child's exit payload at -1 and
       allocproc founds it, so the FORKING PROGRAM supplies it here.  At
       [Q := fun _ => True] -- what a program that wants nothing back
       passes -- it is free. *)
    □ (app_taint -∗ Q (-1)) -∗
    urun N h m pc avail -∗
    ((∀ (h' : CpuId) (r : mword 64),
        ⌜r <> (mword_of_int 0 : mword 64)⌝ -∗
        (* FORK'S TWO ARMS, as the program sees them: it FAILED, returning
           -1, and the caller's children set is the one it had AND WHAT IT
           LENT ITS CHILD COMES BACK (lane FORK-REFUND: the kernel created
           no process, so nothing consumed [Rc] -- and a parent that could
           not get it back could not report the failure, since init's
           "init: fork failed" and sh's "fork" are printed on exactly the
           console credential the parent lends); or it returned the child's
           pid, and the parent gets [ChildTok.child_tok] -- the quarter a
           later wait() redeems -- beside the set grown by that child's
           generation, the lend having gone to the child. *)
        ((⌜r = (mword_of_int (-1) : mword 64)⌝ ∗
            UserChildren.uch (ukn_ch N) Sc ∗ Rc)
         ∨ ∃ (γ : gname) (pidv : mword 32),
             ⌜r = (sign_extend' 64 pidv : mword 64)⌝ ∗
             ⌜(1 <= bv_unsigned pidv <= PIDMAX)%Z⌝ ∗
             (* ...AND THE GENERATION IS FRESH (design app-pipe SS4.3y,
                lane SH-PIPE-ROUND-11): [UexecRet.ufork_ans]'s own row,
                which this arm was RE-SPELLING and dropping.  The child's
                generation was in no row of the <wait_lock> children map
                when kfork put it in the caller's, so the union beside it
                is a GROWTH BY ONE and not a no-op -- which is what lets a
                parent that forks twice tell its two children apart.  A
                consumer that does not want it introduces and drops it. *)
             ⌜γ ∉ Sc⌝ ∗
             child_tok γ pidv Q ∗
             UserChildren.uch (ukn_ch N) (Sc ∪ {[γ]})) -∗
        P (ukn_t N) (ukn_d N) (ukn_s N) -∗ usz (ukn_s N) szv -∗
        (* the parent keeps what it had: fork writes nothing into its table *)
        UserFd.ustd (ukn_fd N) l -∗
        ([∗ map] fd ↦ st ∈ D, UserFd.ufd (ukn_fd N) fd st) -∗
        (* ...and its working directory, which fork did not move *)
        UserCwd.ucwd (ukn_cwd N) c -∗
        urun N h' (<[Regidx (mword_of_int 10) := r]> m)
          (add_vec_int pc 4) avail -∗
        mWP (Loop : expr riscv_lang)) ∗
     (* THE CHILD GETS A FRESH DESCRIPTOR NAME TOO.  It already got a fresh
        heap triple -- its ghost state is not the parent's -- and the fd
        authority is no different: parent and child each own a full map, and
        one name could not carry both.  (This is why the descriptor name is a
        FIELD of the record rather than an ambient: an ambient name would
        make this arm unprovable.)  Its WORKING DIRECTORY is a fresh name
        for the same reason and at the same value: fork keeps the cwd.
        ...AND IT GETS THE HANDLES FOR EVERYTHING IT INHERITED, at that
        fresh name.  [fdv] is the PARENT's table -- fork copies it, which is
        what [UexecRet]'s child arm now says -- so the map is exactly what
        the parent had open, and each entry is a handle the child can spend
        on a close.  Without this the child could not close fd 0, the pipe
        ends its parent had just made, or anything else it did not itself
        open, which is what parked sh's runner.  The parent's own handles
        are NOT consumed: it keeps its table and its authority, and the
        child's are freshly minted at γfd'. *)
     (∀ (N' : uk_names Σ) (h' : CpuId) (γ' : gname),
        (* THE CHILD'S HELD SET IS THE ONE THE PARENT CHOSE (lane
           OFF-HAND-4, S1), exactly as its payload is. *)
        (* THE CHILD LEARNS ITS OWN PAYLOAD: what its exit owes its parent,
           persistent, out of the generation the kernel minted for it
           ([ChildTok.my_pay]).  A child that pays nothing ignores it.
           ...AND ITS RECORD IS KEYED AT IT: the arm MINTS the child's
           record, so it is the party that says what its [UkRun.ukn_pay]
           is, exactly as an entry constructor does. *)
        ⌜ ukn_pay N' = Q ⌝ -∗
        my_pay γ' Q -∗
        (* ...AND WHAT THE PARENT LENT IT, verbatim *)
        Rc -∗
        P (ukn_t N') (ukn_d N') (ukn_s N') -∗ usz (ukn_s N') szv -∗
        (* ...and the child gets the same descriptors at its OWN name --
           INCLUDING THE LEDGER, at the parent's own states: fork copies the
           table, so the child's standard streams are the parent's, and that
           is what lets a forked child redirect one ([close(1); dup(x)] in
           sh's PIPE runs in the child). *)
        UserFd.ustd (ukn_fd N') l -∗
        ([∗ map] fd ↦ st ∈ D, UserFd.ufd (ukn_fd N') fd st) -∗
        UserCwd.ucwd (ukn_cwd N') c -∗
        (* ...AND ITS OWN HALF OF ITS CHILDREN SET, at [∅] on the nose: a
           process that has just been created has created nothing
           ([UexecRet.uexec_fork_child_F]'s row).  No binder, because there
           is only one value it can be -- which is why this arm can name
           it where it cannot name the parent's. *)
        UserChildren.uch (ukn_ch N') ∅ -∗
        (* ...AND ITS OWN PID, AS A HANDLE, WITH THE ONE FACT THAT MAKES IT
           WORTH HAVING (lane TRAP-ROWS-4, B1b).  The number <allocpid>
           gave it, at the child record's own ghost name, AND that the
           number is not <init>'s -- which is the literal 1, registered
           forever, so the pid scan that found this one refutes it
           ([SlotGen.init_reg_ne], via
           [SpecAllocproc.allocproc_post]'s uncounted arm).  A forked child
           is the one process that can PROVE it is not <init>, and that is
           exactly what it spends on wait's reaping arm
           ([UkRunSys.wp_uk_ecall_wait_null_pid]). *)
        (∃ p : Z, ⌜p <> 1⌝ ∗ UserChildren.upid (ukn_pid N') p) -∗
        urun N' h'
          (<[Regidx (mword_of_int 10) := (mword_of_int 0 : mword 64)]> m)
          (add_vec_int pc 4) avail -∗
        mWP (Loop : expr riscv_lang))) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intros Hn Hal4. iIntros "#Hi HRc HP Hsz Hstd HD Hcwd Hchf #Hkw Hrun [Hpar Hchild]".
    iDestruct "Hrun" as (xi C pt Rfd Rut sz M pm fdv cw gn cs pidv) "(%Hlo & %Hpm & %Hlzf & %HRut & Hheap & Hstk & Hufd & Hcwda & Hcha & #Hmy & #Hdep & #Hnpx & Hb)".
    (* THE CHILD'S ROW, AT THE PARENT'S TABLE: the pipe half is the
       parent's verbatim, and there is no offset half any more (lane
       OFF-HAND-6, H3). *)
    iAssert (urun_rows (MkUkNames (ukn_t N) (ukn_d N) (ukn_s N) (ukn_fd N)
                          (ukn_cwd N) (ukn_ch N) (ukn_pay N) (ukn_pid N)) fdv)
      as "#Hnpc";
      [ rewrite /urun_rows; iApply (urun_rows_nopipe N fdv with "Hnpx") | ].
    (* the caller's half pins the key's working directory *)
    iDestruct (ucwd_agree with "Hcwda Hcwd") as %->.
    (* ...and its other half pins the key's children set, which is why the
       set has to come IN: [urun] binds it existentially, and the arm has
       to name it to say what it grew to *)
    iDestruct (urun_ids_ch with "Hcha") as "[Hchauth Hidsb0]".
    iDestruct (uch_agree with "Hchauth Hchf") as %->.
    iDestruct ("Hidsb0" $! Sc with "Hchauth") as "Hcha".
    iDestruct (uinstr_is_uk_instr with "Hheap Hi") as %Hui.
    iDestruct (uvb_x0 with "Hb") as "[%Hx0 Hb]".
    (* the caller's handles ARE the parent's table, at the slots they name --
       which is what licenses re-minting them at the child's fresh name *)
    (* the program's break IS the key's, now that the heap carries it *)
    iDestruct (uheap_usz with "Hheap Hsz") as %<-.
    iDestruct (ufd_auth_len with "Hufd") as %Hfdlen.
    iDestruct (ufd_sub_hi (ukn_fd N) fdv D with "Hufd HD") as %Hsub.
    (* ...and the ledger says the child's standard streams are these *)
    iDestruct (ustd_agree with "Hufd Hstd") as %Hstl.
    (* ---- fork the payload TOGETHER WITH THE FREE STACK: [ustack] is a
       payload like any other, so the two cross through one reveal ---- *)
    pose proof (forkable_sep P
                  (fun _ γd0 _ => ustack γd0 (m !!! Regidx csp_rs1) avail)
                  FP (forkable_ustack (m !!! Regidx csp_rs1) avail)) as FPS.
    iDestruct (FPS (ukn_t N) (ukn_d N) (ukn_s N) with "[HP Hstk]")
      as (Ft Fp F) "(#Htf & #Hpf & Hdf & Hrestore & #Hrebuild)";
      [ iSplitL "HP"; [ iExact "HP" | iExact "Hstk" ] | ].
    iMod (uheap_fork (ukn_t N) (ukn_d N) (ukn_s N) M pm sz Ft Fp F with "Hheap Htf Hpf Hdf")
      as "(Hheap & Hdf & Hchildres)".
    iDestruct ("Hrestore" with "Hdf") as "[HP Hstk]".
    iDestruct "Hchildres" as (γt' γd' γs')
      "(Hheap' & Hsz' & #Htf' & #Hpf' & Hdf')".
    iMod ("Hrebuild" $! γt' γd' γs' with "Htf' Hpf' Hdf'") as "[HP' Hstk']".
    (* ---- the trap ---- *)
    iApply (UkStep.wp_uk_ecall C pt Rfd Rut pm sz Hlo Hpm HRut Hlzf M m pc fdv c gn Sc pidv Hui
              (fun (s : mstate)
                   (Hp : register_lookup cur_privilege s.(sregs) = User)
                   (Hc : register_lookup (R_bitvector_64 PC) s.(sregs) = pc) =>
                 UserExecFacts.goodmb_execute_ECALL_U UserFrame.Du_r UserFrame.Du_w
                   s pc ltac:(vm_compute; reflexivity)
                   ltac:(vm_compute; reflexivity) Hp Hc)
              with "Hb Hmy").
    rewrite (uexec_ret_ecall _ _ eq_refl).
    assert (Hnum : usys_num (uvis_tf (uvis_of_run m pc M pm sz fdv c gn Sc pidv false secc_all))
                   = USYS_fork).
    { cbn [uvis_tf uvis_of_run]. rewrite tf_of_num. exact Hn. }
    rewrite Hnum. cbv zeta.
    destruct (decide (USYS_fork = USYS_exit)) as [He | _];
      [ exfalso; unfold USYS_fork, USYS_exit in He; lia | ].
    destruct (decide (USYS_fork = USYS_fork)) as [_ | Hne];
      [ | exfalso; exact (Hne eq_refl) ].
    cbn [uvis_M uvis_perm uvis_sz uvis_gen uvis_ch uvis_of_run].
    (* THE FAMILIES THE PROCESS CHOOSES AT THIS TRAP, and at a fork trap
       the only field either leg reads is the child's exit payload -- so
       the point family at [Q] is exactly what the two legs need
       ([UexecSG.sfam_pay] / [sfork_pay_pay]). *)
    iExists (sfam_at (ukn_pay N) (sfam_pay Q Rc)).
    rewrite (sfork_pay_at (ukn_pay N) (sfam_pay Q Rc)) sfork_pay_pay.
    (* ...AND THE LEND IS A FIELD OF THE SAME VALUE (lane FORK-REFUND):
       what the deposit hands down and what the failing arm hands back are
       the same resource because [f] carries both. *)
    rewrite (sfork_lend_at (ukn_pay N) (sfam_pay Q Rc)) sfork_lend_pay.
    (* THE PAY FACT, at the PARENT's own payload -- the child's is [Q], and
       the two live in one value ([UexecSG.sfam_at]).  Nothing travels
       beside it (lane SELF-KILL, P6b). *)
    iSplitR;
      [ iApply (uexec_pay_dep_ret USYS_fork m pc M pm sz fdv c gn Sc pidv
                  false secc_all _ (sfam_at (ukn_pay N) (sfam_pay Q Rc))
                  ltac:(rewrite tf_of_num; exact Hn)
                  ltac:(unfold USYS_fork, USYS_exit; lia)
                  (sexit_pay_at (ukn_pay N) (sfam_pay Q Rc)) with "Hmy") | ].
    (* the PARENT keeps the descriptor authority it had -- fork does not
       touch the parent's table -- and the CHILD mints its own below. *)
    iSplitL "Hpar HP Hsz Hstd HD Hcwd Hheap Hstk Hufd Hcwda Hcha Hchf";
      [ | iSplitR; [ iModIntro; iExact "Hkw" | iSplitL "HRc"; [ iExact "HRc" | ] ] ].
    (* ---- the parent: same heap, r <> 0, and the children set grown by
       the child's generation ---- *)
    - iIntros (r fdv' cw' cs') "%Hr %Hfv %Hcv Hans". subst fdv' cw'.
      (* FORK'S TWO ARMS, and the mirror moves on the second: both halves
         of the program's children variable are in hand -- the engine's
         inside the [urun] just destructed, the program's as a premise --
         which is why the set has to come IN.  What the mirror tracks is
         the kernel's own map ([WaitInv.children_own_at]), whose per-slot
         row the kernel moves at the same fork. *)
      iApply uslot_bupd.
      (* the run's identity conjunct is the PAIR now ([UkRun.urun_ids]): the
         children half is what this arm moves, the pid half rides through
         untouched (lane TRAP-ROWS-4, B). *)
      iDestruct (urun_ids_ch with "Hcha") as "[Hcha Hidsback]".
      iAssert (|==> ∃ cs2 : gset gname,
                 ⌜cs' = cs2⌝ ∗ uch_auth (ukn_ch N) cs2 ∗
                 ((⌜r = (mword_of_int (-1) : mword 64)⌝ ∗
                     UserChildren.uch (ukn_ch N) Sc ∗ Rc)
                  ∨ ∃ (γ : gname) (pidv : mword 32),
                      ⌜r = (sign_extend' 64 pidv : mword 64)⌝ ∗
                      ⌜(1 <= bv_unsigned pidv <= PIDMAX)%Z⌝ ∗
                      ⌜γ ∉ Sc⌝ ∗
                      child_tok γ pidv Q ∗
                      UserChildren.uch (ukn_ch N) (Sc ∪ {[γ]})))%I
        with "[Hcha Hchf Hans]" as ">Hmv".
      { rewrite /ufork_ans. iDestruct "Hans" as "[[%Hm1 HRc] | Hpid]".
        - destruct Hm1 as [Hm1 Hcs]. iModIntro. iExists Sc.
          iSplitR; [iPureIntro; exact Hcs |]. iFrame "Hcha".
          iLeft. iSplitR; [iPureIntro; exact Hm1 |]. iFrame "Hchf HRc".
        (* [%Hnin] is the kernel's freshness row (design app-pipe SS4.3x),
           and it is RELAYED now (SS4.3y): this arm re-spells fork's answer
           at the run's own children handle and carries the conjunct with
           it, so the sh tier ([UkShRun.wp_kshr_fork]) can relay it on to
           a round that has to tell two children apart. *)
        - iDestruct "Hpid" as (γ pidk) "(%Hpv & %Hrng & %Hnin & %Hcs & Htok)".
          iMod (uch_update (ukn_ch N) Sc Sc (Sc ∪ {[γ]}) with "Hcha Hchf")
            as "[Hcha Hchf]".
          iModIntro. iExists (Sc ∪ {[γ]}).
          iSplitR; [iPureIntro; exact Hcs |]. iFrame "Hcha".
          iRight. iExists γ, pidk. iSplitR; [iPureIntro; exact Hpv |].
          iSplitR; [iPureIntro; exact Hrng |].
          iSplitR; [iPureIntro; exact Hnin |].
          iFrame "Htok Hchf". }
      iDestruct "Hmv" as (cs2) "(%Hcs2 & Hcha & Harm)". subst cs'.
      iDestruct ("Hidsback" $! cs2 with "Hcha") as "Hcha".
      iModIntro.
      rewrite (uslot_bump_run m pc M M pm pm sz sz fdv fdv c c gn gn Sc
                 cs2 pidv false false secc_all secc_all r Hx0 Hal4).
      iApply ukcq_ukc.
      iApply (urun_close_upd N M pm m (mword_of_int 10) r sz fdv c gn
                cs2 pidv (add_vec_int pc 4) avail
                ltac:(unfold unot_sp; vm_compute; discriminate)
                with "Hheap Hstk Hufd Hcwda Hcha Hmy Hdep Hnpx").
      iIntros (h') "Hrun".
      iApply ("Hpar" $! h' r with "[%] Harm HP Hsz Hstd HD Hcwd Hrun").
      exact Hr.
    (* ---- the child: fresh heap, r = 0, payload rebuilt at the new names *)
    - iIntros (fdv' cw' g' pidc) "%Hpidc #Hmp %Hfdv' %Hcv' HRc". subst fdv' cw'.
      (* THE CHILD'S OWN DESCRIPTOR AUTHORITY, minted at the view the kernel
         handed it -- BEFORE the key is rewritten to [ukc], since the update
         is absorbed by the [uslot] and not by what it unfolds to.  The
         parent's cannot be shared (both are full maps at the full
         fraction), which is exactly why [urun] takes the fd name as a
         PARAMETER: the child needs its own, as it needs its own heap
         triple.
         [ufd_alloc_open] rather than [ufd_alloc]: the child's table is the
         parent's, so the map is non-empty and its fragments are the
         inherited handles.  [ufd_alloc] would mint the same authority and
         drop them. *)
      iApply uslot_bupd.
      iMod (ufd_alloc_std fdv D Hfdlen Hsub)
        as (γfd') "(Hufd' & Hstd' & Hfrag')".
      iEval (rewrite Hstl) in "Hstd'".
      (* ...AND ITS OWN WORKING-DIRECTORY PAIR, at the inum the kernel
         resumed it at, which is the parent's: fork keeps the cwd. *)
      iMod (ucwd_alloc c) as (γc') "[Hcwa' Hcwf']".
      (* ...AND ITS OWN CHILDREN PAIR, at [∅]: the child has no children.
         A fresh name for the parent's reason -- both halves of a variable
         are full, and one name cannot carry two processes' sets. *)
      iMod (uch_alloc (∅ : gset gname)) as (γch') "[Hcha' Hchf']".
      (* ...AND ITS OWN PID PAIR, at the number <allocpid> gave it (lane
         TRAP-ROWS-4, B).  A fresh name for the children pair's reason, and
         at the CHILD's pid rather than the parent's: this is a different
         process.  <init>'s number is nothing the record has to carry any
         more -- it is the literal 1 (B1b) -- and the kernel's fork answer
         is what says this pid is not it. *)
      iMod (upid_alloc (bv_unsigned pidc)) as (γpid') "[Hpida' Hpidf']".
      iModIntro.
      rewrite (uslot_bump_at_run m pc M M pm pm sz sz fdv fdv c c gn g' Sc ∅
                 pidv pidc false false secc_all secc_all (mword_of_int 0) Hx0 Hal4).
      (* THE CHILD'S RECORD IS MINTED AT THE PARENT'S CHOSEN PAYLOAD, and
         the fact that BACKS it is the [ChildTok.my_pay] the kernel handed
         in on this very arm ([SpecSyscall.sysc_fork_in]): the parent chose
         [Q] at the ecall, kfork set it on the child's generation, and the
         child's run is keyed by it -- which is what makes the child's own
         exit leaf able to pay what its parent will redeem. *)
      iApply ukcq_ukc.
      iDestruct (urun_ids_intro
                   (MkUkNames γt' γd' γs' γfd' γc' γch' Q γpid')
                   ∅ pidc with "Hcha' Hpida'") as "Hcha'".
      iApply (urun_close_upd
                (MkUkNames γt' γd' γs' γfd' γc' γch' Q γpid')
                M pm m
                (mword_of_int 10)
                (mword_of_int 0) sz fdv c g' ∅ pidc (add_vec_int pc 4) avail
                ltac:(unfold unot_sp; vm_compute; discriminate)
                with "Hheap' Hstk' Hufd' Hcwa' Hcha' Hmp Hdep Hnpc").
      iIntros (h') "Hrun".
      iApply ("Hchild" $!
                (MkUkNames γt' γd' γs' γfd' γc' γch' Q γpid') h' g'
                with "[%] Hmp HRc HP' Hsz' Hstd' Hfrag' Hcwf' Hchf' [Hpidf'] Hrun").
      { reflexivity. }
      iExists (bv_unsigned pidc). iSplitR; [| iExact "Hpidf'"].
      (* THE CHILD IS NOT <INIT>, unsigned: the kernel's fork answer says
         the pid is not the word 1 and [bv_unsigned] is injective. *)
      iPureIntro. intro He. apply Hpidc. apply bv_eq.
      rewrite He. vm_compute. reflexivity.
  Qed.

  (* ===================================================================== *)
  (* §5b FORK FOR A PROGRAM THAT DOES NOT TRACK ITS CHILDREN -- DELETED    *)
  (* (lane IO-LEAF, M3a).                                                  *)
  (*                                                                       *)
  (* [wp_uk_ecall_fork_any] was the leaf above with all three of the        *)
  (* caller's binders hard-wired -- the child's payload at [fun _ => True], *)
  (* the lend at [emp], the children set behind an existential -- and the   *)
  (* token the pid arm mints DROPPED.  Its one caller was sh                *)
  (* ([UkShRun.wp_kshr_fork]), and sh's console credential travels on       *)
  (* exactly those three, so it now takes the leaf itself and passes the    *)
  (* trivial values where it wants nothing back.  A wrapper that can only   *)
  (* be used by throwing the answer away is not a shape worth keeping.      *)
  (* ===================================================================== *)

  (* ===================================================================== *)
  (* §6 A WORKED SHAPE: init's fork.                                       *)
  (*                                                                       *)
  (* init's child unwinds only to its exec: what it needs is the program   *)
  (* TEXT (to re-derive its instruction facts at the child's fresh text    *)
  (* name and run                                                          *)
  (* to the exec ecall) and the ARGUMENT VECTOR it passes exec -- the      *)
  (* array-of-pointers word run and the strings, exactly [uargv].  Both    *)
  (* are payload instances, so the payload is the two-conjunct family and  *)
  (* the instance is found by search; nothing is flattened to a byte map   *)
  (* at the call site.                                                     *)
  (*                                                                       *)
  (* Note what the PARENT's continuation does NOT receive back: the text   *)
  (* and argv views are persistent, so the caller never gave them up.      *)
  (* Only the exclusive things round-trip.  And note what is absent        *)
  (* altogether: init's console fds and its wait-loop state are not        *)
  (* address-space facts, so they never enter the payload -- whoever holds *)
  (* them splits them between the two continuations at the [∗].            *)
  (* ===================================================================== *)
  Lemma wp_uk_ecall_fork_argv (N : uk_names Σ) (h : CpuId) (m : regfile)
      (pc : mword 64) (avail : nat) (szv : Z)
      (M0 : gmap Z (bv 8)) (pm0 : gmap (mword 27) uperm)
      (av : Z) (args : list uarg) (l : list fdstate) (D : gmap nat fdstate)
      (c : Z) (Sc : gset gname) (Q : Z -> iProp Σ) (Rc : iProp Σ) :
    usysno m = USYS_fork ->
    is_aligned_vaddr (Virtaddr (add_vec_int pc 4)) 2 = true ->
    uinstr_is (ukn_t N) pc false (ECALL tt) -∗
    (* the child's payload, relayed -- see [wp_uk_ecall_fork] *)

    (* ...and the parent's lend, relayed with it *)
    Rc -∗
    utext_all (ukn_t N) M0 pm0 -∗
    uargv (ukn_d N) av args -∗
    usz (ukn_s N) szv -∗
    UserFd.ustd (ukn_fd N) l -∗
    ([∗ map] fd ↦ st ∈ D, UserFd.ufd (ukn_fd N) fd st) -∗
    (* the caller's half of its working directory -- [wp_uk_ecall_fork]'s
       own note says why it has to come in to reach the child *)
    UserCwd.ucwd (ukn_cwd N) c -∗
    (* the caller's half of its children set -- see [wp_uk_ecall_fork] *)
    UserChildren.uch (ukn_ch N) Sc -∗
    (* ...AND HOW A KILLER PAYS FOR THE CHILD (lane SELF-KILL, §4b'): the
       child's killed row publishes a wand from the application's TAINT
       ([RiscvPtsto.app_taint]) to the child's exit payload at -1 and
       allocproc founds it, so the FORKING PROGRAM supplies it here.  At
       [Q := fun _ => True] -- what a program that wants nothing back
       passes -- it is free. *)
    □ (app_taint -∗ Q (-1)) -∗
    urun N h m pc avail -∗
    ((∀ (h' : CpuId) (r : mword 64),
        ⌜r <> (mword_of_int 0 : mword 64)⌝ -∗
        (* fork's two arms -- see [wp_uk_ecall_fork] *)
        ((⌜r = (mword_of_int (-1) : mword 64)⌝ ∗
            UserChildren.uch (ukn_ch N) Sc ∗ Rc)
         ∨ ∃ (γ : gname) (pidv : mword 32),
             ⌜r = (sign_extend' 64 pidv : mword 64)⌝ ∗
             ⌜(1 <= bv_unsigned pidv <= PIDMAX)%Z⌝ ∗
             (* ...and the generation is fresh -- see
                [wp_uk_ecall_fork] (design app-pipe SS4.3y) *)
             ⌜γ ∉ Sc⌝ ∗
             child_tok γ pidv Q ∗
             UserChildren.uch (ukn_ch N) (Sc ∪ {[γ]})) -∗
        usz (ukn_s N) szv -∗
        UserFd.ustd (ukn_fd N) l -∗
        ([∗ map] fd ↦ st ∈ D, UserFd.ufd (ukn_fd N) fd st) -∗
        UserCwd.ucwd (ukn_cwd N) c -∗
        urun N h' (<[Regidx (mword_of_int 10) := r]> m)
          (add_vec_int pc 4) avail -∗
        mWP (Loop : expr riscv_lang)) ∗
     (* THE CHILD GETS A FRESH DESCRIPTOR NAME TOO.  It already got a fresh
        heap triple -- its ghost state is not the parent's -- and the fd
        authority is no different: parent and child each own a full map, and
        one name could not carry both.  (This is why the descriptor name is a
        FIELD of the record rather than an ambient: an ambient name would
        make this arm unprovable.) *)
     (∀ (N' : uk_names Σ) (h' : CpuId) (γ' : gname),
        (* the child's held set, relayed -- see [wp_uk_ecall_fork] *)
        ⌜ ukn_pay N' = Q ⌝ -∗
        my_pay γ' Q -∗
        Rc -∗
        utext_all (ukn_t N') M0 pm0 -∗
        uargv (ukn_d N') av args -∗
        usz (ukn_s N') szv -∗
        (* the inherited ledger and handles, forwarded verbatim -- see
           [wp_uk_ecall_fork]'s own note *)
        UserFd.ustd (ukn_fd N') l -∗
        ([∗ map] fd ↦ st ∈ D, UserFd.ufd (ukn_fd N') fd st) -∗
        UserCwd.ucwd (ukn_cwd N') c -∗
        (* ...AND ITS OWN HALF OF ITS CHILDREN SET, at [∅] on the nose: a
           process that has just been created has created nothing
           ([UexecRet.uexec_fork_child_F]'s row).  No binder, because there
           is only one value it can be -- which is why this arm can name
           it where it cannot name the parent's. *)
        UserChildren.uch (ukn_ch N') ∅ -∗
        (* ...and its own pid, as a handle, with the "not <init>" fact --
           see [wp_uk_ecall_fork] *)
        (∃ p : Z, ⌜p <> 1⌝ ∗ UserChildren.upid (ukn_pid N') p) -∗
        urun N' h'
          (<[Regidx (mword_of_int 10) := (mword_of_int 0 : mword 64)]> m)
          (add_vec_int pc 4) avail -∗
        mWP (Loop : expr riscv_lang))) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intros Hn Hal4.
    iIntros "#Hi HRc #Htext #Hargv Hsz Hstd HD Hcwd Hchf #Hkw Hrun [Hpar Hchild]".
    iApply (wp_uk_ecall_fork N h m pc avail szv l D c Sc Q Rc
              (fun γt0 γd0 γs0 => (utext_all γt0 M0 pm0 ∗ uargv γd0 av args)%I)
              Hn Hal4 with "Hi HRc [] Hsz Hstd HD Hcwd Hchf Hkw Hrun [Hpar Hchild]").
    { iSplitR; [ iExact "Htext" | iExact "Hargv" ]. }
    iSplitL "Hpar".
    - iIntros (h' r) "%Hr Harm _ Hsz Hstd HD Hcwd Hrun".
      iApply ("Hpar" $! h' r with "[%] Harm Hsz Hstd HD Hcwd Hrun"). exact Hr.
    - iIntros (N' h' γ') "%Hpeq Hmp HRc' [Ht' Ha'] Hsz' Hstd' Hfrag' Hcwd' Hch' Hpid' Hrun".
      iApply ("Hchild" $! N' h' γ'
                with "[%] Hmp HRc' Ht' Ha' Hsz' Hstd' Hfrag' Hcwd' Hch' Hpid' Hrun").
      exact Hpeq.
  Qed.

End UkFork.
