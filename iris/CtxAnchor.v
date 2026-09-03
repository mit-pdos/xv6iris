(* CtxAnchor.v -- THE ANCHOR (A6.142; the owner's parked-context ruling on
   the ξ-bodied invariant blocker, designed at the bcache escrow):

   a parked context ("pin box") CUSTODIED BY AN INVARIANT, guarded by any
   number of locks.  The problem it solves: an [inv] whose body owns
   ξ-indexed cells at a fixed ambient ξ is untransportable (§0.16′) -- two
   ambients give two different invariants, and no morph can exist because
   the body is not in anyone's hands to re-justify.  The ruling: the body
   custodies its cells at a PARKED, hart-free context XI instead
   ([TsoCtx.ctx_parked XI T]).  A box has no dirty-forwarding arm, so
   everything it certifies is clean under its stamp T -- "any view ≥ T
   reads v" -- and the invariant becomes ONE fixed proposition: fork and
   boot hand it around like any persistent fact.

   The three pieces:

   - [anchor γ n XI T]: the custody token, inside the [inv] body, beside
     the cells at XI.  Generation n counts the deposits; the stamp T only
     rises ([anchor_deposit] wraps [TsoCtx.ctx_deposit], which raises the
     box past the depositor's K ⊔ W -- fresh buffered stores included, with
     NOTHING to prove at the deposit site).

   - [astamp γ n T]: the persistent generation witness "generation n's
     stamp is T" (an [agree] fragment).  Handed out by the deposit;
     comparable against the custody token ([astamp_agree]).

   - [aguard γ n ξ]: the guard -- "context ξ's bound has passed generation
     n's stamp" ([ctx_floor] at some lo ≥ T beside the witness).  This is
     the token a LOCK PAYLOAD carries, one slot per guarding lock:
     PERSISTENT, [CtxMorph] (the floor transports along every acquire,
     [TsoCtx.ctx_floor_dom]), and cashable at ANY instruction against the
     running token -- no AMO needed at the use site
     ([TsoCtx.own_context_floor_view] inside [anchor_withdraw]).

   The access rule is [anchor_withdraw]: a running thread whose guard
   matches the custody token's CURRENT generation pulls the cells out of
   the box to its own context (the borrow: [TsoCtxAbsorbLb.ctx_absorb_lb];
   the box stays parked, nothing is resumed).  That the reachable guard IS
   current-generation is the per-protocol freshness theorem -- proved from
   the client invariant's own ghost state machine, NOT here; this file is
   the mechanism, deliberately protocol-free.

   WHERE FIRST GUARDS COME FROM (the fresh-stores asymmetry, same as the
   lock's own A6.113→A6.120 saga): a depositor whose deposit covered its
   buffered stores CANNOT floor the new stamp at its own context (its
   bound is capped by its view, and a buffered store sits above it).  The
   mint routes provided:
   - [aguard_boot]: generation 0 / stamp 0 is free at every context
     (the boot allocation, before any store -- [ctx_floor_0]);
   - [aguard_intro]: from any floor already ≥ the stamp (a refresher whose
     own receipts cover it -- e.g. the thread that just withdrew);
   - [aguard_receipt]: from a view receipt at the stamp
     ([TsoCtx.ctx_bound_raise]): the post-AMO route.  The deposit exports
     [llb loglen_name T'], and [TsoCtx.hart_view_lb_get] at any later
     AMO leaf turns that llb into exactly the needed receipt -- so the
     depositor's own next acquire, or any other thread's, buys the guard.
   How a given protocol's release site reaches one of these routes is a
   per-site measurement (the lock's own record floor, [WpLock.lock_pay_won],
   is the precedent instrument).

   WHY ITS OWN FILE: the [TsoCtxPark.v]/[TsoCtxAbsorbLb.v] precedent --
   built off [TsoCtx]'s PUBLIC gates plus one small cmra of its own, so
   [TsoCtx.v] (under the whole tree) is not rebuilt. *)
From Stdlib Require Import ZArith Lia.
From stdpp Require Import gmap.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import auth agree gmap.
From iris.base_logic.lib Require Import own.
Require Import RiscvLang RiscvPtsto.
Require Import TsoGhost.
Require Import TsoCtx.
Require Import TsoCtxAbsorbLb.
Require Import Xv6Cameras.

(* ---- the anchor's own ghost: an append-only generation ledger -------- *)
(* [auth] of a [gmap nat (agree nat)]: the custody token holds the
   authority; each deposit allocates the next key; fragments are core-id,
   hence persistent -- the generation witness. *)
(* [anchorR]/[anchorG] live in [Xv6Cameras] (section 15), bundled into
   [xv6G] through [bioboxG]. *)

Section Anchor.
  Context `{!riscvGS Σ} `{!anchorG Σ}.

  Definition anchor_map (m : gmap nat nat) : gmapUR nat (agreeR natO) :=
    to_agree <$> m.

  (* the custody token: lives inside the client [inv]'s body, beside the
     cells at XI.  Exclusive (the auth); [n] is the current generation,
     [T] its stamp = the box's bound. *)
  Definition anchor (γ : gname) (n : nat) (XI : CtxId) (T : nat) : iProp Σ :=
    (∃ m : gmap nat nat,
       own γ (● anchor_map m) ∗
       ⌜m !! n = Some T⌝ ∗
       ⌜∀ k, k ∈ dom m → (k ≤ n)%nat⌝ ∗
       ctx_parked XI T)%I.

  (* the persistent generation witness *)
  Definition astamp (γ : gname) (n T : nat) : iProp Σ :=
    own γ (◯ {[ n := to_agree T ]}).

  (* the guard: what a lock-payload slot carries.  DELIBERATELY on
     [ctx_floor] (the left arm) alone: a wrote-arm holder cashes only
     [ledger_vis], which cannot justify borrowing OTHER harts' cells from
     under the stamp; every cross-thread delivery lands on the left arm
     anyway ([WpLock.lk_floor_morph]'s own measurement). *)
  Definition aguard (γ : gname) (n : nat) (ξ : CtxId) : iProp Σ :=
    (∃ T lo : nat, astamp γ n T ∗ ⌜(T ≤ lo)%nat⌝ ∗ ctx_floor ξ lo)%I.

  (* ---- instances --------------------------------------------------- *)

  Global Instance astamp_persistent γ n T : Persistent (astamp γ n T).
  Proof. rewrite /astamp. apply _. Qed.
  Global Instance astamp_timeless γ n T : Timeless (astamp γ n T).
  Proof. rewrite /astamp. apply _. Qed.

  Global Instance aguard_persistent γ n ξ : Persistent (aguard γ n ξ).
  Proof. rewrite /aguard. apply _. Qed.
  Global Instance aguard_timeless γ n ξ : Timeless (aguard γ n ξ).
  Proof. rewrite /aguard. apply _. Qed.

  Global Instance anchor_timeless γ n XI T : Timeless (anchor γ n XI T).
  Proof. rewrite /anchor. apply _. Qed.

  (* the guard rides lock payloads: floor transport is [ctx_floor_dom] *)
  Global Instance aguard_morph γ n : CtxMorph (aguard γ n).
  Proof.
    iIntros (ξ ξ') "Hd (%T & %lo & #Hst & %Hlo & #Hfl)".
    iDestruct (ctx_floor_dom with "Hd Hfl") as "[Hd #Hfl']".
    iModIntro. iFrame "Hd". iExists T, lo. by iFrame "Hst Hfl'".
  Qed.

  (* ---- allocation --------------------------------------------------- *)

  (* boot's mint: a fresh box at stamp 0 (an era-image custody: everything
     under stamp 0 is the initial image, visible to every view). *)
  Lemma anchor_alloc :
    ⊢ |==> ∃ (γ : gname) (XI : CtxId), anchor γ 0 XI 0 ∗ astamp γ 0 0.
  Proof.
    iMod ctx_parked_alloc as (XI) "Hpk".
    iMod (own_alloc (● anchor_map {[0%nat := 0%nat]} ⋅
                     ◯ {[0%nat := to_agree 0%nat]})) as (γ) "[Hauth Hfrag]".
    { apply auth_both_valid_discrete. split.
      - rewrite /anchor_map map_fmap_singleton.
        apply singleton_included_l. exists (to_agree 0%nat).
        split; [by rewrite lookup_singleton | by apply Some_included; left].
      - rewrite /anchor_map map_fmap_singleton. by apply singleton_valid. }
    iModIntro. iExists γ, XI. iFrame "Hfrag".
    iExists {[0%nat := 0%nat]}. iFrame "Hauth Hpk".
    iPureIntro. split.
    - by rewrite lookup_singleton.
    - intros k Hk. rewrite dom_singleton_L in Hk.
      apply elem_of_singleton in Hk. lia.
  Qed.

  (* generation 0's guard is free at every context: stamp 0 needs no
     receipt at all ([ctx_floor_0]). *)
  Lemma aguard_boot γ ξ : astamp γ 0 0 -∗ aguard γ 0 ξ.
  Proof.
    iIntros "#Hst". iExists 0%nat, 0%nat. iFrame "Hst".
    iSplit; [by iPureIntro | iApply ctx_floor_0].
  Qed.

  (* ---- agreement ---------------------------------------------------- *)

  (* ENDGAME §3.2: a witness's generation never exceeds the anchor's --
     the map's dom bound, read through the fragment. *)
  Lemma astamp_le γ n XI T n' T' :
    anchor γ n XI T -∗ astamp γ n' T' -∗ ⌜(n' ≤ n)%nat⌝.
  Proof.
    iIntros "(%m & Hauth & %Hlook & %Hdom & _) Hst".
    iDestruct (own_valid_2 with "Hauth Hst") as %[Hincl _]%auth_both_valid_discrete.
    iPureIntro.
    apply singleton_included_l in Hincl as [y [Hy _]].
    apply Hdom. apply elem_of_dom.
    rewrite /anchor_map lookup_fmap in Hy.
    destruct (m !! n') eqn:Hm; [by eexists | by inversion Hy].
  Qed.

  Lemma astamp_agree γ n XI T T' :
    anchor γ n XI T -∗ astamp γ n T' -∗ ⌜T' = T⌝.
  Proof.
    iIntros "(%m & Hauth & %Hlook & %Hdom & _) Hfrag".
    iDestruct (own_valid_2 with "Hauth Hfrag")
      as %[Hincl _]%auth_both_valid_discrete.
    iPureIntro.
    apply singleton_included_l in Hincl as (y & Hy & Hinc).
    rewrite lookup_fmap Hlook /= in Hy.
    apply (inj Some) in Hy.
    rewrite Some_included_total -Hy in Hinc.
    apply to_agree_included in Hinc. by fold_leibniz.
  Qed.

  (* ---- the deposit --------------------------------------------------- *)

  (* park a morphable bundle into the box.  [ctx_deposit] raises the box's
     stamp past the depositor's K ⊔ W -- its buffered stores included, with
     nothing to prove here; whoever later withdraws pays the raised stamp
     through its guard.  The generation bumps; the new witness and the
     stamp's log-length receipt come out (the llb is what a later AMO
     cashes into the guard's receipt, [TsoCtx.hart_view_lb_get]). *)
  Lemma anchor_deposit `{CID : CpuId} (R : CtxId → iProp Σ) `{!CtxMorph R}
      (γ : gname) (n : nat) (ξd XI : CtxId) (T : nat) :
    own_context ξd -∗ anchor γ n XI T -∗ R ξd ==∗
    own_context ξd ∗
    ∃ T', ⌜(T ≤ T')%nat⌝ ∗ anchor γ (S n) XI T' ∗ R XI ∗
          astamp γ (S n) T' ∗ llb loglen_name T'.
  Proof.
    iIntros "Hrun (%m & Hauth & %Hlook & %Hdom & Hpk) HR".
    iMod (ctx_deposit R ξd XI T with "Hrun Hpk HR")
      as "[Hrun (%T' & %HTT' & Hpk & HR)]".
    iDestruct (ctx_parked_llb with "Hpk") as "[Hpk #Hllb]".
    assert (HSn : m !! S n = None).
    { apply not_elem_of_dom. intros Hin. specialize (Hdom _ Hin). lia. }
    iMod (own_update with "Hauth") as "[Hauth Hfrag]".
    { apply auth_update_alloc.
      apply (alloc_singleton_local_update _ (S n) (to_agree T')); [|done].
      by rewrite lookup_fmap HSn. }
    iModIntro. iFrame "Hrun". iExists T'.
    iSplitR; [by iPureIntro|].
    iSplitR "HR Hfrag"; last by iFrame "HR Hfrag Hllb".
    iExists (<[S n := T']> m).
    rewrite /anchor_map fmap_insert. iFrame "Hauth Hpk".
    iPureIntro. split.
    - by rewrite lookup_insert.
    - intros k Hk. rewrite dom_insert_L in Hk.
      apply elem_of_union in Hk as [Hk | Hk].
      + apply elem_of_singleton in Hk. lia.
      + specialize (Hdom _ Hk). lia.
  Qed.

  (* ---- guard mints --------------------------------------------------- *)

  (* from a floor already past the stamp (a refresher: e.g. the thread
     that just withdrew at this generation, whose own bound absorbed lo) *)
  Lemma aguard_intro γ n T ξ lo :
    (T ≤ lo)%nat →
    astamp γ n T -∗ ctx_floor ξ lo -∗ aguard γ n ξ.
  Proof.
    iIntros (Hle) "#Hst #Hfl". iExists T, lo. by iFrame "Hst Hfl".
  Qed.

  (* from a view receipt at the stamp: the post-AMO route.  [hart_view_lb]
     at K ≥ T (from [TsoCtx.hart_view_lb_get] against the deposit's llb at
     any AMO leaf) absorbs into the runner's own bound
     ([TsoCtx.ctx_bound_raise]) and the floor is the guard's. *)
  Lemma aguard_receipt `{CID : CpuId} γ n T K ξ :
    (T ≤ K)%nat →
    own_context ξ -∗ hart_view_lb K -∗ astamp γ n T ==∗
    own_context ξ ∗ aguard γ n ξ.
  Proof.
    iIntros (HTK) "Hrun #HK #Hst".
    iMod (ctx_bound_raise ξ K with "Hrun HK") as "[Hrun #Hfl]".
    iModIntro. iFrame "Hrun". iExists T, K. by iFrame "Hst Hfl".
  Qed.

  (* ---- the withdraw (the borrow) ------------------------------------- *)

  (* a running thread with a CURRENT-generation guard pulls a morphable
     bundle out of the box to its own context.  The box stays parked; the
     custody token comes back untouched.  That the guard's generation
     matches the custody token's is the caller's (per-protocol) freshness
     obligation -- here it is simply the index [n] appearing in both. *)
  Lemma anchor_withdraw `{CID : CpuId} (R : CtxId → iProp Σ) `{!CtxMorph R}
      (γ : gname) (n : nat) (ξ XI : CtxId) (T : nat) :
    own_context ξ -∗ aguard γ n ξ -∗ anchor γ n XI T -∗ R XI ==∗
    own_context ξ ∗ anchor γ n XI T ∗ R ξ.
  Proof.
    iIntros "Hrun #Hg Ha HR".
    iDestruct "Hg" as (T0 lo) "(#Hst & %Hlo & #Hfl)".
    iDestruct (astamp_agree with "Ha Hst") as %->.
    iDestruct "Ha" as "(%m & Hauth & %Hlook & %Hdom & Hpk)".
    iDestruct (own_context_floor_view with "Hrun Hfl")
      as "[Hrun (%K & #HK & %HloK)]".
    iAssert (hart_view_lb K) as "#HKv".
    { rewrite hart_view_lb_unseal /hart_view_lb_def. iExact "HK". }
    iMod (ctx_absorb_lb R XI ξ T K ltac:(lia) with "Hrun HKv Hpk HR")
      as "(Hrun & Hpk & HR)".
    iModIntro. iFrame "Hrun HR".
    iExists m. iFrame "Hauth Hpk". by iPureIntro.
  Qed.

  (* the round trip most openers make: withdraw at the current generation,
     work at your own context, deposit back (bumping the generation), and
     walk away with the new witness + llb -- the makings of the next
     guard. *)
  Lemma anchor_open_close `{CID : CpuId} (R R' : CtxId → iProp Σ)
      `{!CtxMorph R} `{!CtxMorph R'}
      (γ : gname) (n : nat) (ξ XI : CtxId) (T : nat) :
    own_context ξ -∗ aguard γ n ξ -∗ anchor γ n XI T -∗ R XI -∗
    (own_context ξ -∗ R ξ ==∗ own_context ξ ∗ R' ξ) ==∗
    own_context ξ ∗
    ∃ T', ⌜(T ≤ T')%nat⌝ ∗ anchor γ (S n) XI T' ∗ R' XI ∗
          astamp γ (S n) T' ∗ llb loglen_name T'.
  Proof.
    iIntros "Hrun #Hg Ha HR Hwork".
    iMod (anchor_withdraw R γ n ξ XI T with "Hrun Hg Ha HR")
      as "(Hrun & Ha & HR)".
    iMod ("Hwork" with "Hrun HR") as "[Hrun HR']".
    iApply (anchor_deposit R' γ n ξ XI T with "Hrun Ha HR'").
  Qed.

End Anchor.
