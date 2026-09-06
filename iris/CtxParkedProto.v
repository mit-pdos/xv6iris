(* CtxParkedProto.v -- A CONTEXT PARKED UNDER A CONTEXT
   (claude-notes/projects/ctx-parent.md).  PROTOTYPE: stated over TsoCtx.v's
   public unseal lemmas the way TsoCtxPark.v / TsoCtxMove.v are, so the
   design can be checked against the real tokens before TsoCtx.v moves.

   THE SHAPE.  Today's parked record [ctx_parked ξ T] stamps a context at a
   log position T and asks the resumer for a view past T.  Here a parked
   record names the CONTEXT it is parked under:

       ctx_under ξ ξ'   "ξ's bound and every key of ξ are justified at ξ'
                         exactly as a fact of ξ' would be"

   [key_at ξ' k] is the justification a byte fact at ξ' carries (clean under
   ξ''s bound, or registered dirty at ξ'), factored out of [ctx_pointsto].
   Parking and resuming are then statements about two contexts running on
   one hart -- no view receipt, no stamp, no fence -- and the token is a
   payload of ξ' (a [CtxMorph] and a [CtxMove] instance), so it rides the
   ordinary lock transport.  The stamped form survives as the ROOT of a
   chain (the record a lock invariant or a box holds); [ctx_under_of_pair]
   shows the new token GENERALIZES today's [ctx_parked XIp Tp ∗ ctx_floor
   ξl Tp] pair, which is what lets every existing site convert in place.

   NAME: [ctx_under]; the stamped form keeps [ctx_parked ξ T] and its whole
   law family (ctx-parent.md §2, §8(a)).  The file becomes [TsoCtxUnder.v]
   when the design is adopted.

   WHAT THE TOKEN IS A RESOURCE ABOUT.  [ctx_under ξ ξ'] owns ξ's whole
   authority and holds only LOWER BOUNDS and MEMBERSHIPS about ξ' -- both
   persistent, both preserved by everything that can happen to ξ': ξ' may
   itself be parked under a third context, stamped, resumed on another
   hart, moved or morphed, and the child stays validly parked (the park
   joined the parent's dirty watermark with the child's, so a later stamp
   of the parent covers the child's keys).  Consequences worth stating as
   rules:
     - chains resume parents first: ξ under P under S is resumed by
       resuming P (needs S running here) and then ξ;
     - there is NO transitivity law [ctx_under ξ P ∗ ctx_under P S ⊢
       ctx_under ξ S]: ξ's keys registered at P are not registered at S;
     - there is NO deposit into a parked child: it would need a domination
       [ctx_dom parent child], whose target bound must exceed the parent's
       dirty watermark, which sits above the hart's view -- fill a child
       while it RUNS ([CtxMove]) and park it afterwards;
     - a pinned scheduler context that is never stamped accumulates the
       keys of every record ever parked under it (the dirty set is
       monotone).  Sound -- membership is justification, not ownership --
     and free of proof-term cost, since the set is abstract.
   Every law below is sound because parent and child share ONE ambient
   hart ([CpuId]): the parent's own-message justification is what the
   child inherits.  Never state a two-hart variant.

   STATUS: everything PROVED; nothing here consults the interpretation. *)
From Stdlib Require Import ZArith Lia.
From stdpp Require Import bitvector.definitions gmap.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import auth.
From iris.base_logic.lib Require Import ghost_map mono_nat.
Require Import SailStdpp.Values SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes RiscvLang RiscvPtsto Ktier.
Require Import TsoMemPa TsoGhost.
Require Import TsoCtx TsoCtxMove.

Section under.
  Context `{!riscvGS Σ}.

  (* ------------------------------------------------------------------ *)
  (** * 1. The justification of a key at a context                       *)
  (* ------------------------------------------------------------------ *)

  (** [ctx_pointsto]'s clean/dirty disjunct, at a key rather than a fact. *)
  Definition key_at (ξ' : CtxId) (k : nat * Arch.pa) : iProp Σ :=
    (llb (ctx_bound_name ξ') k.1 ∨ dset_in (ctx_dirty_name ξ') k)%I.

  Global Instance key_at_persistent ξ' k : Persistent (key_at ξ' k).
  Proof. rewrite /key_at. apply _. Qed.
  Global Instance key_at_timeless ξ' k : Timeless (key_at ξ' k).
  Proof. rewrite /key_at. apply _. Qed.

  (* [TsoGhost.llb_valid] at a fraction of the authority (TsoCtx keeps its
     copy Local). *)
  Local Lemma llb_valid_q (γ : gname) (q : Qp) (n K : nat) :
    mono_nat_auth_own γ q n -∗ llb γ K -∗ ⌜(K ≤ n)%nat⌝.
  Proof.
    iIntros "Ha [Hlb|%Hz]".
    - by iDestruct (mono_nat_lb_own_valid with "Ha Hlb") as %[_ ?].
    - iPureIntro. lia.
  Qed.

  (** Every key justified at ξ' is under ξ''s bound or in ξ''s dirty set --
      read off ξ''s authority (at any fraction), which is threaded, not
      consumed.  A set induction, because the authority is spatial and
      [big_sepS_intro]'s □ would drop it. *)
  Local Lemma keys_pure (ξ' : CtxId) (q : Qp) (B' : nat)
      (D' D : gset (nat * Arch.pa)) :
    ctx_at ξ' q B' D' -∗ ([∗ set] k ∈ D, key_at ξ' k) -∗
    ctx_at ξ' q B' D' ∗ ⌜∀ k, k ∈ D → (k.1 ≤ B')%nat ∨ k ∈ D'⌝.
  Proof.
    induction D as [|k D Hk IH] using set_ind_L.
    - iIntros "Hat _". iFrame "Hat". iPureIntro. intros k Hk. set_solver.
    - iIntros "Hat Hks". rewrite big_sepS_insert; [|exact Hk].
      iDestruct "Hks" as "[#Hkey Hks]".
      iDestruct (IH with "Hat Hks") as "[[Hb Hd] %HD]".
      iAssert (⌜(k.1 ≤ B')%nat ∨ k ∈ D'⌝)%I as %Hk'.
      { iDestruct "Hkey" as "[Hcl|Hdt]".
        - iDestruct (llb_valid_q with "Hb Hcl") as %?. iPureIntro. by left.
        - iDestruct (dset_lookup with "Hd Hdt") as %?. iPureIntro. by right. }
      iFrame "Hb Hd". iPureIntro. intros k' Hk'in.
      apply elem_of_union in Hk'in as [->%elem_of_singleton | Hin]; [exact Hk' | exact (HD _ Hin)].
  Qed.

  Local Lemma view_lb_max' (gv gl : gname) (h : agent) (K1 K2 : nat) :
    view_lb gv gl h K1 -∗ view_lb gv gl h K2 -∗ view_lb gv gl h (Nat.max K1 K2).
  Proof.
    iIntros "H1 H2".
    destruct (Nat.le_ge_cases K1 K2) as [Hle|Hle].
    - rewrite (Nat.max_r _ _ Hle). iExact "H2".
    - rewrite (Nat.max_l _ _ Hle). iExact "H1".
  Qed.

  (* register a whole set of keys at once *)
  Local Lemma dset_insert_set (γ : gname) (S D : gset (nat * Arch.pa)) :
    dset_auth γ 1 S ==∗ dset_auth γ 1 (S ∪ D) ∗ [∗ set] k ∈ D, dset_in γ k.
  Proof.
    induction D as [|k D Hk IH] using set_ind_L.
    - iIntros "H". rewrite union_empty_r_L big_sepS_empty. by iFrame.
    - iIntros "H". iMod (IH with "H") as "[H #Hs]".
      iMod (dset_insert _ _ k with "H") as "[H #Hk]".
      iModIntro. rewrite big_sepS_insert; [|exact Hk]. iFrame "Hk Hs".
      replace (S ∪ ({[k]} ∪ D)) with (S ∪ D ∪ {[k]}) by set_solver. iFrame.
  Qed.

  (* ------------------------------------------------------------------ *)
  (** * 2. The token                                                     *)
  (* ------------------------------------------------------------------ *)

  (** ξ parked under ξ': ξ's whole authority, its bound under ξ''s, its
      every key justified at ξ'. *)
  Definition ctx_under_def (ξ ξ' : CtxId) : iProp Σ :=
    (∃ (B : nat) (D : gset (nat * Arch.pa)),
       ctx_at ξ 1 B D ∗ ctx_floor ξ' B ∗
       [∗ set] k ∈ D, key_at ξ' k)%I.
  Lemma ctx_under_aux : { f | f = ctx_under_def }.
  Proof. by eexists. Qed.
  Definition ctx_under (ξ ξ' : CtxId) : iProp Σ := proj1_sig ctx_under_aux ξ ξ'.
  Lemma ctx_under_unseal ξ ξ' : ctx_under ξ ξ' = ctx_under_def ξ ξ'.
  Proof. unfold ctx_under. by rewrite (proj2_sig ctx_under_aux). Qed.

  Global Instance ctx_under_timeless ξ ξ' : Timeless (ctx_under ξ ξ').
  Proof. rewrite ctx_under_unseal /ctx_under_def. apply _. Qed.

  (* ------------------------------------------------------------------ *)
  (** * 3. The bridge from today's pair                                   *)
  (* ------------------------------------------------------------------ *)

  (** [ctx_parked XIp Tp ∗ ctx_floor ξl Tp] -- the shape every parked record
      travels in today ([SchedCtx.proc_ctx_at], [SwtchCtx.resume_tok]) -- IS
      a record parked under ξl: every key is under Tp, and Tp is under ξl's
      bound.  Pure, so the sweep can convert sites one at a time. *)
  Lemma ctx_under_of_pair (ξ ξ' : CtxId) (T : nat) :
    ctx_parked ξ T -∗ ctx_floor ξ' T -∗ ctx_under ξ ξ'.
  Proof.
    rewrite ctx_parked_unseal /ctx_parked_def ctx_under_unseal /ctx_under_def.
    iIntros "(%D & Hat & #HT & %HDT) #Hfl".
    iExists T, D. iFrame "Hat Hfl".
    iApply big_sepS_intro. iIntros "!>" (k Hk).
    iLeft. iApply (ctx_floor_le with "Hfl"). exact (HDT _ Hk).
  Qed.

  (** A floor of the child is a floor of the parent. *)
  Lemma ctx_under_floor (ξ ξ' : CtxId) (lo : nat) :
    ctx_under ξ ξ' -∗ ctx_floor ξ lo -∗ ctx_under ξ ξ' ∗ ctx_floor ξ' lo.
  Proof.
    rewrite ctx_under_unseal /ctx_under_def /ctx_floor.
    iIntros "(%B & %D & [Hb Hd] & #Hfl & #Hks) #Hlo".
    iDestruct (llb_valid with "Hb Hlo") as %HloB.
    iSplitL.
    { iExists B, D. iFrame "Hb Hd Hfl Hks". }
    iApply (llb_le with "Hfl"). exact HloB.
  Qed.

  (* ------------------------------------------------------------------ *)
  (** * 4. Resume                                                        *)
  (* ------------------------------------------------------------------ *)

  (** RESUME: the parent is running here, so the child can run here.  The
      child's new bound is the parent's; every child key is under it
      (clean at ξ') or registered at ξ' (so ξ''s own justification at this
      hart applies); the watermark is the join of the parent's with its
      view.  No receipt, no interp. *)
  Lemma ctx_resume_under `{CID : CpuId} (ξ ξ' : CtxId) :
    own_context ξ' -∗ ctx_under ξ ξ' ==∗ own_context ξ' ∗ own_context ξ.
  Proof.
    rewrite !own_context_unseal /own_context_def ctx_under_unseal /ctx_under_def.
    iIntros "(%B' & %K' & %W' & %D' & [Hb' Hd'] & #HK' & %HBK' & #HW' & %HD'W' & #Hoks')
             (%B & %D & [Hb Hd] & #Hfl & #Hks)".
    iDestruct (llb_valid with "Hb' Hfl") as %HBB'.
    (* every child key is under the parent's bound or in its set *)
    iDestruct (keys_pure ξ' 1 B' D' D with "[$Hb' $Hd'] Hks") as "[[Hb' Hd'] %Hkeys]".
    (* the child's bound rises to the parent's *)
    iMod (mono_nat_own_update B' with "Hb") as "[Hb _]"; first exact HBB'.
    iModIntro.
    iSplitL "Hb' Hd'".
    { iExists B', K', W', D'. iFrame "Hb' Hd' HK' HW' Hoks'". by iPureIntro. }
    (* the child's token at this hart: the parent's justifications *)
    iAssert ([∗ set] k ∈ D, dirty_ok logm_name (hart_agent cpu_id) B' k)%I as "#Hoks".
    { iApply big_sepS_intro. iIntros "!>" (k Hk).
      destruct (Hkeys k Hk) as [HkB' | HkD'].
      - iLeft. by iPureIntro.
      - iApply (big_sepS_elem_of with "Hoks'"). exact HkD'. }
    iExists B', K', (Nat.max W' K'), D. iFrame "Hb Hd HK' Hoks".
    iSplitR; first done.
    iSplitR.
    { iApply (llb_max with "HW'"). by iApply view_lb_llb. }
    iPureIntro. intros k Hk. destruct (Hkeys k Hk) as [HkB' | HkD'].
    - lia.
    - have := HD'W' _ HkD'. lia.
  Qed.

  (* ------------------------------------------------------------------ *)
  (** * 5. Park                                                          *)
  (* ------------------------------------------------------------------ *)

  (** PARK: both running here.  ξ's dirty keys are this hart's own messages
      (its [dirty_ok]), so registering them at ξ' keeps ξ''s invariant once
      ξ''s bound has risen to [max B' B] (both under this hart's view, the
      [ctx_bound_raise] argument); ξ''s watermark joins by [llb_max].  What
      ξ keeps is its authority, the floor and the per-key registrations.
      THE WATERMARK JOIN [max W' W] IS LOAD-BEARING: it is what makes a later
      STAMP of the parent (at or above its watermark) cover the child's
      keys, hence what keeps the child validly parked when the parent is
      stamped and resumed on another hart. *)
  Lemma ctx_park_under `{CID : CpuId} (ξ ξ' : CtxId) :
    own_context ξ' -∗ own_context ξ ==∗ own_context ξ' ∗ ctx_under ξ ξ'.
  Proof.
    rewrite !own_context_unseal /own_context_def ctx_under_unseal /ctx_under_def.
    iIntros "(%B' & %K' & %W' & %D' & [Hb' Hd'] & #HK' & %HBK' & #HW' & %HD'W' & #Hoks')
             (%B & %K & %W & %D & [Hb Hd] & #HK & %HBK & #HW & %HDW & #Hoks)".
    (* the joined receipt; the parent's bound rises over the child's *)
    iDestruct (view_lb_max' with "HK' HK") as "#HKK".
    iMod (mono_nat_own_update (Nat.max B' B) with "Hb'") as "[Hb' #Hlb']"; first lia.
    (* the child's keys register at the parent *)
    iMod (dset_insert_set (ctx_dirty_name ξ') D' D with "Hd'") as "[Hd' #Hins]".
    (* every key of the union is justified at the raised bound *)
    iAssert ([∗ set] k ∈ D' ∪ D, dirty_ok logm_name (hart_agent cpu_id) (Nat.max B' B) k)%I
      as "#Hoks''".
    { iApply big_sepS_intro. iIntros "!>" (k Hk).
      apply elem_of_union in Hk as [Hk|Hk].
      - iApply (dirty_ok_mono _ _ B' with "[]"); [lia|].
        iApply (big_sepS_elem_of with "Hoks'"). exact Hk.
      - iApply (dirty_ok_mono _ _ B with "[]"); [lia|].
        iApply (big_sepS_elem_of with "Hoks"). exact Hk. }
    iModIntro.
    iSplitL "Hb' Hd'".
    { iExists (Nat.max B' B), (Nat.max K' K), (Nat.max W' W), (D' ∪ D).
      iFrame "Hb' Hd' HKK Hoks''".
      iSplitR; [iPureIntro; lia|].
      iSplitR; [iApply (llb_max with "HW' HW")|].
      iPureIntro. intros k Hk. apply elem_of_union in Hk as [Hk|Hk].
      - have := HD'W' _ Hk. lia.
      - have := HDW _ Hk. lia. }
    iExists B, D. iFrame "Hb Hd".
    iSplitR.
    { rewrite /ctx_floor. iApply (llb_le _ (Nat.max B' B)); [lia|].
      rewrite /llb. iLeft. iExact "Hlb'". }
    iApply big_sepS_intro. iIntros "!>" (k Hk).
    iRight. iApply (big_sepS_elem_of with "Hins"). exact Hk.
  Qed.

  (* ------------------------------------------------------------------ *)
  (** * 6. The token is a payload of its parent                          *)
  (* ------------------------------------------------------------------ *)

  (** Along domination ([ctx_dom ξ' ξ'']): every key at ξ' -- clean under B'
      or dirty under W' -- is clean under B'' at ξ''; the floor rides by
      [ctx_floor_dom].  The pointsto morph's proof, once per key. *)
  Global Instance ctx_under_morph (ξ : CtxId) : CtxMorph (λ ξ', ctx_under ξ ξ').
  Proof.
    iIntros (ξ' ξ'') "Hd HP".
    rewrite !ctx_under_unseal /ctx_under_def.
    iDestruct "HP" as "(%B & %D & Hat & #Hfl & #Hks)".
    iDestruct (ctx_floor_dom with "Hd Hfl") as "[Hd #Hfl'']".
    rewrite ctx_dom_unseal /ctx_dom_def.
    iDestruct "Hd" as "(%B' & %W' & %B'' & %D' & Hat' & %HD'W' & %HBB'' & %HWB'' & #Hlb'')".
    iDestruct (keys_pure ξ' (1/2) B' D' D with "Hat' Hks") as "[[Hb' Hdm'] %Hkeys]".
    iAssert ([∗ set] k ∈ D, key_at ξ'' k)%I as "#Hks''".
    { iApply big_sepS_intro. iIntros "!>" (k Hk).
      iLeft. rewrite /llb. iLeft. iApply (mono_nat_lb_own_le with "Hlb''").
      destruct (Hkeys k Hk) as [HkB' | HkD']; [lia | have := HD'W' _ HkD'; lia]. }
    iModIntro. iSplitL "Hb' Hdm'".
    { iExists B', W', B'', D'. iFrame "Hb' Hdm' Hlb''". by iPureIntro. }
    iExists B, D. iFrame "Hat Hfl'' Hks''".
  Qed.

  (** Along the same-hart move: [ctx_move_floor] per clean key,
      [ctx_move_wrote] per dirty key (whose conclusion is the floor or the
      registration at ξ1 -- either is a [key_at]); a set induction threading
      both running tokens through the bupd. *)
  Global Instance ctx_under_move `{CID : CpuId} (ξ : CtxId) :
    CtxMove (λ ξ', ctx_under ξ ξ').
  Proof.
    iIntros (ξ0 ξ1) "H0 H1 HP". rewrite !ctx_under_unseal /ctx_under_def.
    iDestruct "HP" as "(%B & %D & Hat & #Hfl & #Hks)".
    iMod (ctx_move_floor ξ0 ξ1 B with "H0 H1 Hfl") as "(H0 & H1 & #Hfl1)".
    iAssert (|==> own_context ξ0 ∗ own_context ξ1 ∗ [∗ set] k ∈ D, key_at ξ1 k)%I
      with "[H0 H1]" as ">(H0 & H1 & #Hks1)".
    { iInduction D as [|k D Hk] "IH" using set_ind_L forall "H0 H1".
      - iModIntro. iFrame "H0 H1". by iApply big_sepS_empty.
      - rewrite !big_sepS_insert; [|exact Hk|exact Hk].
        iDestruct "Hks" as "[#Hkey Hks]".
        iMod ("IH" with "Hks H0 H1") as "(H0 & H1 & #Hks1)".
        iDestruct "Hkey" as "[Hcl|Hdt]".
        + iMod (ctx_move_floor ξ0 ξ1 k.1 with "H0 H1 Hcl") as "(H0 & H1 & #Hf1)".
          iModIntro. iFrame "H0 H1 Hks1". iLeft. iExact "Hf1".
        + destruct k as [t a].
          iMod (ctx_move_wrote ξ0 ξ1 t a with "H0 H1 Hdt") as "(H0 & H1 & #Hk1)".
          iModIntro. iFrame "H0 H1 Hks1". rewrite /key_at /=.
          iDestruct "Hk1" as "[Hf|Hw]"; [iLeft; iExact "Hf" | iRight; iExact "Hw"]. }
    iModIntro. iFrame "H0 H1". iExists B, D. iFrame "Hat Hfl1 Hks1".
  Qed.

  (* ------------------------------------------------------------------ *)
  (** * 7. Roots                                                         *)
  (* ------------------------------------------------------------------ *)

  (** A record parked under a STAMPED root is itself stamped at the root's
      stamp: every key of ξ is clean under T at ξ' or registered at ξ',
      hence ≤ T by the root's own row; ξ's bound RISES to T (a bupd -- the
      child's bound authority sits at B ≤ T and a wand cannot move it).
      A convenience: on the lock path a nested record rides the payload
      morph and is never flattened.  The root is threaded, not consumed. *)
  Lemma ctx_stamped_of_under (ξ ξ' : CtxId) (T : nat) :
    ctx_parked ξ' T -∗ ctx_under ξ ξ' ==∗ ctx_parked ξ' T ∗ ctx_parked ξ T.
  Proof.
    rewrite !ctx_parked_unseal /ctx_parked_def ctx_under_unseal /ctx_under_def.
    iIntros "(%D' & Hat' & #HT & %HD'T) (%B & %D & [Hb Hd] & #Hfl & #Hks)".
    iDestruct (keys_pure ξ' 1 T D' D with "Hat' Hks") as "[[Hb' Hd'] %Hkeys]".
    iDestruct (llb_valid with "Hb' Hfl") as %HBT.
    iMod (mono_nat_own_update T with "Hb") as "[Hb _]"; first exact HBT.
    iModIntro. iSplitL "Hb' Hd'".
    { iExists D'. iFrame "Hb' Hd' HT". by iPureIntro. }
    iExists D. iFrame "Hb Hd HT". iPureIntro. intros k Hk.
    destruct (Hkeys k Hk) as [?|HkD']; [lia | exact (HD'T _ HkD')].
  Qed.

  (* ------------------------------------------------------------------ *)
  (** * 8. Exclusivity                                                   *)
  (* ------------------------------------------------------------------ *)

  (** The whole authority is inside, so a context is parked under at most
      one parent and never both parked and running ([mono_nat_auth_own] at 1
      twice is invalid).  Corollary: [ctx_park_under ξ ξ] and
      [ctx_resume_under ξ ξ] are vacuous. *)
  Lemma ctx_under_excl (ξ ξ1 ξ2 : CtxId) :
    ctx_under ξ ξ1 -∗ ctx_under ξ ξ2 -∗ False.
  Proof.
    rewrite !ctx_under_unseal /ctx_under_def.
    iIntros "(%B1 & %D1 & [Hb1 _] & _ & _) (%B2 & %D2 & [Hb2 _] & _ & _)".
    iDestruct (mono_nat_auth_own_agree with "Hb1 Hb2") as %[Hq _].
    exfalso. by apply (Qp.not_add_le_l 1 1).
  Qed.

  Lemma ctx_under_running_excl `{CID : CpuId} (ξ ξ' : CtxId) :
    ctx_under ξ ξ' -∗ own_context ξ -∗ False.
  Proof.
    rewrite ctx_under_unseal /ctx_under_def own_context_unseal /own_context_def.
    iIntros "(%B1 & %D1 & [Hb1 _] & _ & _) (%B & %K & %W & %D & [Hb _] & _)".
    iDestruct (mono_nat_auth_own_agree with "Hb1 Hb") as %[Hq _].
    exfalso. by apply (Qp.not_add_le_l 1 1).
  Qed.

  (* ------------------------------------------------------------------ *)
  (** * 9. The thread record, in the new shape                           *)
  (* ------------------------------------------------------------------ *)

  (** What [SwtchCtx.resume_tok None XIt] AND [park_tok None XIo] become:
      the record parked under the context that is running where the token
      is read -- the resumer's own.  At the crossing the parker parks under
      the TARGET (the only other running token it has; a lock record is
      stamped and cannot be a parent), so the resumed thread reads
      [ctx_under XIo cur_ctx] at its own identity, and its later release
      carries it to the lock as a payload conjunct ([ctx_under_morph]).
      In [SwtchCtx.valid_context_pre] this must be written at the record's
      identity and hart, [(XI := XIp) (CID := h)], not at the section's
      ambient ones.  Today's form implies it ([ctx_under_of_pair]). *)
  Definition resume_tok_under `{XI : CurCtx} (XIt : CtxId) : iProp Σ :=
    ctx_under XIt cur_ctx.
  Definition park_tok_under `{XI : CurCtx} (XIo : CtxId) : iProp Σ :=
    ctx_under XIo cur_ctx.

  Lemma resume_tok_under_of_today `{XI : CurCtx} (XIt : CtxId) :
    (∃ Tt : nat, ctx_parked XIt Tt ∗ ctx_floor cur_ctx Tt) -∗ resume_tok_under XIt.
  Proof.
    iIntros "(%Tt & Hpk & #Hfl)". iApply (ctx_under_of_pair with "Hpk Hfl").
  Qed.

  (** The resumer's half of swtch ([TsoCtxPark.ctx_resume_floor]'s
      successor): both tokens running after it. *)
  Lemma swtch_resume `{CID : CpuId} `{XI : CurCtx} (XIt : CtxId) :
    own_context cur_ctx -∗ resume_tok_under XIt ==∗ own_context cur_ctx ∗ own_context XIt.
  Proof. rewrite /resume_tok_under. apply ctx_resume_under. Qed.

  (** The parker's half ([TsoCtxPark.ctx_park_box]'s successor): the caller
      [XIo] parks under the TARGET [XIt], whose token the resume half has
      just produced ("both tokens running at the crossing").  The target
      then holds [park_tok_under XIo] at its own identity. *)
  Lemma swtch_park `{CID : CpuId} (XIt XIo : CtxId) :
    own_context XIt -∗ own_context XIo ==∗ own_context XIt ∗ ctx_under XIo XIt.
  Proof. apply ctx_park_under. Qed.
End under.
