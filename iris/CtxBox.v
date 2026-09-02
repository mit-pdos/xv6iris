(* CtxBox.v -- THE TRANSIT BOX, v2 (claude-notes/design/tso-escrow-endgame.md
   §2/§3).

   STATUS: PROVEN (R2; no [Admitted]).  The six lemmas (a)-(f), the
   allocator [box_alloc_at], the shape-changing deposit [box_deposit_L1_shape]
   and the reference kit are closed; each proof still follows the case
   skeleton its statement was written with (destruct the window flag,
   destruct the arm, name the refutation or the transition, list the rows
   the close re-establishes).  This file is the design of record for the
   box's LEMMAS: the endgame doc points here for premises and conclusions,
   and a change to a lemma's shape is a change to this file first.

   WHY A SKELETON.  Five design leaks in one day (F1, F6, F7, F8, F9) were
   all of the kind a statement catches and prose does not: a missing arm
   case, a conclusion asserted from a spec parameter rather than derived
   from a premise, a binder scoped over the wrong parameter.  Typing the
   statements and writing the case split BEFORE building is the fix.  The
   first rule-0 audit of this file (F10–F13) then found four conclusions
   without a producing premise in the statements themselves -- fixed
   here: (a)/(b) name the window's x through the register, (d) takes
   llb td, (e) takes Q, out_l2 records keyed m i for (f).

   THE BOX (parameters of the section):
     id       the client's identity type (bcache: dev × blockno)
     X        the client's shared witness type (bcache: the data bytes bs;
              P_hdr and P_rest share ONE binder over it -- F8)
     P_hdr    the header: cells the L1 side reads or writes, at an identity
     P_rest   the rest of the bundle
     Q        the client's ξ-free ghost residue during an L2 checkout
     tok      the L2 exclusivity token (bcache: bown; icache: ic_tok)
   with the two exclusivity laws the arms are refuted by.  tok and Q must
   be GHOST (no cells): CtxMorph of a constant is trivial, so only
   ξ-freedom keeps the box CtxMove-able across the fork (R-4).
   THE L2 HOLDER'S HANDLE pins the parked fragment's keys AND mass when it
   instantiates l2_hold (bcache: a unit singleton at ((dev,bno), t); icache:
   the share singleton at mass s) -- never ∃ over the map (R-1).

   THE GHOSTS (one per box; §3.2):
     stamps   authR (gmapUR (id * nat) ufracR) -- the STAMPED SHARES.  Each
              counted reference owns one unit of mass at key (identity,
              stamp of the last deposit it witnessed); shares own part of a
              unit.  Row (I): every live key names the box's identity.
     cnt      ghost_var nat -- half in the box, half beside L1's refcount.
     slot_d   ghost_var slot_reg -- THE L1 SLOT REGISTER {| td; win; ident;
              x |}, half in the box, half in L1's payload row.  The only
              state L1 and the box share.  [x] names the witness the open
              window's P_rest sits at (F10), so (b) re-deposits a header
              at the SAME x -- the bcache header ignores it, the icache's
              valid re-deposit needs it.
     slot_p   ghost_var l2_reg -- THE L2 SLOT REGISTER {| tp; hold |},
              half in the box, half in L2's payload row (at rest) or in the
              L2 holder's handle (during a checkout).  [hold] records
              exactly the fragment the checkout parked in the OUT_L2 arm --
              key(s) AND mass -- so the park can take it back and re-form
              the unit.  (F7 without the split: the vetted half-split left
              the rejoined mass ∃-bound, and refs-- needs a unit.)

   THE ARMS: IN | OUT_L2 | OUT_L1, selected by the L1 register's flag:
     win = false:  (∃ x, P_hdr ident x ξb ∗ P_rest x ξb)  ∨  OUT_L2
     win = true :  hdr_out ∗ P_rest x ξb  at the x the register names
                   (sr_x = Some (x, T); (a) set it at the box stamp, (b) re-deposits at it)
   OUT_L2 := Q ∗ tok ∗ (the L2 payload's own row is NOT here: its slot_p
   half rides the holder's handle) ∗ the parked fragment named by [hold].

   THE ROWS (pure, in the body):
     (I)  ∀ p ∈ dom m, p.1 = ident          the checkout's identity tie
     (C)  (∀ p ∈ dom m, T ≤ p.2) ∨ T ≤ tp   the L2-side cover
     (D)  T ≤ td ∨ T ∈ snd <$> dom m         the L1-side cover
     (Σ)  qsum m = c                        mass = refcount

   THE SIX LEMMAS: withdraw_L1 (a), deposit_L1 (b), ref_incr (c),
   ref_decr (d), checkout (e), park (f); plus box_alloc (boot).  No others.

   The cmra/class declarations here move to Xv6Cameras §15 at R1'; they are
   local so this file type-checks standalone. *)
From Stdlib Require Import ZArith Lia QArith Qcanon.
From stdpp Require Import gmap countable.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import auth gmap ufrac.
From iris.base_logic.lib Require Import own ghost_var invariants.
Require Import RiscvLang RiscvPtsto.
Require Import TsoMemPa TsoGhost.
Require Import TsoCtx.
Require Import TsoCtxPark.
Require Import TsoCtxAbsorbLb.

(* the registers' value types, the stamps camera, the class [boxG] and the
   names record [box_names] live in Xv6Cameras §15 (one camera bundle). *)
Require Import Xv6Cameras.

(* ---- pure helpers over the stamps map ------------------------------- *)
Section helpers.
  Context {id : Type} `{Countable id}.

  (* the mass, in Q (F3's Q-valued sum: ∅ ↦ 0, no case split).  The step
     is a named Definition over Qcplus (R-3): an anonymous (_ + _)%Qc body
     resolves through the Qc→Q coercion under map_fold_insert_L. *)
  Definition qsum_step (_ : id * nat) (q : ufrac) (acc : Qc) : Qc := Qcplus (Qp_to_Qc q) acc.
  Definition qsum (m : gmap (id * nat) ufrac) : Qc := map_fold qsum_step 0%Qc m.
  Definition nat_Qc (n : nat) : Qc := Qc_of_Z (Z.of_nat n).

  (* the largest stamp a fragment names (0 on ∅) -- what R1 presents *)
  Definition max_step (p : id * nat) (_ : ufrac) (acc : nat) : nat := Nat.max p.2 acc.
  Definition max_stamp (m : gmap (id * nat) ufrac) : nat := map_fold max_step 0%nat m.

  (* every key of the fragment is at this identity *)
  Definition keyed (m : gmap (id * nat) ufrac) (i : id) : Prop :=
    ∀ p, p ∈ dom m → p.1 = i.

  (* the unit's mass, as a positive: 1 at c = 0 (the bump), c otherwise *)
  Definition unit_mass (c : nat) : ufrac := pos_to_Qp (Pos.of_nat (Nat.max 1 c)).

  Implicit Types m : gmap (id * nat) ufrac.

  (* iris' inclusion lemmas pinned to this file's cmras: `apply … in` with
     the cmra left implicit cannot invert the carrier coercion; explicit
     instances go through by conversion *)
  Lemma gincl_lookup_iff (m1 m2 : gmap (id * nat) ufrac) :
    m1 ≼ m2 ↔ ∀ i, m1 !! i ≼ m2 !! i.
  Proof. exact (lookup_included (K := id * nat) (A := ufracR) m1 m2). Qed.
  Lemma gincl_option_iff (ma mb : option ufrac) :
    ma ≼ mb ↔ ma = None ∨ ∃ a b, ma = Some a ∧ mb = Some b ∧ (a ≡ b ∨ a ≼ b).
  Proof. exact (option_included (A := ufracR) ma mb). Qed.
  Lemma gincl_Some_iff (a b : ufrac) : Some a ≼ Some b ↔ a ≡ b ∨ a ≼ b.
  Proof. exact (Some_included (A := ufracR) a b). Qed.
  Lemma gincl_singleton_l (m : gmap (id * nat) ufrac) (i : id * nat) (x : ufrac) :
    {[i := x]} ≼ m ↔ ∃ y, m !! i ≡ Some y ∧ Some x ≼ Some y.
  Proof. exact (singleton_included_l (K := id * nat) (A := ufracR) m i x). Qed.
  Lemma gincl_dom (m1 m2 : gmap (id * nat) ufrac) : m1 ≼ m2 → dom m1 ⊆ dom m2.
  Proof. exact (dom_included (K := id * nat) (A := ufracR) m1 m2). Qed.

  (* ---- Qc arithmetic ---- *)
  Lemma Qc_plus_pos_not_le (x y : Qc) : (0 < y)%Qc -> ¬ (y + x <= x)%Qc.
  Proof.
    intros Hy Hle. apply (Qcle_not_lt _ _ Hle). apply Qclt_minus_iff.
    rewrite -Qcplus_assoc Qcplus_opp_r Qcplus_0_r. exact Hy.
  Qed.
  Lemma Qc_plus_pos_not_le_r (x y : Qc) : (0 < y)%Qc -> ¬ (x + y <= x)%Qc.
  Proof. intros Hy. rewrite Qcplus_comm. by apply Qc_plus_pos_not_le. Qed.
  Lemma Qc_plus_cancel_l (x y z : Qc) : (x + y)%Qc = (x + z)%Qc -> y = z.
  Proof.
    intros Hxyz. apply (f_equal (fun w => (- x + w)%Qc)) in Hxyz.
    rewrite !Qcplus_assoc (Qcplus_comm (- x) x) Qcplus_opp_r !Qcplus_0_l in Hxyz. exact Hxyz.
  Qed.
  Lemma Qp_to_Qc_1 : Qp_to_Qc 1%Qp = 1%Qc.
  Proof. apply Qc_is_canon. by vm_compute. Qed.
  Lemma nat_Qc_0 : nat_Qc 0 = 0%Qc.
  Proof. apply Z2Qc_inj_0. Qed.
  Lemma nat_Qc_1 : nat_Qc 1 = 1%Qc.
  Proof. apply Z2Qc_inj_1. Qed.
  Lemma nat_Qc_S (c : nat) : nat_Qc (S c) = (1 + nat_Qc c)%Qc.
  Proof. rewrite /nat_Qc Nat2Z.inj_succ -Z.add_1_l Z2Qc_inj_add Z2Qc_inj_1. reflexivity. Qed.
  Lemma nat_Qc_pos (n : nat) : (0 < n)%nat -> Qp_to_Qc (pos_to_Qp (Pos.of_nat n)) = nat_Qc n.
  Proof.
    intros Hn. destruct n as [|n]; [lia|]. rewrite -Pos.of_nat_succ.
    unfold pos_to_Qp; simpl. unfold nat_Qc. rewrite Zpos_P_of_succ_nat Nat2Z.inj_succ. reflexivity.
  Qed.
  Lemma unit_mass_Qc (c : nat) : Qp_to_Qc (unit_mass c) = nat_Qc (Nat.max 1 c).
  Proof. rewrite /unit_mass. apply nat_Qc_pos. lia. Qed.

  (* ---- qsum ---- *)
  Lemma qsum_step_comm (j1 j2 : id * nat) (z1 z2 : ufrac) (y : Qc) :
    qsum_step j1 z1 (qsum_step j2 z2 y) = qsum_step j2 z2 (qsum_step j1 z1 y).
  Proof. unfold qsum_step. rewrite !Qcplus_assoc (Qcplus_comm (Qp_to_Qc z1)). reflexivity. Qed.
  Lemma qsum_empty : qsum ∅ = 0%Qc.
  Proof. by rewrite /qsum map_fold_empty. Qed.
  Lemma qsum_insert m (p : id * nat) (q : ufrac) :
    m !! p = None -> qsum (<[p := q]> m) = Qcplus (Qp_to_Qc q) (qsum m).
  Proof.
    intros Hp. rewrite /qsum.
    rewrite (map_fold_insert_L qsum_step 0%Qc p q m
               (fun j1 j2 z1 z2 y _ _ _ => qsum_step_comm j1 j2 z1 z2 y) Hp).
    reflexivity.
  Qed.
  Lemma qsum_delete m (p : id * nat) (q : ufrac) :
    m !! p = Some q -> qsum m = Qcplus (Qp_to_Qc q) (qsum (delete p m)).
  Proof.
    intros Hp. rewrite /qsum.
    rewrite (map_fold_delete_L qsum_step 0%Qc p q m
               (fun j1 j2 z1 z2 y _ _ _ => qsum_step_comm j1 j2 z1 z2 y) Hp).
    reflexivity.
  Qed.
  Lemma qsum_nonneg m : (0 <= qsum m)%Qc.
  Proof.
    induction m as [|p q m Hp IH] using map_ind.
    { rewrite qsum_empty. apply Qcle_refl. }
    rewrite (qsum_insert _ _ _ Hp). pose proof (Qp_prf q) as Hq.
    rewrite -(Qcplus_0_l 0). apply Qcplus_le_compat; [apply Qclt_le_weak; exact Hq | exact IH].
  Qed.
  Lemma qsum_pos m : m ≠ ∅ -> (0 < qsum m)%Qc.
  Proof.
    induction m as [|p q m Hp IH] using map_ind; [done|].
    intros _. rewrite (qsum_insert _ _ _ Hp). pose proof (Qp_prf q) as Hq.
    eapply Qclt_le_trans; [exact Hq|].
    rewrite -{1}(Qcplus_0_r (Qp_to_Qc q)). apply Qcplus_le_compat; [apply Qcle_refl | apply qsum_nonneg].
  Qed.
  Lemma qsum_zero_empty m : qsum m = 0%Qc -> m = ∅.
  Proof.
    intros Hz. destruct (decide (m = ∅)) as [|Hne]; [done|].
    pose proof (qsum_pos m Hne) as Hp. rewrite Hz in Hp. exfalso. exact (Qclt_not_eq _ _ Hp eq_refl).
  Qed.
  Lemma qsum_incl_le (m1 m2 : gmap (id * nat) ufrac) : m1 ≼ m2 -> (qsum m1 <= qsum m2)%Qc.
  Proof.
    revert m2. induction m1 as [|p q m1 Hp IH] using map_ind; intros m2 Hincl.
    { rewrite qsum_empty. apply qsum_nonneg. }
    pose proof (proj1 (gincl_lookup_iff _ _) Hincl) as Hl.
    pose proof (Hl p) as Hp2. rewrite lookup_insert in Hp2.
    destruct (proj1 (gincl_option_iff _ _) Hp2) as [Hc | (a & b & Ha & Hb & Hab)]; [discriminate|].
    injection Ha as <-.
    assert (Hqle : (Qp_to_Qc q <= Qp_to_Qc b)%Qc).
    { destruct Hab as [Heq | Hlt].
      - apply leibniz_equiv in Heq. subst b. apply Qcle_refl.
      - apply (proj1 (ufrac_included q b)) in Hlt. apply Qclt_le_weak. by apply Qp.to_Qc_inj_lt. }
    assert (Hrest : m1 ≼ delete p m2).
    { apply (proj2 (gincl_lookup_iff m1 (delete p m2))). intros i. destruct (decide (i = p)) as [->|Hne].
      - rewrite Hp lookup_delete. apply (proj2 (gincl_option_iff None None)). by left.
      - rewrite lookup_delete_ne; [|done]. pose proof (Hl i) as Hi.
        by rewrite lookup_insert_ne in Hi. }
    rewrite (qsum_insert _ _ _ Hp) (qsum_delete _ _ _ Hb).
    apply Qcplus_le_compat; [exact Hqle | exact (IH _ Hrest)].
  Qed.
  Lemma qsum_singleton (p : id * nat) (q : ufrac) : qsum {[p := q]} = Qp_to_Qc q.
  Proof.
    rewrite -(insert_empty p q) qsum_insert; [| apply lookup_empty].
    rewrite qsum_empty. apply Qcplus_0_r.
  Qed.

  Lemma qsum_singleton_op m (p : id * nat) (q : ufrac) :
    qsum ({[p := q]} ⋅ m) = (Qp_to_Qc q + qsum m)%Qc.
  Proof.
    destruct (m !! p) as [q0|] eqn:Hp.
    - assert (Heq : {[p := q]} ⋅ m = <[p := (q ⋅ q0)]> (delete p m)).
      { apply map_eq. intros i. rewrite lookup_op. destruct (decide (i = p)) as [->|Hne].
        - rewrite lookup_singleton lookup_insert Hp. by rewrite -Some_op.
        - rewrite lookup_singleton_ne; [|done]. rewrite lookup_insert_ne; [|done].
          rewrite lookup_delete_ne; [|done]. by rewrite left_id_L. }
      rewrite Heq qsum_insert; [| apply lookup_delete].
      rewrite (qsum_delete m p q0 Hp). rewrite ufrac_op Qp.to_Qc_inj_add. by rewrite Qcplus_assoc.
    - rewrite -insert_singleton_op; [| exact Hp]. by apply qsum_insert.
  Qed.
  Lemma qsum_op (m1 m2 : gmap (id * nat) ufrac) : qsum (m1 ⋅ m2) = (qsum m1 + qsum m2)%Qc.
  Proof.
    induction m1 as [|p q m1 Hp IH] using map_ind.
    { rewrite left_id_L qsum_empty. by rewrite Qcplus_0_l. }
    rewrite (insert_singleton_op m1 p q Hp) -assoc_L qsum_singleton_op IH.
    rewrite (qsum_singleton_op m1 p q). by rewrite Qcplus_assoc.
  Qed.
  (* equal mass under inclusion: no key of the larger map is missing *)
  Lemma qsum_eq_dom (m1 m2 : gmap (id * nat) ufrac) :
    m1 ≼ m2 -> qsum m1 = qsum m2 -> dom m2 ⊆ dom m1.
  Proof.
    intros Hincl Heq p Hp. destruct (decide (p ∈ dom m1)) as [|Hnot]; [done|]. exfalso.
    apply elem_of_dom in Hp as [q Hq]. apply not_elem_of_dom in Hnot.
    assert (Hincl' : m1 ≼ delete p m2).
    { apply (proj2 (gincl_lookup_iff m1 (delete p m2))). intros i. destruct (decide (i = p)) as [->|Hne].
      - rewrite Hnot lookup_delete. apply (proj2 (gincl_option_iff None None)). by left.
      - rewrite lookup_delete_ne; [|done]. exact (proj1 (gincl_lookup_iff m1 m2) Hincl i). }
    apply qsum_incl_le in Hincl'. rewrite (qsum_delete m2 p q Hq) in Heq.
    rewrite Heq in Hincl'. exact (Qc_plus_pos_not_le _ _ (Qp_prf q) Hincl').
  Qed.
  Lemma singleton_ne_empty_map (p : id * nat) (q : ufrac) : ({[p := q]} : gmap (id * nat) ufrac) ≠ ∅.
  Proof.
    intros Hc. apply (f_equal (lookup p)) in Hc. rewrite lookup_singleton lookup_empty in Hc. discriminate.
  Qed.

  (* ---- max_stamp ---- *)
  Lemma max_step_comm (j1 j2 : id * nat) (z1 z2 : ufrac) (y : nat) :
    max_step j1 z1 (max_step j2 z2 y) = max_step j2 z2 (max_step j1 z1 y).
  Proof. unfold max_step. lia. Qed.
  Lemma max_stamp_insert m (p : id * nat) (q : ufrac) :
    m !! p = None -> max_stamp (<[p := q]> m) = Nat.max p.2 (max_stamp m).
  Proof.
    intros Hp. rewrite /max_stamp.
    rewrite (map_fold_insert_L max_step 0%nat p q m
               (fun j1 j2 z1 z2 y _ _ _ => max_step_comm j1 j2 z1 z2 y) Hp).
    reflexivity.
  Qed.
  Lemma max_stamp_ge m (p : id * nat) : p ∈ dom m -> (p.2 <= max_stamp m)%nat.
  Proof.
    induction m as [|p' q m Hp' IH] using map_ind.
    { intros Hp. rewrite dom_empty_L in Hp. by apply not_elem_of_empty in Hp. }
    intros Hp. rewrite (max_stamp_insert _ _ _ Hp'). rewrite dom_insert_L in Hp.
    apply elem_of_union in Hp as [Hp | Hp].
    - apply elem_of_singleton in Hp. subst p'. lia.
    - pose proof (IH Hp). lia.
  Qed.
  Lemma max_stamp_singleton (p : id * nat) (q : ufrac) : max_stamp {[p := q]} = p.2.
  Proof.
    rewrite -insert_empty (max_stamp_insert ∅ p q (lookup_empty _)).
    rewrite /max_stamp map_fold_empty. lia.
  Qed.

  (* ---- keyed ---- *)
  Lemma keyed_singleton (i : id) (t : nat) (q : ufrac) : keyed {[(i, t) := q]} i.
  Proof.
    intros p Hp. rewrite dom_singleton_L in Hp. apply elem_of_singleton in Hp. by subst p.
  Qed.
  Lemma keyed_sub (m m' : gmap (id * nat) ufrac) (i : id) :
    dom m' ⊆ dom m -> keyed m i -> keyed m' i.
  Proof. intros Hsub Hk p Hp. apply Hk. by apply Hsub. Qed.
  Lemma keyed_singleton_op m (i : id) (t : nat) (q : ufrac) :
    keyed m i -> keyed ({[(i, t) := q]} ⋅ m) i.
  Proof.
    intros Hk p Hp. rewrite dom_op dom_singleton_L in Hp.
    apply elem_of_union in Hp as [Hp | Hp]; [apply elem_of_singleton in Hp; by subst p | by apply Hk].
  Qed.
  Lemma keyed_agree (m mh : gmap (id * nat) ufrac) (i i' : id) :
    mh ≠ ∅ -> dom mh ⊆ dom m -> keyed mh i -> keyed m i' -> i = i'.
  Proof.
    intros Hne Hsub Hk Hk'. destruct (map_choose mh Hne) as (p & q & Hp).
    assert (Hpd : p ∈ dom mh) by (apply elem_of_dom; by exists q).
    rewrite -(Hk p Hpd). apply Hk'. by apply Hsub.
  Qed.

  (* ---- the two local updates on the stamps auth ---- *)
  Lemma stamps_alloc_upd m (p : id * nat) (q : ufrac) :
    (● m : stampsR id) ~~> ● ({[p := q]} ⋅ m) ⋅ ◯ {[p := q]}.
  Proof.
    apply auth_update_alloc. apply local_update_unital_discrete. intros z _ Hz.
    rewrite left_id in Hz. rewrite -Hz. split; [| done].
    intros i. match goal with |- ✓ ?x => destruct x as [q'|] end; exact I.
  Qed.
  (* one key loses mass d (all of it: the key leaves) *)
  Definition msub_key m (p : id * nat) (d : ufrac) : gmap (id * nat) ufrac :=
    match m !! p with
    | Some q => match (q - d)%Qp with Some r => <[p := r]> m | None => delete p m end
    | None => m
    end.
  Lemma msub_key_lookup_ne m (p i : id * nat) (d : ufrac) :
    i ≠ p -> msub_key m p d !! i = m !! i.
  Proof.
    intros Hne. rewrite /msub_key. destruct (m !! p) as [q|]; [|done].
    destruct (q - d)%Qp; [by rewrite lookup_insert_ne | by rewrite lookup_delete_ne].
  Qed.
  Lemma msub_key_upd m (p : id * nat) (d : ufrac) :
    {[p := d]} ≼ m ->
    (● m : stampsR id) ⋅ ◯ {[p := d]} ~~> ● (msub_key m p d).
  Proof.
    intros Hincl. apply auth_update_dealloc.
    apply (gmap_local_update (K := id * nat) (A := ufracR) m {[p := d]} (msub_key m p d) ∅). intros i.
    destruct (decide (i = p)) as [->|Hne]; last first.
    { rewrite lookup_singleton_ne; [|done]. rewrite (msub_key_lookup_ne _ _ _ _ Hne).
      rewrite lookup_empty.
      apply (local_update_unital_discrete (A := optionUR ufracR)). intros z Hv Hz. by split. }
    destruct (proj1 (gincl_singleton_l m p d) Hincl) as (y & Hy & Hle).
    apply leibniz_equiv in Hy. rewrite lookup_singleton lookup_empty.
    destruct (proj1 (gincl_Some_iff d y) Hle) as [Heq | Hlt].
    - apply leibniz_equiv in Heq. subst y.
      assert (Hsub : (d - d)%Qp = None) by (apply Qp.sub_None; reflexivity).
      rewrite /msub_key Hy Hsub lookup_delete.
      apply (local_update_unital_discrete (A := optionUR ufracR)). intros z _ Hz.
      destruct z as [r|].
      { exfalso. rewrite -Some_op in Hz. apply (inj Some) in Hz. apply leibniz_equiv in Hz.
        rewrite ufrac_op in Hz. exact (Qp.add_id_free d r (eq_sym Hz)). }
      split; [done | by rewrite left_id].
    - apply (proj1 (ufrac_included d y)) in Hlt. apply Qp.lt_sum in Hlt as [r Hr]. subst y.
      assert (Hsub : (d + r - d)%Qp = Some r) by (by apply Qp.sub_Some).
      rewrite /msub_key Hy Hsub lookup_insert.
      apply (local_update_unital_discrete (A := optionUR ufracR)). intros z _ Hz.
      destruct z as [r'|]; last first.
      { exfalso. rewrite right_id in Hz. apply (inj Some) in Hz. apply leibniz_equiv in Hz.
        exact (Qp.add_id_free d r Hz). }
      rewrite -Some_op in Hz. apply (inj Some) in Hz. apply leibniz_equiv in Hz.
      rewrite ufrac_op in Hz. apply (inj (Qp.add d)) in Hz. subst r'.
      split; [done | by rewrite left_id].
  Qed.
  Lemma qsum_msub_key m (p : id * nat) (d : ufrac) :
    {[p := d]} ≼ m -> (Qp_to_Qc d + qsum (msub_key m p d))%Qc = qsum m.
  Proof.
    intros Hincl. destruct (proj1 (gincl_singleton_l m p d) Hincl) as (y & Hy & Hle).
    apply leibniz_equiv in Hy. destruct (proj1 (gincl_Some_iff d y) Hle) as [Heq | Hlt].
    - apply leibniz_equiv in Heq. subst y.
      assert (Hsub : (d - d)%Qp = None) by (apply Qp.sub_None; reflexivity).
      rewrite /msub_key Hy Hsub. by rewrite -(qsum_delete m p d Hy).
    - apply (proj1 (ufrac_included d y)) in Hlt. apply Qp.lt_sum in Hlt as [r Hr]. subst y.
      assert (Hsub : (d + r - d)%Qp = Some r) by (by apply Qp.sub_Some).
      rewrite /msub_key Hy Hsub. rewrite -(insert_delete_insert m p r) qsum_insert; [| apply lookup_delete].
      rewrite (qsum_delete m p (d + r)%Qp Hy) Qp.to_Qc_inj_add. by rewrite Qcplus_assoc.
  Qed.
  Lemma dom_msub_key_sub m (p : id * nat) (d : ufrac) : dom (msub_key m p d) ⊆ dom m.
  Proof.
    rewrite /msub_key. destruct (m !! p) as [q|] eqn:Hp; [|done].
    destruct (q - d)%Qp as [r|].
    - rewrite dom_insert_L. intros i Hi. apply elem_of_union in Hi as [Hi | Hi]; [|done].
      apply elem_of_singleton in Hi. subst i. exact (elem_of_dom_2 m p q Hp).
    - rewrite dom_delete_L. set_solver.
  Qed.
  Lemma dom_msub_key_cases m (p i : id * nat) (d : ufrac) :
    i ∈ dom m -> i ∈ dom (msub_key m p d) ∨ i = p.
  Proof.
    intros Hi. destruct (decide (i = p)) as [->|Hne]; [by right|]. left.
    apply elem_of_dom in Hi as [x Hx]. apply (elem_of_dom_2 _ i x).
    by rewrite (msub_key_lookup_ne _ _ _ _ Hne).
  Qed.

  (* ---- shares (icache M-5): a fragment scaled by s, and joins ---- *)
  Definition mscale (s : Qp) m : gmap (id * nat) ufrac := (fun q : ufrac => (q * s)%Qp) <$> m.
  Lemma mscale_lookup (s : Qp) m (p : id * nat) :
    mscale s m !! p = (fun q : ufrac => (q * s)%Qp) <$> (m !! p).
  Proof. by rewrite /mscale lookup_fmap. Qed.
  Lemma dom_mscale (s : Qp) m : dom (mscale s m) = dom m.
  Proof. by rewrite /mscale dom_fmap_L. Qed.
  Lemma mscale_empty_iff (s : Qp) m : mscale s m = ∅ <-> m = ∅.
  Proof. by rewrite /mscale fmap_empty_iff. Qed.
  (* m = mscale s m ⋅ mscale s' m when s + s' = 1 *)
  Lemma mscale_split (s s' : Qp) m :
    (s + s')%Qp = 1%Qp -> m = mscale s m ⋅ mscale s' m.
  Proof.
    intros Hss. apply map_eq. intros p. rewrite lookup_op !mscale_lookup.
    destruct (m !! p) as [q|]; simpl; [| done].
    change (Some (q * s)%Qp ⋅ Some (q * s')%Qp) with (Some ((q * s) + (q * s'))%Qp).
    f_equal. rewrite -Qp.mul_add_distr_l Hss Qp.mul_1_r. reflexivity.
  Qed.
  Lemma qsum_mscale (s : Qp) m : qsum (mscale s m) = (qsum m * Qp_to_Qc s)%Qc.
  Proof.
    induction m as [|p q m Hp IH] using map_ind.
    { rewrite /mscale fmap_empty !qsum_empty. by rewrite Qcmult_0_l. }
    rewrite /mscale fmap_insert (qsum_insert _ _ _ Hp).
    rewrite qsum_insert; [| by rewrite lookup_fmap Hp].
    fold (mscale s m). rewrite IH Qp.to_Qc_inj_mul. by rewrite Qcmult_plus_distr_l.
  Qed.
  Lemma max_stamp_mscale (s : Qp) m : max_stamp (mscale s m) = max_stamp m.
  Proof.
    induction m as [|p q m Hp IH] using map_ind.
    { by rewrite /mscale fmap_empty. }
    rewrite /mscale fmap_insert (max_stamp_insert _ _ _ Hp).
    rewrite max_stamp_insert; [| by rewrite lookup_fmap Hp]. by rewrite IH.
  Qed.
  Lemma max_stamp_singleton_op m (p : id * nat) (q : ufrac) :
    max_stamp ({[p := q]} ⋅ m) = Nat.max p.2 (max_stamp m).
  Proof.
    destruct (m !! p) as [q0|] eqn:Hp.
    - assert (Heq : {[p := q]} ⋅ m = <[p := (q ⋅ q0)]> (delete p m)).
      { apply map_eq. intros i. rewrite lookup_op. destruct (decide (i = p)) as [->|Hne].
        - rewrite lookup_singleton lookup_insert Hp. by rewrite -Some_op.
        - rewrite lookup_singleton_ne; [|done]. rewrite lookup_insert_ne; [|done].
          rewrite lookup_delete_ne; [|done]. by rewrite left_id_L. }
      rewrite Heq max_stamp_insert; [| apply lookup_delete].
      rewrite {2}/max_stamp (map_fold_delete_L max_step 0%nat p q0 m
                (fun j1 j2 z1 z2 y _ _ _ => max_step_comm j1 j2 z1 z2 y) Hp).
      unfold max_step at 1. fold (max_stamp (delete p m)). lia.
    - rewrite -insert_singleton_op; [| exact Hp]. by apply max_stamp_insert.
  Qed.
  Lemma max_stamp_op (m1 m2 : gmap (id * nat) ufrac) :
    max_stamp (m1 ⋅ m2) = Nat.max (max_stamp m1) (max_stamp m2).
  Proof.
    induction m1 as [|p q m1 Hp IH] using map_ind.
    { rewrite left_id_L /max_stamp map_fold_empty. lia. }
    rewrite (insert_singleton_op m1 p q Hp) -assoc_L max_stamp_singleton_op IH.
    rewrite (max_stamp_singleton_op m1 p q). lia.
  Qed.
  Lemma keyed_op (m1 m2 : gmap (id * nat) ufrac) (i : id) :
    keyed m1 i -> keyed m2 i -> keyed (m1 ⋅ m2) i.
  Proof.
    intros H1 H2 p Hp. rewrite dom_op in Hp.
    apply elem_of_union in Hp as [Hp | Hp]; [by apply H1 | by apply H2].
  Qed.
  Lemma op_ne_empty_l (m1 m2 : gmap (id * nat) ufrac) : m1 ≠ ∅ -> m1 ⋅ m2 ≠ ∅.
  Proof.
    intros Hne Hc. apply Hne. apply map_eq. intros p.
    apply (f_equal (lookup p)) in Hc. rewrite lookup_op lookup_empty in Hc.
    rewrite lookup_empty. destruct (m1 !! p) as [q|] eqn:Hq; [| done].
    exfalso. rewrite Hq in Hc. destruct (m2 !! p) as [q'|] eqn:Hq2; rewrite Hq2 in Hc.
    - rewrite -Some_op in Hc. discriminate.
    - rewrite right_id_L in Hc. discriminate.
  Qed.
End helpers.

Section box.
  Context `{!riscvGS Σ}.
  Context {id : Type} `{Countable id} `{!Inhabited id}.
  Context {X : Type}.
  Context `{!boxG id X Σ}.

  (* ---- the client's parameters -------------------------------------- *)
  Context (P_hdr : id → X → CtxId → iProp Σ).
  Context (P_rest : X → CtxId → iProp Σ).
  (* THE RESIDUES (the second edit, endgame plan §6¹²–§6¹⁸): the client's
     ξ-free ghost while the bundle is out, INDEXED BY ARM so that every
     party that gets a residue back -- (b)/(b′) at OUT_L1, (g) across, (f′)'s
     join at OUT_L2 -- receives exactly its own and refutes nothing (F41):
       Q1 c : the OUT_L1 window's residue at the body's COUNT c (stable
              across the window: (c)/(d) need win = false), so the recycler
              (c = 0) and the guard (c = 1) are separated by type (§6¹⁴);
       Q2   : the OUT_L2 (checkout) residue.
     A viewer (box_view) reads Q1 c / Q2 by arm; each arm of each must be
     refutable or readable-with-identity from what a viewer holds, on EVERY
     state the rows admit (F44's tripwire). *)
  Context (Q1 : nat → iProp Σ).
  Context (Q2 : iProp Σ).

  (* the client's obligations *)
  Context `{!∀ i x, CtxMorph (P_hdr i x)} `{!∀ x, CtxMorph (P_rest x)}.
  Context `{!∀ i x ξ, Timeless (P_hdr i x ξ)} `{!∀ x ξ, Timeless (P_rest x ξ)}.
  Context `{!∀ c, Timeless (Q1 c)} `{!Timeless Q2}.
  (* THE EDIT (endgame plan §6⁶(A)): the arm is SELECTED by the two
     registers -- IN = (win false, hold None), OUT_L1 = (win true, hold
     None), OUT_L2 = (win false, hold Some) -- so the clients owe no
     cell-clash obligations (P_hdr_excl / P_rest_excl) and no token: (f)
     selects OUT_L2 by agreement on its L2 half, (e) refutes OUT_L1 by Σ
     and needs no token to refute OUT_L2 (its L2 half says hold = None).
     A one-cell client (the off box, R4b) can instantiate the box. *)

  Implicit Types (γ : box_names) (m : gmap (id * nat) ufrac).

  (* ---- the ghosts, named ------------------------------------------- *)
  Definition stamps_auth γ m : iProp Σ := own (bx_stamps γ) (● m).
  Definition stamps_frag γ m : iProp Σ := own (bx_stamps γ) (◯ m).
  Definition cnt_half γ (c : nat) : iProp Σ := ghost_var (bx_cnt γ) (1/2) c.
  Definition slotd_half γ (r : slot_reg id X) : iProp Σ := ghost_var (bx_slotd γ) (1/2) r.
  Definition slotp_half γ (s : l2_reg id) : iProp Σ := ghost_var (bx_slotp γ) (1/2) s.

  (* ---- the reference: ONE spelling, ghost-only (§3.3) --------------- *)
  (* a counted reference has [qsum m = 1]; a share has any positive mass *)
  Definition reference γ (i : id) m : iProp Σ :=
    (⌜m ≠ ∅⌝ ∗ ⌜keyed m i⌝ ∗ stamps_frag γ m ∗ llb loglen_name (max_stamp m))%I.

  (* ---- the arms ----------------------------------------------------- *)
  (* the L1 out-window's ghost: the withdrawer's whole unit(s), or ∅ *)
  Definition hdr_out γ m : iProp Σ :=
    (∃ m', ⌜qsum m' = qsum m⌝ ∗ stamps_frag γ m' ∗ llb loglen_name (max_stamp m'))%I.

  Definition in_arm (i : id) (ξb : CtxId) : iProp Σ :=
    (∃ x, P_hdr i x ξb ∗ P_rest x ξb)%I.
  (* the same bundle over a SPLIT header (what (e′) absorbs) *)
  Definition in_arm_of (P : id → X → CtxId → iProp Σ) (i : id) (ξb : CtxId) : iProp Σ :=
    (∃ x, P i x ξb ∗ P_rest x ξb)%I.
  Global Instance in_arm_of_morph (P : id → X → CtxId → iProp Σ)
      `{!∀ i x, CtxMorph (P i x)} (i : id) : CtxMorph (in_arm_of P i).
  Proof. rewrite /in_arm_of. apply ctx_morph_exist. intros x. apply ctx_morph_sep; apply _. Qed.

  (* ---- the body (§2; the edit's register-selected arms) ------------- *)
  (* THE ARM, selected by (lr_hold s, sr_win r).  A PUBLIC definition: the
     collection's view lemma (box_view, §6⁸ Q5) exposes it, so a non-owner
     matches on this and never on the body's layout. *)
  Definition box_arm γ (T : nat) (ξb : CtxId) m (c : nat) (r : slot_reg id X) (s : l2_reg id) : iProp Σ :=
    (match lr_hold s with
     | Some (i, mh) =>                                          (* OUT_L2 *)
         ⌜sr_win r = false⌝ ∗ ⌜mh ≠ ∅⌝ ∗ ⌜keyed mh i⌝ ∗ stamps_frag γ mh ∗ Q2
     | None =>
         if sr_win r
         then hdr_out γ m ∗ (∃ x, ⌜sr_x r = Some (x, T)⌝ ∗ P_rest x ξb) ∗ Q1 c   (* OUT_L1 *)
         else in_arm (sr_ident r) ξb                                          (* IN *)
     end)%I.
  (* the four pure rows, named for the view *)
  Definition box_rows (T : nat) m (c : nat) (r : slot_reg id X) (s : l2_reg id) : Prop :=
    qsum m = nat_Qc c ∧                                        (* Σ *)
    keyed m (sr_ident r) ∧                                     (* I *)
    ((∀ p, p ∈ dom m → (T ≤ p.2)%nat) ∨ (T ≤ lr_tp s)%nat) ∧  (* C *)
    ((T ≤ sr_td r)%nat ∨ ∃ p, p ∈ dom m ∧ p.2 = T).            (* D *)
  Definition box_body γ : iProp Σ :=
    (∃ (T : nat) (ξb : CtxId) m (c : nat) (r : slot_reg id X) (s : l2_reg id),
       ctx_parked ξb T ∗ llb loglen_name T ∗
       stamps_auth γ m ∗ cnt_half γ c ∗ slotd_half γ r ∗ slotp_half γ s ∗
       ⌜box_rows T m c r s⌝ ∗
       box_arm γ T ξb m c r s)%I.
  Definition is_box (N : namespace) γ : iProp Σ := inv N (box_body γ).

  (* the boot fold: fifty deposit stamps under one llb bound (from BioInv) *)
  (* the L1 floor slot at boot: the maximum of the per-buffer boot stamps *)
  Lemma big_sepL_llb_max (l : list nat) (P : nat -> nat -> iProp Σ) :
    ([∗ list] k ∈ l, ∃ Td : nat, llb loglen_name Td ∗ P k Td) -∗
    ∃ tl : nat, llb loglen_name tl ∗
      [∗ list] k ∈ l, ∃ Td : nat, ⌜(Td <= tl)%nat⌝ ∗ llb loglen_name Td ∗ P k Td.
  Proof.
    iInduction l as [|k l] "IH".
    { iIntros "_". iExists 0%nat. iSplitR; [iApply TsoGhost.llb_0|]. done. }
    iIntros "[Hk Hl]". iDestruct "Hk" as (Td) "[#Hllb HP]".
    iDestruct ("IH" with "Hl") as (tl) "[#Hllbtl Hl]".
    iExists (Nat.max tl Td). iSplitR.
    { destruct (Nat.max_spec tl Td) as [[_ ->] | [_ ->]]; [iExact "Hllb" | iExact "Hllbtl"]. }
    iSplitL "HP". { iExists Td. iSplitR; [iPureIntro; lia|]. iFrame "Hllb HP". }
    iApply (big_sepL_mono with "Hl"). intros i k' _. iIntros "(%Td' & %Hb & #Hl' & HP')".
    iExists Td'. iSplitR; [iPureIntro; lia|]. iFrame "Hl' HP'".
  Qed.

  (* ---- instances and the ghost-level kit ------------------------------ *)
  Global Instance in_arm_morph i : CtxMorph (in_arm i).
  Proof. rewrite /in_arm. apply ctx_morph_exist. intros x. apply ctx_morph_sep; apply _. Qed.
  Global Instance in_arm_timeless i ξb : Timeless (in_arm i ξb).
  Proof. rewrite /in_arm. apply _. Qed.
  Global Instance hdr_out_timeless γ m : Timeless (hdr_out γ m).
  Proof. rewrite /hdr_out /stamps_frag. apply _. Qed.

  Global Instance box_arm_timeless γ T ξb m c r s : Timeless (box_arm γ T ξb m c r s).
  Proof.
    rewrite /box_arm. destruct (lr_hold s) as [[i mh]|]; [apply _|].
    destruct (sr_win r); apply _.
  Qed.
  Lemma stamps_frag_incl γ m m' :
    stamps_auth γ m -∗ stamps_frag γ m' -∗ ⌜m' ≼ m⌝.
  Proof.
    iIntros "Ha Hf". iDestruct (own_valid_2 with "Ha Hf") as %[Hincl _]%auth_both_valid_discrete.
    by iPureIntro.
  Qed.
  Lemma stamps_frag_incl_2 γ m m1 m2 :
    stamps_auth γ m -∗ stamps_frag γ m1 -∗ stamps_frag γ m2 -∗ ⌜m1 ⋅ m2 ≼ m⌝.
  Proof.
    iIntros "Ha H1 H2". iDestruct (own_valid_3 with "Ha H1 H2") as %Hv.
    rewrite -assoc -auth_frag_op in Hv. apply auth_both_valid_discrete in Hv as [Hincl _].
    by iPureIntro.
  Qed.
  (* a whole fragment leaves the auth: the mass is subtracted, no key is
     added, and every key not in the fragment survives *)
  Lemma stamps_dealloc γ m mD :
    stamps_auth γ m -∗ stamps_frag γ mD ==∗
    ∃ m', stamps_auth γ m' ∗ ⌜(qsum mD + qsum m')%Qc = qsum m⌝ ∗ ⌜dom m' ⊆ dom m⌝ ∗
          ⌜∀ p, p ∈ dom m → p ∉ dom mD → p ∈ dom m'⌝.
  Proof.
    iIntros "Ha Hf".
    iInduction mD as [|p d mD Hp] "IH" using map_ind forall (m).
    { iModIntro. iExists m. iFrame "Ha". iPureIntro. split_and!; [by rewrite qsum_empty Qcplus_0_l | done | done]. }
    iEval (rewrite (insert_singleton_op mD p d Hp) /stamps_frag auth_frag_op own_op) in "Hf".
    iDestruct "Hf" as "[Hf1 Hf2]".
    iDestruct (stamps_frag_incl with "Ha Hf1") as %Hincl.
    iMod (own_update_2 _ _ _ _ (msub_key_upd m p d Hincl) with "Ha Hf1") as "Ha".
    iMod ("IH" with "Ha Hf2") as (m') "(Ha & %Hq & %Hdom & %Hkeep)".
    iModIntro. iExists m'. iFrame "Ha". iPureIntro. split_and!.
    - rewrite (qsum_insert _ _ _ Hp) -Qcplus_assoc Hq. exact (qsum_msub_key m p d Hincl).
    - intros i Hi. apply (dom_msub_key_sub m p d). by apply Hdom.
    - intros i Hi Hni. rewrite dom_insert_L in Hni.
      apply Hkeep.
      + destruct (dom_msub_key_cases m p i d Hi) as [Hi' | ->]; [exact Hi'|].
        exfalso. apply Hni. apply elem_of_union_l. by apply elem_of_singleton.
      + intros Hc. apply Hni. by apply elem_of_union_r.
  Qed.

  (* the body, opened with its prefix named (the box's own binders carry a
     b suffix so the caller's r / s / c stay distinct until agreement) *)
  Local Ltac box_open Hbox Hcl :=
    iInv Hbox as (T ξb m cb rb sb)
      "(>Hpk & >#Hllb & >Hst & >Hc & >Hrd & >Hrp & >%Hrows & Harm)" Hcl;
    lazymatch goal with
    | Hr : box_rows _ _ _ _ _ |- _ => destruct Hr as (Hsum & HI & HC & HD)
    end;
    iEval (rewrite /box_arm) in "Harm".

  (* the floor → view bound plumbing of a withdraw *)
  Local Lemma box_floor_view `{CID : CpuId} (ξ : CtxId) (K : nat) :
    own_context ξ -∗ ctx_floor ξ K -∗
    own_context ξ ∗ ∃ K' : nat, ⌜(K ≤ K')%nat⌝ ∗ hart_view_lb K'.
  Proof.
    iIntros "Hrun #Hfl".
    iDestruct (own_context_floor_view with "Hrun Hfl") as "[Hrun (%K' & #HK & %HKK)]".
    iFrame "Hrun". iExists K'. iSplitR; [done|].
    rewrite hart_view_lb_unseal /hart_view_lb_def. iExact "HK".
  Qed.

  (* ---- two full ownerships of one word cell, at any two contexts, clash
     (the clients' P_hdr_excl / P_rest_excl run on it) ------------------ *)
  Lemma ctx_word4_excl_x (ξ1 ξ2 : CtxId) a (dq : dfrac) w1 w2 :
    ctx_word4_pointsto ξ1 a (DfracOwn 1) w1 -∗
    ctx_word4_pointsto ξ2 a dq w2 -∗ False.
  Proof.
    iIntros "H1 H2".
    iDestruct (ctx_word4_pointsto_bytes with "H1") as "H1".
    iDestruct (ctx_word4_pointsto_bytes with "H2") as "H2".
    iEval (cbn [seq]; rewrite big_sepL_cons) in "H1". iDestruct "H1" as "[H1 _]".
    iEval (cbn [seq]; rewrite big_sepL_cons) in "H2". iDestruct "H2" as "[H2 _]".
    iDestruct (ctx_pointsto_ne with "H1 H2") as %Hne. exfalso. by apply Hne.
  Qed.

  (* ---- shares: a reference splits by mass and joins (M-5) ------------ *)
  Lemma reference_split γ (i : id) m (s s' : Qp) :
    (s + s')%Qp = 1%Qp ->
    reference γ i m -∗ reference γ i (mscale s m) ∗ reference γ i (mscale s' m).
  Proof.
    iIntros (Hss) "(%Hne & %Hk & Hf & #Hllb)".
    iAssert (stamps_frag γ (mscale s m) ∗ stamps_frag γ (mscale s' m))%I with "[Hf]" as "[Hf1 Hf2]".
    { rewrite /stamps_frag -own_op -auth_frag_op -(mscale_split s s' m Hss). iExact "Hf". }
    iSplitL "Hf1".
    - iFrame "Hf1". rewrite max_stamp_mscale. iFrame "Hllb". iPureIntro. split.
      + intros Hc. apply Hne. by apply (mscale_empty_iff s).
      + intros p Hp. rewrite dom_mscale in Hp. by apply Hk.
    - iFrame "Hf2". rewrite max_stamp_mscale. iFrame "Hllb". iPureIntro. split.
      + intros Hc. apply Hne. by apply (mscale_empty_iff s').
      + intros p Hp. rewrite dom_mscale in Hp. by apply Hk.
  Qed.
  Lemma reference_llb γ (i : id) m : reference γ i m -∗ llb loglen_name (max_stamp m).
  Proof. iIntros "(_ & _ & _ & #H)". iExact "H". Qed.

  Lemma reference_join γ (i : id) (m1 m2 : gmap (id * nat) ufrac) :
    reference γ i m1 -∗ reference γ i m2 -∗ reference γ i (m1 ⋅ m2).
  Proof.
    iIntros "(%Hne1 & %Hk1 & Hf1 & #Hl1) (%Hne2 & %Hk2 & Hf2 & #Hl2)".
    rewrite /reference /stamps_frag auth_frag_op own_op. iFrame "Hf1 Hf2".
    iSplitR; [iPureIntro; by apply op_ne_empty_l|].
    iSplitR; [iPureIntro; by apply keyed_op|].
    rewrite max_stamp_op. iApply (llb_max with "Hl1 Hl2").
  Qed.

  (* ---- the two payload rows the locks carry (client-facing) --------- *)
  (* L1's payload row, at rest: the register half with the window shut,
     the floor row at td, and its llb.  The client adds ⌜sr_ident r = its
     identity cells' values⌝ beside it (bcache: (devs k, bnos k)). *)
  Definition l1_row γ (r : slot_reg id X) (ξ : CtxId) : iProp Σ :=
    (slotd_half γ r ∗ ⌜sr_win r = false⌝ ∗ ⌜sr_x r = None⌝ ∗
     ctx_floor ξ (sr_td r) ∗ llb loglen_name (sr_td r))%I.

  (* L2's payload row, at rest: the token, the register half with nothing
     held, and the floor row at tp *)
  Definition l2_row γ (s : l2_reg id) (ξ : CtxId) : iProp Σ :=
    (slotp_half γ s ∗ ⌜lr_hold s = None⌝ ∗ ctx_floor ξ (lr_tp s))%I.

  (* what the L2 HOLDER carries across the checkout (behind the frozen
     handle's token row, F7): the register half naming the parked fragment,
     and the llb of that fragment's stamps *)
  Definition l2_hold γ (i : id) m : iProp Σ :=
    (∃ tp, slotp_half γ (L2Reg tp (Some (i, m))) ∗ llb loglen_name (max_stamp m))%I.

  (* ================================================================== *)
  (*  (a) withdraw_L1 : IN → OUT_L1, under L1                            *)
  (* ================================================================== *)
  (* Caller holds: L1's register half (window shut), the cnt half at c,
     ALL c units as one fragment (∅ at c = 0), and floors covering L1's row
     (Kd ≥ td) and the fragment's stamps (Kt ≥ max_stamp mD, from R1).
     Proof skeleton:
       open; agree slot_d ⇒ win = false ⇒ in_arm ∨ out_l2.
       out_l2: its fragment m0 ≠ ∅ composes with mD: qsum m ≥ qsum mD +
               qsum m0 > nat_Qc c = qsum m.  Contradiction.
       in_arm: (D) with m = mD (mD ≼ m, equal sums ⇒ equal maps):
               T ≤ td ≤ Kd  or  T ∈ snd dom mD ⇒ T ≤ Kt.
               own_context_floor_view at max Kd Kt ⇒ hart_view_lb K ≥ T;
               ctx_absorb_lb pulls P_hdr ident x to ξ; P_rest stays.
       close: win := true, sr_x := Some x0 (the arm's x, F10 -- both
              halves in hand); hdr_out := ◯ mD; P_rest stays at x0;
              rows (Σ),(I),(C),(D) unchanged (m, T, r.td, r.ident, s unchanged). *)
  Lemma box_withdraw_L1 `{CID : CpuId} (N : namespace) γ (ξ : CtxId) (r : slot_reg id X)
      (c : nat) (mD : gmap (id * nat) ufrac) (Kd Kt : nat) (E : coPset) :
    ↑N ⊆ E →
    sr_win r = false →
    qsum mD = nat_Qc c →
    (sr_td r ≤ Kd)%nat →
    (max_stamp mD ≤ Kt)%nat →
    is_box N γ -∗
    own_context ξ -∗
    ctx_floor ξ Kd -∗
    ctx_floor ξ Kt -∗
    llb loglen_name (max_stamp mD) -∗
    slotd_half γ r -∗
    cnt_half γ c -∗
    stamps_frag γ mD -∗
    Q1 c ={E}=∗
    own_context ξ ∗
    cnt_half γ c ∗
    ∃ (x0 : X) (T0 : nat),
      ⌜(T0 ≤ Nat.max Kd Kt)%nat⌝ ∗
      slotd_half γ (SlotReg (sr_td r) true (sr_ident r) (Some (x0, T0))) ∗
      P_hdr (sr_ident r) x0 ξ.
  Proof.
    iIntros (HE Hw HmD HKd HKt) "#Hbox Hrun #Hfld #Hflt #HllbD Hrd0 Hcnt HfD HQ".
    rewrite /is_box. box_open "Hbox" "Hcl".
    iDestruct (ghost_var_agree with "Hrd Hrd0") as %->.
    iDestruct (ghost_var_agree with "Hc Hcnt") as %->.
    iDestruct (stamps_frag_incl with "Hst HfD") as %HinclD.
    destruct (lr_hold sb) as [[i0 m0]|] eqn:Hh.
    { (* OUT_L2: the parked fragment's mass beside all c units overflows Σ *)
      iDestruct "Harm" as "(_ & >%Hne0 & _ & >Hf0 & _)".
      iDestruct (stamps_frag_incl_2 with "Hst HfD Hf0") as %Hincl2.
      exfalso. apply qsum_incl_le in Hincl2. rewrite qsum_op HmD Hsum in Hincl2.
      exact (Qc_plus_pos_not_le_r _ _ (qsum_pos _ Hne0) Hincl2). }
    iEval (rewrite Hw) in "Harm". iDestruct "Harm" as ">Hin".
    (* the cover: (D) -- and its pure export, the window's stamp bound (F30) *)
    assert (HTmax : (T ≤ Nat.max Kd Kt)%nat).
    { destruct HD as [HD | (p & Hp & HpT)]; [lia|].
      assert (Hp' : p ∈ dom mD).
      { apply (qsum_eq_dom mD m HinclD); [by rewrite HmD Hsum | exact Hp]. }
      pose proof (max_stamp_ge mD p Hp'). lia. }
    iAssert (own_context ξ ∗ ∃ K : nat, ⌜(T ≤ K)%nat⌝ ∗ hart_view_lb K)%I
      with "[Hrun]" as "[Hrun (%K & %HTK & #HKv)]".
    { destruct HD as [HD | (p & Hp & HpT)].
      - iDestruct (box_floor_view ξ Kd with "Hrun Hfld") as "[Hrun (%K & %HKK & #HKv)]".
        iFrame "Hrun". iExists K. iFrame "HKv". iPureIntro. lia.
      - assert (Hp' : p ∈ dom mD).
        { apply (qsum_eq_dom mD m HinclD); [by rewrite HmD Hsum | exact Hp]. }
        pose proof (max_stamp_ge mD p Hp').
        iDestruct (box_floor_view ξ Kt with "Hrun Hflt") as "[Hrun (%K & %HKK & #HKv)]".
        iFrame "Hrun". iExists K. iFrame "HKv". iPureIntro. lia. }
    iDestruct "Hin" as (x0) "[Hhdr Hrest]".
    iMod (ctx_absorb_lb (P_hdr (sr_ident r) x0) ξb ξ T K HTK with "Hrun HKv Hpk Hhdr")
      as "(Hrun & Hpk & Hhdr)".
    iMod (ghost_var_update_2 (SlotReg (sr_td r) true (sr_ident r) (Some (x0, T))) with "Hrd Hrd0")
      as "[Hrd Hrd0]"; [by rewrite Qp.half_half|].
    iMod ("Hcl" with "[Hpk Hst Hc Hrd Hrp HfD Hrest HQ]") as "_".
    { iNext. iExists T, ξb, m, c, (SlotReg (sr_td r) true (sr_ident r) (Some (x0, T))), sb.
      iFrame "Hpk Hllb Hst Hc Hrd Hrp". simpl.
      iSplitR; [iPureIntro; exact (conj Hsum (conj HI (conj HC HD)))|].
      rewrite /box_arm.
      rewrite Hh. simpl.
      iSplitL "HfD".
      { iExists mD. iSplitR; [iPureIntro; by rewrite HmD Hsum|]. iFrame "HfD". iExact "HllbD". }
      iSplitL "Hrest"; [iExists x0; iFrame "Hrest"; done | iExact "HQ"]. }
    iModIntro. iFrame "Hrun Hcnt". iExists x0, T. iFrame "Hrd0 Hhdr". iPureIntro. exact HTmax.
  Qed.



  (* ================================================================== *)
  (*  (b') deposit_L1 WITH A SHAPE CHANGE (F14, generic)                   *)
  (* ================================================================== *)
  (* The header comes back at a TARGET shape x1; the arm's P_rest at the
     register's x0 converts to x1 by a client entailment.  bcache: x1 = x0
     (reflexivity).  icache: Raw ↔ Unloaded share one P_rest term (the
     recycle), Loaded → Raw is a weakening (the eviction).  [box_deposit_L1]
     above is the x1 := x0 instance: prove this statement and derive that
     one from it (F10's "same x" was too strong).  Same case skeleton as
     (b); the only new step is the entailment applied to the arm's P_rest
     before the close. *)
  Lemma box_deposit_L1_shape `{CID : CpuId} (N : namespace) γ (ξ : CtxId) (r : slot_reg id X)
      (c : nat) (i' : id) (x0 x1 : X) (T0 : nat) (E : coPset) :
    ↑N ⊆ E →
    sr_win r = true →
    sr_x r = Some (x0, T0) →
    (∀ ξb : CtxId, P_rest x0 ξb ⊢ P_rest x1 ξb) →
    is_box N γ -∗
    own_context ξ -∗
    slotd_half γ r -∗
    cnt_half γ c -∗
    P_hdr i' x1 ξ ={E}=∗
    own_context ξ ∗ Q1 c ∗
    ∃ T' : nat,
      slotd_half γ (SlotReg T' false i' None) ∗
      cnt_half γ (Nat.max 1 c) ∗
      reference γ i' {[ (i', T') := unit_mass c ]} ∗
      llb loglen_name T'.
  Proof.
    iIntros (HE Hw Hx Hent) "#Hbox Hrun Hrd0 Hcnt Hhdr".
    rewrite /is_box. box_open "Hbox" "Hcl".
    iDestruct (ghost_var_agree with "Hrd Hrd0") as %->.
    iDestruct (ghost_var_agree with "Hc Hcnt") as %->.
    destruct (lr_hold sb) as [[i0 m0]|] eqn:Hh.
    { (* OUT_L2 records win = false; the caller's half says true *)
      iDestruct "Harm" as "(>%Hwf & _)". congruence. }
    iEval (rewrite Hw) in "Harm".
    iDestruct "Harm" as "(>Hho & >Hrest & >HQ)". iDestruct "Hrest" as (x) "[%Hx' Hrest]".
    assert (x = x0) as -> by congruence.
    (* F14: the arm's rest converts to the target shape *)
    iDestruct (Hent ξb with "Hrest") as "Hrest".
    iDestruct "Hho" as (m') "(%Hsum' & Hf' & _)".
    iMod (stamps_dealloc with "Hst Hf'") as (m1) "(Hst & %Hq1 & _ & _)".
    assert (m1 = ∅) as ->.
    { apply qsum_zero_empty. rewrite Hsum' in Hq1.
      apply (Qc_plus_cancel_l (qsum m)). by rewrite Hq1 Qcplus_0_r. }
    iMod (ctx_deposit (P_hdr i' x1) ξ ξb T with "Hrun Hpk Hhdr")
      as "(Hrun & %T' & %HTT' & Hpk & Hhdr)".
    iDestruct (ctx_parked_llb with "Hpk") as "[Hpk #Hllb']".
    iMod (own_update _ _ _ (stamps_alloc_upd ∅ (i', T') (unit_mass c)) with "Hst") as "[Hst Hfr]".
    iEval (rewrite right_id) in "Hst".
    iMod (ghost_var_update_2 (SlotReg T' false i' None) with "Hrd Hrd0")
      as "[Hrd Hrd0]"; [by rewrite Qp.half_half|].
    iMod (ghost_var_update_2 (Nat.max 1 c) with "Hc Hcnt") as "[Hc Hcnt]"; [by rewrite Qp.half_half|].
    iMod ("Hcl" with "[Hpk Hst Hc Hrd Hrp Hhdr Hrest]") as "_".
    { iNext. iExists T', ξb, {[(i', T') := unit_mass c]}, (Nat.max 1 c), (SlotReg T' false i' None), sb.
      iFrame "Hpk Hllb' Hst Hc Hrd Hrp". simpl.
      iSplitR.
      { iPureIntro. split_and!.
        - rewrite -insert_empty (qsum_insert ∅ _ _ (lookup_empty _)) qsum_empty Qcplus_0_r.
          apply unit_mass_Qc.
        - apply keyed_singleton.
        - left. intros p Hp. rewrite dom_singleton_L in Hp.
          apply elem_of_singleton in Hp. subst p. simpl. lia.
        - left. cbn [sr_td]. lia. }
      rewrite /box_arm Hh. simpl. iExists x1. iFrame "Hhdr Hrest". }
    iModIntro. iFrame "Hrun HQ". iExists T'. iFrame "Hrd0 Hcnt".
    iSplitL "Hfr"; [| iExact "Hllb'"].
    rewrite /reference. iFrame "Hfr".
    iSplitR; [iPureIntro; apply singleton_ne_empty_map|].
    iSplitR; [iPureIntro; apply keyed_singleton|].
    rewrite max_stamp_singleton. iExact "Hllb'".
  Qed.

  (* (b): the instance x1 := x0 (the reflexive entailment) *)
  Lemma box_deposit_L1 `{CID : CpuId} (N : namespace) γ (ξ : CtxId) (r : slot_reg id X)
      (c : nat) (i' : id) (x0 : X) (T0 : nat) (E : coPset) :
    ↑N ⊆ E →
    sr_win r = true →
    sr_x r = Some (x0, T0) →
    is_box N γ -∗
    own_context ξ -∗
    slotd_half γ r -∗
    cnt_half γ c -∗
    P_hdr i' x0 ξ ={E}=∗
    own_context ξ ∗ Q1 c ∗
    ∃ T' : nat,
      slotd_half γ (SlotReg T' false i' None) ∗
      cnt_half γ (Nat.max 1 c) ∗
      reference γ i' {[ (i', T') := unit_mass c ]} ∗
      llb loglen_name T'.
  Proof.
    intros HE Hw Hx.
    apply (box_deposit_L1_shape N γ ξ r c i' x0 x0 T0 E HE Hw Hx).
    intros ξb. reflexivity.
  Qed.

  (* ================================================================== *)
  (*  (c) ref_incr, under L1 (legal at c = 0: bget's hit on a cached      *)
  (*      refcnt-0 buffer takes this path, not the recycler's)            *)
  (* ================================================================== *)
  (* Caller holds: L1's register half (window shut) and the cnt half.  It
     learns the identity from the register (its own row ties sr_ident to
     its identity cells) -- never from the bundle, which may be OUT_L2.
     Proof skeleton:
       open; agree slot_d ⇒ win = false; the arm is untouched.
       stamps: alloc {[(ident, T) := 1]} on ● m; cnt := S c.
       rows: (Σ) +1, (I) new key at ident, (C) T ≤ T keeps the left
       disjunct if it held (the right is untouched), (D) untouched.
       export llb T (the box's own). *)
  Lemma box_ref_incr (N : namespace) γ (r : slot_reg id X) (c : nat) (E : coPset) :
    ↑N ⊆ E →
    sr_win r = false →
    is_box N γ -∗
    slotd_half γ r -∗
    cnt_half γ c ={E}=∗
    slotd_half γ r ∗
    cnt_half γ (S c) ∗
    ∃ T : nat, reference γ (sr_ident r) {[ (sr_ident r, T) := 1%Qp ]}.
  Proof.
    iIntros (HE Hw) "#Hbox Hrd0 Hcnt".
    rewrite /is_box. box_open "Hbox" "Hcl".
    iDestruct (ghost_var_agree with "Hrd Hrd0") as %->.
    iDestruct (ghost_var_agree with "Hc Hcnt") as %->.
    iMod (own_update _ _ _ (stamps_alloc_upd m (sr_ident r, T) 1%Qp) with "Hst") as "[Hst Hfr]".
    iMod (ghost_var_update_2 (S c) with "Hc Hcnt") as "[Hc Hcnt]"; [by rewrite Qp.half_half|].
    iMod ("Hcl" with "[Hpk Hst Hc Hrd Hrp Harm]") as "_".
    { iNext. iExists T, ξb, ({[(sr_ident r, T) := 1%Qp]} ⋅ m), (S c), r, sb.
      iFrame "Hpk Hllb Hst Hc Hrd Hrp".
      iSplitR.
      { iPureIntro. split_and!.
        - rewrite qsum_singleton_op Hsum Qp_to_Qc_1 nat_Qc_S. done.
        - by apply keyed_singleton_op.
        - destruct HC as [HC | HC]; [left | by right].
          intros p Hp. rewrite dom_op dom_singleton_L in Hp.
          apply elem_of_union in Hp as [Hp | Hp]; [apply elem_of_singleton in Hp; subst p; simpl; lia | by apply HC].
        - right. exists (sr_ident r, T). split; [| done].
          rewrite dom_op dom_singleton_L. apply elem_of_union_l. by apply elem_of_singleton. }
      (* the arm mentions m only inside the shut window *)
      iEval (rewrite Hw) in "Harm". rewrite /box_arm Hw. iExact "Harm". }
    iModIntro. iFrame "Hrd0 Hcnt". iExists T. rewrite /reference. iFrame "Hfr".
    iSplitR; [iPureIntro; apply singleton_ne_empty_map|].
    iSplitR; [iPureIntro; apply keyed_singleton|].
    rewrite max_stamp_singleton. iExact "Hllb".
  Qed.

  (* ================================================================== *)
  (*  (d) ref_decr, under L1 (refs 1 → 0 is THIS, not a withdraw)         *)
  (* ================================================================== *)
  (* Caller holds: L1's register half (window shut), the cnt half at S c,
     ONE UNIT (qsum = 1) as a reference, and L1's row's `llb td` (F11:
     the conclusion's llb of the max needs both llbs).  It pays the
     unit's debt: td := max td (max_stamp mD); the release folds the new
     td by R2.
     Proof skeleton:
       open; agree slot_d ⇒ win = false; the arm is untouched.
       stamps: dealloc mD (mD ≼ m by validity; ufrac cancels).
       cnt := c; slot_d.td := max td (max_stamp mD) (both halves).
       rows: (Σ) −1, (I) monotone under removal, (C) monotone under
       removal (left) / untouched (right), (D): a removed witness p.2 = T
       has T ≤ max_stamp mD ≤ td'. *)
  Lemma box_ref_decr (N : namespace) γ (r : slot_reg id X) (c : nat) (i : id)
      (mD : gmap (id * nat) ufrac) (E : coPset) :
    ↑N ⊆ E →
    sr_win r = false →
    qsum mD = nat_Qc 1 →
    is_box N γ -∗
    slotd_half γ r -∗
    llb loglen_name (sr_td r) -∗
    cnt_half γ (S c) -∗
    reference γ i mD ={E}=∗
    slotd_half γ (SlotReg (Nat.max (sr_td r) (max_stamp mD)) false (sr_ident r) (sr_x r)) ∗
    cnt_half γ c ∗
    llb loglen_name (Nat.max (sr_td r) (max_stamp mD)).
  Proof.
    iIntros (HE Hw HmD) "#Hbox Hrd0 #Hllbtd Hcnt Href".
    iDestruct "Href" as "(%Hne & %Hkeyed & HfD & #HllbD)".
    rewrite /is_box. box_open "Hbox" "Hcl".
    iDestruct (ghost_var_agree with "Hrd Hrd0") as %->.
    iDestruct (ghost_var_agree with "Hc Hcnt") as %->.
    (* the arm names the register only through win / ident / x, which the
       re-stamp keeps *)
    iEval (rewrite Hw) in "Harm".
    iMod (stamps_dealloc with "Hst HfD") as (m1) "(Hst & %Hq1 & %Hdom1 & %Hkeep)".
    iMod (ghost_var_update_2 c with "Hc Hcnt") as "[Hc Hcnt]"; [by rewrite Qp.half_half|].
    iMod (ghost_var_update_2 (SlotReg (Nat.max (sr_td r) (max_stamp mD)) false (sr_ident r) (sr_x r))
            with "Hrd Hrd0") as "[Hrd Hrd0]"; [by rewrite Qp.half_half|].
    iMod ("Hcl" with "[Hpk Hst Hc Hrd Hrp Harm]") as "_".
    { iNext. iExists T, ξb, m1, c, (SlotReg (Nat.max (sr_td r) (max_stamp mD)) false (sr_ident r) (sr_x r)), sb.
      iFrame "Hpk Hllb Hst Hc Hrd Hrp". simpl.
      iSplitR.
      { iPureIntro. split_and!.
        - apply (Qc_plus_cancel_l 1%Qc). rewrite -{1}nat_Qc_1 -HmD Hq1 Hsum nat_Qc_S. done.
        - exact (keyed_sub _ _ _ Hdom1 HI).
        - destruct HC as [HC | HC]; [left | by right].
          intros p Hp. apply HC. by apply Hdom1.
        - cbn [sr_td]. destruct HD as [HD | (p & Hp & HpT)]; [left; lia|].
          destruct (decide (p ∈ dom mD)) as [HpD | HpD].
          + left. pose proof (max_stamp_ge mD p HpD). lia.
          + right. exists p. split; [by apply Hkeep | exact HpT]. }
      rewrite /box_arm. simpl. iExact "Harm". }
    iModIntro. iFrame "Hrd0 Hcnt". iApply (llb_max with "Hllbtd HllbD").
  Qed.

  (* ================================================================== *)
  (*  (e) checkout : IN → OUT_L2, under L2                                *)
  (* ================================================================== *)
  (* Caller holds: its reference (mass q > 0, keyed at i, stamps ≤ Kt by
     R1 at the acquire), the L2 payload row's pieces (tok, the register
     half with nothing held, its floor Kp ≥ tp), floors, and the client's
     residue Q (F12: the OUT_L2 arm is closed with it).
     Proof skeleton:
       open; the flag is NOT known (no slot_d in hand): destruct sr_win.
       win = true : hdr_out's ◯ m' (qsum m' = qsum m) composes with the
                    caller's ◯ mh (qsum > 0) ⇒ qsum m > qsum m.  Contradiction.
       win = false, out_l2 : tok vs the arm's tok (tok_excl).
       win = false, in_arm : agree slot_p ⇒ tp = lr_tp s0.
                    (I): mh's keys ∈ dom m ⇒ i = sr_ident r.
                    (C): T ≤ every key's stamp ≤ Kt, or T ≤ tp ≤ Kp.
                    own_context_floor_view at max Kt Kp; ctx_absorb_lb pulls
                    ∃ x, P_hdr i x ∗ P_rest x to ξ (ONE binder, F8).
       close out_l2 with Q, tok, the caller's WHOLE fragment parked with
       its ⌜keyed mh i⌝ (F13, from the reference), and slot_p := {| tp;
       Some (i, mh) |} (both halves in hand); the caller keeps the
       register half for its handle (l2_hold).
       rows unchanged (m, T, r untouched; s.tp untouched). *)
  Lemma box_checkout_split `{CID : CpuId} (N : namespace) γ (ξ : CtxId) (i : id)
      (P_hdr' : id → X → CtxId → iProp Σ) `{!∀ i x, CtxMorph (P_hdr' i x)}
      (Qc : iProp Σ)
      (mh : gmap (id * nat) ufrac) (s0 : l2_reg id) (Kt Kp : nat) (E : coPset) :
    ↑N ⊆ E →
    lr_hold s0 = None →
    (max_stamp mh ≤ Kt)%nat →
    (lr_tp s0 ≤ Kp)%nat →
    (* F33: the residue is built from the CALLER's Qc beside the header --
       the icache's Q is the descriptor half the caller mints ∗ the share in
       its hand ∗ the 3/4 leg from the header; only the leg comes out of
       P_hdr.  (e) is the instance Qc := Q, P_hdr' := P_hdr. *)
    (∀ (x : X) (ξ' : CtxId), Qc ∗ P_hdr i x ξ' ⊢ P_hdr' i x ξ' ∗ Q2) →
    is_box N γ -∗
    own_context ξ -∗
    ctx_floor ξ Kt -∗
    ctx_floor ξ Kp -∗
    reference γ i mh -∗
    Qc -∗
    slotp_half γ s0 ={E}=∗
    own_context ξ ∗
    (∃ x, P_hdr' i x ξ ∗ P_rest x ξ) ∗
    l2_hold γ i mh.
  Proof.
    iIntros (HE Hs0 HKt HKp Hsplit) "#Hbox Hrun #Hflt #Hflp Href HQc Hrp0".
    iDestruct "Href" as "(%Hne & %Hkeyed & Hfh & #Hllbh)".
    rewrite /is_box. box_open "Hbox" "Hcl".
    iDestruct (ghost_var_agree with "Hrp Hrp0") as %->.
    iDestruct (stamps_frag_incl with "Hst Hfh") as %Hinclh.
    iEval (rewrite Hs0 /=) in "Harm".
    destruct (sr_win rb) eqn:Hw.
    { (* OUT_L1: the window's fragment carries all of Σ; mine overflows it *)
      iDestruct "Harm" as "(>Hho & _ & _)". iDestruct "Hho" as (m') "(%Hsum' & Hf' & _)".
      iDestruct (stamps_frag_incl_2 with "Hst Hf' Hfh") as %Hincl2.
      exfalso. apply qsum_incl_le in Hincl2. rewrite qsum_op Hsum' in Hincl2.
      exact (Qc_plus_pos_not_le_r _ _ (qsum_pos _ Hne) Hincl2). }
    iDestruct "Harm" as ">Hin".
    (* the identity (F6): my keys are live, so they name the box's identity *)
    assert (Hid : i = sr_ident rb).
    { eapply keyed_agree; [exact Hne | exact (gincl_dom _ _ Hinclh) | exact Hkeyed | exact HI]. }
    (* the cover: (C) *)
    iAssert (own_context ξ ∗ ∃ K : nat, ⌜(T ≤ K)%nat⌝ ∗ hart_view_lb K)%I
      with "[Hrun]" as "[Hrun (%K & %HTK & #HKv)]".
    { destruct HC as [HC | HC].
      - destruct (map_choose mh Hne) as (p & q & Hp).
        assert (Hpd : p ∈ dom mh) by (apply elem_of_dom; by exists q).
        pose proof (HC p (gincl_dom _ _ Hinclh p Hpd)). pose proof (max_stamp_ge mh p Hpd).
        iDestruct (box_floor_view ξ Kt with "Hrun Hflt") as "[Hrun (%K & %HKK & #HKv)]".
        iFrame "Hrun". iExists K. iFrame "HKv". iPureIntro. lia.
      - iDestruct (box_floor_view ξ Kp with "Hrun Hflp") as "[Hrun (%K & %HKK & #HKv)]".
        iFrame "Hrun". iExists K. iFrame "HKv". iPureIntro. lia. }
    (* the split, at the box's context: the residue stays, the rest is absorbed *)
    iEval (rewrite -Hid /in_arm) in "Hin". iDestruct "Hin" as (x) "[Hhdr Hrest]".
    iDestruct (Hsplit x ξb with "[$HQc $Hhdr]") as "[Hhdr' HQ]".
    iMod (ctx_absorb_lb (in_arm_of P_hdr' i) ξb ξ T K HTK with "Hrun HKv Hpk [Hhdr' Hrest]")
      as "(Hrun & Hpk & Hin')".
    { rewrite /in_arm_of. iExists x. iFrame "Hhdr' Hrest". }
    iMod (ghost_var_update_2 (L2Reg (lr_tp s0) (Some (i, mh))) with "Hrp Hrp0")
      as "[Hrp Hrp0]"; [by rewrite Qp.half_half|].
    iMod ("Hcl" with "[Hpk Hst Hc Hrd Hrp HQ Hfh]") as "_".
    { iNext. iExists T, ξb, m, cb, rb, (L2Reg (lr_tp s0) (Some (i, mh))).
      iFrame "Hpk Hllb Hst Hc Hrd Hrp". simpl.
      iSplitR; [iPureIntro; exact (conj Hsum (conj HI (conj HC HD)))|].
      rewrite /box_arm.
      iFrame "Hfh HQ". iPureIntro. split_and!; done. }
    iModIntro. iFrame "Hrun". iSplitL "Hin'". { rewrite /in_arm_of. iExact "Hin'". }
    rewrite /l2_hold. iExists (lr_tp s0). iFrame "Hrp0". iExact "Hllbh".
  Qed.

  (* (e): the instance -- the caller's Q passes straight into the arm.  The
     split wand of (e′) is a pure entailment, so the caller's own Q cannot
     ride it; (e) is proven directly, the same case skeleton. *)
  Lemma box_checkout `{CID : CpuId} (N : namespace) γ (ξ : CtxId) (i : id)
      (mh : gmap (id * nat) ufrac) (s0 : l2_reg id) (Kt Kp : nat) (E : coPset) :
    ↑N ⊆ E →
    lr_hold s0 = None →
    (max_stamp mh ≤ Kt)%nat →
    (lr_tp s0 ≤ Kp)%nat →
    is_box N γ -∗
    own_context ξ -∗
    ctx_floor ξ Kt -∗
    ctx_floor ξ Kp -∗
    reference γ i mh -∗
    Q2 -∗
    slotp_half γ s0 ={E}=∗
    own_context ξ ∗
    (∃ x, P_hdr i x ξ ∗ P_rest x ξ) ∗
    l2_hold γ i mh.
  Proof.
    iIntros (HE Hs0 HKt HKp) "#Hbox Hrun #Hflt #Hflp Href HQ Hrp0".
    iDestruct "Href" as "(%Hne & %Hkeyed & Hfh & #Hllbh)".
    rewrite /is_box. box_open "Hbox" "Hcl".
    iDestruct (ghost_var_agree with "Hrp Hrp0") as %->.
    iDestruct (stamps_frag_incl with "Hst Hfh") as %Hinclh.
    iEval (rewrite Hs0 /=) in "Harm".
    destruct (sr_win rb) eqn:Hw.
    { iDestruct "Harm" as "(>Hho & _ & _)". iDestruct "Hho" as (m') "(%Hsum' & Hf' & _)".
      iDestruct (stamps_frag_incl_2 with "Hst Hf' Hfh") as %Hincl2.
      exfalso. apply qsum_incl_le in Hincl2. rewrite qsum_op Hsum' in Hincl2.
      exact (Qc_plus_pos_not_le_r _ _ (qsum_pos _ Hne) Hincl2). }
    iDestruct "Harm" as ">Hin".
    assert (Hid : i = sr_ident rb).
    { eapply keyed_agree; [exact Hne | exact (gincl_dom _ _ Hinclh) | exact Hkeyed | exact HI]. }
    iAssert (own_context ξ ∗ ∃ K : nat, ⌜(T ≤ K)%nat⌝ ∗ hart_view_lb K)%I
      with "[Hrun]" as "[Hrun (%K & %HTK & #HKv)]".
    { destruct HC as [HC | HC].
      - destruct (map_choose mh Hne) as (p & q & Hp).
        assert (Hpd : p ∈ dom mh) by (apply elem_of_dom; by exists q).
        pose proof (HC p (gincl_dom _ _ Hinclh p Hpd)). pose proof (max_stamp_ge mh p Hpd).
        iDestruct (box_floor_view ξ Kt with "Hrun Hflt") as "[Hrun (%K & %HKK & #HKv)]".
        iFrame "Hrun". iExists K. iFrame "HKv". iPureIntro. lia.
      - iDestruct (box_floor_view ξ Kp with "Hrun Hflp") as "[Hrun (%K & %HKK & #HKv)]".
        iFrame "Hrun". iExists K. iFrame "HKv". iPureIntro. lia. }
    iMod (ctx_absorb_lb (in_arm (sr_ident rb)) ξb ξ T K HTK with "Hrun HKv Hpk Hin")
      as "(Hrun & Hpk & Hin)".
    iMod (ghost_var_update_2 (L2Reg (lr_tp s0) (Some (i, mh))) with "Hrp Hrp0")
      as "[Hrp Hrp0]"; [by rewrite Qp.half_half|].
    iMod ("Hcl" with "[Hpk Hst Hc Hrd Hrp HQ Hfh]") as "_".
    { iNext. iExists T, ξb, m, cb, rb, (L2Reg (lr_tp s0) (Some (i, mh))).
      iFrame "Hpk Hllb Hst Hc Hrd Hrp". simpl.
      iSplitR; [iPureIntro; exact (conj Hsum (conj HI (conj HC HD)))|].
      rewrite /box_arm.
      iFrame "Hfh HQ". iPureIntro. split_and!; done. }
    iModIntro. iFrame "Hrun". iSplitL "Hin". { rewrite Hid. iExact "Hin". }
    rewrite /l2_hold. iExists (lr_tp s0). iFrame "Hrp0". iExact "Hllbh".
  Qed.

  (* ================================================================== *)
  (*  (f) park : OUT_L2 → IN, under L2 (before releasesleep)              *)
  (* ================================================================== *)
  (* Caller holds: the bundle at identity i (the handle's cells), and the
     handle's ghost row l2_hold naming the parked fragment (i, mh).  The
     identity witness is the REGISTER, agreed against the box, and the
     parked fragment's keys are then tied to sr_ident by (I) -- F7's gap
     closed without a spec parameter.
     Proof skeleton:
       open; destruct sr_win.
       win = true : the arm's P_rest x ξb vs the caller's P_rest x' ξ
                    (P_rest_excl).
       win = false, in_arm : the arm's P_hdr vs the caller's (P_hdr_excl).
       win = false, out_l2 : agree slot_p ⇒ the arm's fragment IS (i, mh);
                    take Q, tok, ◯ mh, ⌜keyed mh i⌝.  (I) on mh's keys
                    (◯ mh ≼ ● m, mh ≠ ∅) + keyed mh i ⇒ i = sr_ident r
                    (F13); rewrite the deposit to in_arm (sr_ident r).
                    ctx_deposit (∃ x, P_hdr i x ∗ P_rest x) at ξb ⇒ T'.
                    stamps: dealloc mh, alloc {[(i, T') := mass mh]} --
                    the caller's mass, known from the register.
                    slot_p := {| T'; None |} (both halves).
       close in_arm at sr_ident r; rows: (Σ) unchanged (same mass),
       (I) i = sr_ident r, (C) right disjunct T' ≤ tp = T', (D) T' ∈ dom.
       export llb T' for the _in releasesleep. *)
  Lemma box_park_join `{CID : CpuId} (N : namespace) γ (ξ : CtxId) (i : id)
      (P_hdr' : id → X → CtxId → iProp Σ) (Qc' Q' : iProp Σ)
      (mh : gmap (id * nat) ufrac) (E : coPset) :
    ↑N ⊆ E →
    (* F43 (the mirror of F33's Qc): the join sees the CALLER's residue Qc'
       beside the split header and the arm's Q2 -- the icache's descriptor
       half, which is what selects the arm within Q2. *)
    (∀ (x : X) (ξ' : CtxId), Qc' ∗ P_hdr' i x ξ' ∗ Q2 ⊢ P_hdr i x ξ' ∗ Q') →
    is_box N γ -∗
    own_context ξ -∗
    (∃ x, P_hdr' i x ξ ∗ P_rest x ξ) -∗
    Qc' -∗
    l2_hold γ i mh ={E}=∗
    own_context ξ ∗ Q' ∗
    ∃ (T' : nat) (q : ufrac),
      ⌜Qp_to_Qc q = qsum mh⌝ ∗
      slotp_half γ (L2Reg T' None) ∗
      reference γ i {[ (i, T') := q ]} ∗
      llb loglen_name T'.
  Proof.
    iIntros (HE Hjoin) "#Hbox Hrun Hbun HQc Hhold".
    iDestruct "Hhold" as (tp) "[Hrp0 #Hllbh]".
    rewrite /is_box. box_open "Hbox" "Hcl".
    iDestruct (ghost_var_agree with "Hrp Hrp0") as %->.
    (* the register selects OUT_L2: nothing to refute *)
    iEval (cbn [lr_hold]) in "Harm".
    iDestruct "Harm" as "(>%Hwf & >%Hne0 & >%Hkeyed0 & >Hf0 & >HQ)".
    iDestruct (stamps_frag_incl with "Hst Hf0") as %Hincl0.
    (* the identity (F13): the parked keys are live, so they name the box's *)
    assert (Hid : i = sr_ident rb).
    { eapply keyed_agree; [exact Hne0 | exact (gincl_dom _ _ Hincl0) | exact Hkeyed0 | exact HI]. }
    (* the join, at the holder's context, with the arm's residue *)
    iDestruct "Hbun" as (x) "[Hhdr' Hrest]".
    iDestruct (Hjoin x ξ with "[$HQc $Hhdr' $HQ]") as "[Hhdr HQ']".
    iMod (ctx_deposit (in_arm i) ξ ξb T with "Hrun Hpk [Hhdr Hrest]")
      as "(Hrun & %T' & %HTT' & Hpk & Hbun)".
    { rewrite /in_arm. iExists x. iFrame "Hhdr Hrest". }
    iDestruct (ctx_parked_llb with "Hpk") as "[Hpk #Hllb']".
    iMod (stamps_dealloc with "Hst Hf0") as (m1) "(Hst & %Hq1 & %Hdom1 & _)".
    set (q := mk_Qp (qsum mh) (qsum_pos mh Hne0)).
    iMod (own_update _ _ _ (stamps_alloc_upd m1 (i, T') q) with "Hst") as "[Hst Hfr]".
    iMod (ghost_var_update_2 (L2Reg T' None) with "Hrp Hrp0") as "[Hrp Hrp0]"; [by rewrite Qp.half_half|].
    iMod ("Hcl" with "[Hpk Hst Hc Hrd Hrp Hbun]") as "_".
    { iNext. iExists T', ξb, ({[(i, T') := q]} ⋅ m1), cb, rb, (L2Reg T' None).
      iFrame "Hpk Hllb' Hst Hc Hrd Hrp". simpl.
      iSplitR.
      { iPureIntro. split_and!.
        - rewrite qsum_singleton_op. simpl. rewrite Hq1. exact Hsum.
        - rewrite Hid. apply keyed_singleton_op. exact (keyed_sub _ _ _ Hdom1 HI).
        - right. cbn [lr_tp]. lia.
        - right. exists (i, T'). split; [| done].
          rewrite dom_op dom_singleton_L. apply elem_of_union_l. by apply elem_of_singleton. }
      rewrite /box_arm. simpl. rewrite Hwf -Hid. iExact "Hbun". }
    iModIntro. iFrame "Hrun HQ'". iExists T', q. iFrame "Hrp0".
    iSplitR; [iPureIntro; reflexivity|].
    iSplitL "Hfr"; [| iExact "Hllb'"].
    rewrite /reference. iFrame "Hfr".
    iSplitR; [iPureIntro; apply singleton_ne_empty_map|].
    iSplitR; [iPureIntro; apply keyed_singleton|].
    rewrite max_stamp_singleton. iExact "Hllb'".
  Qed.

  (* (f): the instance P_hdr' := P_hdr, Qc' := emp, Q' := Q2 (the arm's Q2 handed back) *)
  Lemma box_park `{CID : CpuId} (N : namespace) γ (ξ : CtxId) (i : id)
      (mh : gmap (id * nat) ufrac) (E : coPset) :
    ↑N ⊆ E →
    is_box N γ -∗
    own_context ξ -∗
    (∃ x, P_hdr i x ξ ∗ P_rest x ξ) -∗
    l2_hold γ i mh ={E}=∗
    own_context ξ ∗ Q2 ∗
    ∃ (T' : nat) (q : ufrac),
      ⌜Qp_to_Qc q = qsum mh⌝ ∗
      slotp_half γ (L2Reg T' None) ∗
      reference γ i {[ (i, T') := q ]} ∗
      llb loglen_name T'.
  Proof.
    intros HE.
    assert (Hjoin : ∀ (x : X) (ξ' : CtxId), emp ∗ P_hdr i x ξ' ∗ Q2 ⊢ P_hdr i x ξ' ∗ Q2).
    { intros x ξ'. by rewrite left_id. }
    iIntros "#Hbox Hrun Hbun Hhold".
    iApply (box_park_join N γ ξ i P_hdr emp Q2 mh E HE Hjoin with "Hbox Hrun Hbun [//] Hhold").
  Qed.

  (* ================================================================== *)
  (*  (g) l1_to_l2 : OUT_L1 → OUT_L2, under BOTH locks (F30)              *)
  (* ================================================================== *)
  (* iput's free path, the unique both-locks site: inside its own (a)
     window (the register says so: win = true, shape x0, opened at the box
     stamp T0 -- (a) exported T0 ≤ max Kd Kt) and holding the sleeplock's
     tok, the caller takes P_rest out WITHOUT re-depositing the header.
     Cover: P_rest is clean at the box stamp T = T0 (the body's tie), under
     any floor K ≥ T0 the caller holds.  The L1 register closes at ITS OWN
     old stamp (no content deposited, nothing minted: rule 0); the window's
     fragment moves from hdr_out to out_l2 as the holder's l2_hold; the
     count stays.  Rows: m, T, td, tp unchanged ⇒ (Σ)(I)(C)(D) untouched.
     Refutation: none (win agreement selects OUT_L1).  Stated at c = 1,
     which is where the free path runs (the guard's (a) at c = 1). *)
  Lemma box_l1_to_l2 `{CID : CpuId} (N : namespace) γ (ξ : CtxId) (r : slot_reg id X)
      (x0 : X) (T0 K : nat) (s0 : l2_reg id) (E : coPset) :
    ↑N ⊆ E →
    sr_win r = true →
    sr_x r = Some (x0, T0) →
    (T0 ≤ K)%nat →
    lr_hold s0 = None →
    is_box N γ -∗
    own_context ξ -∗
    ctx_floor ξ K -∗
    slotd_half γ r -∗
    cnt_half γ 1 -∗
    Q2 -∗
    slotp_half γ s0 ={E}=∗
    own_context ξ ∗ Q1 1 ∗
    P_rest x0 ξ ∗
    slotd_half γ (SlotReg (sr_td r) false (sr_ident r) None) ∗
    cnt_half γ 1 ∗
    ∃ m', ⌜qsum m' = nat_Qc 1⌝ ∗ l2_hold γ (sr_ident r) m'.
  Proof.
    iIntros (HE Hw Hx HTK Hs0) "#Hbox Hrun #Hfl Hrd0 Hcnt HQn Hrp0".
    rewrite /is_box. box_open "Hbox" "Hcl".
    iDestruct (ghost_var_agree with "Hrd Hrd0") as %->.
    iDestruct (ghost_var_agree with "Hc Hcnt") as %->.
    iDestruct (ghost_var_agree with "Hrp Hrp0") as %->.
    iEval (rewrite Hs0 /= Hw) in "Harm".
    iDestruct "Harm" as "(>Hho & >Hrest & >HQo)". iDestruct "Hrest" as (x) "[%Hx' Hrest]".
    rewrite Hx in Hx'. injection Hx' as -> ->.
    iDestruct "Hho" as (m') "(%Hsum' & Hf' & #Hllb')".
    iDestruct (stamps_frag_incl with "Hst Hf'") as %Hincl'.
    assert (Hne' : m' ≠ ∅).
    { intros ->. rewrite qsum_empty Hsum nat_Qc_1 in Hsum'.
      assert (H01 : (0 < 1)%Qc) by (vm_compute; reflexivity).
      exact (Qclt_not_eq _ _ H01 Hsum'). }
    assert (Hkeyed' : keyed m' (sr_ident r))
      by exact (keyed_sub _ _ _ (gincl_dom _ _ Hincl') HI).
    (* the cover: the register's stamp IS the box's, under the caller's floor *)
    iDestruct (box_floor_view ξ K with "Hrun Hfl") as "[Hrun (%K' & %HKK' & #HKv)]".
    iMod (ctx_absorb_lb (P_rest x) ξb ξ T K' ltac:(lia) with "Hrun HKv Hpk Hrest")
      as "(Hrun & Hpk & Hrest)".
    iMod (ghost_var_update_2 (SlotReg (sr_td r) false (sr_ident r) None) with "Hrd Hrd0")
      as "[Hrd Hrd0]"; [by rewrite Qp.half_half|].
    iMod (ghost_var_update_2 (L2Reg (lr_tp s0) (Some (sr_ident r, m'))) with "Hrp Hrp0")
      as "[Hrp Hrp0]"; [by rewrite Qp.half_half|].
    iMod ("Hcl" with "[Hpk Hst Hc Hrd Hrp HQn Hf']") as "_".
    { iNext. iExists T, ξb, m, 1, (SlotReg (sr_td r) false (sr_ident r) None),
               (L2Reg (lr_tp s0) (Some (sr_ident r, m'))).
      iFrame "Hpk Hllb Hst Hc Hrd Hrp". simpl.
      iSplitR; [iPureIntro; exact (conj Hsum (conj HI (conj HC HD)))|].
      rewrite /box_arm.
      iFrame "Hf' HQn". iPureIntro. split_and!; done. }
    iModIntro. iFrame "Hrun HQo Hrest Hrd0 Hcnt". iExists m'.
    iSplitR; [iPureIntro; by rewrite Hsum' Hsum|].
    rewrite /l2_hold. iExists (lr_tp s0). iFrame "Hrp0". iExact "Hllb'".
  Qed.

  (* ================================================================== *)
  (*  THE TWO NON-TRANSITION ACCESSORS (§6⁸ Q4/Q5).  Neither moves an arm,  *)
  (*  a stamp, a register or a row; the law stays "seven transitions".     *)
  (* ================================================================== *)

  (* box_q_update: the L2 holder rewrites its residue in place (main's
     ic_shrink_tx / ic_grow_tx: the descriptor half and the parked ln_tx
     share change together under two write locks).  Selects OUT_L2 by the
     caller's L2 half; runs the client's fupd on Q; puts it back. *)
  Lemma box_q_update (N : namespace) γ (i : id) (R : iProp Σ) (mh : gmap (id * nat) ufrac) (E : coPset) :
    ↑N ⊆ E →
    is_box N γ -∗
    l2_hold γ i mh -∗
    (* §6¹³: the client's fupd may hand an OUTPUT RESIDUE R back to the
       caller (a shrink/grow's updated descriptor half rides out as R) *)
    (Q2 ={E ∖ ↑N}=∗ Q2 ∗ R) ={E}=∗
    l2_hold γ i mh ∗ R.
  Proof.
    iIntros (HE) "#Hbox Hhold Hupd".
    iDestruct "Hhold" as (tp) "[Hrp0 #Hllbh]".
    rewrite /is_box. box_open "Hbox" "Hcl".
    iDestruct (ghost_var_agree with "Hrp Hrp0") as %->.
    iEval (cbn [lr_hold]) in "Harm".
    iDestruct "Harm" as "(>%Hwf & >%Hne0 & >%Hkeyed0 & >Hf0 & >HQ)".
    iMod ("Hupd" with "HQ") as "[HQ HR]".
    iMod ("Hcl" with "[Hpk Hst Hc Hrd Hrp Hf0 HQ]") as "_".
    { iNext. iExists T, ξb, m, cb, rb, (L2Reg tp (Some (i, mh))).
      iFrame "Hpk Hllb Hst Hc Hrd Hrp".
      iSplitR; [iPureIntro; exact (conj Hsum (conj HI (conj HC HD)))|].
      rewrite /box_arm. cbn [lr_hold]. iFrame "Hf0 HQ". iPureIntro. split_and!; done. }
    iModIntro. iFrame "HR". rewrite /l2_hold. iExists tp. iFrame "Hrp0". iExact "Hllbh".
  Qed.

  (* box_view: a read-only three-way view for a NON-OWNER (the commit's
     collection, which holds no lock of the box's).  Opens the inv, hands
     out the registers' values with the four rows and the ARM (a public
     definition -- the caller matches on lr_hold / sr_win and reads the
     client content inside: IN's header and rest at ξb, OUT_L1's window
     pair and Q1 c, OUT_L2's parked fragment and Q2), and closes with what it
     opened.  The collection's ic_slot_cover is stated over box_arm. *)
  Lemma box_view (N : namespace) γ (E : coPset) :
    ↑N ⊆ E →
    is_box N γ ={E, E ∖ ↑N}=∗
    ∃ (T : nat) (ξb : CtxId) m (c : nat) (r : slot_reg id X) (s : l2_reg id),
      ⌜box_rows T m c r s⌝ ∗
      box_arm γ T ξb m c r s ∗
      (box_arm γ T ξb m c r s ={E ∖ ↑N, E}=∗ True).
  Proof.
    iIntros (HE) "#Hbox". rewrite /is_box.
    iMod (inv_acc E N with "Hbox") as "[Hbody Hcl]"; [exact HE|].
    iDestruct "Hbody" as (T ξb m c r s) "(>Hpk & >#Hllb & >Hst & >Hc & >Hrd & >Hrp & >%Hrows & >Harm)".
    iModIntro. iExists T, ξb, m, c, r, s. iSplitR; [iPureIntro; exact Hrows|].
    iFrame "Harm". iIntros "Harm".
    iMod ("Hcl" with "[Hpk Hst Hc Hrd Hrp Harm]") as "_"; [| done].
    iNext. iExists T, ξb, m, c, r, s. iFrame "Hpk Hllb Hst Hc Hrd Hrp Harm".
    iPureIntro. exact Hrows.
  Qed.

  (* ================================================================== *)
  (*  boot: the box is born IN, at the boot deposit's stamp               *)
  (* ================================================================== *)
  (* The caller (bio_init / icache boot) deposits the bundle at identity
     i0 and receives: L1's register half at {| T_boot; false; i0 |} with
     llb T_boot (L1's floor row must start at td = T_boot -- the newlock
     twin over lock_pay_intro_llb folds it), the cnt half at 0, and L2's
     register half at {| 0; None |} (ctx_floor_0 serves its row).
     Proof skeleton: ctx_parked_alloc; ctx_deposit the bundle (T_boot);
     own_alloc (● ∅); ghost_var_alloc ×3; inv_alloc with m = ∅ (rows: Σ
     trivial, I vacuous, C vacuous-left, D td = T_boot). *)
  Lemma box_alloc `{CID : CpuId} (N : namespace) (ξ : CtxId) (i0 : id) (E : coPset) :
    own_context ξ -∗
    (∃ x, P_hdr i0 x ξ ∗ P_rest x ξ) ={E}=∗
    own_context ξ ∗
    ∃ (γ : box_names) (T_boot : nat),
      is_box N γ ∗
      slotd_half γ (SlotReg T_boot false i0 None) ∗ llb loglen_name T_boot ∗
      cnt_half γ 0 ∗
      slotp_half γ (L2Reg 0 None).
  Proof.
    iIntros "Hrun Hbun".
    iMod ctx_parked_alloc as (ξb) "Hpk".
    iMod (ctx_deposit (in_arm i0) ξ ξb 0 with "Hrun Hpk [Hbun]")
      as "(Hrun & %Tb & _ & Hpk & Hbun)".
    { rewrite /in_arm. iExact "Hbun". }
    iDestruct (ctx_parked_llb with "Hpk") as "[Hpk #Hllb]".
    iMod (own_alloc (● (∅ : gmapUR (id * nat) ufracR))) as (γst) "Hst"; [by apply auth_auth_valid|].
    iMod (ghost_var_alloc 0%nat) as (γc) "Hc".
    iEval (rewrite -Qp.half_half) in "Hc". iDestruct (ghost_var_split with "Hc") as "[Hc1 Hc2]".
    iMod (ghost_var_alloc (SlotReg Tb false i0 None : slot_reg id X)) as (γd) "Hd".
    iEval (rewrite -Qp.half_half) in "Hd". iDestruct (ghost_var_split with "Hd") as "[Hd1 Hd2]".
    iMod (ghost_var_alloc (L2Reg 0 None : l2_reg id)) as (γp) "Hp".
    iEval (rewrite -Qp.half_half) in "Hp". iDestruct (ghost_var_split with "Hp") as "[Hp1 Hp2]".
    set (γ := BoxNames γst γc γd γp).
    iMod (inv_alloc N _ (box_body γ) with "[Hpk Hst Hc1 Hd1 Hp1 Hbun]") as "#Hinv".
    { iNext. rewrite /box_body.
      iExists Tb, ξb, ∅, 0%nat, (SlotReg Tb false i0 None), (L2Reg 0 None).
      iFrame "Hpk Hllb Hst Hc1 Hd1 Hp1". simpl.
      iSplitR.
      { iPureIntro. split_and!.
        - by rewrite qsum_empty nat_Qc_0.
        - intros p Hp. rewrite dom_empty_L in Hp. by apply not_elem_of_empty in Hp.
        - left. intros p Hp. rewrite dom_empty_L in Hp. by apply not_elem_of_empty in Hp.
        - left. cbn [sr_td]. lia. }
      rewrite /box_arm. simpl. iExact "Hbun". }
    iModIntro. iFrame "Hrun". iExists γ, Tb. iFrame "Hinv Hd2 Hllb Hc2 Hp2".
  Qed.

  (* ================================================================== *)
  (*  boot at PRE-MINTED names (bio_init / bio_init_at: the names record   *)
  (*  is minted first; the boxes are built into it).  The L2 register half *)
  (*  and the cnt half arrive already split (the other halves seed the    *)
  (*  sleeplock payload and the L1 slot row); slot_d arrives whole.       *)
  (* ================================================================== *)
  Lemma box_alloc_at `{CID : CpuId} (N : namespace) γ (ξ : CtxId) (i0 : id) (E : coPset) :
    stamps_auth γ ∅ -∗
    ghost_var (bx_cnt γ) 1 0%nat -∗
    ghost_var (bx_slotd γ) 1 (inhabitant : slot_reg id X) -∗
    ghost_var (bx_slotp γ) 1 (inhabitant : l2_reg id) -∗
    own_context ξ -∗
    (∃ x, P_hdr i0 x ξ ∗ P_rest x ξ) ={E}=∗
    own_context ξ ∗
    ∃ T_boot : nat,
      is_box N γ ∗
      slotd_half γ (SlotReg T_boot false i0 None) ∗ llb loglen_name T_boot ∗
      cnt_half γ 0 ∗
      slotp_half γ (L2Reg 0 None).
  Proof.
    iIntros "Hst Hc Hd Hp Hrun Hbun".
    iMod ctx_parked_alloc as (ξb) "Hpk".
    iMod (ctx_deposit (in_arm i0) ξ ξb 0 with "Hrun Hpk [Hbun]")
      as "(Hrun & %Tb & _ & Hpk & Hbun)".
    { rewrite /in_arm. iExact "Hbun". }
    iDestruct (ctx_parked_llb with "Hpk") as "[Hpk #Hllb]".
    iMod (ghost_var_update (SlotReg Tb false i0 None) with "Hd") as "Hd".
    iEval (rewrite -Qp.half_half) in "Hd". iDestruct (ghost_var_split with "Hd") as "[Hd1 Hd2]".
    iMod (ghost_var_update (L2Reg 0 None) with "Hp") as "Hp".
    iEval (rewrite -Qp.half_half) in "Hp". iDestruct (ghost_var_split with "Hp") as "[Hp1 Hp2]".
    iEval (rewrite -Qp.half_half) in "Hc". iDestruct (ghost_var_split with "Hc") as "[Hc1 Hc2]".
    iMod (inv_alloc N _ (box_body γ) with "[Hpk Hst Hc1 Hd1 Hp1 Hbun]") as "#Hinv".
    { iNext. rewrite /box_body.
      iExists Tb, ξb, ∅, 0%nat, (SlotReg Tb false i0 None), (L2Reg 0 None).
      iFrame "Hpk Hllb Hst Hc1 Hd1 Hp1". simpl.
      iSplitR.
      { iPureIntro. split_and!.
        - by rewrite qsum_empty nat_Qc_0.
        - intros p Hp. rewrite dom_empty_L in Hp. by apply not_elem_of_empty in Hp.
        - left. intros p Hp. rewrite dom_empty_L in Hp. by apply not_elem_of_empty in Hp.
        - left. cbn [sr_td]. lia. }
      rewrite /box_arm. simpl. iExact "Hbun". }
    iModIntro. iFrame "Hrun". iExists Tb. iFrame "Hinv Hd2 Hllb Hc2 Hp2".
  Qed.


  (* boot at PRE-MINTED names with the cnt / L2 halves ALREADY split (the
     bcache's bio_init_at: the other halves seed the sleeplock payload and
     the L1 slot row before the boxes are built) *)
  Lemma box_alloc_at_halves `{CID : CpuId} (N : namespace) γ (ξ : CtxId) (i0 : id) (E : coPset) :
    own_context ξ -∗
    stamps_auth γ ∅ -∗
    cnt_half γ 0 -∗
    (∃ r0 : slot_reg id X, ghost_var (bx_slotd γ) 1 r0) -∗
    slotp_half γ (L2Reg 0 None) -∗
    (∃ x, P_hdr i0 x ξ ∗ P_rest x ξ) ={E}=∗
    own_context ξ ∗
    ∃ T_boot : nat,
      is_box N γ ∗
      slotd_half γ (SlotReg T_boot false i0 None) ∗ llb loglen_name T_boot.
  Proof.
    iIntros "Hrun Hst Hc Hd Hp Hbun". iDestruct "Hd" as (r0) "Hd".
    iMod ctx_parked_alloc as (ξb) "Hpk".
    iMod (ctx_deposit (in_arm i0) ξ ξb 0 with "Hrun Hpk [Hbun]")
      as "(Hrun & %Tb & _ & Hpk & Hbun)".
    { rewrite /in_arm. iExact "Hbun". }
    iDestruct (ctx_parked_llb with "Hpk") as "[Hpk #Hllb]".
    iMod (ghost_var_update (SlotReg Tb false i0 None) with "Hd") as "Hd".
    iEval (rewrite -Qp.half_half) in "Hd". iDestruct (ghost_var_split with "Hd") as "[Hd1 Hd2]".
    iMod (inv_alloc N _ (box_body γ) with "[Hpk Hst Hc Hd1 Hp Hbun]") as "#Hinv".
    { iNext. rewrite /box_body.
      iExists Tb, ξb, ∅, 0%nat, (SlotReg Tb false i0 None), (L2Reg 0 None).
      iFrame "Hpk Hllb Hst Hc Hd1 Hp". simpl.
      iSplitR.
      { iPureIntro. split_and!.
        - by rewrite qsum_empty nat_Qc_0.
        - intros p Hp. rewrite dom_empty_L in Hp. by apply not_elem_of_empty in Hp.
        - left. intros p Hp. rewrite dom_empty_L in Hp. by apply not_elem_of_empty in Hp.
        - left. cbn [sr_td]. lia. }
      rewrite /box_arm. simpl. iExact "Hbun". }
    iModIntro. iFrame "Hrun". iExists Tb. iFrame "Hinv Hd2 Hllb".
  Qed.
  (* ---- the derived facts the client rows need ------------------------ *)

  (* the L1 payload row folds at release: the register half comes back
     shut with whatever td the lemmas set, and the caller has llb td *)
  Lemma l1_row_fold γ (r : slot_reg id X) (ξ : CtxId) :
    sr_win r = false → sr_x r = None →
    slotd_half γ r -∗ ctx_floor ξ (sr_td r) -∗ llb loglen_name (sr_td r) -∗
    l1_row γ r ξ.
  Proof. iIntros (Hw Hx) "Hd #Hfl #Hllb". iFrame "Hd Hfl Hllb". by iPureIntro. Qed.

  (* the L2 payload row folds at releasesleep (the _in form mints the
     floor from the park's llb T') *)
  Lemma l2_row_fold γ (T' : nat) (ξ : CtxId) :
    slotp_half γ (L2Reg T' None) -∗ ctx_floor ξ T' -∗
    l2_row γ (L2Reg T' None) ξ.
  Proof. iIntros "Hp #Hfl". iFrame "Hp Hfl". by iPureIntro. Qed.

  (* the L2 row is a CtxMorph payload (the floor is the only ξ-row) *)
  Global Instance l2_row_morph γ (s : l2_reg id) : CtxMorph (l2_row γ s).
  Proof.
    rewrite /l2_row. apply ctx_morph_sep; [apply ctx_morph_const|].
    apply ctx_morph_sep; [apply ctx_morph_const| apply _].
  Qed.

End box.
