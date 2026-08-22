(** * WeakRvwmoProbeRestr.v — FINDING F3: the gmo prefix below the minimal
    violating write is NOT a [restr_ok] restriction.

    §4b's closure claim holds only for the witness's hart; B1b needs causal
    hulls (route-b §4d.1 F3).

    THE WITNESS [erg]: the minimal violation of §4b, plus a SECOND HART
    WITH AN EARLY READ.

      hart 0:  e  = (0,0)  LLoad  byte 0  (ts = [0], the era-initial image)
               w  = (0,1)  LStore byte 8            (the violating write)
      hart 1:  r1 = (1,0)  LLoad  byte 16 (ts = [0])
               r2 = (1,1)  LLoad  byte 24 (ts = [0])

      gmo:     r2  <  w  <  r1  <  e

    [r2] is gmo-BELOW [w] while its own po-PREDECESSOR [r1] is gmo-above
    it.  Nothing forbids that: two plain loads of DIFFERENT bytes are
    related by no arm of ppo⁻ (no poloc, no fence, no acquire, no RCsc
    pair), so the graph is consistent ([erg_consistent]) — and hart 1's
    pair is not a rule-14 violation either (neither load is a write), so
    NOTHING in the minimality of [w] excludes it ([erg_w_min_viol]: [w] is
    the gmo-minimal violating write and [e] its po-minimal witness).

    THE POINT.  [restr_ok erg cs n] at [n = gpos w = 1] — the cut that
    B1a's [restrict_consistent] consumes and B1b wants to realize — has NO
    solution ([erg_no_restr]): [take 1 (gx_gmo erg) = [r2]], so the cut
    must admit [r2], hence (the cut is a per-hart PREFIX) it admits [r1]
    too, and then [restr_ok]'s second clause puts [r1] in a gmo prefix
    that does not contain it.  The obstruction is generic: any hart whose
    events straddle the frontier out of po order breaks the
    "per-hart cut = gmo prefix" tie.  The right object is the CAUSAL HULL
    (closed under po-predecessors and rf-sources), which is what B1b must
    be restated over.

    NOTE ON THE IMAGE: [erg] uses the TOTAL era-initial image "every byte
    is 0" rather than [WeakLitmus.img0]'s two-entry map, because hart 1's
    loads read bytes 16 and 24 at the initial index; nothing in the model
    constrains [gx_img].

    A LEAF: nothing imports this file. *)
From Stdlib.ssr Require Import ssreflect.
From stdpp Require Import gmap finite list relations.
From stdpp Require Import bitvector.definitions.
From xv6iris Require Import WeakMem WeakLitmus WeakAxiomatic WeakAxiomatic2
                            WeakAxiomatic3 WeakRvwmoGraph WeakRvwmoLin
                            WeakRvwmoXchg WeakRvwmoRestr.

(* ====================================================================== *)
(** * 1. The graph *)

(** Every byte reads as 0 at the era-initial index. *)
Definition imgE : image := λ _, Some WeakLitmus.b0.

Definition erg : gexec :=
  GExec imgE
        [[LLoad false 0 [0%nat] [WeakLitmus.b0];
          LStore false 8 [WeakLitmus.b1] WCplain];
         [LLoad false 16 [0%nat] [WeakLitmus.b0];
          LLoad false 24 [0%nat] [WeakLitmus.b0]]]
        [(1%nat, 1%nat); (0%nat, 1%nat); (1%nat, 0%nat); (0%nat, 0%nat)].

(* ====================================================================== *)
(** * 2. The byte footprints *)

Lemma erg_acc (e : geid) (a : Z) :
  gaccesses erg e a →
  (e = (0%nat, 0%nat) ∧ a = 0%Z) ∨ (e = (0%nat, 1%nat) ∧ a = 8%Z) ∨
  (e = (1%nat, 0%nat) ∧ a = 16%Z) ∨ (e = (1%nat, 1%nat) ∧ a = 24%Z).
Proof.
  intros [Hw|Hr].
  - destruct Hw as (v & l & b & vs & j & Hl & Hwr & Hv & Ha).
    destruct e as [i k]. rewrite /gx_lbl /= in Hl.
    destruct i as [|[|i]]; simpl in Hl; [| |done];
      destruct k as [|[|k]]; simplify_eq/=;
      destruct j as [|j]; simplify_eq/=;
      rewrite /acc_addr /=; naive_solver.
  - destruct Hr as (t & v & l & b & ts & vs & j & Hl & Hrd & Ht & Hv & Ha).
    destruct e as [i k]. rewrite /gx_lbl /= in Hl.
    destruct i as [|[|i]]; simpl in Hl; [| |done];
      destruct k as [|[|k]]; simplify_eq/=;
      destruct j as [|j]; simplify_eq/=;
      rewrite /acc_addr /=; naive_solver.
Qed.

(** THE ONLY WRITE is hart 0's store, and it touches byte 8 alone. *)
Lemma erg_wr (e : geid) (a : Z) (v : bv 8) :
  gwrites_byte erg e a v → e = (0%nat, 1%nat) ∧ a = 8%Z.
Proof.
  intros (l & b & vs & j & Hl & Hwr & Hv & Ha).
  destruct e as [i k]. rewrite /gx_lbl /= in Hl.
  destruct i as [|[|i]]; simpl in Hl; [| |done];
    destruct k as [|[|k]]; simplify_eq/=;
    destruct j as [|j]; simplify_eq/=;
    rewrite /acc_addr /=; naive_solver.
Qed.

(* ====================================================================== *)
(** * 3. (a) [erg] is RVWMO⁻-consistent *)

Theorem erg_consistent : rvwmo_minus_consistent erg.
Proof.
  split_and!.
  - (* gwf *) split_and!.
    + repeat constructor; rewrite ?elem_of_list_In; simpl; intuition congruence.
    + intros e. split.
      * intros He. rewrite !elem_of_cons elem_of_nil in He.
        destruct He as [-> |[-> |[-> |[-> | []]]]]; eexists; split; reflexivity.
      * intros (l & Hl & Hm).
        destruct e as [i k]. rewrite /gx_lbl /= in Hl.
        destruct i as [|[|i]]; simpl in Hl; [| |done];
          destruct k as [|[|k]]; simplify_eq/=;
          rewrite !elem_of_cons; auto.
    + intros i p k l Hp Hk.
      destruct i as [|[|i]]; simplify_eq/=;
        destruct k as [|[|k]]; simplify_eq/=; done.
  - (* ppo⁻ ⊆ gmo: there are NO ppo⁻ edges.  In particular hart 1's two
       LOADS are unordered — different bytes, and load–load is not a ppo⁻
       arm.  This is exactly what makes the early read possible. *)
    intros e1 e2 Hppo. exfalso.
    destruct Hppo as [Hpl|[Hf|[Ha|Hr]]].
    + destruct Hpl as ((Hag & Hlt & _ & _) & a & H1 & H2).
      destruct (erg_acc e1 a H1)
        as [[He1 Ha1]|[[He1 Ha1]|[[He1 Ha1]|[He1 Ha1]]]];
        destruct (erg_acc e2 a H2)
          as [[He2 Ha2]|[[He2 Ha2]|[[He2 Ha2]|[He2 Ha2]]]];
        subst e1; subst e2; simpl in Hag, Hlt; lia.
    + destruct Hf as (pr & pw & sr & sw & (Hag & Hlt & kf & Hk1 & Hk2 & Hlf)
                      & _ & _).
      destruct e1 as [i1 k1], e2 as [i2 k2]; simpl in *; subst i2.
      rewrite /gx_lbl /= in Hlf.
      destruct i1 as [|[|i1]]; simpl in Hlf; [| |done];
        destruct kf as [|[|kf]]; simplify_eq/=; lia.
    + destruct Ha as (Hpo & (l & Hl & Hr') & (l' & Hl' & Haq) & _).
      destruct e1 as [i1 k1]. rewrite Hl in Hl'. simplify_eq.
      rewrite /gx_lbl /= in Hl.
      destruct i1 as [|[|i1]]; simpl in Hl; [| |done];
        destruct k1 as [|[|k1]]; simplify_eq/=; done.
    + destruct Hr as (Hpo & _ & (l & Hl & Hrl) & _).
      destruct e1 as [i1 k1]. rewrite /gx_lbl /= in Hl.
      destruct i1 as [|[|i1]]; simpl in Hl; [| |done];
        destruct k1 as [|[|k1]]; simplify_eq/=; done.
  - (* load value: all three reads name the ERA-INITIAL image, and the one
       write in the graph touches none of their bytes *)
    intros e a t v Hr.
    destruct Hr as (l & base & ts & vs & j & Hl & Hrd & Hj & Hv & Ha).
    destruct e as [i k]. rewrite /gx_lbl /= in Hl.
    destruct i as [|[|i]]; simpl in Hl; [| |done];
      destruct k as [|[|k]]; simplify_eq/=;
      destruct j as [|j]; simplify_eq/=;
      (split; [reflexivity|]);
      intros w' v' Hw' Hvis;
      destruct (erg_wr w' _ _ Hw') as [-> Hab];
      exfalso; rewrite /acc_addr /= in Hab; lia.
  - (* atomicity: no event both reads and writes *)
    intros e a t v Hr (l & Hl & Hw).
    destruct Hr as (l' & base & ts & vs & j & Hl' & Hrd & _).
    rewrite Hl in Hl'. simplify_eq.
    destruct e as [i k]. rewrite /gx_lbl /= in Hl.
    destruct i as [|[|i]]; simpl in Hl; [| |done];
      destruct k as [|[|k]]; simplify_eq/=; done.
Qed.

(* ====================================================================== *)
(** * 4. (b) [w = (0,1)] is the gmo-minimal violating write, [e = (0,0)]
       its po-minimal witness — the two minimality clauses of the kills *)

Theorem erg_w_min_viol :
  gviol erg (0%nat, 0%nat) (0%nat, 1%nat) ∧
  (∀ e' w', gviol erg e' w' → ¬ gmo_lt erg w' (0%nat, 1%nat)) ∧
  (∀ e', gviol erg e' (0%nat, 1%nat) → ¬ (e'.2 < (0%nat, 0%nat).2)%nat).
Proof.
  split_and!.
  - (* the violation: [e] po-before [w], [w] gmo-before [e] *)
    split_and!.
    + split_and!; [done|simpl; lia|by eexists|by eexists].
    + eexists. split; reflexivity.
    + eexists. split; reflexivity.
    + split_and!; [rewrite !elem_of_cons; auto|rewrite !elem_of_cons; auto
                  |vm_compute; lia].
  - (* gmo-MINIMAL among violating writes: the only write in the graph is
       [w] itself, and nothing precedes itself *)
    intros e' w' (_ & _ & Hw' & _) (Hin & _ & Hpos).
    rewrite !elem_of_cons elem_of_nil in Hin.
    destruct Hw' as (l & Hl & Hisw).
    destruct Hin as [->|[->|[->|[->|[]]]]];
      rewrite /gx_lbl /= in Hl; simplify_eq/=; try done.
    revert Hpos. vm_compute. lia.
  - (* po-MINIMAL witness: [e] sits at po position 0 *)
    intros e' _ Hlt. simpl in Hlt. lia.
Qed.

(* ====================================================================== *)
(** * 5. (c) THE POINT: no cut vector restricts [erg] at the frontier *)

Lemma erg_take1 : take 1%nat (gx_gmo erg) = [(1%nat, 1%nat)].
Proof. reflexivity. Qed.

(** [gpos erg w = 1], so the gmo prefix strictly below the minimal
    violating write is [take 1 (gx_gmo erg) = [r2]]. *)
Lemma erg_gpos_w : gpos erg (0%nat, 1%nat) = 1%nat.
Proof. by vm_compute. Qed.

Theorem erg_no_restr : ∀ cs, ¬ restr_ok erg cs 1%nat.
Proof.
  intros cs Hok.
  (* [r2 = (1,1)] is in the gmo prefix, so the cut admits it ... *)
  assert (Hr2 : gcut cs (1%nat, 1%nat) = true).
  { apply (restr_ok_cut erg cs 1%nat (1%nat, 1%nat) Hok).
    rewrite erg_take1. apply elem_of_list_here. }
  apply gcut_elim in Hr2 as (c & Hc & Hlt). simpl in Hc, Hlt.
  (* ... and a cut is a per-hart PREFIX, so it admits [r1 = (1,0)] too *)
  assert (Hr1 : gcut cs (1%nat, 0%nat) = true).
  { apply (gcut_intro cs (1%nat, 0%nat) c); [done|simpl; lia]. }
  assert (Hm : gmem erg (1%nat, 0%nat)) by (eexists; split; reflexivity).
  (* but then [restr_ok]'s second clause puts [r1] in a prefix without it *)
  pose proof (restr_ok_in erg cs 1%nat _ Hok Hm Hr1) as Hin.
  rewrite erg_take1 elem_of_list_singleton in Hin. by simplify_eq.
Qed.
