(** * WeakRvwmoFab.v — B1b-2: THE FABRIC ORDER AS BUNDLE DATA

    Design: [claude-notes/design/weak-memory-route-b.md] §4d.4's
    **B1b — DESIGNED** entry (the B1b-2 paragraph).  [WeakRvwmoSupply] is
    B1b-1 (fabric QUIESCENCE — no [LDev] anywhere, so the global fabric is
    the constant [λ _, d0]); this file lifts the quiescence restriction by
    making the FABRIC ORDER part of the conformance bundle.

    ** THE SHAPE

    A row event's EMISSION BLOCK is the administrative stretch that precedes
    it together with the realizing step(s) ([WeakRvwmoConf.hemit]'s [HEone] /
    [HEpair]).  MMIO is administrative ([WeakEvInst] emits [LDev], and
    [proj_lbl _ LDev = None]), so the fabric moves ONLY inside blocks, and a
    block either contains an [LDev] (a DEV BLOCK: it moves the fabric) or
    does not (then it is fabric-PRESERVING and fabric-BLIND —
    [WeakEvInst.pdev_ev_ok]).  The bundle therefore carries

      - [gf_dev : list geid] — the dev blocks, IN FABRIC ORDER;
      - [fab : nat → dev_state] — the global fabric trace, [fab n] the state
        the [n]-th dev block starts from and [fab (S n)] the one it ends at.

    A whole dev block is ONE fabric transition [fab n → fab (S n)]: a block's
    administrative run can span several instructions and hence several MMIO
    accesses, so the fabric ordinal indexes BLOCKS, not [LDev] steps.  That
    is what makes [NoDup (gf_dev GF)] the right well-formedness clause.

    ** *** A DESIGN CORRECTION THE BRIEF ASKED TO RECORD ***

    The brief's bundle used [WeakRvwmoConf.hart_conf] — ONE fabric function
    [dvf i] per hart, with the block at row position [k] running
    [dvf i k → dvf i (S k)].  THAT SHAPE IS JOINTLY UNSATISFIABLE as soon as
    a hart has two dev blocks with ANOTHER hart's dev block between them.
    [hemit] forces a hart's block to START where its predecessor ENDED, and
    a non-dev block preserves the fabric ([hemitf_states]' third conjunct,
    and [hart_conf_no_gap] below, which states exactly this for the landed
    [hart_conf]).  So for hart [i]'s consecutive dev blocks at row positions
    [k1 < k2] with fabric ordinals [m1 < m2], [hart_conf] forces
    [dvf i k2 = dvf i (S k1) = fab (S m1)] while the bundle clause demands
    [dvf i k2 = fab m2] — and [fab (S m1) ≠ fab m2] exactly when some other
    hart moved the fabric in between, which is the whole point of B1b-2.
    A bundle stated that way would be VACUOUS on every execution with two
    interleaved dev harts (the failure mode the witness slice caught for
    [cs_kill]).

    THE FIX, additive and local to this leaf: [hemitf], the emission with
    the block's two fabric endpoints carried by SEPARATE functions
    ([dvi k → dvo k], with no relation between [dvo k] and [dvi (S k)]).
    [hart_conf] embeds ([hart_conf_hemitf], [dvo := dv ∘ S]), so
    [gdexec_qconf] embeds into the new bundle unchanged (§6), and the
    per-hart discontinuity the global interleaving needs is expressible.
    [hemitf] is used ONLY as the bundle's hypothesis shape; nothing landed
    changes.

    ** WHAT IS HERE

    (1) §2 — DEV BLOCKS, read off the tagged item list: [em_dev] (a boolean
        fold: an administrative item belongs to the block of the nearest
        tagged item at or after it) and [is_dev_block].
    (2) §3 — [hemitf], the two-endpoint emission, [hart_conff], the
        embedding, and [hemitf_states]: per block the [hblk] fact, PLUS —
        for a non-dev block — fabric preservation and full BLINDNESS
        ([∀ d, hblk d d …], the [block_refab] the brief asks for).
    (3) §4 — the bundle [gfexec] / [gfexec_conf].
    (4) §5 — the model arm: [gdev_adj], [gfexec_consistent], [RacyF],
        [RF_gmo], [RF_acyclic], [racyF_dec], [lin_extF],
        [topo_linearizes_F], [topo_exists_F], and the new content — a
        linear extension ORDERS [gf_dev] ([lin_extF_dev_before]).
    (5) §6 — NON-VACUITY: [gfexec_conf_of_qconf] (B1b-1's bundle embeds,
        [gf_dev = []], [fab = λ _, d0]).  A witness with a NON-EMPTY
        [gf_dev] is NOT provided and cannot be yet: no [LDev]-emitting run
        witness exists in the tree (B1b-1 records the same gap from the
        other side), so the honest non-vacuity statement here is the
        embedding plus §5's decidability/acyclicity, which are unconditional.
    (6) §7 — THE SUPPLY [supply_of_fconf]: the interleaving theorem at a
        MOVING fabric, and [fconf_supply], its composition with the bundle.
    (7) §8 — HULLS: [gf_hull], and the [dclosed] condition a hull needs
        (a hull that drops a dev block CHANGES the device trajectory, so
        consistency restricts only for cuts that keep a PREFIX of the
        fabric order — [dclosed_prefix]).  Consistency is proved
        ([gf_hull_consistent]); the conformance restriction (O1–O5) and the
        [cycle_kill] mirror are ENUMERATED AS OBLIGATIONS in §8's closing
        comment — nothing is [Admitted] and no [Axiom] is introduced.

    A LEAF: nothing imports this file. *)
From Stdlib.ssr Require Import ssreflect.
From stdpp Require Import gmap finite list relations.
From stdpp Require Import bitvector.definitions.
Require Import SailStdpp.Operators_mwords.
Require Import SailStdpp.ConcurrencyInterfaceTypes.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import DevModel.
Require Import WeakMem.
Require Import WeakDeps.
Require Import WeakAxiomatic.
Require Import WeakAxiomatic2.
Require Import WeakAxiomatic3.
Require Import WeakRvwmoGraph.
Require Import WeakRvwmoNorm.
Require Import WeakRvwmoXchg.
Require Import WeakRvwmoLin.
Require Import WeakRvwmoRestr.
Require Import WeakRvwmoAcyc.
Require Import WeakRvwmoHull.
Require Import WeakRvwmoTopo.
Require Import WeakRvwmoDec.
Require Import WeakInterp.
Require Import WeakEvLang.
Require Import WeakEvPf.
(* AFTER the axiomatic band, exactly as [WeakRvwmoConf]/[WeakRvwmoSupply] do
   it: the WLABEL constructors are the unqualified ones here. *)
Require Import WeakPromise.
Require Import WeakPromiseFact.
Require Import WeakPromiseBridge.
Require Import WeakAxRealize.
Require Import WeakEvInst.
Require Import WeakRvwmoConf.
Require Import WeakRvwmoSupply.

Local Open Scope Z_scope.

(* ====================================================================== *)
(** * 1. BOOLEAN PRELIMINARIES *)

Lemma orb_false_split (b1 b2 : bool) :
  (b1 || b2)%bool = false → b1 = false ∧ b2 = false.
Proof. destruct b1, b2; simpl; naive_solver. Qed.

(* ====================================================================== *)
(** * 2. DEV BLOCKS

    An emission item is a label TAGGED with the row position it realizes
    ([None] for an administrative label — [WeakRvwmoConf]'s scope note
    (S-b)).  An item belongs to the block of the NEAREST TAGGED ITEM AT OR
    AFTER IT; [em_dev pend k es] folds that convention into a boolean
    ([pend] = "an [LDev] has been seen since the last tagged item").  The
    exclusive PAIR is handled by the tagged branch not resetting the answer:
    both of a pair's tagged items carry the SAME row position, so an [LDev]
    in the pair's interior run is attributed to the same block. *)

Definition lb_isdev (l : wlabel) : bool :=
  match l with LDev => true | _ => false end.

Lemma lb_isdev_ne l : lb_isdev l = false → l ≠ LDev.
Proof. by destruct l. Qed.

Fixpoint has_dev (ls : list wlabel) : bool :=
  match ls with
  | [] => false
  | l :: ls' => (lb_isdev l || has_dev ls')%bool
  end.

Lemma has_dev_false ls : has_dev ls = false → LDev ∉ ls.
Proof.
  induction ls as [|l ls IH]; intros H; [apply not_elem_of_nil|].
  simpl in H. destruct (orb_false_split _ _ H) as [Hl Hls].
  intros [Heq|Hin]%elem_of_cons; [by rewrite -Heq in Hl|by apply IH].
Qed.

Fixpoint em_dev (pend : bool) (k : nat) (es : list eitem) : bool :=
  match es with
  | [] => false
  | (l, None) :: es' => em_dev (pend || lb_isdev l)%bool k es'
  | (l, Some j) :: es' =>
      if bool_decide (j = k)
      then ((pend || lb_isdev l) || em_dev false k es')%bool
      else em_dev false k es'
  end.

Definition is_dev_block (em : hemission) (k : nat) : Prop :=
  em_dev false k (em_items em) = true.

Global Instance is_dev_block_dec em k : Decision (is_dev_block em k).
Proof. rewrite /is_dev_block. apply _. Defined.

(** The administrative stretch folds into [pend]. *)
Lemma em_dev_eadm ls pend k rest :
  em_dev pend k (eadm ls ++ rest) = em_dev (pend || has_dev ls)%bool k rest.
Proof.
  revert pend. induction ls as [|l ls IH]; intros pend; simpl.
  - by rewrite orb_false_r.
  - rewrite IH. by rewrite orb_assoc.
Qed.

(** ONE BLOCK, at its own row position … *)
Lemma em_dev_tag_eq pend ls l k es :
  em_dev pend k (eadm ls ++ (l, Some k) :: es)
  = (((pend || has_dev ls) || lb_isdev l) || em_dev false k es)%bool.
Proof. rewrite em_dev_eadm /=. by rewrite bool_decide_eq_true_2. Qed.

(** … and at any other. *)
Lemma em_dev_tag_ne pend ls l k n es :
  k ≠ n → em_dev pend n (eadm ls ++ (l, Some k) :: es) = em_dev false n es.
Proof. intros Hne. rewrite em_dev_eadm /=. by rewrite bool_decide_eq_false_2. Qed.

(** A [LDev]-free item list has no dev block — the bridge to B1b-1's
    [em_devfree]. *)
Lemma em_dev_devfree k es : LDev ∉ es.*1 → em_dev false k es = false.
Proof.
  induction es as [|it es IH]; intros Hnd; [done|].
  destruct it as [l o]. simpl in Hnd.
  have Hl : lb_isdev l = false.
  { destruct l; try done. exfalso. apply Hnd, elem_of_list_here. }
  have Hrest : LDev ∉ es.*1
    by (intros Hin; apply Hnd, elem_of_list_further).
  destruct o as [j|]; simpl.
  - case_bool_decide as Hc; [|by apply IH].
    rewrite Hl (IH Hrest) //.
  - rewrite Hl. by apply IH.
Qed.

Lemma em_devfree_no_dev_block em k : em_devfree em → ¬ is_dev_block em k.
Proof.
  rewrite /em_devfree /is_dev_block /em_labels. intros H.
  by rewrite (em_dev_devfree k (em_items em) H).
Qed.

(** [em_dev] is blind to the ts renaming: [wlbl_ren] neither makes nor
    unmakes an [LDev] ([WeakRvwmoSupply.wlbl_ren_dev]) and [eitem_ren] keeps
    the tag. *)
Lemma has_dev_ren π ls : has_dev (wlbl_ren π <$> ls) = has_dev ls.
Proof.
  induction ls as [|l ls IH]; [done|]. simpl. rewrite IH. f_equal.
  destruct (lb_isdev l) eqn:E.
  - destruct l; try done.
  - destruct l; try done.
Qed.

Lemma em_dev_ren π pend k es :
  em_dev pend k (eitem_ren π <$> es) = em_dev pend k es.
Proof.
  revert pend. induction es as [|it es IH]; intros pend; [done|].
  destruct it as [l o]. rewrite fmap_cons /eitem_ren /=.
  have Hl : lb_isdev (wlbl_ren π l) = lb_isdev l
    by (destruct l; try done).
  destruct o as [j|]; simpl.
  - case_bool_decide as Hc; [|by apply IH]. by rewrite Hl IH.
  - rewrite Hl. by apply IH.
Qed.

(* ====================================================================== *)
(** * 3. [hemitf]: THE EMISSION WITH TWO FABRIC ENDPOINTS

    Identical to [WeakRvwmoConf.hemit] except that the block at row position
    [k] runs from [dvi k] to [dvo k], with NO relation between [dvo k] and
    [dvi (S k)] — see the header's design correction. *)

Inductive hemitf (dvi dvo : nat → dev_state)
    : nat → wstate → list lbl → pexv6 → list eitem → pexv6 → Prop :=
| HFnil k ws p : hemitf dvi dvo k ws [] p [] p
| HFone k ws lb row p ls pa da l p' es pfin :
    adm_run true p (dvi k) ls pa da →
    hlbl_realizes pa ws lb l →
    pstep_ev pa da l p' (dvo k) →
    hemitf dvi dvo (S k) (lbl_post k ws lb) row p' es pfin →
    hemitf dvi dvo k ws (lb :: row) p (eadm ls ++ (l, Some k) :: es) pfin
| HFpair k ws lb row p ls1 pa da l1 pm dm ls2 pm2 dm2 l2 p' es pfin :
    adm_run true p (dvi k) ls1 pa da →
    hlbl_realizes_pair pa pm2 ws lb l1 l2 →
    pstep_ev pa da l1 pm dm →
    adm_run false pm dm ls2 pm2 dm2 →
    pstep_ev pm2 dm2 l2 p' (dvo k) →
    hemitf dvi dvo (S k) (lbl_post k ws lb) row p' es pfin →
    hemitf dvi dvo k ws (lb :: row) p
      (eadm ls1 ++ (l1, Some k) :: eadm ls2 ++ (l2, Some k) :: es) pfin.

Definition hart_conff (i : agent) (row : list lbl) (p0 : pexv6)
    (dvi dvo : nat → dev_state) (em : hemission) : Prop :=
  hemitf dvi dvo 0%nat ws_init row p0 (em_items em) (em_fin em).

(** THE EMBEDDING: the landed one-fabric emission is the special case
    [dvo = dv ∘ S]. *)
Lemma hemit_hemitf dv k ws row p es pfin :
  hemit dv k ws row p es pfin →
  hemitf dv (λ n, dv (S n)) k ws row p es pfin.
Proof.
  induction 1 as [k ws p
                 |k ws lb row p ls pa da l p' es pfin Har Hre Hst Hem IH
                 |k ws lb row p ls1 pa da l1 pm dm ls2 pm2 dm2 l2 p' es pfin
                  Har1 Hre Hst1 Har2 Hst2 Hem IH].
  - apply HFnil.
  - by eapply HFone.
  - by eapply HFpair.
Qed.

Lemma hart_conf_hemitf i row p0 dv em :
  hart_conf i row p0 dv em → hart_conff i row p0 dv (λ n, dv (S n)) em.
Proof. apply hemit_hemitf. Qed.

(** ** 3.1 The block, with its two fabric endpoints explicit *)

Definition hblk (d d' : dev_state) (ws : wstate) (lb : lbl) (p p' : pexv6)
    : Prop :=
  ∃ pa da,
    adm_star pstep_ev true p d pa da ∧
    ((∃ l, hlbl_realizes pa ws lb l ∧ pstep_ev pa da l p' d')
     ∨ (∃ pm dm pm2 dm2 l1 l2,
          hlbl_realizes_pair pa pm2 ws lb l1 l2 ∧
          pstep_ev pa da l1 pm dm ∧
          adm_star pstep_ev false pm dm pm2 dm2 ∧
          pstep_ev pm2 dm2 l2 p' d')).

(** [WeakRvwmoSupply.hblock] IS [hblk] at the two fabric values it reads. *)
Lemma hblock_hblk dv k ws lb p p' :
  hblock dv k ws lb p p' ↔ hblk (dv k) (dv (S k)) ws lb p p'.
Proof. split; intros H; exact H. Qed.

(** ** 3.2 THE STATE EXTRACTION, with block classification

    Exactly [WeakRvwmoSupply.hemit_states]' induction (the existential
    witness is BUILT BY THE INDUCTION — no choice principle), strengthened
    with what B1b-2 needs: for a NON-DEV block the fabric is PRESERVED and
    the block REPLAYS AT ANY CONSTANT FABRIC.  That second conjunct is the
    brief's [block_refab]. *)
Lemma hemitf_states dvi dvo k ws row p es pfin :
  hemitf dvi dvo k ws row p es pfin →
  ∃ f : nat → pexv6, f 0%nat = p ∧
    ∀ n lb, row !! n = Some lb →
      hblk (dvi (n + k)%nat) (dvo (n + k)%nat)
           (row_ws_aux k ws (take n row)) lb (f n) (f (S n))
      ∧ (em_dev false (n + k)%nat es = false →
         dvo (n + k)%nat = dvi (n + k)%nat ∧
         ∀ d, hblk d d (row_ws_aux k ws (take n row)) lb (f n) (f (S n))).
Proof.
  induction 1 as [k ws p
                 |k ws lb row p ls pa da l p' es pfin Har Hre Hst Hem IH
                 |k ws lb row p ls1 pa da l1 pm dm ls2 pm2 dm2 l2 p' es pfin
                  Har1 Hre Hst1 Har2 Hst2 Hem IH].
  - exists (λ _, p). split; [done|]. intros n lb Hn. by rewrite lookup_nil in Hn.
  - destruct IH as (f' & Hf0 & Hf).
    exists (λ n, match n with 0%nat => p | S n' => f' n' end).
    split; [done|]. intros n lb0 Hn. destruct n as [|n]; simpl in Hn |- *.
    + injection Hn as <-. rewrite Hf0. split.
      * exists pa, da.
        split; [exact (adm_run_star _ _ _ _ _ _ Har)|]. left. by exists l.
      * rewrite em_dev_tag_eq. intros Hnd.
        destruct (orb_false_split _ _ Hnd) as [Hnd1 _].
        destruct (orb_false_split _ _ Hnd1) as [Hls Hl].
        destruct (orb_false_split _ _ Hls) as [_ Hls'].
        have Hne := lb_isdev_ne l Hl.
        have Hnl : LDev ∉ ls := has_dev_false ls Hls'.
        have Hda : da = dvi k := adm_run_devfree _ _ _ _ _ _ Har Hnl.
        destruct (pstep_ev_devfree _ _ _ _ _ Hst Hne) as [Hd Hall].
        split; [by rewrite Hd Hda|].
        intros d. exists pa, d. split.
        { exact (adm_run_star _ _ _ _ _ _
                   (adm_run_refab _ _ _ _ _ _ Har Hnl d)). }
        left. exists l. split; [exact Hre|apply Hall].
    + replace (S (n + k))%nat with (n + S k)%nat by lia.
      destruct (Hf n lb0 Hn) as [H1 H2]. split; [exact H1|].
      rewrite (em_dev_tag_ne false ls l k (n + S k)%nat es ltac:(lia)).
      exact H2.
  - destruct IH as (f' & Hf0 & Hf).
    exists (λ n, match n with 0%nat => p | S n' => f' n' end).
    split; [done|]. intros n lb0 Hn. destruct n as [|n]; simpl in Hn |- *.
    + injection Hn as <-. rewrite Hf0. split.
      * exists pa, da.
        split; [exact (adm_run_star _ _ _ _ _ _ Har1)|]. right.
        exists pm, dm, pm2, dm2, l1, l2.
        split_and!; [done|done|exact (adm_run_star _ _ _ _ _ _ Har2)|done].
      * rewrite em_dev_tag_eq em_dev_tag_eq. intros Hnd.
        destruct (orb_false_split _ _ Hnd) as [Hnd1 Hnd2].
        destruct (orb_false_split _ _ Hnd1) as [Hls1 Hl1].
        destruct (orb_false_split _ _ Hls1) as [_ Hls1'].
        destruct (orb_false_split _ _ Hnd2) as [Hnd3 _].
        destruct (orb_false_split _ _ Hnd3) as [Hls2 Hl2].
        destruct (orb_false_split _ _ Hls2) as [_ Hls2'].
        have Hn1 : LDev ∉ ls1 := has_dev_false ls1 Hls1'.
        have Hn2 : LDev ∉ ls2 := has_dev_false ls2 Hls2'.
        have Hda : da = dvi k := adm_run_devfree _ _ _ _ _ _ Har1 Hn1.
        destruct (pstep_ev_devfree _ _ _ _ _ Hst1 (lb_isdev_ne _ Hl1))
          as [Hd1 Hall1].
        have Hdm2 : dm2 = dm := adm_run_devfree _ _ _ _ _ _ Har2 Hn2.
        destruct (pstep_ev_devfree _ _ _ _ _ Hst2 (lb_isdev_ne _ Hl2))
          as [Hd2 Hall2].
        split; [by rewrite Hd2 Hdm2 Hd1 Hda|].
        intros d. exists pa, d. split.
        { exact (adm_run_star _ _ _ _ _ _
                   (adm_run_refab _ _ _ _ _ _ Har1 Hn1 d)). }
        right. exists pm, d, pm2, d, l1, l2. split_and!.
        -- exact Hre.
        -- apply Hall1.
        -- exact (adm_run_star _ _ _ _ _ _
                    (adm_run_refab _ _ _ _ _ _ Har2 Hn2 d)).
        -- apply Hall2.
    + replace (S (n + k))%nat with (n + S k)%nat by lia.
      destruct (Hf n lb0 Hn) as [H1 H2]. split; [exact H1|].
      rewrite (em_dev_tag_ne false ls1 l1 k (n + S k)%nat _ ltac:(lia)).
      rewrite (em_dev_tag_ne false ls2 l2 k (n + S k)%nat es ltac:(lia)).
      exact H2.
Qed.

Lemma hart_conff_states i row p0 dvi dvo em :
  hart_conff i row p0 dvi dvo em →
  ∃ f : nat → pexv6, f 0%nat = p0 ∧
    ∀ n lb, row !! n = Some lb →
      hblk (dvi n) (dvo n) (row_ws row n) lb (f n) (f (S n))
      ∧ (¬ is_dev_block em n →
         dvo n = dvi n ∧
         ∀ d, hblk d d (row_ws row n) lb (f n) (f (S n))).
Proof.
  intros Hem. destruct (hemitf_states _ _ _ _ _ _ _ _ Hem) as (f & Hf0 & Hf).
  exists f. split; [done|]. intros n lb Hn.
  destruct (Hf n lb Hn) as [H1 H2]. rewrite Nat.add_0_r in H1, H2.
  rewrite /row_ws. split; [exact H1|].
  rewrite /is_dev_block. intros Hnd. apply H2.
  by destruct (em_dev false n (em_items em)); [destruct (Hnd eq_refl)|].
Qed.

(** ** 3.3 THE OBSTRUCTION, machine-checked

    Why the bundle cannot use [hart_conf] (header): a one-fabric emission
    forces the fabric to be CONSTANT across a non-dev block, hence across
    every stretch of a hart's row between two of ITS dev blocks — so the
    hart cannot observe another hart's fabric motion in between. *)
Lemma hart_conf_no_gap i row p0 dv em n lb :
  hart_conf i row p0 dv em → row !! n = Some lb → ¬ is_dev_block em n →
  dv (S n) = dv n.
Proof.
  intros Hem Hn Hnd.
  destruct (hart_conff_states i row p0 dv (λ m, dv (S m)) em
              (hart_conf_hemitf i row p0 dv em Hem)) as (f & _ & Hf).
  by destruct (proj2 (Hf n lb Hn) Hnd) as [Heq _].
Qed.

(* ====================================================================== *)
(** * 4. THE BUNDLE

    [gf_dev] lists the dev blocks IN FABRIC ORDER; [fab] is the global
    fabric trace, indexed by that order.  The per-hart emission is at the
    hart's own two endpoint functions, pinned to [fab] exactly at the hart's
    own dev blocks — everywhere else fabric-blindness makes the values
    irrelevant ([hemitf_states]). *)

Record gfexec := GFExec { gf_gd : gdexec; gf_dev : list geid }.

Definition gfexec_conf (boot : agent → pexv6) (d0 : dev_state)
    (fab : nat → dev_state) (GF : gfexec) : Prop :=
  fab 0%nat = d0 ∧
  NoDup (gf_dev GF) ∧
  (∀ n i k, gf_dev GF !! n = Some (i, k) →
     ∃ row, gx_prog (gd_g (gf_gd GF)) !! i = Some row ∧ (k < length row)%nat) ∧
  (∀ i row, gx_prog (gd_g (gf_gd GF)) !! i = Some row →
     ∃ (em : hemission) (dvi dvo : nat → dev_state),
       hart_conff i row (boot i) dvi dvo em ∧
       (∀ k, (k < length row)%nat →
             (is_dev_block em k ↔ (i, k) ∈ gf_dev GF)) ∧
       (∀ k n, gf_dev GF !! n = Some (i, k) →
               dvi k = fab n ∧ dvo k = fab (S n)) ∧
       (∀ jk, jk ∈ row_deps (em_items em) →
              ((i, jk.1), (i, jk.2)) ∈ gd_deps (gf_gd GF))).

(* ====================================================================== *)
(** * 5. THE MODEL ARM

    Consecutive dev blocks are globally ordered.  THIS IS A MODEL CLAUSE,
    not a theorem: what makes hardware honor it is the M5 FENCE DISCIPLINE
    — an MMIO access is bracketed by [fence io,io]-strength ordering against
    the surrounding memory accesses, so the row events the dev blocks hang
    off cannot be reordered against each other.  Recorded as a conjunct of
    [gfexec_consistent], the same way [gdeps_gmo] records the store-dep
    fragment in [rvwmo_minus_deps_consistent]. *)

Definition gdev_adj (GF : gfexec) (a b : geid) : Prop :=
  ∃ n, gf_dev GF !! n = Some a ∧ gf_dev GF !! S n = Some b.

Definition gfexec_consistent (GF : gfexec) : Prop :=
  rvwmo_minus_deps_consistent (gf_gd GF) ∧
  (∀ a b, gdev_adj GF a b → gmo_lt (gd_g (gf_gd GF)) a b).

Definition RacyF (GF : gfexec) (x y : geid) : Prop :=
  RacyD (gf_gd GF) x y ∨ gdev_adj GF x y.

Lemma RF_gmo GF x y :
  gfexec_consistent GF → grule14 (gd_g (gf_gd GF)) →
  RacyF GF x y → gmo_lt (gd_g (gf_gd GF)) x y.
Proof.
  intros [Hc Hdev] H14 [HR|Hd]; [by eapply RD_gmo|by apply Hdev].
Qed.

Lemma tc_RF_gmo GF x y :
  gfexec_consistent GF → grule14 (gd_g (gf_gd GF)) →
  tc (RacyF GF) x y → gmo_lt (gd_g (gf_gd GF)) x y.
Proof.
  intros Hc H14. induction 1 as [x y HR|x u y HR Htc IH].
  - by eapply RF_gmo.
  - eapply gmo_lt_trans; [by eapply RF_gmo|exact IH].
Qed.

Theorem RF_acyclic GF x :
  gfexec_consistent GF → grule14 (gd_g (gf_gd GF)) →
  tc (RacyF GF) x x → False.
Proof. intros Hc H14 Htc. by eapply gmo_lt_irrefl, tc_RF_gmo. Qed.

(** ** 5.1 Decidability: bounded search over [gf_dev] *)

Global Instance gdev_adj_dec GF a b : Decision (gdev_adj GF a b).
Proof.
  apply (dec_iff (P := gdev_adj GF a b)
           (Q := ∃ n, n ∈ seq 0 (length (gf_dev GF)) ∧
                      (gf_dev GF !! n = Some a ∧ gf_dev GF !! S n = Some b))).
  - split.
    + intros (n & Hn & Hsn). exists n. split; [|done].
      apply elem_of_seq. split; [lia|]. simpl.
      by eapply lookup_lt_Some.
    + intros (n & _ & H). by exists n.
  - apply list_exists_dec. intros n. apply _.
Defined.

Global Instance racyF_dec GF x y : Decision (RacyF GF x y).
Proof. rewrite /RacyF. apply _. Defined.

(** ** 5.2 Linear extensions *)

Definition lin_extF (GF : gfexec) (L : list geid) : Prop :=
  L ≡ₚ gx_gmo (gd_g (gf_gd GF)) ∧ ∀ x y, RacyF GF x y → before L x y.

Lemma lin_extF_lin_extD GF L : lin_extF GF L → lin_extD (gf_gd GF) L.
Proof. intros [HL Hord]. split; [done|]. intros x y HR. apply Hord. by left. Qed.

(** [topo_linearizes] applies VERBATIM — the fabric arm only strengthens the
    hypothesis. *)
Theorem topo_linearizes_F GF L :
  gfexec_consistent GF → lin_extF GF L →
  rvwmo_minus_deps_consistent
    (GDExec (retime (gd_g (gf_gd GF)) L) (gd_deps (gf_gd GF))) ∧
  grule14 (retime (gd_g (gf_gd GF)) L) ∧
  rows_rel (tren (gd_g (gf_gd GF)) L) (gd_g (gf_gd GF))
           (retime (gd_g (gf_gd GF)) L) ∧
  wperm (tren (gd_g (gf_gd GF)) L) (gd_g (gf_gd GF))
        (retime (gd_g (gf_gd GF)) L).
Proof.
  intros [Hc _] Hlin.
  exact (topo_linearizes (gf_gd GF) L Hc (lin_extF_lin_extD GF L Hlin)).
Qed.

(** THE NEW CONTENT: a linear extension of [RacyF] ORDERS the fabric list.
    Adjacency is immediate; the general case needs transitivity of [before],
    which holds on a duplicate-free list. *)
Lemma before_trans {A} (L : list A) x y z :
  NoDup L → before L x y → before L y z → before L x z.
Proof.
  intros Hnd (i & j & Hi & Hj & Hij) (i' & j' & Hi' & Hj' & Hij').
  have Hji : j = i' by (eapply NoDup_lookup; [exact Hnd|exact Hj|exact Hi']).
  exists i, j'. split_and!; [done|done|lia].
Qed.

Lemma lin_extF_nodup GF L : gfexec_consistent GF → lin_extF GF L → NoDup L.
Proof.
  intros [((Hwf & _ & _ & _) & _ & _) _] [HL _].
  rewrite HL. by destruct Hwf as (Hnd & _ & _).
Qed.

Lemma lin_extF_dev_before GF L m n e e' :
  gfexec_consistent GF → lin_extF GF L → (m < n)%nat →
  gf_dev GF !! m = Some e → gf_dev GF !! n = Some e' → before L e e'.
Proof.
  intros Hc Hlin Hlt Hm Hn.
  have Hnd : NoDup L := lin_extF_nodup GF L Hc Hlin.
  remember (n - S m)%nat as d eqn:Hd. revert m n e e' Hlt Hm Hn Hd.
  induction d as [|d IH]; intros m n e e' Hlt Hm Hn Hd.
  - have Heq : n = S m by lia. rewrite Heq in Hn.
    apply (proj2 Hlin). right. by exists m.
  - destruct (lookup_lt_is_Some_2 (gf_dev GF) (S m)) as [e2 He2].
    { pose proof (lookup_lt_Some _ _ _ Hn). lia. }
    eapply before_trans; [exact Hnd| |].
    + apply (proj2 Hlin). right. by exists m.
    + apply (IH (S m) n e2 e'); [lia|done|done|lia].
Qed.

(** ** 5.3 Existence *)

Lemma RacyF_mem GF x y :
  gfexec_consistent GF → RacyF GF x y →
  x ∈ gx_gmo (gd_g (gf_gd GF)) ∧ y ∈ gx_gmo (gd_g (gf_gd GF)).
Proof.
  intros [Hc Hdev] [HR|Hd].
  - by eapply RacyD_mem.
  - destruct (Hdev x y Hd) as (Hx & Hy & _). done.
Qed.

Theorem topo_exists_F (GF : gfexec) :
  gfexec_consistent GF →
  (∀ x, ¬ tc (RacyF GF) x x) →
  ∃ L, lin_extF GF L.
Proof.
  intros Hc Hacy.
  have Hnd : NoDup (gx_gmo (gd_g (gf_gd GF))).
  { destruct Hc as [((Hwf & _ & _ & _) & _ & _) _].
    by destruct Hwf as (Hn & _ & _). }
  destruct (topo_sort_exists (RacyF GF) (λ x y, racyF_dec GF x y) Hacy _ Hnd)
    as (L & HL & Hord).
  exists L. split; [exact HL|].
  intros x y HR. destruct (RacyF_mem GF x y Hc HR) as [Hx Hy].
  by apply Hord.
Qed.

(* ====================================================================== *)
(** * 6. NON-VACUITY: B1b-1's BUNDLE EMBEDS

    [gdexec_qconf] is [gfexec_conf] with an EMPTY fabric order and the
    constant trace.  (A witness with a NON-EMPTY [gf_dev] is not available:
    no [LDev]-emitting run witness exists in the tree yet — the same gap
    B1b-1 records from the other side.  §5's decidability and acyclicity are
    unconditional and hold for every [gf_dev].) *)

Lemma gfexec_conf_of_qconf boot d0 GD :
  gdexec_qconf boot d0 GD →
  gfexec_conf boot d0 (λ _, d0) (GFExec GD []).
Proof.
  intros Hq. split_and!; [done|apply NoDup_nil_2| |].
  - intros n i k Hn. by rewrite lookup_nil in Hn.
  - intros i row Hrow. simpl in Hrow.
    destruct (Hq i row Hrow) as (em & Hem & Hdf & Hdep).
    exists em, (λ _, d0), (λ _, d0). split_and!.
    + exact (hart_conf_hemitf i row (boot i) (λ _, d0) em Hem).
    + intros k _. split.
      * intros Hd. by destruct (em_devfree_no_dev_block em k Hdf Hd).
      * intros Hin. by apply elem_of_nil in Hin.
    + intros k n Hn. by rewrite lookup_nil in Hn.
    + exact Hdep.
Qed.

(* ====================================================================== *)
(** * 7. THE SUPPLY AT A MOVING FABRIC

    The global fabric at trace position [k] is [fab] at the NUMBER OF DEV
    BLOCKS STRICTLY BEFORE [k] in the trace.  A trace step is a dev step iff
    the acting hart's row position at that step is one of [gf_dev]'s
    entries. *)

Definition dstep_at (GF : gfexec) (tr : list estep) (j : nat) : bool :=
  match tr !! j with
  | Some s => bool_decide ((es_ag s, tcnt (es_ag s) (take j tr)) ∈ gf_dev GF)
  | None => false
  end.

Fixpoint dcnt (GF : gfexec) (tr : list estep) (k : nat) : nat :=
  match k with
  | 0%nat => 0%nat
  | S k' => (dcnt GF tr k' + (if dstep_at GF tr k' then 1 else 0))%nat
  end.

Lemma dcnt_0 GF tr : dcnt GF tr 0%nat = 0%nat.
Proof. done. Qed.

Lemma dcnt_step_dev GF tr k :
  dstep_at GF tr k = true → dcnt GF tr (S k) = S (dcnt GF tr k).
Proof. intros H. simpl. rewrite H. lia. Qed.

Lemma dcnt_step_ne GF tr k :
  dstep_at GF tr k = false → dcnt GF tr (S k) = dcnt GF tr k.
Proof. intros H. simpl. rewrite H. lia. Qed.

(** THE INTERLEAVING THEOREM.  [supply_of_qconf]'s proof, with the constant
    fabric replaced by [fab ∘ dcnt] and the per-block fabric endpoints
    supplied by either the bundle clause (at a dev block) or blindness (at a
    non-dev block).  The per-hart data is taken in the [em]-FREE form
    [fconf_rows] below produces from [gfexec_conf]. *)
Theorem supply_of_fconf (c : cand) (boot : agent → pexv6)
    (fab : nat → dev_state) (GF : gfexec)
    (rows : agent → list lbl) (N : nat) :
  (* the trace is an interleaving of the rows ... *)
  (∀ i, (λ s, es_lb s) <$> filter (λ s, es_ag s = i) (cd_tr c) = rows i) →
  (* ... over the agents below [N] ... *)
  (∀ i, (N ≤ i)%nat → rows i = []) →
  (* ... every row emits, with its dev blocks pinned to [fab] and its
     non-dev blocks fabric-blind ... *)
  (∀ i, (i < N)%nat → ∃ f : nat → pexv6, f 0%nat = boot i ∧
     ∀ n lb, rows i !! n = Some lb →
       (∀ m, gf_dev GF !! m = Some (i, n) →
             hblk (fab m) (fab (S m)) (row_ws (rows i) n) lb (f n) (f (S n)))
       ∧ ((i, n) ∉ gf_dev GF →
          ∀ d, hblk d d (row_ws (rows i) n) lb (f n) (f (S n)))) →
  (* ... and the trace respects [gf_dev]'s order. *)
  (∀ k s, cd_tr c !! k = Some s →
     (es_ag s, tcnt (es_ag s) (take k (cd_tr c))) ∈ gf_dev GF →
     gf_dev GF !! dcnt GF (cd_tr c) k
       = Some (es_ag s, tcnt (es_ag s) (take k (cd_tr c)))) →
  ∃ pst : nat → list pexv6,
    pst 0%nat = boot <$> seq 0 N ∧
    exec_prog_ok' pstep_ev pcls_ev pst
      (λ k, fab (dcnt GF (cd_tr c) k)) (cand_exec c).
Proof.
  intros Hrows Hbnd Hch Hord.
  destruct (nat_bounded_choice (λ _ : nat, PDisk None) _ N Hch) as (F & HF).
  exists (λ k, (λ i, F i (tcnt i (take k (cd_tr c)))) <$> seq 0 N).
  split.
  - apply list_eq. intros j. rewrite !list_lookup_fmap.
    destruct (decide (j < N)%nat) as [Hj|Hj].
    + rewrite lookup_seq_lt //=. by rewrite (proj1 (HF j Hj)).
    + rewrite lookup_seq_ge //. lia.
  - intros k s Hs. simpl in Hs.
    have Hklen : (k ≤ length (cd_tr c))%nat.
    { pose proof (lookup_lt_Some _ _ _ Hs). lia. }
    have Hrow : rows (es_ag s) !! tcnt (es_ag s) (take k (cd_tr c))
                = Some (es_lb s).
    { rewrite -Hrows. exact (trow_at (es_ag s) (cd_tr c) k s Hs eq_refl). }
    have HiN : (es_ag s < N)%nat.
    { destruct (decide (es_ag s < N)%nat) as [?|Hge]; [done|].
      rewrite (Hbnd (es_ag s) ltac:(lia)) in Hrow.
      by rewrite lookup_nil in Hrow. }
    destruct (HF (es_ag s) HiN) as (Hf0 & Hfb).
    destruct (Hfb _ _ Hrow) as [Hdev Hnodev].
    (* THE BLOCK, at the two GLOBAL fabric values *)
    have Hblk : hblk (fab (dcnt GF (cd_tr c) k))
                     (fab (dcnt GF (cd_tr c) (S k)))
                     (row_ws (rows (es_ag s))
                             (tcnt (es_ag s) (take k (cd_tr c))))
                     (es_lb s)
                     (F (es_ag s) (tcnt (es_ag s) (take k (cd_tr c))))
                     (F (es_ag s) (S (tcnt (es_ag s) (take k (cd_tr c))))).
    { destruct (decide ((es_ag s, tcnt (es_ag s) (take k (cd_tr c)))
                          ∈ gf_dev GF)) as [Hin|Hnin].
      - have Hda : dstep_at GF (cd_tr c) k = true.
        { rewrite /dstep_at Hs. by apply bool_decide_eq_true_2. }
        rewrite (dcnt_step_dev _ _ _ Hda).
        by apply (Hdev (dcnt GF (cd_tr c) k)), Hord.
      - have Hda : dstep_at GF (cd_tr c) k = false.
        { rewrite /dstep_at Hs. by apply bool_decide_eq_false_2. }
        rewrite (dcnt_step_ne _ _ _ Hda). by apply Hnodev. }
    destruct Hblk as (pa & da & Hstar & Hdisj).
    have Hrelp : w_relp (ms_ws (stt (cand_exec c) k) (es_ag s))
               = w_relp (row_ws (rows (es_ag s))
                                (tcnt (es_ag s) (take k (cd_tr c)))).
    { rewrite (cand_ws_relp c (es_ag s) k Hklen) /trow. by rewrite Hrows. }
    exists (F (es_ag s) (tcnt (es_ag s) (take k (cd_tr c)))), pa, da,
           (F (es_ag s) (S (tcnt (es_ag s) (take k (cd_tr c))))).
    split_and!.
    + rewrite list_lookup_fmap lookup_seq_lt //=.
    + apply list_eq. intros j. rewrite list_lookup_fmap.
      destruct (decide (j < N)%nat) as [Hj|Hj].
      * rewrite lookup_seq_lt //=.
        destruct (decide (j = es_ag s)) as [->|Hji].
        { rewrite list_lookup_insert;
            [|rewrite length_fmap length_seq; lia].
          by rewrite (tcnt_step_eq _ (cd_tr c) k s Hs eq_refl). }
        { rewrite list_lookup_insert_ne // list_lookup_fmap
                  lookup_seq_lt //=.
          rewrite (tcnt_step_ne j (cd_tr c) k s Hs
                     (λ H, Hji (eq_sym H))) //. }
      * rewrite lookup_seq_ge; [|lia]. simpl.
        rewrite list_lookup_insert_ne; [|lia].
        rewrite list_lookup_fmap lookup_seq_ge //. lia.
    + exact Hstar.
    + destruct Hdisj as [(l & Hre & Hst)|
                         (pm & dm & pm2 & dm2 & l1 & l2 & Hre & Hs1 & Hs2 & Hs3)].
      * left. exists l. split; [|exact Hst].
        apply hlbl_realizes_ax.
        by eapply hlbl_realizes_relp; [exact Hrelp|exact Hre].
      * right. exists pm, dm, pm2, dm2, l1, l2.
        split_and!; [|exact Hs1|exact Hs2|exact Hs3].
        apply hlbl_realizes_pair_ax.
        by eapply hlbl_realizes_pair_relp; [exact Hrelp|exact Hre].
Qed.

(** ** 7.1 The bundle supplies [supply_of_fconf]'s third hypothesis *)

Lemma fconf_rows boot d0 fab GF i row :
  gfexec_conf boot d0 fab GF →
  gx_prog (gd_g (gf_gd GF)) !! i = Some row →
  ∃ f : nat → pexv6, f 0%nat = boot i ∧
    ∀ n lb, row !! n = Some lb →
      (∀ m, gf_dev GF !! m = Some (i, n) →
            hblk (fab m) (fab (S m)) (row_ws row n) lb (f n) (f (S n)))
      ∧ ((i, n) ∉ gf_dev GF →
         ∀ d, hblk d d (row_ws row n) lb (f n) (f (S n))).
Proof.
  intros (_ & _ & _ & Hc) Hrow.
  destruct (Hc i row Hrow) as (em & dvi & dvo & Hem & Hiff & Hpin & _).
  destruct (hart_conff_states i row (boot i) dvi dvo em Hem) as (f & Hf0 & Hf).
  exists f. split; [done|]. intros n lb Hn.
  destruct (Hf n lb Hn) as [H1 H2]. split.
  - intros m Hm. destruct (Hpin n m Hm) as [Hi Ho].
    by rewrite -Hi -Ho.
  - intros Hnin d.
    have Hnd : ¬ is_dev_block em n.
    { intros Hd. apply Hnin.
      apply (proj1 (Hiff n (lookup_lt_Some _ _ _ Hn))). exact Hd. }
    by destruct (H2 Hnd) as [_ Hall].
Qed.

(** THE COMPOSITION: a bundle plus a fabric-order-respecting interleaving of
    its rows IS an [exec_prog_ok'] supply, and the run starts at [d0]. *)
Theorem fconf_supply (c : cand) (boot : agent → pexv6) (d0 : dev_state)
    (fab : nat → dev_state) (GF : gfexec) (N : nat) :
  gfexec_conf boot d0 fab GF →
  (∀ i, (λ s, es_lb s) <$> filter (λ s, es_ag s = i) (cd_tr c)
        = default [] (gx_prog (gd_g (gf_gd GF)) !! i)) →
  (length (gx_prog (gd_g (gf_gd GF))) ≤ N)%nat →
  (∀ k s, cd_tr c !! k = Some s →
     (es_ag s, tcnt (es_ag s) (take k (cd_tr c))) ∈ gf_dev GF →
     gf_dev GF !! dcnt GF (cd_tr c) k
       = Some (es_ag s, tcnt (es_ag s) (take k (cd_tr c)))) →
  ∃ pst : nat → list pexv6,
    pst 0%nat = boot <$> seq 0 N ∧
    (λ k, fab (dcnt GF (cd_tr c) k)) 0%nat = d0 ∧
    exec_prog_ok' pstep_ev pcls_ev pst
      (λ k, fab (dcnt GF (cd_tr c) k)) (cand_exec c).
Proof.
  intros Hconf Hrows HN Hord.
  destruct (supply_of_fconf c boot fab GF
              (λ i, default [] (gx_prog (gd_g (gf_gd GF)) !! i)) N)
    as (pst & Hpst0 & Hprog).
  - exact Hrows.
  - intros i Hi. apply prog_row_nil. lia.
  - intros i _.
    destruct (gx_prog (gd_g (gf_gd GF)) !! i) as [row|] eqn:E; simpl.
    + exact (fconf_rows boot d0 fab GF i row Hconf E).
    + exists (λ _, boot i). split; [done|].
      intros n lb Hn. by rewrite lookup_nil in Hn.
  - exact Hord.
  - exists pst. split_and!; [done| |done].
    rewrite dcnt_0. by destruct Hconf as (H & _).
Qed.

(* ====================================================================== *)
(** * 8. HULLS

    *** A SECOND DESIGN FINDING. ***  [gf_hull GF cs] filters the fabric
    order by the cut, as the brief asks — but the hull's fabric trace is NOT
    a re-indexing of [fab] unless the cut keeps a PREFIX of the fabric
    order.  Dropping the [m]-th dev block changes the device state every
    LATER dev block starts from, so [fab] cannot be reused and no
    re-indexing of it is available (the hull's device trajectory is a
    different run of the fabric).  [dev_closed] is exactly the condition
    that makes the filtered list a prefix, and then [fab] itself works.
    This is the fabric analogue of [hull_ok]'s rf-closure. *)

Definition gf_hull (GF : gfexec) (cs : list nat) : gfexec :=
  GFExec (gd_hull (gf_gd GF) cs) (filter (gcut cs) (gf_dev GF)).

Definition dclosed (cs : list nat) (l : list geid) : Prop :=
  ∀ m n e e', (m < n)%nat → l !! m = Some e → l !! n = Some e' →
              gcut cs e' = true → gcut cs e = true.

Lemma dclosed_cons cs e l : dclosed cs (e :: l) → dclosed cs l.
Proof.
  intros H m n x y Hlt Hm Hn Hc.
  by apply (H (S m) (S n) x y ltac:(lia) Hm Hn Hc).
Qed.

Lemma filter_none_nil (l : list geid) (cs : list nat) :
  (∀ n e, l !! n = Some e → gcut cs e = false) → filter (gcut cs) l = [].
Proof.
  induction l as [|e l IH]; intros H; [done|].
  rewrite filter_cons.
  have He : gcut cs e = false := H 0%nat e eq_refl.
  case_decide as Hd.
  { exfalso. rewrite He in Hd. exact Hd. }
  apply IH. intros n x Hx. by apply (H (S n) x).
Qed.

(** UNDER [dclosed] THE FILTERED FABRIC ORDER IS A PREFIX — so its [n]-th
    entry is the ORIGINAL [n]-th entry, and [fab] transports unchanged. *)
Lemma dclosed_prefix cs l :
  dclosed cs l → filter (gcut cs) l `prefix_of` l.
Proof.
  induction l as [|e l IH]; intros Hdc; [apply prefix_nil|].
  rewrite filter_cons. case_decide as Hd.
  - apply prefix_cons. by apply IH, (dclosed_cons cs e).
  - have He : gcut cs e = false.
    { destruct (gcut cs e) eqn:E; [|done]. exfalso.
      by apply Hd, Is_true_true_2. }
    rewrite (filter_none_nil l cs); [apply prefix_nil|].
    intros n x Hx. destruct (gcut cs x) eqn:E; [|done]. exfalso.
    rewrite (Hdc 0%nat (S n) e x ltac:(lia) eq_refl Hx E) in He. discriminate.
Qed.

Lemma gf_hull_dev_lookup GF cs n e :
  dclosed cs (gf_dev GF) →
  gf_dev (gf_hull GF cs) !! n = Some e → gf_dev GF !! n = Some e.
Proof.
  intros Hdc Hn. simpl in Hn.
  destruct (dclosed_prefix cs (gf_dev GF) Hdc) as [t Ht].
  rewrite Ht. by apply lookup_app_l_Some.
Qed.

Lemma gf_hull_dev_cut GF cs n e :
  gf_dev (gf_hull GF cs) !! n = Some e → gcut cs e = true.
Proof.
  intros Hn. simpl in Hn.
  have Hin : e ∈ filter (gcut cs) (gf_dev GF)
    by (eapply elem_of_list_lookup_2).
  apply elem_of_list_filter in Hin as [Hc _].
  by apply Is_true_true.
Qed.

(** CONSISTENCY RESTRICTS. *)
Theorem gf_hull_consistent GF cs :
  gfexec_consistent GF → hull_ok (gd_g (gf_gd GF)) cs →
  dclosed cs (gf_dev GF) →
  gfexec_consistent (gf_hull GF cs).
Proof.
  intros [Hc Hdev] Hok Hdc. split.
  - by apply hull_deps_consistent.
  - intros a b (n & Ha & Hb).
    have Hca : gcut cs a = true := gf_hull_dev_cut GF cs n a Ha.
    have Hcb : gcut cs b = true := gf_hull_dev_cut GF cs (S n) b Hb.
    have Hmo : gmo_lt (gd_g (gf_gd GF)) a b.
    { apply Hdev. exists n. split.
      - by apply (gf_hull_dev_lookup GF cs n a).
      - by apply (gf_hull_dev_lookup GF cs (S n) b). }
    change (gd_g (gf_gd (gf_hull GF cs))) with (gx_hull (gd_g (gf_gd GF)) cs).
    apply gxh_gmo_lt; [|by split_and!].
    destruct Hc as ((Hwf & _ & _ & _) & _ & _). by destruct Hwf as (Hnd & _ & _).
Qed.

(** *** THE CONFORMANCE RESTRICTION — OBLIGATIONS, NOT ADMITTED.
    [gfexec_conf boot d0 fab GF → hull_ok … → dclosed cs (gf_dev GF) →
     gfexec_conf boot d0 fab (gf_hull GF cs)] needs, and ONLY needs:

    (O1) [hemitf_prefix] — [WeakRvwmoConf.hemit_prefix]'s induction for
         [hemitf] (same three cases, the tail's [es'] replaced by its
         prefix); giving [hart_conff i (take c row) … em'] with
         [em_items em' `prefix_of` em_items em].
    (O2) [hemitf_ren] — [WeakRvwmoConf.hemit_ren]'s induction for [hemitf];
         [em_dev] is already known renaming-blind ([em_dev_ren] above), so
         [is_dev_block (em_ren π em') k ↔ is_dev_block em' k] is free.
    (O3) [em_dev] under an ITEM PREFIX: [hemit_prefix] cuts at a BLOCK
         boundary, so for [k] below the cut every item of block [k] is in
         the prefix and every tag in the dropped tail is [≥] the cut.  The
         missing ingredient is TAG MONOTONICITY of [hemitf] (every tag in
         the item list of [hemitf … k0 …] is [≥ k0]), a two-line induction;
         with it, [em_dev false k (es1 ++ es2) = em_dev false k es1] for
         [k] below the cut, by [em_dev]'s [app] lemma.
    (O4) the [gf_dev] membership clause: [(i,k) ∈ filter (gcut cs) (gf_dev GF)]
         iff [(i,k) ∈ gf_dev GF ∧ gcut cs (i,k) = true], and [gcut] holds
         exactly for [k] below the cut — so the iff of (O3) matches.
    (O5) the [fab] clause: unchanged, by [gf_hull_dev_lookup] (the filtered
         list's [n]-th entry IS the original's), which is proved above.
    Nothing here needs a new mechanism; it is bookkeeping of the same kind
    as [gdexec_qconf_hull].  Priced as a follow-up rather than landed. *)

(** *** THE [cycle_kill] MIRROR — likewise an obligation, not a hole.
    [WeakRvwmoLinInd]'s induction transports verbatim once the conformance
    restriction above lands: [cycle_kill_F] is [cycle_kill] with [RacyD]/
    [gdexec_qconf] replaced by [RacyF]/[gfexec_conf] and [gd_hull] by
    [gf_hull], its [t2lin_aux] needs exactly (a) consistency restricts
    ([gf_hull_consistent], proved), (b) conformance restricts (O1–O5), and
    (c) the event-count decrease ([WeakRvwmoLinInd.hull_events_lt], which is
    about the GRAPH only and is unchanged). *)

(* ====================================================================== *)
(** * 9. THE AUDIT *)

Print Assumptions em_dev_devfree.
Print Assumptions em_dev_ren.
Print Assumptions hemit_hemitf.
Print Assumptions hemitf_states.
Print Assumptions hart_conff_states.
Print Assumptions hart_conf_no_gap.
Print Assumptions RF_acyclic.
Print Assumptions topo_linearizes_F.
Print Assumptions lin_extF_dev_before.
Print Assumptions topo_exists_F.
Print Assumptions gfexec_conf_of_qconf.
Print Assumptions supply_of_fconf.
Print Assumptions fconf_supply.
Print Assumptions gf_hull_consistent.
