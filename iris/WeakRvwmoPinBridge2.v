(** * WeakRvwmoPinBridge2.v — THE INDUCTION THAT DISCHARGES
      [WeakRvwmoPinBridge.checker_taint_sub_prov]

    [WeakRvwmoPinBridge] §3 states ONE hypothesis and proves the three
    witness classes from it: the static checker's taint walk is a
    SUB-approximation of the emission's provenance.  This file proves that
    hypothesis.  Nothing here is admitted and nothing is axiomatised; what
    it costs instead is a SITE ORACLE that is no longer a bare parameter
    but a DEFINED relation ([psites]), and the two structural facts about
    the emission that relation packages.

    ------------------------------------------------------------------
    THE SHAPE OF THE ARGUMENT.

    Both sides run the same decoder ([KernelPinsDef.taint_step] is
    [deps_rd]/[deps_rd2] of [WeakDeps.deps_of_bits]; [WeakRvwmoConf.dstep]'s
    [LRegW] arm is [dsrcs_pos] of the list [WeakEvLang.erw_of] computes from
    [deps_of_ib] of the SAME announced word).  What was missing is the
    induction that lines an emission's ITEM LIST up with the checker's PC
    walk.  It is supplied here by ONE inductive relation:

      [reaches own stop s g s'] — "from walk state [s], the emission emits
      the item group [g], one group per instruction, following the
      checker's own fall-through successor [wstep], and arrives at [s']
      whose pc is [stop]".

    Its step carries exactly two obligations per instruction, both
    DECIDABLE and both [vm_compute]-checkable at a concrete pc:

      (a) [grp_okb pc g1 g2 = true] — the group's register writes are the
          DECODED ones.  Every [LRegW rd srcs] of the group is at a
          destination the decoder names ([deps_rd]/[deps_rd2] at [pc]) with
          [srcs] a SUPERSET of the decoded sources — which is DEC-7's
          [erw_srcs_covers] read as a boolean, and which is exactly what
          [WeakEvLang.erw_of] emits (it fires [ERWreg rd (erw_srcs …)] ONLY
          where the Sail register matches the decoded [rd], and [erw_srcs]
          only ADDS sources).  Everything else in the group is
          provenance-neutral: no other label arm of [dstep] touches
          [ds_prov].

      (b) [taint_sub (ps_t s') (taint_step (ps_t s) (ps_pc s))] — the walk's
          successor taint is the decoded update.  [wstep_taint] shows the
          only alternative [pstep] ever takes is "the taint is carried
          unchanged" (the [FLjump]/[FLret] arms), and [taint_step_id] says
          that agrees whenever the pc's decoded role writes no register —
          which is the case for [c.j] / [jal x0] / [ret].

    The INVARIANT carried across the induction is [inv_ok j s t]: every
    register the checker calls tainted has [j] in the emission's [dprov].
    It is preserved because the checker's TAINTING of [rd] is matched by
    [dstep] overwriting [dprov rd] with the sources' positions (⊇ the
    decoded sources' positions, by (a)), and the checker's UNTAINTING of a
    written register only WEAKENS the antecedent — the claim is a ⊆, so an
    emission that keeps more provenance than the checker keeps taint is
    fine.  This is why the direction is the safe one.

    THE BASE CASE is [ld_carrier_sound]: the load at [pcL] emits its own
    destination-register write with [DLdRes] among the sources, and
    [dstep]'s [LLoad] arm has just put the load's row position [j] into
    [ds_ld], so [dprov rd] contains [j].  That is the [LRegW 15 [DLdRes;
    …]] [WeakRvwmoAdm.la_stretch_regw] COMPUTES on real image bytes.

    ------------------------------------------------------------------
    WHAT IS AND IS NOT PROVED, precisely.

    PROVED: [checker_taint_sub_prov es psites pcL j own] for the site
    oracle [psites] defined here, from the two emission facts above
    ([base_ok] for the load's own group, [reaches] for the stretch).  The
    theorem is [checker_taint_sub_prov_proof]; [pin_seg_pin'] restates
    [WeakRvwmoPinBridge.pin_seg_pin] with the hypothesis discharged.

    NOT PROVED HERE (the residual, stated so it cannot hide): that a
    [pstep_ev] run's items ARE so grouped — i.e. "the items between two
    consecutive [LInstr] boundaries are exactly [erw_of]'s outputs at the
    announced word, and the announced word at the [n]th group is
    [kword pc_n] for the pc the checker walks to".  That is a statement
    about [WeakEvInst.pstep_ev]'s announce discipline and about the image
    agreeing with the fetched bits; §6 EXHIBITS both halves on the one
    stretch of the tree that is computed from real image bytes
    ([WeakRvwmoAdm]'s spin-load stretch), by [vm_compute], so the
    obligations are not vacuous — but the general form is left as the
    honest residual, [R-3] in the file's own numbering.

    NOTE ON THE FALL-THROUGH PATH.  [checker_taint_sub_prov] speaks of
    [fwalk], the FALL-THROUGH walk, so [reaches] follows [pstep]'s FIRST
    successor.  The all-paths [pdfs] check is a separate conjunct of
    [pinnedb] and is not needed here: the hypothesis is per-path, and the
    path is the one the emission realizes. *)

From Stdlib.ssr Require Import ssreflect.
From Stdlib Require Import Bool ZArith.
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
Require Import WeakRvwmoGraph.
Require Import WeakPromise.
Require Import WeakEvLang.
Require Import WeakRvwmoConf.
Require Import WeakRvwmoKillArms.
Require Import WeakRvwmoGlue.
Require Import RiscvLang.
Require Import WeakLang.
Require Import WeakRvwmoAdm.
Require Import KernelSitesDef.
Require Import KernelPinsDef.
Require Import WeakRvwmoPinBridge.
From Kernel Require KernelSyms.

(* ====================================================================== *)
(** * 1. THE TAINT SET, AS A PREDICATE

    [taint_mem] is a boolean membership over a duplicate-tolerant list; the
    two facts the induction needs are how [taint_del] and [taint_upd1]
    change it. *)

Lemma taint_del_mem (r rd : wreg) (t : list wreg) :
  taint_mem r (taint_del rd t) = true → r ≠ rd ∧ taint_mem r t = true.
Proof.
  induction t as [|x t IH]; [done|]. simpl.
  destruct (Nat.eqb x rd) eqn:Hx.
  - intros H. destruct (IH H) as [H1 H2]. split; [done|].
    rewrite orb_true_iff. by right.
  - simpl. rewrite orb_true_iff. intros [Hxr|H].
    + apply Nat.eqb_eq in Hxr. subst x. apply Nat.eqb_neq in Hx.
      split; [done|]. rewrite orb_true_iff. left. apply Nat.eqb_refl.
    + destruct (IH H) as [H1 H2]. split; [done|].
      rewrite orb_true_iff. by right.
Qed.

(** THE ONE INVERSION: a register tainted AFTER a destination update is
    either THE destination, updated from a tainted source, or a register the
    update did not touch and which was tainted BEFORE. *)
Lemma taint_upd1_inv (t : list wreg) (rd : wreg) (dec : list dsrc) (r : wreg) :
  taint_mem r (taint_upd1 t (Some (rd, dec))) = true →
  (r = rd ∧ srcs_tainted t dec = true) ∨ (r ≠ rd ∧ taint_mem r t = true).
Proof.
  rewrite /taint_upd1. destruct (srcs_tainted t dec) eqn:Hs.
  - destruct (taint_mem rd t) eqn:Hrd.
    + intros H. destruct (decide (r = rd)) as [->|Hne];
        [left; by split|right; by split].
    + simpl. rewrite orb_true_iff. intros [H|H].
      * apply Nat.eqb_eq in H. left. by split.
      * destruct (decide (r = rd)) as [->|Hne];
          [left; by split|right; by split].
  - intros H. right. by apply taint_del_mem.
Qed.

(** THE UNFOLDING EQUATION, stated as a lemma rather than reached by
    [simpl].  NEVER [simpl] a goal that mentions [krole pc] / [kw pc] at a
    VARIABLE [pc]: [kw] bottoms out in [KernelInstrs.kernel_bytes !! a], and
    [simpl] will try to unfold the whole image literal (the file then
    "compiles" forever with no error — [coqc -time]'s last line is the
    tactic).  Every reduction below is by [reflexivity], by a stated
    equation, or by [cbv beta iota zeta], which cannot delta-unfold the
    image. *)
Lemma taint_step_unfold (t : list wreg) (pc : Z) :
  taint_step t pc
  = taint_upd1 (taint_upd1 t (deps_rd (krole pc))) (deps_rd2 (krole pc)).
Proof. reflexivity. Qed.

(** ... and the update is the IDENTITY when the decoder names no
    destination, which is what makes the [FLjump] / [FLret] arms of [pstep]
    (which carry the taint through unchanged) agree with [taint_step]. *)
Lemma taint_step_id (t : list wreg) (pc : Z) :
  deps_rd (krole pc) = None → deps_rd2 (krole pc) = None →
  taint_step t pc = t.
Proof. intros H1 H2. by rewrite taint_step_unfold H1 H2. Qed.

Definition taint_sub (t t' : list wreg) : Prop :=
  ∀ r, taint_mem r t = true → taint_mem r t' = true.

Lemma taint_sub_refl t : taint_sub t t.
Proof. by intros r Hr. Qed.

(* ====================================================================== *)
(** * 2. THE INVARIANT, AND WHAT ONE ITEM DOES TO IT *)

(** THE INVARIANT: every register the checker calls tainted carries the row
    position [j] in the emission's provenance. *)
Definition inv_ok (j : nat) (s : dstate) (t : list wreg) : Prop :=
  ∀ r : wreg, taint_mem r t = true → j ∈ dprov s r.

(** [dprov] after a register-write item. *)
Lemma dprov_regw_eq (s : dstate) (rd : wreg) (srcs : list dsrc)
    (k : option nat) :
  dprov (dstep s (LRegW rd srcs, k)).1 rd = dsrcs_pos s srcs.
Proof. rewrite /dstep /dprov /=. by rewrite lookup_insert. Qed.

Lemma dprov_regw_ne (s : dstate) (rd : wreg) (srcs : list dsrc)
    (k : option nat) (r : wreg) :
  r ≠ rd → dprov (dstep s (LRegW rd srcs, k)).1 r = dprov s r.
Proof. intros Hne. rewrite /dstep /dprov /=. by rewrite lookup_insert_ne. Qed.

(** EVERY OTHER LABEL ARM LEAVES [ds_prov] ALONE — [LInstr] resets [ds_ld],
    [LCtrl] appends to [ds_ctl], the memory arms push a row position onto
    [ds_ld] or emit edges, and none of them writes a register. *)
Definition prov_neutralb (it : eitem) : bool :=
  match it.1 with LRegW _ _ => false | _ => true end.

Lemma dstep_prov_neutral (s : dstate) (it : eitem) :
  prov_neutralb it = true → ds_prov (dstep s it).1 = ds_prov s.
Proof.
  destruct it as [l k]. destruct l; destruct k as [k0|]; intros H;
    first [ discriminate H | reflexivity ].
Qed.

Lemma dprov_neutral_item (s : dstate) (it : eitem) (r : wreg) :
  prov_neutralb it = true → dprov (dstep s it).1 r = dprov s r.
Proof. intros H. by rewrite /dprov (dstep_prov_neutral s it H). Qed.

Lemma inv_neutral (j : nat) (s : dstate) (t : list wreg) (it : eitem) :
  prov_neutralb it = true → inv_ok j s t → inv_ok j (dstep s it).1 t.
Proof.
  intros Hn Hinv r Hr. rewrite (dprov_neutral_item s it r Hn). by apply Hinv.
Qed.

Lemma inv_neutral_run (j : nat) (s : dstate) (t : list wreg) (g : list eitem) :
  forallb prov_neutralb g = true → inv_ok j s t → inv_ok j (ds_run s g) t.
Proof.
  revert s. induction g as [|it g IH]; intros s Hg Hinv; [done|].
  simpl in Hg. apply andb_prop in Hg as [H1 H2].
  rewrite ds_run_cons. apply IH; [done|]. by apply inv_neutral.
Qed.

(* ====================================================================== *)
(** * 3. DEC-7 AS A BOOLEAN: the emitted sources COVER the decoded ones *)

Definition dsubb (dec srcs : list dsrc) : bool :=
  forallb (λ x, existsb (λ y, bool_decide (x = y)) srcs) dec.

Lemma existsb_dsrc_elem (x : dsrc) (l : list dsrc) :
  existsb (λ y, bool_decide (x = y)) l = true → x ∈ l.
Proof.
  induction l as [|y l IH]; [done|]. simpl. rewrite orb_true_iff.
  intros [Hy|Hl].
  - apply bool_decide_eq_true in Hy as ->. apply elem_of_list_here.
  - apply elem_of_list_further, IH, Hl.
Qed.

Lemma dsubb_elem (dec srcs : list dsrc) (x : dsrc) :
  dsubb dec srcs = true → x ∈ dec → x ∈ srcs.
Proof.
  rewrite /dsubb. induction dec as [|y dec IH]; [by intros _ ?%elem_of_nil|].
  simpl. intros [H1 H2]%andb_prop [->|Hx]%elem_of_cons.
  - by apply existsb_dsrc_elem.
  - by apply IH.
Qed.

(** A TAINTED DECODED SOURCE IS A POSITION OF THE EMITTED SOURCE LIST. *)
Lemma dsrcs_pos_of_tainted (j : nat) (s : dstate) (t : list wreg)
    (dec srcs : list dsrc) :
  inv_ok j s t → dsubb dec srcs = true → srcs_tainted t dec = true →
  j ∈ dsrcs_pos s srcs.
Proof.
  intros Hinv Hsub Ht.
  destruct (srcs_tainted_reg t dec Ht) as (r & Hr & Htr).
  eapply dsrcs_pos_reg; [by eapply dsubb_elem|by apply Hinv].
Qed.

(** ONE INSTRUCTION'S REGISTER WRITE, both sides at once. *)
Lemma regw_step (j : nat) (s : dstate) (t : list wreg) (rd : wreg)
    (dec srcs : list dsrc) (k : option nat) :
  inv_ok j s t → dsubb dec srcs = true →
  inv_ok j (dstep s (LRegW rd srcs, k)).1 (taint_upd1 t (Some (rd, dec))).
Proof.
  intros Hinv Hsub r Hr.
  apply taint_upd1_inv in Hr as [[-> Hs]|[Hne Hr]].
  - rewrite dprov_regw_eq. by eapply dsrcs_pos_of_tainted.
  - rewrite (dprov_regw_ne _ _ _ _ _ Hne). by apply Hinv.
Qed.

(* ====================================================================== *)
(** * 4. ONE INSTRUCTION'S ITEM GROUP

    [regw_seg rd dec g] — the group [g] realizes the destination update
    [(rd, dec)]: provenance-neutral items, then the [LRegW] at [rd] whose
    emitted sources cover [dec], then nothing that writes a register at
    all.  [realizesb None g] is "no register write in [g]", which is what
    [erw_of] emits at a pc whose role names no destination. *)

Fixpoint regw_seg (rd : wreg) (dec : list dsrc) (g : list eitem) : bool :=
  match g with
  | [] => false
  | it :: g' =>
      match it.1 with
      | LRegW rd' srcs =>
          Nat.eqb rd' rd && dsubb dec srcs && forallb prov_neutralb g'
      | _ => regw_seg rd dec g'
      end
  end.

Definition realizesb (d : option (wreg * list dsrc)) (g : list eitem) : bool :=
  match d with
  | None => forallb prov_neutralb g
  | Some (rd, dec) => regw_seg rd dec g
  end.

Lemma regw_seg_sound (j : nat) (rd : wreg) (dec : list dsrc)
    (g : list eitem) (s : dstate) (t : list wreg) :
  regw_seg rd dec g = true → inv_ok j s t →
  inv_ok j (ds_run s g) (taint_upd1 t (Some (rd, dec))).
Proof.
  revert s. induction g as [|it g IH]; intros s Hg Hinv; [done|].
  rewrite ds_run_cons. destruct it as [l k]; destruct l; simpl in Hg;
    (* the provenance-neutral arms: step and recurse *)
    try (apply IH; [exact Hg|apply inv_neutral; [reflexivity|exact Hinv]]).
  (* the [LRegW] arm *)
  apply andb_prop in Hg as [Hg Hn]. apply andb_prop in Hg as [Hrd Hsub].
  apply Nat.eqb_eq in Hrd as ->.
  apply inv_neutral_run; [exact Hn|]. by apply regw_step.
Qed.

Lemma realizesb_sound (j : nat) (d : option (wreg * list dsrc))
    (g : list eitem) (s : dstate) (t : list wreg) :
  realizesb d g = true → inv_ok j s t →
  inv_ok j (ds_run s g) (taint_upd1 t d).
Proof.
  destruct d as [[rd dec]|]; simpl;
    [apply regw_seg_sound|apply inv_neutral_run].
Qed.

(** THE GROUP TEST AT A PC: the two decoded destinations, in the order
    [taint_step] applies them ([deps_rd] first, then [deps_rd2] — which for
    a Zicsr access reads the CSR pseudo-register the first arm just
    wrote, so the order is not cosmetic). *)
Definition grp_okb (pc : Z) (g1 g2 : list eitem) : bool :=
  realizesb (deps_rd (krole pc)) g1 && realizesb (deps_rd2 (krole pc)) g2.

Lemma grp_sound (j : nat) (pc : Z) (g1 g2 : list eitem)
    (s : dstate) (t : list wreg) :
  grp_okb pc g1 g2 = true → inv_ok j s t →
  inv_ok j (ds_run s (g1 ++ g2)) (taint_step t pc).
Proof.
  intros [H1 H2]%andb_prop Hinv. rewrite ds_run_app taint_step_unfold.
  apply realizesb_sound; [exact H2|].
  apply realizesb_sound; [exact H1|exact Hinv].
Qed.

(* ====================================================================== *)
(** * 5. THE WALK, WITH THE EMISSION ALONGSIDE *)

(** The checker's FALL-THROUGH successor — [fwalk]'s own step. *)
Definition wstep (own : bool) (s : pstate) : option pstate :=
  match pstep own s with Some (s' :: _) => Some s' | _ => None end.

(** THE ALIGNMENT.  [reaches own stop s g s'] — from walk state [s] the
    emission emits the groups of [g], one per instruction along the
    checker's fall-through path, and arrives at [s'] sitting at [stop]. *)
Inductive reaches (own : bool) (stop : Z) : pstate → list eitem → pstate → Prop :=
| RC_stop (s : pstate) :
    (ps_pc s =? stop)%Z = true → reaches own stop s [] s
| RC_step (s : pstate) (g1 g2 : list eitem) (s' : pstate)
          (mid : list eitem) (s'' : pstate) :
    (ps_pc s =? stop)%Z = false →
    grp_okb (ps_pc s) g1 g2 = true →
    wstep own s = Some s' →
    taint_sub (ps_t s') (taint_step (ps_t s) (ps_pc s)) →
    reaches own stop s' mid s'' →
    reaches own stop s (g1 ++ g2 ++ mid) s''.

Lemma wstep_pstep (own : bool) (s s' : pstate) :
  wstep own s = Some s' → ∃ l, pstep own s = Some (s' :: l).
Proof.
  rewrite /wstep. destruct (pstep own s) as [[|s0 l]|] eqn:Hp;
    intros H; try discriminate H. injection H as <-. by exists l.
Qed.

Lemma fwalk_S (fuel : nat) (own : bool) (stop : Z) (s : pstate) :
  fwalk (S fuel) own stop s
  = if (ps_pc s =? stop)%Z then Some (ps_t s)
    else match pstep own s with
         | Some (s' :: _) => fwalk fuel own stop s'
         | _ => None
         end.
Proof. reflexivity. Qed.

(** (i) THE WALK IS [fwalk]'S.  Both recursions branch on the same
    [ps_pc =? stop] test and take the same first successor, so an arriving
    [reaches] pins [fwalk]'s answer — for EVERY fuel, which is why the
    statement quantifies over the fuel rather than mentioning [pin_fuel]
    (a [destruct] on [Z.to_nat 64] is not what one wants in a proof). *)
Lemma reaches_fwalk (own : bool) (stop : Z) (s : pstate) (g : list eitem)
    (s'' : pstate) :
  reaches own stop s g s'' →
  ∀ (fuel : nat) (t : list wreg), fwalk fuel own stop s = Some t →
  t = ps_t s''.
Proof.
  induction 1 as [s Hs|s g1 g2 s' mid s'' Hne Hg Hw Hsub Hr IH];
    intros [|fuel] t Hf; try (by discriminate Hf).
  - rewrite fwalk_S Hs in Hf. cbv iota in Hf. injection Hf as ->.
    reflexivity.
  - destruct (wstep_pstep own s s' Hw) as [l Hp].
    rewrite fwalk_S Hne Hp in Hf. cbv iota in Hf. exact (IH _ _ Hf).
Qed.

(** (ii) THE INVARIANT TRAVELS.  This is the induction the hypothesis was
    waiting for. *)
Lemma reaches_inv (j : nat) (own : bool) (stop : Z) (s : pstate)
    (g : list eitem) (s'' : pstate) :
  reaches own stop s g s'' →
  ∀ d0, inv_ok j d0 (ps_t s) → inv_ok j (ds_run d0 g) (ps_t s'').
Proof.
  induction 1 as [s Hs|s g1 g2 s' mid s'' Hne Hg Hw Hsub Hr IH];
    intros d0 Hinv; [by rewrite ds_run_nil|].
  rewrite app_assoc ds_run_app. apply IH.
  intros r Hr'. apply (grp_sound j _ _ _ _ _ Hg Hinv). by apply Hsub.
Qed.

(** (iii) THE SUCCESSOR'S TAINT.  [pstep] takes the decoded update on every
    arm but the two that carry the taint through unchanged. *)
Lemma wstep_taint (own : bool) (s s' : pstate) :
  wstep own s = Some s' →
  ps_t s' = taint_step (ps_t s) (ps_pc s) ∨ ps_t s' = ps_t s.
Proof.
  intros [l Hp]%wstep_pstep. revert Hp. rewrite /pstep. cbv beta zeta.
  destruct ((ps_pc s <? text_lo) || (text_hi <=? ps_pc s))%Z;
    cbv beta iota; [by intros H; discriminate H|].
  destruct (w_is_fence (kw (ps_pc s)));
    cbv beta iota; [by intros H; discriminate H|].
  destruct (role_is_store (krole (ps_pc s))); cbv beta iota.
  - destruct (srcs_tainted (ps_t s) (deps_addr (krole (ps_pc s)))
              || srcs_tainted (ps_t s) (deps_vsrc (krole (ps_pc s))));
      cbv beta iota; [by intros H; discriminate H|].
    destruct (own && stack_store (krole (ps_pc s)));
      cbv beta iota; [|by intros H; discriminate H].
    intros H. inversion H; subst. left; reflexivity.
  - destruct (kflow_of (ps_pc s)) as [ | tgt | tgt | tgt | | ]; cbv beta iota.
    + intros H. inversion H; subst. left; reflexivity.
    + destruct (srcs_tainted (ps_t s) (deps_ctrl (krole (ps_pc s))));
        cbv beta iota; [by intros H; discriminate H|].
      intros H. inversion H; subst. left; reflexivity.
    + intros H. inversion H; subst. right; reflexivity.
    + destruct (Nat.ltb (length (ps_rs s)) pin_depth);
        cbv beta iota; [|by intros H; discriminate H].
      intros H. inversion H; subst. left; reflexivity.
    + destruct (ps_rs s) as [|a rs'];
        cbv beta iota; [by intros H; discriminate H|].
      intros H. inversion H; subst. right; reflexivity.
    + by intros H; discriminate H.
Qed.

(** ... so the alignment's taint obligation is DISCHARGED at every pc whose
    decoded role names no destination — [c.j], [jal x0], [ret] — and is the
    identity elsewhere. *)
Lemma wstep_taint_sub (own : bool) (s s' : pstate) :
  wstep own s = Some s' →
  (deps_rd (krole (ps_pc s)) = None ∧ deps_rd2 (krole (ps_pc s)) = None)
  ∨ ps_t s' = taint_step (ps_t s) (ps_pc s) →
  taint_sub (ps_t s') (taint_step (ps_t s) (ps_pc s)).
Proof.
  intros Hw [[H1 H2]|Heq].
  - rewrite (taint_step_id _ _ H1 H2).
    destruct (wstep_taint own s s' Hw) as [-> | ->];
      [rewrite (taint_step_id _ _ H1 H2)|]; apply taint_sub_refl.
  - rewrite Heq. apply taint_sub_refl.
Qed.

(* ====================================================================== *)
(** * 6. THE BASE CASE: the load's own destination register

    [pin_start]'s taint is [[rd]], [rd] the load's destination.  The
    emission's matching fact is the [LRegW rd srcs] with [DLdRes ∈ srcs]
    that the load instruction emits AFTER the [LLoad] item tagged with the
    row position [j] — [dstep] put [j] into [ds_ld] there, and [DLdRes]'s
    denotation IS [ds_ld]. *)

Lemma has_ldres_elem (l : list dsrc) : has_ldres l = true → DLdRes ∈ l.
Proof.
  induction l as [|x l IH]; [done|]. destruct x as [r|]; simpl.
  - intros H. by apply elem_of_list_further, IH.
  - intros _. apply elem_of_list_here.
Qed.

Lemma dsrcs_pos_ldres (s : dstate) (xs : list dsrc) (j : nat) :
  DLdRes ∈ xs → j ∈ ds_ld s → j ∈ dsrcs_pos s xs.
Proof.
  intros Hx Hj. rewrite /dsrcs_pos. apply elem_of_list_join.
  exists (dsrc_pos s DLdRes). split; [exact Hj|].
  apply elem_of_list_fmap. by exists DLdRes.
Qed.

(** [ds_ld] only grows — except at [LInstr], which is exactly the
    instruction boundary the load's own group does not cross. *)
Definition keeps_ldb (it : eitem) : bool :=
  match it.1 with LInstr => false | _ => true end.

Lemma dstep_ld_mono (s : dstate) (it : eitem) (i : nat) :
  keeps_ldb it = true → i ∈ ds_ld s → i ∈ ds_ld (dstep s it).1.
Proof.
  destruct it as [l k]. destruct l; destruct k as [k0|]; intros H Hi;
    first [ discriminate H | exact Hi | by apply elem_of_list_further ].
Qed.

(** No later item of the group overwrites the carrier. *)
Definition no_regw_of (rd : wreg) (g : list eitem) : bool :=
  forallb (λ it, match it.1 with
                 | LRegW r _ => negb (Nat.eqb r rd)
                 | _ => true
                 end) g.

Lemma dprov_stable (rd : wreg) (g : list eitem) (s : dstate) :
  no_regw_of rd g = true → dprov (ds_run s g) rd = dprov s rd.
Proof.
  revert s. induction g as [|it g IH]; intros s Hg; [done|].
  simpl in Hg. apply andb_prop in Hg as [H1 H2].
  rewrite ds_run_cons (IH _ H2).
  destruct it as [l k]; destruct l; simpl in H1;
    try (apply dprov_neutral_item; reflexivity).
  apply negb_true_iff, Nat.eqb_neq in H1.
  apply dprov_regw_ne. by intros ->.
Qed.

(** THE LOAD'S GROUP, as a boolean test. *)
Fixpoint ld_carrier (rd : wreg) (g : list eitem) : bool :=
  match g with
  | [] => false
  | it :: g' =>
      match it.1 with
      | LRegW rd' srcs =>
          Nat.eqb rd' rd && has_ldres srcs && no_regw_of rd g'
      | LInstr => false
      | _ => ld_carrier rd g'
      end
  end.

Lemma ld_carrier_sound (j : nat) (rd : wreg) (g : list eitem) (s : dstate) :
  ld_carrier rd g = true → j ∈ ds_ld s → j ∈ dprov (ds_run s g) rd.
Proof.
  revert s. induction g as [|it g IH]; intros s Hg Hj; [done|].
  rewrite ds_run_cons. destruct it as [l k]; destruct l; simpl in Hg;
    try discriminate;
    try (apply IH; [exact Hg|apply dstep_ld_mono; [reflexivity|exact Hj]]).
  apply andb_prop in Hg as [Hg Hn]. apply andb_prop in Hg as [Hrd Hld].
  apply Nat.eqb_eq in Hrd as ->.
  rewrite (dprov_stable _ _ _ Hn) dprov_regw_eq.
  by apply dsrcs_pos_ldres; [apply has_ldres_elem|].
Qed.

(** THE ITEM THAT PUTS THE LOAD'S OWN ROW POSITION INTO [ds_ld] — the
    three read-carrying label arms, stated once. *)
Definition ld_item (j : nat) (it : eitem) : Prop :=
  ∀ s : dstate, j ∈ ds_ld (dstep s it).1.

Lemma ld_item_load (j : nat) (aq lat : bool) (b : Z)
    (tvs : list (nat * bv 8)) (asrc : list dsrc) :
  ld_item j (LLoad aq lat b tvs asrc, Some j).
Proof. intros s. apply elem_of_list_here. Qed.

Lemma ld_item_exload (j : nat) (aq : bool) (b : Z)
    (tvs : list (nat * bv 8)) (asrc : list dsrc) :
  ld_item j (LExLoad aq b tvs asrc, Some j).
Proof. intros s. apply elem_of_list_here. Qed.

Lemma ld_item_rmw (j : nat) (aq rl : bool) (b : Z)
    (tvs : list (nat * bv 8)) (dat : list (bv 8)) (asrc vsrc : list dsrc) :
  ld_item j (LRmw aq rl b tvs dat asrc vsrc, Some j).
Proof. intros s. apply elem_of_list_here. Qed.

(** THE BASE FACT the top-level theorem consumes: the emission's prefix up
    to (and including) the load's own group already has [j] in the
    provenance of everything [pin_start]'s taint names. *)
Lemma base_ok (j : nat) (pcL : Z) (pre0 g : list eitem) (rd : wreg)
    (lit : eitem) :
  load_rd pcL = Some rd →
  ld_item j lit →
  ld_carrier rd g = true →
  inv_ok j (ds_run ds_init (pre0 ++ lit :: g)) (pin_t0 pcL).
Proof.
  intros Hrd Hlit Hg r Hr. rewrite /pin_t0 Hrd in Hr. simpl in Hr.
  rewrite orb_false_r in Hr. apply Nat.eqb_eq in Hr. subst r.
  rewrite ds_run_app ds_run_cons.
  apply ld_carrier_sound; [exact Hg|apply Hlit].
Qed.

(* ====================================================================== *)
(** * 7. THE HYPOTHESIS, DISCHARGED *)

Section Discharge.

  Context (pcL : Z) (j : nat) (own : bool).
  (** The emission's prefix up to and including the load's own item group.
      Everything after it is walk-aligned. *)
  Context (base : list eitem).

  (** THE SITE ORACLE, no longer a parameter: "the item [it] is reached
      after the prefix [pre]" means [pre] is [base] followed by the groups
      the checker's fall-through walk emitted on its way to [pc']. *)
  Definition psites (pre : list eitem) (_ : eitem) (pc' : Z) : Prop :=
    ∃ (mid : list eitem) (s : pstate),
      pre = base ++ mid ∧ reaches own pc' (pin_start pcL) mid s.

  Theorem checker_taint_sub_prov_proof (es : list eitem) :
    inv_ok j (ds_run ds_init base) (pin_t0 pcL) →
    checker_taint_sub_prov es psites pcL j own.
  Proof.
    intros Hbase pre it post pc' t r Hes Hsite Hfw Ht.
    destruct Hsite as (mid & s & -> & Hre).
    rewrite ds_run_app.
    apply (reaches_inv j own pc' _ _ _ Hre _ Hbase).
    rewrite -(reaches_fwalk own pc' _ _ _ Hre pin_fuel t Hfw). exact Ht.
  Qed.

End Discharge.

(** [pin_seg_pin], WITH THE HYPOTHESIS GONE.  Same conclusion, same
    conformance and row premises; where [WeakRvwmoPinBridge.pin_seg_pin]
    asked for [checker_taint_sub_prov] it now asks for the emission's own
    two structural facts — the load's carrier group ([base_ok]) and the
    walk alignment ([psites]). *)
Theorem pin_seg_pin' (GD : gdexec) (i : agent) (em : hemission) (sg : seg)
    (pcL pc' : Z) (j k : nat) (own : bool)
    (base pre post : list eitem) (rl : bool) (a : Z) (v : list (bv 8)) :
  (∀ jk, jk ∈ row_deps (em_items em) →
         ((i, jk.1), (i, jk.2)) ∈ gd_deps GD) →
  sg_entry sg = (i, j) → sg_exit sg = (i, k) →
  inv_ok j (ds_run ds_init base) (pin_t0 pcL) →
  em_items em
    = pre ++ (LStore rl a v (deps_addr (krole pc')) (deps_vsrc (krole pc')),
              Some k) :: post →
  psites pcL own base pre
    (LStore rl a v (deps_addr (krole pc')) (deps_vsrc (krole pc')), Some k)
    pc' →
  (j < k)%nat →
  pinnedb pin_fuel pcL (PDep pc' own) = true →
  seg_pin GD sg.
Proof.
  intros Hconf He Hx Hbase Hes Hsite Hlt Hpin.
  eapply (pin_seg_pin GD i em sg (psites pcL own base) pcL pc' j k own);
    [exact Hconf|exact He|exact Hx| |exact Hes|exact Hsite|exact Hlt|exact Hpin].
  by apply checker_taint_sub_prov_proof.
Qed.

(* ====================================================================== *)
(** * 8. NON-VACUITY, on the one stretch computed from real image bytes

    [WeakRvwmoAdm] §3 runs the INSTANCE at hart 1's spin load
    [lw a5,0(a4)] (main+0x16) and computes the 117 administrative items it
    emits, uniformly in the word read.  Here are the two obligations this
    file's induction places on that group, decided by [vm_compute] against
    the very same image bytes the checker decodes. *)

(** (i) THE CHECKER'S SIDE.  The spin load is COMPRESSED (two bytes), its
    decoded destination is [a5] with the load result and the base register
    [a4] as sources (DEC-4's transitive provenance), and it has no second
    destination. *)
Lemma la_deps_rd :
  deps_rd (krole (KernelSyms.main + 0x16))
  = Some (15%nat, [DLdRes; DReg 14%nat]).
Proof. vm_cast_no_check (eq_refl (Some (15%nat, [DLdRes; DReg 14%nat]))). Qed.

Lemma la_deps_rd2 : deps_rd2 (krole (KernelSyms.main + 0x16)) = None.
Proof. vm_cast_no_check (eq_refl (@None (wreg * list dsrc))). Qed.

Lemma la_load_size : w_size (kw (KernelSyms.main + 0x16)) = 2.
Proof. vm_cast_no_check (eq_refl 2%Z). Qed.

(** (ii) THE INSTANCE'S SIDE, COMPUTED.  Of the stretch's 117 items exactly
    ONE is a register write; it is at [a5]; and its emitted source list
    [[DLdRes; DReg 14; DReg 39; DReg 45; DReg 44]] (the DEC-7 dynamic read
    set) CONTAINS the decoded list [[DLdRes; DReg 14]].  So [grp_okb] — the
    group obligation of [reaches]' step — passes on real bytes.  This is
    [WeakEvLang.erw_srcs_covers], decided rather than assumed. *)
Theorem la_grp_ok (w : bv 32) :
  grp_okb (KernelSyms.main + 0x16)
          (eadm (adm_lbls false 200 (ah_read (bv_unsigned w) la_x2))) []
  = true.
Proof. vm_cast_no_check (eq_refl true). Qed.

(** ... and the same stretch is the LOAD'S CARRIER group: that [LRegW]
    carries [DLdRes], and no item below it writes [a5] again — which is the
    base case's obligation. *)
Theorem la_ld_carrier (w : bv 32) :
  ld_carrier 15 (eadm (adm_lbls false 200 (ah_read (bv_unsigned w) la_x2)))
  = true.
Proof. vm_cast_no_check (eq_refl true). Qed.

(** (iii) THE BASE FACT, on that stretch: after the load's own row item and
    the group the instance emits, [j] is in [dprov a5] — which is exactly
    what [pin_start]'s taint [[a5]] claims. *)
Corollary la_base_ok (w : bv 32) (jj : nat) (pre0 : list eitem)
    (lit : eitem) :
  ld_item jj lit →
  inv_ok jj
    (ds_run ds_init
       (pre0 ++ lit
        :: eadm (adm_lbls false 200 (ah_read (bv_unsigned w) la_x2))))
    (pin_t0 (KernelSyms.main + 0x16)).
Proof.
  intros Hlit.
  eapply base_ok; [apply la_load_rd|exact Hlit|apply la_ld_carrier].
Qed.

(** (iv) THE SITE ORACLE IS INHABITED.  [pin_start] of the spin load
    already sits at [main+0x18] — the pc [KernelPinsDef.pin_started]'s
    [PFence] witness names — so the zero-step walk relates the emission's
    prefix to that site. *)
Lemma la_reaches0 (own : bool) :
  reaches own (KernelSyms.main + 0x18) (pin_start (KernelSyms.main + 0x16))
          [] (pin_start (KernelSyms.main + 0x16)).
Proof. apply RC_stop. vm_cast_no_check (eq_refl true). Qed.

Corollary la_psites (own : bool) (base : list eitem) (it : eitem) :
  psites (KernelSyms.main + 0x16) own base base it (KernelSyms.main + 0x18).
Proof.
  exists [], (pin_start (KernelSyms.main + 0x16)).
  split; [by rewrite app_nil_r|apply la_reaches0].
Qed.

(** (v) AND THE HYPOTHESIS ITSELF, DISCHARGED at that site for the
    instance's own emission. *)
Theorem la_checker_taint_sub_prov (w : bv 32) (own : bool) (jj : nat)
    (pre0 : list eitem) (lit : eitem) (es : list eitem) :
  ld_item jj lit →
  checker_taint_sub_prov es
    (psites (KernelSyms.main + 0x16) own
       (pre0 ++ lit
        :: eadm (adm_lbls false 200 (ah_read (bv_unsigned w) la_x2))))
    (KernelSyms.main + 0x16) jj own.
Proof. intros Hlit. apply checker_taint_sub_prov_proof. by apply la_base_ok. Qed.

(* ====================================================================== *)
(** * 9. AUDIT *)

Print Assumptions taint_upd1_inv.
Print Assumptions regw_step.
Print Assumptions grp_sound.
Print Assumptions reaches_fwalk.
Print Assumptions reaches_inv.
Print Assumptions wstep_taint.
Print Assumptions ld_carrier_sound.
Print Assumptions base_ok.
Print Assumptions checker_taint_sub_prov_proof.
Print Assumptions pin_seg_pin'.
Print Assumptions la_grp_ok.
Print Assumptions la_ld_carrier.
Print Assumptions la_checker_taint_sub_prov.
