(* CrashProto.v -- a self-contained PROTOTYPE of the power/crash/generation
   design (claude-notes/design/crash.md), on a MINIATURE language, validating
   every novel Iris mechanic before the real port touches the tree:

     - generation-indexed, stateless thread expressions with CORPSE arms
       (a dead generation's thread can only self-loop, which needs no
       resources -- [wp_dead]);
     - a ghost POWER THREAD owning both boot and crash: PowerOff bumps the
       generation (killing it instantly -- "dead" is one mono-nat lower
       bound), PowerOn resets the machine, keeps the disk, and FORKS the
       new generation's threads (stock Iris fork via prim_step's [efs]);
     - a generational state_interp: fixed layer (generation counter, the
       generation->era-gname REGISTRY with its dom-shape, the durable disk
       auth) + a per-era layer (the current generation's memory auth),
       abandoned wholesale at PowerOff;
     - the base-rule FOUR-WAY case split (live / dead / powered-off-refuted-
       by-registry / unborn-refuted-by-birth-bound) -- [wp_work];
     - the crash-spanning invariant [crash_inv] owning the disk's persistent
       contents as an iProp, opened INSTANTANEOUSLY around the one step that
       writes the disk, and FRAMED (never opened) by both power arms;
     - whole-system adequacy over the singleton pool [PowerE] via stock
       [wp_strong_adequacy], with ONE hypothesis (the initial disk satisfies
       the invariant's content), concluding not-stuck AND the invariant's
       pure shadow at every reachable state.

   The mini-machine: memory is a [gmap nat nat] with one interesting cell 0;
   a live work thread may bump mem[0] or add 2 to disk[0] (the toy "valid
   file system" is: disk[0] is even).  Nothing here imports the Sail model;
   this file is a leaf and compiles in seconds. *)

From stdpp Require Import gmap sets.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_map mono_nat invariants.
From iris.program_logic Require Import language weakestpre lifting adequacy.
Local Open Scope nat_scope.

(* ---------------------------------------------------------------------- *)
(* 1. The machine.                                                         *)
(* ---------------------------------------------------------------------- *)

Record pstate := PState {
  pgen  : nat;            (* current generation *)
  ppow  : bool;           (* power *)
  pmem  : gmap nat nat;   (* volatile memory (era-scoped ghosts) *)
  pdisk : gmap nat nat;   (* persistent disk (crash-surviving ghosts) *)
}.

Inductive pexpr :=
  | WorkE (gen : nat)     (* a "hart", indexed by the generation it belongs to *)
  | PowerE.               (* the ghost power thread *)
Definition pval := Empty_set.
Definition pobs := Empty_set.
Definition p_of_val (v : pval) : pexpr := match v with end.
Definition p_to_val (_ : pexpr) : option pval := None.

(* A generation-[gen] work thread is LIVE iff the power is on and [gen] is
   current; its real arms are gated on exactly that, and the CORPSE arm is
   the complement.  The power thread alternates: PowerOff BUMPS the
   generation (so "gen is dead" is simply [pgen > gen], stable forever);
   PowerOn keeps the generation, havocs memory (boot_shape: cell 0 is
   mapped -- "the loader"), PRESERVES the disk, and forks the new
   generation's work thread. *)
Definition prim_step
    (e : pexpr) (σ : pstate) (κ : list pobs)
    (e' : pexpr) (σ' : pstate) (efs : list pexpr) : Prop :=
  (exists gen, e = WorkE gen /\ e' = WorkE gen /\ κ = [] /\ efs = [] /\
     ((ppow σ = true /\ pgen σ = gen /\
        ((exists n, pmem σ !! 0 = Some n /\
            σ' = PState (pgen σ) true (<[0 := S n]> (pmem σ)) (pdisk σ))
         \/
         (exists d, pdisk σ !! 0 = Some d /\
            σ' = PState (pgen σ) true (pmem σ) (<[0 := d + 2]> (pdisk σ)))))
      \/
      (~ (ppow σ = true /\ pgen σ = gen) /\ σ' = σ)))
  \/
  (e = PowerE /\ e' = PowerE /\ κ = [] /\
     ((ppow σ = true /\ efs = [] /\
        σ' = PState (S (pgen σ)) false (pmem σ) (pdisk σ))
      \/
      (ppow σ = false /\ efs = [WorkE (pgen σ)] /\
        (exists m', is_Some (m' !! 0) /\
           σ' = PState (pgen σ) true m' (pdisk σ))))).

Lemma proto_lang_mixin : LanguageMixin p_of_val p_to_val prim_step.
Proof.
  split.
  - intros [].
  - intros e v Hv. discriminate Hv.
  - intros; reflexivity.
Qed.

Definition proto_lang : language := Language proto_lang_mixin.

(* ---------------------------------------------------------------------- *)
(* 2. Ghost state.  The FIXED layer is the typeclass; the ERA layer is the  *)
(*    existentially-quantified memory gname inside [state_interp], keyed by *)
(*    the persistent registry entry for the current generation.             *)
(* ---------------------------------------------------------------------- *)

Class crashProtoGS (Σ : gFunctors) := CrashProtoGS {
  cp_invGS :: invGS Σ;
  cp_monoGS :: mono_natG Σ;
  cp_memG :: ghost_mapG Σ nat nat;    (* every era's memory map + the disk *)
  cp_regG :: ghost_mapG Σ nat gname;  (* the generation -> era registry *)
  cp_genname : gname;                 (* mono-nat: the generation counter *)
  cp_regname : gname;                 (* the registry *)
  cp_durname : gname;                 (* the durable disk map *)
}.

Section proto.
Context `{!crashProtoGS Σ}.

(* birth and death certificates: one mono-nat *)
Definition born (gen : nat) : iProp Σ := mono_nat_lb_own cp_genname gen.
Definition dead (gen : nat) : iProp Σ := mono_nat_lb_own cp_genname (S gen).

(* the registry's dom shape: generations [0, pgen) are over; the current one
   is registered iff the power is on (PowerOn registers it; PowerOff's bump
   moves [pgen] to a never-registered value, preserving the shape). *)
Definition reg_bound (σ : pstate) : nat :=
  pgen σ + (if ppow σ then 1 else 0).

(* the era layer: when the power is on, the current generation's era exists
   -- a memory-map gname, tied by the persistent registry entry, whose auth
   interprets the volatile memory.  Off: nothing (memory unconstrained). *)
Definition era_interp (σ : pstate) : iProp Σ :=
  if ppow σ then
    (∃ γm : gname, pgen σ ↪[cp_regname]□ γm ∗ ghost_map_auth γm 1 (pmem σ))%I
  else True%I.

Definition proto_interp (σ : pstate) : iProp Σ :=
  (mono_nat_auth_own cp_genname 1 (pgen σ) ∗
   (∃ R : gmap nat gname,
      ghost_map_auth cp_regname 1 R ∗
      ⌜dom R = set_seq 0 (reg_bound σ)⌝) ∗
   ghost_map_auth cp_durname 1 (pdisk σ) ∗
   era_interp σ)%I.

End proto.

Global Program Instance proto_irisGS `{!crashProtoGS Σ} : irisGS proto_lang Σ := {
  iris_invGS := cp_invGS;
  state_interp σ _ _ _ := proto_interp σ;
  fork_post _ := True%I;
  num_laters_per_step _ := 0%nat;
}.
Next Obligation. intros. iIntros "H". by iModIntro. Qed.

(* Same deal as riscv_lang's [wp_triv] (RiscvPtsto.v): [pval := Empty_set]
   and [p_to_val] is unconditionally [None], so a WP over [proto_lang] never
   inspects its postcondition either. *)
Lemma wp_proto_post_irrel `{!irisGS proto_lang Σ} s E (e : expr proto_lang) (Φ1 Φ2 : pval -> iProp Σ) :
  WP e @ s; E {{ Φ1 }} ⊢ WP e @ s; E {{ Φ2 }}.
Proof. iApply wp_mono. iIntros ([]). Qed.

Definition wp_proto_triv `{!irisGS proto_lang Σ} (E : coPset) (e : expr proto_lang) : iProp Σ :=
  WP e @ E {{ _, True%I }}.

Notation "'WP' e @ E" := (wp_proto_triv E e%E) (at level 20, e at level 20) : bi_scope.
Notation "'WP' e" := (wp_proto_triv ⊤ e%E) (at level 20, e at level 20) : bi_scope.

(* the crash-spanning disk invariant: the toy "valid file system" P_fs is
   "disk cell 0 is even".  Its content is an iProp over FIXED-layer ghosts,
   so it survives every power cycle; neither power arm ever opens it. *)
Definition crashN : namespace := nroot .@ "crashProto".
Definition crash_inv_body `{!crashProtoGS Σ} : iProp Σ :=
  (∃ d : nat, 0 ↪[cp_durname] d ∗ ⌜exists j : nat, d = (2 * j)%nat⌝)%I.
Definition crash_inv `{!crashProtoGS Σ} : iProp Σ := inv crashN crash_inv_body.

(* ---------------------------------------------------------------------- *)
(* 3. Pure set_seq helpers.                                                *)
(* ---------------------------------------------------------------------- *)

Lemma set_seq_snoc (n : nat) :
  set_seq (C := gset nat) 0 (n + 1) = set_seq 0 n ∪ {[n]}.
Proof.
  apply set_eq; intros x.
  rewrite elem_of_union elem_of_singleton !elem_of_set_seq. lia.
Qed.

Lemma not_in_set_seq (n : nat) : n ∉ set_seq (C := gset nat) 0 n.
Proof. rewrite elem_of_set_seq. lia. Qed.

(* ---------------------------------------------------------------------- *)
(* 4. [wp_dead]: a dead generation's thread runs forever on its corpse arm, *)
(*    from the death certificate alone.                                     *)
(* ---------------------------------------------------------------------- *)

Section wps.
Context `{!crashProtoGS Σ}.

Lemma wp_dead (gen : nat) (Φ : pval -> iProp Σ) :
  dead gen ⊢ WP (WorkE gen : expr proto_lang).
Proof.
  iIntros "#Hdead". iLöb as "IH".
  iApply wp_lift_step; first done.
  iIntros (σ1 ns κ κs nt) "(Hgen & Hreg & Hdur & Hera)".
  iDestruct (mono_nat_lb_own_valid with "Hgen Hdead") as %[_ Hge].
  iApply fupd_mask_intro; [set_solver|]. iIntros "Hback".
  iSplitR.
  { iPureIntro. exists [], (WorkE gen), σ1, [].
    left. exists gen. split; [done|]. split; [done|]. split; [done|].
    split; [done|]. right. split; [|done]. intros [_ Heq]. lia. }
  iIntros (e2 σ2 efs Hstep) "!>".
  destruct Hstep as
    [ (gen' & Heq & -> & -> & -> &
        [ (Hpw & Hcur & _) | (_ & ->) ])
    | (Heq & _) ];
    [ injection Heq as <-; exfalso; lia
    | injection Heq as <-
    | discriminate Heq ].
  iIntros "_".
  iMod "Hback" as "_". iModIntro.
  iFrame "Hgen Hreg Hdur Hera". iSplitL; [|done].
  iApply "IH".
Qed.

(* ---------------------------------------------------------------------- *)
(* 5. [wp_work]: the live thread.  This is the prototype of the BASE-RULE   *)
(*    four-way case split: live (old proof), dead (wp_dead), current-but-   *)
(*    off (refuted by the registry shape), unborn (refuted by birth bound). *)
(*    The disk-writing arm opens [crash_inv] instantaneously around its own *)
(*    step -- the only crash obligation any "kernel code" ever carries.     *)
(* ---------------------------------------------------------------------- *)

Lemma wp_work (gen : nat) (γm : gname) (n : nat) (Φ : pval -> iProp Σ) :
  crash_inv -∗ born gen -∗ gen ↪[cp_regname]□ γm -∗ 0 ↪[γm] n -∗
  WP (WorkE gen : expr proto_lang).
Proof.
  iIntros "#Hcinv #Hborn #Hrege Hcell".
  iRevert (n) "Hcell". iLöb as "IH". iIntros (n) "Hcell".
  iApply wp_lift_step; first done.
  iIntros (σ1 ns κ κs nt) "(Hgen & Hreg & Hdur & Hera)".
  destruct σ1 as [gn pw m dsk].
  iDestruct (mono_nat_lb_own_valid with "Hgen Hborn") as %[_ Hge].
  cbn in Hge.
  iDestruct "Hreg" as (R) "[HregA %Hdom]".
  iDestruct (ghost_map_lookup with "HregA Hrege") as %HRgen.
  destruct (decide (gn = gen)) as [->|Hne]; last first.
  { (* DEAD: gn > gen (birth bound rules out gn < gen). *)
    assert (Hlt : gen < gn) by lia.
    iDestruct (mono_nat_lb_own_get with "Hgen") as "#Hlb".
    iDestruct (mono_nat_lb_own_le (n := gn) (S gen) with "Hlb") as "#Hdead";
      [lia|].
    iApply fupd_mask_intro; [set_solver|]. iIntros "Hback".
    iSplitR.
    { iPureIntro. exists [], (WorkE gen), (PState gn pw m dsk), [].
      left. exists gen. split; [done|]. split; [done|]. split; [done|].
      split; [done|]. right. split; [|done]. intros [_ Heq]. cbn in Heq. lia. }
    iIntros (e2 σ2 efs Hstep) "!>".
    destruct Hstep as
      [ (gen' & Heq & -> & -> & -> &
          [ (Hpw & Hcur & _) | (_ & ->) ])
      | (Heq & _) ];
      [ injection Heq as <-; cbn in Hcur; exfalso; lia
      | injection Heq as <-
      | discriminate Heq ].
    iIntros "_".
    iMod "Hback" as "_". iModIntro.
    iFrame "Hgen Hdur Hera".
    iSplitL "HregA".
    { iExists R. iFrame "HregA". iPureIntro. exact Hdom. }
    iSplitL; [|done].
    iApply (wp_dead gen (fun _ => True%I)). iExact "Hdead". }
  destruct pw; last first.
  { (* CURRENT BUT POWERED OFF: impossible -- the registry has no entry for
       a generation whose PowerOn has not happened, yet we hold one. *)
    exfalso.
    apply (not_in_set_seq gen).
    rewrite /reg_bound /= Nat.add_0_r in Hdom. rewrite -Hdom.
    apply elem_of_dom. eauto. }
  (* LIVE: the era exists; tie our gname to it, then handle both real arms. *)
  rewrite /era_interp /=.
  iDestruct "Hera" as (γm') "[#Hrege' HmA]".
  iDestruct (ghost_map_elem_agree with "Hrege Hrege'") as %<-.
  iDestruct (ghost_map_lookup with "HmA Hcell") as %Hm0.
  (* open the crash-spanning invariant around this single step *)
  iInv "Hcinv" as (d) ">[Hd %Hev]" "Hclose".
  iDestruct (ghost_map_lookup with "Hdur Hd") as %Hd0.
  iApply fupd_mask_intro; [solve_ndisj|]. iIntros "Hback".
  iSplitR.
  { iPureIntro. exists [], (WorkE gen),
      (PState gen true (<[0 := S n]> m) dsk), [].
    left. exists gen. split; [done|]. split; [done|]. split; [done|].
    split; [done|]. left. split; [done|]. split; [done|].
    left. exists n. split; [exact Hm0|]. done. }
  iIntros (e2 σ2 efs Hstep) "!>".
  destruct Hstep as
    [ (gen' & Heq & -> & -> & -> &
        [ (_ & _ & [ (n0 & Hn0 & ->) | (d0 & Hd0' & ->) ]) | (Hnl & ->) ])
    | (Heq & _) ]; [ injection Heq as <- .. | injection Heq as <- | discriminate Heq ].
  - (* memory arm: bump cell 0 in the ERA ghost; the invariant closes
       unchanged. *)
    cbn in Hn0. assert (n0 = n) as -> by congruence.
    iIntros "_".
    iMod (ghost_map_update (S n) with "HmA Hcell") as "[HmA Hcell]".
    iMod "Hback" as "_".
    iMod ("Hclose" with "[Hd]") as "_".
    { iNext. iExists d. iFrame "Hd". iPureIntro. exact Hev. }
    iModIntro. cbn.
    iFrame "Hgen Hdur".
    iSplitL "HregA HmA".
    { iSplitL "HregA".
      { iExists R. iFrame "HregA". iPureIntro. exact Hdom. }
      rewrite /era_interp /=. iExists γm. iFrame "HmA". iExact "Hrege'". }
    iSplitL; [|done].
    iApply ("IH" with "Hcell").
  - (* disk arm: update the DURABLE ghost under the opened invariant and
       re-establish P_fs (evenness is preserved by +2). *)
    cbn in Hd0'. assert (d0 = d) as -> by congruence.
    iIntros "_".
    iMod (ghost_map_update (d + 2) with "Hdur Hd") as "[Hdur Hd]".
    iMod "Hback" as "_".
    iMod ("Hclose" with "[Hd]") as "_".
    { iNext. iExists (d + 2). iFrame "Hd". iPureIntro.
      destruct Hev as [j ->]. exists (S j). lia. }
    iModIntro. cbn.
    iFrame "Hgen Hdur".
    iSplitL "HregA HmA".
    { iSplitL "HregA".
      { iExists R. iFrame "HregA". iPureIntro. exact Hdom. }
      rewrite /era_interp /=. iExists γm. iFrame "HmA". iExact "Hrege'". }
    iSplitL; [|done].
    iApply ("IH" with "Hcell").
  - (* corpse arm: refuted -- we are live. *)
    exfalso. apply Hnl. done.
Qed.

(* ---------------------------------------------------------------------- *)
(* 6. [wp_power]: the ghost thread.  PowerOff abandons the era (bump the    *)
(*    counter, drop the memory auth); PowerOn performs THE SURGERY (fresh   *)
(*    era gname over the arbitrary reset memory, registry insert + persist, *)
(*    birth certificate) and discharges the FORK obligation with the        *)
(*    client's boot entailment [Hboot].  Both arms FRAME the durable disk   *)
(*    auth and never open [crash_inv].                                      *)
(* ---------------------------------------------------------------------- *)

Lemma wp_power (Φ : pval -> iProp Σ)
    (Hboot : forall (gen : nat) (γm : gname) (n : nat),
       ⊢ crash_inv -∗ born gen -∗ gen ↪[cp_regname]□ γm -∗ 0 ↪[γm] n -∗
         WP (WorkE gen : expr proto_lang)) :
  crash_inv ⊢ WP (PowerE : expr proto_lang).
Proof.
  iIntros "#Hcinv". iLöb as "IH".
  iApply wp_lift_step; first done.
  iIntros (σ1 ns κ κs nt) "(Hgen & Hreg & Hdur & Hera)".
  destruct σ1 as [gn pw m dsk].
  iDestruct "Hreg" as (R) "[HregA %Hdom]".
  iApply fupd_mask_intro; [set_solver|]. iIntros "Hback".
  destruct pw.
  - (* PowerOff: kill the generation. *)
    iSplitR.
    { iPureIntro. exists [], PowerE, (PState (S gn) false m dsk), [].
      right. split; [done|]. split; [done|]. split; [done|].
      left. done. }
    iIntros (e2 σ2 efs Hstep) "!>".
    destruct Hstep as
      [ (gen' & Heq & _) | (_ & -> & -> & [ (_ & -> & ->) | (Hpw & _) ]) ];
      [ discriminate Heq | | discriminate Hpw ].
    iIntros "_".
    iMod (mono_nat_own_update (n := gn) (S gn) with "Hgen") as "[Hgen _]";
      [lia|].
    iMod "Hback" as "_". iModIntro. cbn.
    iFrame "Hgen Hdur".
    iSplitL "HregA".
    { iExists R. iFrame "HregA". iPureIntro.
      assert (Hbb : reg_bound (PState (S gn) false m dsk)
                  = reg_bound (PState gn true m dsk))
        by (rewrite /reg_bound /=; lia).
      rewrite Hbb. exact Hdom. }
    iSplitL; [|done].
    iApply "IH".
  - (* PowerOn: the surgery + the fork. *)
    iSplitR.
    { iPureIntro. exists [], PowerE, (PState gn true {[0 := 0]} dsk),
        [WorkE gn].
      right. split; [done|]. split; [done|]. split; [done|].
      right. split; [done|]. split; [done|].
      exists {[0 := 0]}. split; [|done].
      rewrite lookup_singleton. eauto. }
    iIntros (e2 σ2 efs Hstep) "!>".
    destruct Hstep as
      [ (gen' & Heq & _)
      | (_ & -> & -> & [ (Hpw & _) | (_ & -> & (m' & [k0 Hk0] & ->)) ]) ];
      [ discriminate Heq | discriminate Hpw | ].
    iIntros "_".
    (* fresh era over the (arbitrary) reset memory *)
    iMod (ghost_map_alloc m') as (γm) "[HmA Hmelems]".
    iDestruct (big_sepM_delete _ _ 0 with "Hmelems") as "[Hcell _]";
      [exact Hk0|].
    (* register the era (the registry has no entry for gn: power was off) *)
    iMod (ghost_map_insert gn γm with "HregA") as "[HregA Hrege]".
    { apply not_elem_of_dom. rewrite Hdom /reg_bound /= Nat.add_0_r.
      apply not_in_set_seq. }
    iMod (ghost_map_elem_persist with "Hrege") as "#Hrege".
    iDestruct (mono_nat_lb_own_get with "Hgen") as "#Hborn".
    iMod "Hback" as "_". iModIntro. cbn.
    iFrame "Hgen Hdur".
    iSplitR "Hcell".
    { iSplitL "HregA".
      { iExists (<[gn := γm]> R). iFrame "HregA". iPureIntro.
        rewrite dom_insert_L Hdom /reg_bound /= Nat.add_0_r set_seq_snoc.
        set_solver. }
      rewrite /era_interp /=. iExists γm. iFrame "HmA". iExact "Hrege". }
    iSplitR; [iApply "IH"|].
    (* the FORK obligation: the new generation's work thread, built from the
       freshly minted era resources + the crash-spanning invariant. *)
    cbn. iSplitL; [|done].
    iApply (wp_wand with "[Hcell]").
    { iApply (Hboot gn γm k0 with "Hcinv Hborn Hrege Hcell"). }
    auto.
Qed.

End wps.

(* ---------------------------------------------------------------------- *)
(* 7. Adequacy: the whole system, from power-off, under any schedule.  ONE  *)
(*    hypothesis (the initial disk satisfies P_fs); the conclusion is       *)
(*    not-stuck for every reachable thread PLUS the invariant's pure shadow *)
(*    (disk cell 0 is even) at every reachable state -- extracted by        *)
(*    opening [crash_inv] against the final state_interp.                   *)
(* ---------------------------------------------------------------------- *)

Class crashProtoGpreS (Σ : gFunctors) := {
  cpp_invGS :: invGpreS Σ;
  cpp_monoGS :: mono_natG Σ;
  cpp_memG :: ghost_mapG Σ nat nat;
  cpp_regG :: ghost_mapG Σ nat gname;
}.

Definition crashProtoΣ : gFunctors :=
  #[invΣ; mono_natΣ; ghost_mapΣ nat nat; ghost_mapΣ nat gname].
Global Instance subG_crashProtoGpreS {Σ} :
  subG crashProtoΣ Σ -> crashProtoGpreS Σ.
Proof. solve_inG. Qed.

Theorem proto_adequacy Σ `{!crashProtoGpreS Σ} (σ0 : pstate) (k : nat)
    (Hpow : ppow σ0 = false) (Hgen0 : pgen σ0 = 0)
    (Hdisk : pdisk σ0 !! 0 = Some (2 * k)) :
  forall t2 σ2 e2,
    rtc erased_step ([PowerE : expr proto_lang], σ0) (t2, σ2) ->
    e2 ∈ t2 ->
    reducible (Λ := proto_lang) e2 σ2 /\
    (exists j, pdisk σ2 !! 0 = Some (2 * j)).
Proof.
  intros t2 σ2 e2 Hrtc He2.
  apply erased_steps_nsteps in Hrtc as (n & κs & Hsteps).
  cut ((forall e, e ∈ t2 -> not_stuck e σ2) /\
       (exists j, pdisk σ2 !! 0 = Some (2 * j))).
  { intros [Hns Hev]. split; [|exact Hev].
    destruct (Hns e2 He2) as [[v Hv]|Hred]; [discriminate Hv|exact Hred]. }
  eapply (wp_strong_adequacy Σ proto_lang NotStuck
            [PowerE : expr proto_lang] σ0 n κs t2 σ2 _ (fun _ => 0%nat));
    last exact Hsteps.
  intros Hinv.
  (* the FIXED layer, allocated once, at power-off, before any boot *)
  iMod (mono_nat_own_alloc (pgen σ0)) as (γgen) "[HgenA _]".
  iMod (ghost_map_alloc_empty (K := nat) (V := gname)) as (γreg) "HregA".
  iMod (ghost_map_alloc (pdisk σ0)) as (γdur) "[HdurA Hdelems]".
  set (HPG := CrashProtoGS Σ Hinv _ _ _ γgen γreg γdur).
  iDestruct (big_sepM_delete _ _ 0 with "Hdelems") as "[Hd0 _]";
    [exact Hdisk|].
  iMod (inv_alloc crashN _ crash_inv_body with "[Hd0]") as "#Hcinv".
  { iNext. rewrite /crash_inv_body. iExists (2 * k). iFrame "Hd0".
    iPureIntro. eauto. }
  iModIntro.
  iExists (fun (σ' : pstate) (_ : nat) (_ : list pobs) (_ : nat) =>
             proto_interp σ'),
    [fun _ : pval => True%I],
    (fun _ : pval => True%I),
    (@state_interp_mono HasLc proto_lang Σ (@proto_irisGS Σ HPG)).
  cbv zeta beta.
  iSplitL "HgenA HregA HdurA".
  { (* the initial state interpretation: off form -- no era at all *)
    rewrite /proto_interp Hgen0. iFrame "HgenA HdurA".
    iSplitL "HregA".
    { iExists ∅. iFrame "HregA". iPureIntro.
      rewrite dom_empty_L /reg_bound Hgen0 Hpow /=. done. }
    rewrite /era_interp Hpow. done. }
  iSplitL.
  { (* the pool: just the power thread; the client boot entailment is
       [wp_work] *)
    cbn. iSplitL; [|done].
    iApply (@wp_power Σ HPG (fun _ : pval => True%I)
              (fun gen γm n0 => @wp_work Σ HPG gen γm n0 (fun _ : pval => True%I))
             with "Hcinv"). }
  (* the final observation: not-stuck (wp_strong_adequacy's own clause) plus
     the crash invariant's pure shadow, read off the final state_interp *)
  iIntros (es' t2') "%Heq %Hlen %Hns Hsi Hes Hts".
  iInv "Hcinv" as (d) ">[Hd %Hev]" "_".
  iDestruct "Hsi" as "(_ & _ & Hdur & _)".
  iDestruct (ghost_map_lookup with "Hdur Hd") as %Hlk.
  iApply fupd_mask_intro; [set_solver|]. iIntros "_".
  iPureIntro. split.
  - intros e He. exact (Hns e eq_refl He).
  - destruct Hev as [j ->]. eauto.
Qed.

(* the closed corollary: the whole story is instantiable *)
Corollary proto_adequacy_closed (σ0 : pstate) (k : nat)
    (Hpow : ppow σ0 = false) (Hgen0 : pgen σ0 = 0)
    (Hdisk : pdisk σ0 !! 0 = Some (2 * k)) :
  forall t2 σ2 e2,
    rtc erased_step ([PowerE : expr proto_lang], σ0) (t2, σ2) ->
    e2 ∈ t2 ->
    reducible (Λ := proto_lang) e2 σ2 /\
    (exists j, pdisk σ2 !! 0 = Some (2 * j)).
Proof.
  apply (proto_adequacy crashProtoΣ σ0 k Hpow Hgen0 Hdisk).
Qed.
