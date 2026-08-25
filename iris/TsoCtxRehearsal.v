(* TsoCtxRehearsal.v -- THE CUTOVER REHEARSAL.

   [TsoCtxTwin.v] showed that a TSO-shaped context machinery EXISTS over
   [TsoMem.v]'s Ztso view machine.  It was written before leg M swept the
   context axis through the tree, so it models only load/store/transport/
   park/resume.  This file asks the question the sweep makes urgent:

     ARE THE STATEMENTS [TsoCtx.v] ACTUALLY EXPORTS -- the ones ~600 files
     now depend on -- SATISFIABLE AT THE TSO DEFINITIONS?

   It is a DISCOVERY file.  A negative result is a result: where a surface
   statement is refutable at the twin, the refutation is PROVED here (as a
   Coq-level [... -> False]) rather than worked around, and the honest
   replacement statement is proved beside it.  Nothing here is admitted and
   nothing here is axiomatised; where a repair is a genuine design question
   rather than a proof obligation, it is left OUT of the file and reported.

   THE HEADLINE RESULTS.

   1. [own_context_alloc : |==> ∃ ξ, own_context ξ] IS REFUTABLE
      ([no_own_context_alloc]).  So is a free allocation of a PARKED token
      ([no_ctx_parked_alloc]) -- for the same structural reason: in the twin
      BOTH tokens are fragments of authorities that live inside
      [tso_interp].  The honest interp-carrying mints are [twin_ctx_mint]
      (a running token, for boot) and [twin_ctx_birth] (a parked token, for
      fork).  Section [roster] then shows what an interp-FREE mint needs to
      be true: an identity carrying ITS OWN gname (which the real
      [TsoCtx.CtxId] does and the twin's [nat] does not).

   2. [CtxMorph]'s pointsto instance IS REFUTABLE ([no_ctx_morph_pointsto]):
      the class has a bare [==∗], and re-registering a byte at another
      context consumes the LEDGER AUTHORITY.  [CtxMorphI] is the honest
      shape (interp threaded), and all five structural instances survive it
      verbatim.

   3. THE SWTCH EXCHANGE IS DERIVABLE, not primitive
      ([twin_swtch_exchange]): park-then-resume DOES compose on one hart,
      because park deletes h from [run] and resume asks only for
      [run !! h = None].  Its premise is [T ≤ tvs h]; the kernel-side form
      [twin_swtch_exchange_at_top] shows THIS HART AT THE LOG TOP suffices
      -- exactly the AMO-acquire evidence that also mints [ctx_dom].

   4. THE FORK STAMP.  [twin_ctx_birth] stamps the child at the CURRENT LOG
      TOP and [twin_deposit_at_fork] then hands the parent's byte facts to
      the child WITH NO VIEW SIDE CONDITION -- the acid test the owner
      asked for, passed.  What it still needs is the LEDGER AUTHORITY, i.e.
      the interp; see the note above [twin_deposit_at_fork].

   Imports: stdpp + Iris + [TsoMem] + [TsoCtxTwin] only.  No Sail, no
   RiscvLang -- this file must build while the main tree rebuilds. *)
From Stdlib Require Import ZArith Lia.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import dfrac.
From iris.base_logic.lib Require Import ghost_map ghost_var.
From xv6iris Require Import TsoMem TsoCtxTwin.

Local Open Scope Z_scope.

(* ================================================================== *)
(** * 0.  A soundness hammer: [|==> False] is absurd                   *)
(* ================================================================== *)

(* Every refutation below ends by deriving a contradiction UNDER a basic
   update -- the surface laws are all [==∗]-shaped, so the pure falsehood
   only becomes available inside the update.  [False] is plain, so the
   update can be stripped. *)
Lemma bupd_absurd (Σ : gFunctors) : (⊢@{iProp Σ} |==> False) → False.
Proof.
  intros H.
  apply (uPred.pure_soundness (M:=iResUR Σ)).
  iApply (bupd_elim (PROP:=iProp Σ) (⌜False⌝)%I).
  iMod H as "[]".
Qed.

(* ================================================================== *)
(** * 1.  The surface's exports, rehearsed at the twin                 *)
(* ================================================================== *)

Section rehearsal.
  Context {Σ : gFunctors} `{!tsoTwinG Σ}.
  Context (γheap γledger γrun γpark : gname).

  Local Notation ownc := (own_context γrun).
  Local Notation parkc := (ctx_parked γpark).
  Local Notation ptc := (ctx_pointsto γheap γledger).
  Local Notation domc := (ctx_dom γrun).
  Local Notation interp := (tso_interp γheap γledger γrun γpark).

  (* ---------------------------------------------------------------- *)
  (** ** 1.1  SUSPECT (1): the mint                                    *)
  (* ---------------------------------------------------------------- *)

  (* [TsoCtx.own_context_alloc] says a running-thread token may be
     conjured from nothing.  At the twin [own_context ξ h] is [h ↪[γrun] ξ]
     -- a full-fraction ghost-map element AT THE KEY [h].  Two of them at
     one hart are contradictory, and the surface's law supplies two.

     THE HART IS WHAT KILLS IT: the existential is over ξ, not over h, so
     the two mints collide even though they name different contexts.  Read
     the statement as: you cannot conjure "I am running as some fresh
     thread ON THIS HART" out of nothing. *)
  Lemma no_own_context_alloc (h : agent) :
    (⊢ |==> ∃ ξ : CtxId, ownc ξ h) → False.
  Proof.
    intros Halloc. apply (bupd_absurd Σ).
    iMod Halloc as (ξ1) "H1". iMod Halloc as (ξ2) "H2".
    rewrite /own_context.
    iDestruct (ghost_map_elem_ne with "H1 H2") as %Hne. done.
  Qed.

  (* THE PROPOSED REPLACEMENT -- a free allocation of a PARKED
     (never-yet-run) token -- is refutable too, and the argument is
     DIFFERENT: [ctx_parked ξ T] is [ξ ↪[γpark] T], whose key IS the
     existential, so two mints do not collide.  What kills it is that the
     [γpark] AUTHORITY lives inside [tso_interp]: hold that authority at a
     map which does not mention ξ, and the conjured fragment contradicts
     it.  Stated against the bare authority, so it depends on no invariant
     clause -- ANY holder of the park authority refutes the law. *)
  Lemma no_ctx_parked_alloc (T : nat) :
    (∀ γp : gname, ⊢ |==> ∃ ξ : CtxId, ctx_parked γp ξ T) → False.
  Proof.
    intros Halloc. apply (bupd_absurd Σ).
    iMod (ghost_map_alloc (∅ : gmap CtxId nat)) as (γp) "[Hauth _]".
    iMod (Halloc γp) as (ξ) "Hfrag".
    rewrite /ctx_parked.
    iDestruct (ghost_map_lookup with "Hauth Hfrag") as %Hlk.
    by rewrite lookup_empty in Hlk.
  Qed.

  (* THE HONEST RUNNING MINT (this is BOOT's rule: adequacy CONSTRUCTS the
     interp, so it may hold it).  It consumes the [γrun] authority and
     carries exactly the three side conditions the invariant needs:
       - [run !! h = None]           the hart is not already running something;
       - [∀ h0, run !! h0 ≠ Some ξ]  RUN-INJECTIVITY;
       - [parked !! ξ = None]        PARKED-NOT-RUNNING.
     Note what is NOT needed: nothing about the log, the views or the
     ledger.  A newborn context owns no bytes, so the SEES invariant has no
     obligation for it -- which is why a mint needs no view evidence. *)
  Lemma twin_ctx_mint img log tvs run parked (ξ : CtxId) (h : agent) :
    run !! h = None →
    (∀ h0, run !! h0 ≠ Some ξ) →
    parked !! ξ = None →
    interp img log tvs run parked ==∗
    interp img log tvs (<[h := ξ]> run) parked ∗ ownc ξ h.
  Proof.
    iIntros (Hh Hnr Hnp) "Hint".
    iDestruct "Hint" as (HM LL) "(Hhp & Hl & Hr & Hp & %Hwf)".
    rewrite /own_context.
    iMod (ghost_map_insert h ξ Hh with "Hr") as "[Hr Hrun]".
    iModIntro. iFrame "Hrun".
    iExists HM, LL. iFrame "Hhp Hl Hr Hp".
    iPureIntro.
    destruct Hwf as [Hlat Hbnd Hsees Hple Hinj Hpnr Huniq].
    constructor.
    - exact Hlat.
    - exact Hbnd.
    - (* sees: [run] only GREW, so the running arm survives *)
      move => ξ0 a0 t0 HL0.
      destruct (Hsees _ _ _ HL0) as [(h0 & Hh0 & Hv0) | (T & HT & Hle)].
      + left. exists h0. split; last done.
        have Hne : h0 ≠ h. { move => Heq. subst h0. rewrite Hh in Hh0. done. }
        rewrite lookup_insert_ne //.
      + right. by exists T.
    - exact Hple.
    - (* run_inj *)
      move => h1 h2 ξ0.
      destruct (decide (h1 = h)) as [->|Hne1];
        destruct (decide (h2 = h)) as [->|Hne2].
      + done.
      + rewrite lookup_insert lookup_insert_ne; last congruence.
        move => [= Heq] HR2. exfalso. apply (Hnr h2). congruence.
      + rewrite lookup_insert_ne; last congruence. rewrite lookup_insert.
        move => HR1 [= Heq]. exfalso. apply (Hnr h1). congruence.
      + rewrite !lookup_insert_ne; [|congruence..]. exact (Hinj h1 h2 ξ0).
    - (* parked_not_run *)
      move => ξ0 T h0 HT.
      destruct (decide (h0 = h)) as [->|Hne].
      + rewrite lookup_insert. move => [= Heq]. congruence.
      + rewrite lookup_insert_ne; last congruence. exact (Hpnr _ _ _ HT).
    - exact Huniq.
  Qed.

  (* Freshness is CONSTRUCTIBLE at the twin, so the mint can also be stated
     in the surface's [∃ ξ] shape -- with the interp threaded. *)
  Definition ctx_used (run : gmap agent CtxId) (parked : gmap CtxId nat)
      : gset CtxId :=
    list_to_set ((map_to_list run).*2) ∪ dom parked.

  Lemma ctx_used_run run parked h ξ :
    run !! h = Some ξ → ξ ∈ ctx_used run parked.
  Proof.
    move => Hh. rewrite /ctx_used elem_of_union. left.
    rewrite elem_of_list_to_set elem_of_list_fmap.
    exists (h, ξ). split; first done. by apply elem_of_map_to_list.
  Qed.

  Lemma ctx_used_parked run parked ξ T :
    parked !! ξ = Some T → ξ ∈ ctx_used run parked.
  Proof.
    move => HT. rewrite /ctx_used elem_of_union. right.
    by eapply elem_of_dom_2.
  Qed.

  Lemma twin_ctx_fresh (run : gmap agent CtxId) (parked : gmap CtxId nat) :
    ∃ ξ : CtxId, (∀ h0, run !! h0 ≠ Some ξ) ∧ parked !! ξ = None.
  Proof.
    exists (fresh (ctx_used run parked)).
    have Hfr : fresh (ctx_used run parked) ∉ ctx_used run parked
      by apply is_fresh.
    split.
    - move => h0 Hh0. apply Hfr. by eapply ctx_used_run.
    - destruct (parked !! fresh (ctx_used run parked)) eqn:Hp; last done.
      exfalso. apply Hfr. by eapply ctx_used_parked.
  Qed.

  Lemma twin_ctx_mint_fresh img log tvs run parked (h : agent) :
    run !! h = None →
    interp img log tvs run parked ==∗
    ∃ ξ : CtxId, interp img log tvs (<[h := ξ]> run) parked ∗ ownc ξ h.
  Proof.
    iIntros (Hh) "Hint".
    destruct (twin_ctx_fresh run parked) as (ξ & Hnr & Hnp).
    iMod (twin_ctx_mint _ _ _ _ _ ξ h Hh Hnr Hnp with "Hint") as "[Hint Hrun]".
    iModIntro. iExists ξ. iFrame.
  Qed.

  (* ---------------------------------------------------------------- *)
  (** ** 1.2  THE FORK MINT AND THE DEPOSIT                            *)
  (* ---------------------------------------------------------------- *)

  (* WHAT THE TWIN'S RUNNING TOKEN CARRIES: [own_context ξ h = h ↪[γrun] ξ]
     -- THE PAIRING AND NOTHING ELSE.  It carries NO bound, no view, no
     timestamp.  So a fork rule of the shape

       own_context ξp ==∗ own_context ξp ∗ ctx_parked ξc T   (T = ξp's bound)

     cannot be read off the token: "ξp's bound" is a property of the LEDGER
     MAP inside the interp (the max t over LL's ξp-entries), not of the
     fragment.  Either the running token grows a bound field, or the mint
     takes the interp.  The rules below take the interp, and stamp at the
     LOG TOP -- which is >= any bound the parent could have, so it is the
     strictly more permissive stamp and is equally sound
     ([twf_parked_le] asks only [T ≤ length log]). *)

  (* THE CHILD IS BORN PARKED, at the current log top.  No view obligation
     of any kind; the only premises are the two disjointness clauses. *)
  Lemma twin_ctx_birth img log tvs run parked (ξc : CtxId) :
    (∀ h0, run !! h0 ≠ Some ξc) →
    parked !! ξc = None →
    interp img log tvs run parked ==∗
    interp img log tvs run (<[ξc := length log]> parked) ∗
    parkc ξc (length log).
  Proof.
    iIntros (Hnr Hnp) "Hint".
    iDestruct "Hint" as (HM LL) "(Hhp & Hl & Hr & Hp & %Hwf)".
    rewrite /ctx_parked.
    iMod (ghost_map_insert ξc (length log) Hnp with "Hp") as "[Hp Hpk]".
    iModIntro. iFrame "Hpk".
    iExists HM, LL. iFrame "Hhp Hl Hr Hp".
    iPureIntro.
    destruct Hwf as [Hlat Hbnd Hsees Hple Hinj Hpnr Huniq].
    constructor.
    - exact Hlat.
    - exact Hbnd.
    - (* sees *)
      move => ξ0 a0 t0 HL0.
      destruct (decide (ξ0 = ξc)) as [->|Hne].
      + right. exists (length log). rewrite lookup_insert. split; first done.
        exact (Hbnd _ _ _ HL0).
      + destruct (Hsees _ _ _ HL0) as [Hleft | (T & HT & Hle)].
        * by left.
        * right. exists T. rewrite lookup_insert_ne; last congruence.
          by split.
    - (* parked_le *)
      move => ξ0 T.
      destruct (decide (ξ0 = ξc)) as [->|Hne].
      + rewrite lookup_insert. move => [= <-]. lia.
      + rewrite lookup_insert_ne; last congruence. exact (Hple ξ0 T).
    - exact Hinj.
    - (* parked_not_run *)
      move => ξ0 T h0.
      destruct (decide (ξ0 = ξc)) as [->|Hne].
      + move => _. exact (Hnr h0).
      + rewrite lookup_insert_ne; last congruence. exact (Hpnr ξ0 T h0).
    - exact Huniq.
  Qed.

  Lemma twin_ctx_birth_fresh img log tvs run parked :
    interp img log tvs run parked ==∗
    ∃ ξc : CtxId,
      interp img log tvs run (<[ξc := length log]> parked) ∗
      parkc ξc (length log).
  Proof.
    iIntros "Hint".
    destruct (twin_ctx_fresh run parked) as (ξc & Hnr & Hnp).
    iMod (twin_ctx_birth _ _ _ _ _ ξc Hnr Hnp with "Hint") as "[Hint Hpk]".
    iModIntro. iExists ξc. iFrame.
  Qed.

  (* THE ACID TEST, PASSED.  The parent hands a byte fact registered at ξp
     to a child stamped at the log top, and there is NO VIEW SIDE
     CONDITION: the child's park token at [length log] IS the domination
     evidence, and the SEES obligation for the re-registered entry is
     discharged by [twf_bound] alone ([t ≤ length log = T]).  Nothing about
     the parent's hart, the child's future hart, or any view is needed.

     WHAT IS STILL NEEDED, AND IT IS THE FINDING: the LEDGER AUTHORITY.
     Re-registering [a] from ξp to ξc deletes one ledger entry and inserts
     another, so this step -- like every transport -- runs with the interp
     open.  An interp-free fork MINT therefore buys nothing on its own: the
     deposit that follows it needs the interp anyway.

     WHAT IS ALSO STILL NEEDED, AND IT IS THE SECOND FINDING: the stamp is
     only good for facts the parent holds AT THE STAMP.  A byte the parent
     writes AFTER the fork gets a ledger timestamp [t > length log_at_fork]
     and no longer satisfies [t ≤ T], so it cannot be deposited.  If xv6's
     fork copies the address space after building the child's record, the
     child's stamp must be taken at the END of fork, or raised when facts
     are added. *)
  Lemma twin_deposit_at_fork img log tvs run parked ξp ξc a v :
    ξp ≠ ξc →
    interp img log tvs run parked -∗ parkc ξc (length log) -∗ ptc ξp a v ==∗
    interp img log tvs run parked ∗ parkc ξc (length log) ∗ ptc ξc a v.
  Proof.
    iIntros (Hne) "Hint Hpk Hpt".
    iDestruct "Hint" as (HM LL) "(Hhp & Hl & Hr & Hp & %Hwf)".
    rewrite /ctx_parked /ctx_pointsto.
    iDestruct "Hpt" as (t) "[Hpt Hreg]".
    iDestruct (ghost_map_lookup with "Hhp Hpt") as %HHa.
    iDestruct (ghost_map_lookup with "Hl Hreg") as %HLa.
    iDestruct (ghost_map_lookup with "Hp Hpk") as %HpT.
    destruct Hwf as [Hlat Hbnd Hsees Hple Hinj Hpnr Huniq].
    have Hbt : (t ≤ length log)%nat by apply (Hbnd _ _ _ HLa).
    iMod (ghost_map_delete with "Hl Hreg") as "Hl".
    have Hfresh : delete (ξp, a) LL !! (ξc, a) = None.
    { destruct (delete (ξp, a) LL !! (ξc, a)) eqn:Hd; last done.
      exfalso. move: Hd.
      rewrite lookup_delete_ne; last congruence.
      move => Hd. exact (Hne (Huniq _ _ _ _ _ HLa Hd)). }
    iMod (ghost_map_insert (ξc, a) t Hfresh with "Hl") as "[Hl Hreg]".
    iModIntro. iFrame "Hpk".
    iSplitR "Hpt Hreg"; last by (iExists t; iFrame).
    iExists _, _. iFrame "Hhp Hl Hr Hp".
    iPureIntro. constructor.
    - exact Hlat.
    - (* bound *)
      move => ξ0 a0 t0.
      destruct (decide ((ξ0, a0) = (ξc, a))) as [[= -> ->]|Hne0].
      + rewrite lookup_insert. intros [= <-]. exact Hbt.
      + rewrite lookup_insert_ne; last congruence.
        rewrite lookup_delete_Some. move => [_ HL0]. exact (Hbnd _ _ _ HL0).
    - (* sees: THE PARKED ARM, discharged by the stamp *)
      move => ξ0 a0 t0.
      destruct (decide ((ξ0, a0) = (ξc, a))) as [[= -> ->]|Hne0].
      + rewrite lookup_insert. intros [= <-].
        right. exists (length log). by split.
      + rewrite lookup_insert_ne; last congruence.
        rewrite lookup_delete_Some. move => [_ HL0]. exact (Hsees _ _ _ HL0).
    - exact Hple.
    - exact Hinj.
    - exact Hpnr.
    - (* uniq *)
      move => ξ1 ξ2 a0 t1 t2.
      destruct (decide ((ξ1, a0) = (ξc, a))) as [[= -> ->]|Hne1].
      + destruct (decide ((ξ2, a) = (ξc, a))) as [[= ->]|Hne2].
        * move => _ _. done.
        * rewrite lookup_insert. rewrite lookup_insert_ne; last congruence.
          rewrite lookup_delete_Some.
          move => _ [Hne2' HL2]. exfalso.
          have : ξ2 = ξp by exact (Huniq _ _ _ _ _ HL2 HLa).
          congruence.
      + destruct (decide ((ξ2, a0) = (ξc, a))) as [[= -> ->]|Hne2].
        * rewrite lookup_insert_ne; last congruence. rewrite lookup_insert.
          rewrite lookup_delete_Some.
          move => [Hne1' HL1] _. exfalso.
          have : ξ1 = ξp by exact (Huniq _ _ _ _ _ HL1 HLa).
          congruence.
        * rewrite !lookup_insert_ne; [|congruence..].
          rewrite !lookup_delete_Some.
          move => [_ HL1] [_ HL2]. exact (Huniq _ _ _ _ _ HL1 HL2).
  Qed.

  (* A context that owns a byte is LIVE (running or parked) -- the SEES
     invariant read backwards.  Used to separate parent from child. *)
  Lemma twin_pt_live img log tvs run parked ξ a v :
    interp img log tvs run parked -∗ ptc ξ a v -∗
    ⌜(∃ h, run !! h = Some ξ) ∨ (∃ T, parked !! ξ = Some T)⌝.
  Proof.
    iIntros "Hint Hpt".
    iDestruct "Hint" as (HM LL) "(_ & Hl & _ & _ & %Hwf)".
    rewrite /ctx_pointsto. iDestruct "Hpt" as (t) "[_ Hreg]".
    iDestruct (ghost_map_lookup with "Hl Hreg") as %HLa.
    iPureIntro.
    destruct (twf_sees _ _ _ _ _ _ _ Hwf _ _ _ HLa)
      as [(h0 & Hh0 & _) | (T & HT & _)].
    - left. by exists h0.
    - right. by exists T.
  Qed.

  (* Birth and deposit compose in one step: the fork mint hands the child a
     byte the parent held, with no premise beyond the interp. *)
  Lemma twin_fork_with_deposit img log tvs run parked ξp a v :
    interp img log tvs run parked -∗ ptc ξp a v ==∗
    ∃ ξc : CtxId,
      interp img log tvs run (<[ξc := length log]> parked) ∗
      parkc ξc (length log) ∗ ptc ξc a v.
  Proof.
    iIntros "Hint Hpt".
    destruct (twin_ctx_fresh run parked) as (ξc & Hnr & Hnp).
    iDestruct (twin_pt_live with "Hint Hpt") as %Hlive.
    have Hne : ξp ≠ ξc.
    { move => Heq. subst ξp.
      destruct Hlive as [(h0 & Hh0) | (T & HT)].
      - exact (Hnr h0 Hh0).
      - congruence. }
    iMod (twin_ctx_birth _ _ _ _ _ ξc Hnr Hnp with "Hint") as "[Hint Hpk]".
    iMod (twin_deposit_at_fork _ _ _ _ _ ξp ξc a v Hne with "Hint Hpk Hpt")
      as "(Hint & Hpk & Hpt)".
    iModIntro. iExists ξc. iFrame.
  Qed.

  (* ---------------------------------------------------------------- *)
  (** ** 1.3  own_context's exclusivity, and migration                 *)
  (* ---------------------------------------------------------------- *)

  (* SAME HART: satisfiable exactly as the surface states it.  (At the
     surface the hart is ambient -- [CpuId] -- so within one file this IS
     the surface's [own_context_excl].) *)
  Lemma twin_own_context_excl (ξ : CtxId) (h : agent) :
    ownc ξ h -∗ ownc ξ h -∗ False.
  Proof.
    rewrite /own_context. iIntros "H1 H2".
    by iDestruct (ghost_map_elem_ne with "H1 H2") as %Hne.
  Qed.

  (* The surface's [Timeless] instances: satisfiable, and load-bearing --
     [ProofSwtch] strips a [▷] off the target record's token with a [>]
     pattern. *)
  Global Instance twin_own_context_timeless ξ h : Timeless (ownc ξ h).
  Proof. rewrite /own_context. apply _. Qed.

  Global Instance twin_ctx_parked_timeless ξ T : Timeless (parkc ξ T).
  Proof. rewrite /ctx_parked. apply _. Qed.

  (* CROSS HART: NOT free.  Two harts claiming one context are ghost-map
     elements at DIFFERENT keys -- perfectly consistent as resources.
     Ruling it out is RUN-INJECTIVITY, an invariant clause, so it needs
     the interp. *)
  Lemma twin_own_context_run_inj img log tvs run parked ξ h1 h2 :
    interp img log tvs run parked -∗ ownc ξ h1 -∗ ownc ξ h2 -∗ ⌜h1 = h2⌝.
  Proof.
    iIntros "Hint H1 H2".
    iDestruct "Hint" as (HM LL) "(_ & _ & Hr & _ & %Hwf)".
    rewrite /own_context.
    iDestruct (ghost_map_lookup with "Hr H1") as %HR1.
    iDestruct (ghost_map_lookup with "Hr H2") as %HR2.
    iPureIntro. exact (twf_run_inj _ _ _ _ _ _ _ Hwf _ _ _ HR1 HR2).
  Qed.

  (* MIGRATION IS NOT FREE EITHER.  The surface's ruling 2 says a migration
     re-anchors [CpuId] while [cur_ctx] stays, so the thread's facts "do not
     change proposition".  That is TRUE of [ctx_pointsto] (no hart index
     anywhere in it -- the ruling holds) but FALSE of [own_context], which
     is pinned to its hart.  Re-hosting it is a real ghost step and it
     needs view evidence: the new hart must have observed everything the
     context has registered, for which "at the log top" suffices. *)
  Lemma twin_rehost img log tvs run parked ξ h h' :
    run !! h' = None → (length log ≤ tvs h')%nat →
    interp img log tvs run parked -∗ ownc ξ h ==∗
    interp img log tvs (<[h' := ξ]> (delete h run)) parked ∗ ownc ξ h'.
  Proof.
    iIntros (Hfresh Htop) "Hint Hrun".
    iDestruct "Hint" as (HM LL) "(Hhp & Hl & Hr & Hp & %Hwf)".
    rewrite /own_context.
    iDestruct (ghost_map_lookup with "Hr Hrun") as %HRh.
    destruct Hwf as [Hlat Hbnd Hsees Hple Hinj Hpnr Huniq].
    iMod (ghost_map_delete with "Hr Hrun") as "Hr".
    have Hfresh' : delete h run !! h' = None.
    { destruct (decide (h' = h)) as [->|Hne].
      - by rewrite lookup_delete.
      - rewrite lookup_delete_ne; [exact Hfresh | congruence]. }
    iMod (ghost_map_insert h' ξ Hfresh' with "Hr") as "[Hr Hrun]".
    iModIntro. iFrame "Hrun".
    iExists HM, LL. iFrame "Hhp Hl Hr Hp".
    iPureIntro. constructor.
    - exact Hlat.
    - exact Hbnd.
    - (* sees *)
      move => ξ0 a0 t0 HL0.
      destruct (decide (ξ0 = ξ)) as [->|Hne].
      + left. exists h'. rewrite lookup_insert. split; first done.
        apply visibleb_below. have := Hbnd _ _ _ HL0. lia.
      + destruct (Hsees _ _ _ HL0) as [(h0 & Hh0 & Hv0) | (T & HT & Hle)].
        * left. exists h0. split; last done.
          have Hneh' : h0 ≠ h'.
          { move => Heq. subst h0. rewrite Hfresh in Hh0. done. }
          have Hneh : h0 ≠ h.
          { move => Heq. subst h0. apply Hne. congruence. }
          rewrite lookup_insert_ne; last congruence.
          rewrite lookup_delete_ne; [exact Hh0 | congruence].
        * right. by exists T.
    - exact Hple.
    - (* run_inj *)
      move => h1 h2 ξ0.
      destruct (decide (h1 = h')) as [->|Hne1];
        destruct (decide (h2 = h')) as [->|Hne2].
      + done.
      + rewrite lookup_insert lookup_insert_ne; last congruence.
        rewrite lookup_delete_Some. move => [= Heq] [Hnh HR2].
        exfalso. apply Hnh. apply (Hinj h h2 ξ0); [congruence | exact HR2].
      + rewrite lookup_insert_ne; last congruence. rewrite lookup_insert.
        rewrite lookup_delete_Some. move => [Hnh HR1] [= Heq].
        exfalso. apply Hnh. apply (Hinj h h1 ξ0); [congruence | exact HR1].
      + rewrite !lookup_insert_ne; [|congruence..].
        rewrite !lookup_delete_Some. move => [_ HR1] [_ HR2].
        exact (Hinj _ _ _ HR1 HR2).
    - (* parked_not_run *)
      move => ξ0 T h0 HT.
      destruct (decide (h0 = h')) as [->|Hne].
      + rewrite lookup_insert. move => [= Heq].
        apply (Hpnr ξ0 T h HT). congruence.
      + rewrite lookup_insert_ne; last congruence.
        rewrite lookup_delete_Some. move => [_ HR0].
        exact (Hpnr _ _ _ HT HR0).
    - exact Huniq.
  Qed.

  (* ---------------------------------------------------------------- *)
  (** ** 1.4  SUSPECT (3): the swtch exchange                          *)
  (* ---------------------------------------------------------------- *)

  (* PARK-THEN-RESUME COMPOSES ON ONE HART.  The question was whether the
     intermediate state (h running nothing) is forbidden: it is NOT.
     [twin_park] deletes h from [run]; [twin_resume] asks only for
     [run !! h' = None], which [lookup_delete] supplies at h' = h.  So the
     exchange is a DERIVED lemma, not a new primitive.

     The premise [T ≤ tvs h] is the whole content of the crossing: THE
     RESUMING HART'S VIEW MUST HAVE PASSED THE TARGET'S PUBLICATION
     TIMESTAMP.  Nothing else relates the two harts' states. *)
  Lemma twin_swtch_exchange img log tvs run parked ξr ξp T h :
    (T ≤ tvs h)%nat →
    interp img log tvs run parked -∗ ownc ξr h -∗ parkc ξp T ==∗
    interp img log tvs
      (<[h := ξp]> (delete h run))
      (delete ξp (<[ξr := length log]> parked)) ∗
    parkc ξr (length log) ∗ ownc ξp h.
  Proof.
    iIntros (Hcov) "Hint Hrun Hpark".
    iMod (twin_park with "Hint Hrun") as "[Hint Hparkr]".
    iMod (twin_resume _ _ _ _ _ _ _ _ _ ξp T h with "Hint Hpark")
      as "[Hint Hrun]".
    { by rewrite lookup_delete. }
    { exact Hcov. }
    iModIntro. iFrame.
  Qed.

  (* THE KERNEL-SIDE FORM.  [T] is the target record's publication
     timestamp -- a number no kernel proof can see.  It does not have to:
     the invariant already knows [T ≤ length log] ([twf_parked_le]), so
     "THIS HART IS AT THE LOG TOP" implies the premise.  And "at the log
     top" is exactly what an AMO acquire of [p->lock] delivers, and exactly
     the evidence [ctx_dom] is minted from ([TsoCtxTwin.ctx_dom_mint]).
     SUSPECTS (2) AND (3) WANT THE SAME TOKEN. *)
  Lemma twin_swtch_exchange_at_top img log tvs run parked ξr ξp T h :
    (length log ≤ tvs h)%nat →
    interp img log tvs run parked -∗ ownc ξr h -∗ parkc ξp T ==∗
    interp img log tvs
      (<[h := ξp]> (delete h run))
      (delete ξp (<[ξr := length log]> parked)) ∗
    parkc ξr (length log) ∗ ownc ξp h.
  Proof.
    iIntros (Htop) "Hint Hrun Hpark".
    iAssert (⌜(T ≤ length log)%nat⌝)%I as %HTle.
    { iDestruct "Hint" as (HM LL) "(_ & _ & _ & Hp & %Hwf)".
      rewrite /ctx_parked.
      iDestruct (ghost_map_lookup with "Hp Hpark") as %HpT.
      iPureIntro. exact (twf_parked_le _ _ _ _ _ _ _ Hwf _ _ HpT). }
    iApply (twin_swtch_exchange with "Hint Hrun Hpark"). lia.
  Qed.

  (* ---------------------------------------------------------------- *)
  (** ** 1.5  SUSPECT (2): CtxMorph                                    *)
  (* ---------------------------------------------------------------- *)

  (* A WELL-FORMED CONFIGURATION with a registered byte, used to refute the
     class.  ξ = 0 is PARKED and owns byte [a]; ξ' = 1 RUNS on hart h.
     Every clause of the twin's invariant holds, so this really is a state
     the machine can be in -- the refutation is not an artefact of an
     impossible ghost configuration.  The four authorities come out
     SEPARATELY rather than packed into [tso_interp] (which existentially
     quantifies the heap and ledger maps) precisely so the ledger map stays
     visible to the refutation. *)
  Lemma twin_populated (a : Z) (v : bv 8) (tvs : agent → nat) (h : agent) :
    ⊢ |==> ∃ γh γl γr γp : gname,
        ghost_map_auth γh 1 {[a := (0%nat, v)]} ∗
        ghost_map_auth γl 1 {[(0%nat, a) := 0%nat]} ∗
        ghost_map_auth γr 1 {[h := 1%nat]} ∗
        ghost_map_auth γp 1 {[0%nat := 0%nat]} ∗
        ⌜twin_wf (img_fun {[a := v]}) [] tvs {[h := 1%nat]}
                 {[0%nat := 0%nat]} {[a := (0%nat, v)]}
                 {[(0%nat, a) := 0%nat]}⌝ ∗
        ctx_pointsto γh γl 0%nat a v ∗
        own_context γr 1%nat h.
  Proof.
    iMod (ghost_map_alloc {[a := (0%nat, v)]}) as (γh) "[Hh Hhf]".
    iMod (ghost_map_alloc {[(0%nat, a) := 0%nat]}) as (γl) "[Hl Hlf]".
    iMod (ghost_map_alloc ({[h := 1%nat]} : gmap agent CtxId))
      as (γr) "[Hr Hrf]".
    iMod (ghost_map_alloc ({[0%nat := 0%nat]} : gmap CtxId nat))
      as (γp) "[Hp _]".
    rewrite !big_sepM_singleton.
    iModIntro. iExists γh, γl, γr, γp. iFrame "Hh Hl Hr Hp".
    iSplitR; last first.
    { rewrite /ctx_pointsto /own_context. iFrame "Hrf".
      iExists 0%nat. iFrame. }
    iPureIntro. constructor.
    - (* latest *)
      move => a0 t0 v0. rewrite lookup_singleton_Some.
      move => [<- [= <- <-]]. split.
      + rewrite /log_byte /img_fun lookup_singleton //.
      + move => t' Ht'. destruct t' as [|i]; first lia.
        rewrite /log_byte /=. done.
    - (* bound *)
      move => ξ0 a0 t0. rewrite lookup_singleton_Some.
      move => [_ <-]. simpl. lia.
    - (* sees *)
      move => ξ0 a0 t0. rewrite lookup_singleton_Some.
      move => [Hk <-]. injection Hk as <- <-.
      right. exists 0%nat. split; [by rewrite lookup_singleton | lia].
    - (* parked_le *)
      move => ξ0 T. rewrite lookup_singleton_Some. move => [_ <-]. simpl. lia.
    - (* run_inj *)
      move => h1 h2 ξ0.
      rewrite !lookup_singleton_Some. move => [Hk1 _] [Hk2 _]. congruence.
    - (* parked_not_run *)
      move => ξ0 T h0. rewrite lookup_singleton_Some.
      move => [<- _]. rewrite lookup_singleton_Some.
      move => [_ Hbad]. done.
    - (* uniq *)
      move => ξ1 ξ2 a0 t1 t2.
      rewrite !lookup_singleton_Some.
      move => [Hk1 _] [Hk2 _].
      injection Hk1 => _ Hx1. injection Hk2 => _ Hx2. congruence.
  Qed.

  (* THE REFUTATION.  [CtxMorph]'s conclusion is a bare [==∗]: no interp,
     no authority.  But re-registering a byte at another context MOVES a
     ledger entry, and the ledger authority is inside the interp.  Applied
     in the well-formed configuration above, the class's own conclusion
     contradicts the ledger authority it never touched.

     Stated over ALL gnames, because the configuration allocates fresh
     ones; that is also the honest reading of the class, which is [Global]
     in a section over an arbitrary [riscvGS]. *)
  Lemma no_ctx_morph_pointsto (a : Z) (v : bv 8) :
    (∀ (γh γl γr : gname) (log : list wmsg) (tvs : agent → nat)
       (ξ ξ' : CtxId) (a0 : Z) (v0 : bv 8),
       ⊢ ctx_dom γr log tvs ξ ξ' -∗ ctx_pointsto γh γl ξ a0 v0 ==∗
         ctx_dom γr log tvs ξ ξ' ∗ ctx_pointsto γh γl ξ' a0 v0) → False.
  Proof.
    intros Hmorph. apply (bupd_absurd Σ).
    iMod (twin_populated a v (λ _, 0%nat) 0%nat)
      as (γh γl γr γp) "(_ & Hl & _ & _ & _ & Hpt & Hrun)".
    iDestruct (ctx_dom_mint γr [] (λ _, 0%nat) 0%nat 1%nat 0%nat
                 with "Hrun") as "Hdom".
    { simpl. lia. }
    iMod (Hmorph γh γl γr [] (λ _, 0%nat) 0%nat 1%nat a v
            with "Hdom Hpt") as "[_ Hpt']".
    rewrite /ctx_pointsto. iDestruct "Hpt'" as (t) "[_ Hreg]".
    iDestruct (ghost_map_lookup with "Hl Hreg") as %Hlk.
    rewrite lookup_singleton_ne in Hlk; last done.
    done.
  Qed.

  (* THE HONEST SHAPE: thread the interp, exactly as [twin_transport] does.
     Every structural instance of the surface's class survives verbatim. *)
  Class CtxMorphI (R : CtxId → iProp Σ) := ctx_morph_i :
    ∀ img log tvs run parked ξ ξ',
      interp img log tvs run parked -∗ domc log tvs ξ ξ' -∗ R ξ ==∗
      interp img log tvs run parked ∗ domc log tvs ξ ξ' ∗ R ξ'.

  #[local] Instance ctx_morph_i_const (P : iProp Σ) : CtxMorphI (λ _, P).
  Proof. iIntros (img log tvs run parked ξ ξ') "Hi Hd HP !>". iFrame. Qed.

  #[local] Instance ctx_morph_i_pointsto (a : Z) (v : bv 8) :
    CtxMorphI (λ ξ, ptc ξ a v).
  Proof.
    iIntros (img log tvs run parked ξ ξ') "Hi Hd HP".
    iApply (twin_transport with "Hi Hd HP").
  Qed.

  #[local] Instance ctx_morph_i_sep (R1 R2 : CtxId → iProp Σ) :
    CtxMorphI R1 → CtxMorphI R2 → CtxMorphI (λ ξ, R1 ξ ∗ R2 ξ)%I.
  Proof.
    iIntros (H1 H2 img log tvs run parked ξ ξ') "Hi Hd [HR1 HR2]".
    iMod (ctx_morph_i with "Hi Hd HR1") as "(Hi & Hd & HR1)".
    iMod (ctx_morph_i with "Hi Hd HR2") as "(Hi & Hd & HR2)".
    iModIntro. iFrame.
  Qed.

  #[local] Instance ctx_morph_i_exist {A} (Φ : A → CtxId → iProp Σ) :
    (∀ x, CtxMorphI (Φ x)) → CtxMorphI (λ ξ, ∃ x, Φ x ξ)%I.
  Proof.
    iIntros (HΦ img log tvs run parked ξ ξ') "Hi Hd [%x HR]".
    iMod (ctx_morph_i with "Hi Hd HR") as "(Hi & Hd & HR)".
    iModIntro. iFrame "Hi Hd". iExists x. iExact "HR".
  Qed.

  #[local] Instance ctx_morph_i_big_sepL {A} (l : list A)
      (Φ : nat → A → CtxId → iProp Σ) :
    (∀ i x, CtxMorphI (Φ i x)) →
    CtxMorphI (λ ξ, [∗ list] i ↦ x ∈ l, Φ i x ξ)%I.
  Proof.
    revert Φ. induction l as [|x l IH] => Φ HΦ.
    - iIntros (img log tvs run parked ξ ξ') "Hi Hd _ !>". by iFrame.
    - iIntros (img log tvs run parked ξ ξ') "Hi Hd [HR HRs]".
      iMod (ctx_morph_i with "Hi Hd HR") as "(Hi & Hd & HR)".
      iMod (IH (λ i y, Φ (S i) y) _ img log tvs run parked ξ ξ'
              with "Hi Hd HRs") as "(Hi & Hd & HRs)".
      iModIntro. iFrame.
  Qed.

  (* The surface's composition acid test, at the honest shape. *)
  Lemma ctx_morph_i_demo (a1 a2 : Z) (v1 : bv 8) (P : iProp Σ) :
    CtxMorphI (λ ξ, ptc ξ a1 v1 ∗
                    (∃ v2 : bv 8, ⌜v2 ≠ v1⌝ ∗ ptc ξ a2 v2) ∗ P)%I.
  Proof. apply _. Qed.

  (* ---------------------------------------------------------------- *)
  (** ** 1.6  The dfrac generalization of the twin's points-to         *)
  (* ---------------------------------------------------------------- *)

  (* The twin's [ctx_pointsto] is fraction-1 only, so the surface's
     [ctx_pointsto_agree] / [_frac_split] / [_persist] and the discarded
     [Persistent] instance had no twin image at all.  Adding the dq axis to
     BOTH components is mechanical and is done here.  What it exposes is
     the real design question, [reh_pt_one_context] below. *)
  Definition ctx_pointsto_dq (ξ : CtxId) (a : Z) (dq : dfrac) (v : bv 8)
      : iProp Σ :=
    (∃ t : nat, a ↪[γheap]{dq} (t, v) ∗ (ξ, a) ↪[γledger]{dq} t)%I.

  Lemma reh_pt_dq_full ξ a v :
    ctx_pointsto_dq ξ a (DfracOwn 1) v ⊣⊢ ptc ξ a v.
  Proof. rewrite /ctx_pointsto_dq /ctx_pointsto //. Qed.

  Global Instance reh_pt_dq_timeless ξ a dq v :
    Timeless (ctx_pointsto_dq ξ a dq v).
  Proof. rewrite /ctx_pointsto_dq. apply _. Qed.

  Global Instance reh_pt_dq_discarded_persistent ξ a v :
    Persistent (ctx_pointsto_dq ξ a DfracDiscarded v).
  Proof. rewrite /ctx_pointsto_dq. apply _. Qed.

  (* CROSS-CONTEXT AGREEMENT: satisfiable, and it needs no interp -- the
     heap component is keyed by the BYTE, not by the context. *)
  Lemma reh_pt_dq_agree ξ1 ξ2 a dq1 v1 dq2 v2 :
    ctx_pointsto_dq ξ1 a dq1 v1 -∗ ctx_pointsto_dq ξ2 a dq2 v2 -∗ ⌜v1 = v2⌝.
  Proof.
    rewrite /ctx_pointsto_dq.
    iIntros "[%t1 [H1 _]] [%t2 [H2 _]]".
    iDestruct (ghost_map_elem_agree with "H1 H2") as %Heq.
    iPureIntro. by injection Heq.
  Qed.

  Lemma reh_pt_dq_ne ξ1 ξ2 a1 a2 dq v1 v2 :
    ctx_pointsto_dq ξ1 a1 (DfracOwn 1) v1 -∗
    ctx_pointsto_dq ξ2 a2 dq v2 -∗ ⌜a1 ≠ a2⌝.
  Proof.
    rewrite /ctx_pointsto_dq.
    iIntros "[%t1 [H1 _]] [%t2 [H2 _]]".
    by iDestruct (ghost_map_elem_ne with "H1 H2") as %Hne.
  Qed.

  Lemma reh_pt_dq_frac_split ξ a q1 q2 v :
    ctx_pointsto_dq ξ a (DfracOwn (q1 + q2)) v ⊣⊢
    ctx_pointsto_dq ξ a (DfracOwn q1) v ∗ ctx_pointsto_dq ξ a (DfracOwn q2) v.
  Proof.
    rewrite /ctx_pointsto_dq. iSplit.
    - iIntros "(%t & [Hh1 Hh2] & [Hl1 Hl2])".
      iSplitL "Hh1 Hl1"; iExists t; iFrame.
    - iIntros "[(%t1 & Hh1 & Hl1) (%t2 & Hh2 & Hl2)]".
      iDestruct (ghost_map_elem_combine with "Hh1 Hh2") as "[Hh _]".
      iDestruct (ghost_map_elem_combine with "Hl1 Hl2") as "[Hl _]".
      rewrite !dfrac_op_own. iExists t1. iFrame.
  Qed.

  Lemma reh_pt_dq_persist ξ a dq v :
    ctx_pointsto_dq ξ a dq v ==∗ ctx_pointsto_dq ξ a DfracDiscarded v.
  Proof.
    rewrite /ctx_pointsto_dq. iIntros "(%t & Hh & Hl)".
    iMod (ghost_map_elem_persist with "Hh") as "Hh".
    iMod (ghost_map_elem_persist with "Hl") as "Hl".
    iModIntro. iExists t. iFrame.
  Qed.

  (* THE LOAD RULE SURVIVES THE dq AXIS UNCHANGED (it only LOOKS the
     ledger up, never updates it): the read-side laws generalize for
     free. *)
  Lemma twin_load_ok_dq img log tvs run parked ξ h a dq v :
    interp img log tvs run parked ∗ ownc ξ h ∗ ctx_pointsto_dq ξ a dq v ⊢
    ⌜∀ tv', (tvs h ≤ tv')%nat →
       tso_read (img_fun img) log h tv' a = Some v⌝.
  Proof.
    iIntros "(Hint & Hrun & Hpt)".
    iDestruct "Hint" as (HM LL) "(Hh & Hl & Hr & Hp & %Hwf)".
    rewrite /own_context /ctx_pointsto_dq.
    iDestruct "Hpt" as (t) "[Hpt Hreg]".
    iDestruct (ghost_map_lookup with "Hh Hpt") as %HHa.
    iDestruct (ghost_map_lookup with "Hl Hreg") as %HLa.
    iDestruct (ghost_map_lookup with "Hr Hrun") as %HRh.
    iPureIntro.
    destruct Hwf as [Hlat Hbnd Hsees Hple Hinj Hpnr Huniq].
    have Hvis : visibleb h (tvs h) log t = true.
    { destruct (Hsees _ _ _ HLa) as [(h0 & Hh0 & Hv0) | (T & HpT & _)].
      - by have -> : h = h0 by apply (Hinj h h0 ξ).
      - exfalso. exact (Hpnr _ _ _ HpT HRh). }
    move => tv' Htv'.
    apply (tso_read_of_latest _ _ _ _ _ t).
    - by apply (Hlat _ _ _ HHa).
    - eapply visibleb_le; last exact Hvis. lia.
  Qed.

  (* THE FINDING THE dq AXIS EXPOSES.  Per-byte ledger uniqueness
     ([twf_uniq]) is load-bearing for transport's re-registration, and it
     says: ALL facts about one byte live in ONE context, whatever their
     fractions.  So under the twin's design a byte fact can never be SHARED
     across two threads -- not at a fraction, not persistently.  In
     particular a DISCARDED [ctx_pointsto] is pinned to its context
     forever, since its ledger entry can no longer be deleted -- and
     deleting it is exactly what transport does.  [ctx_pointsto_persist]
     and [ctx_morph_pointsto] are therefore in tension at TSO. *)
  Lemma reh_pt_one_context img log tvs run parked ξ1 ξ2 a dq1 v1 dq2 v2 :
    interp img log tvs run parked -∗
    ctx_pointsto_dq ξ1 a dq1 v1 -∗ ctx_pointsto_dq ξ2 a dq2 v2 -∗
    ⌜ξ1 = ξ2⌝.
  Proof.
    iIntros "Hint H1 H2".
    iDestruct "Hint" as (HM LL) "(_ & Hl & _ & _ & %Hwf)".
    rewrite /ctx_pointsto_dq.
    iDestruct "H1" as (t1) "[_ Hr1]".
    iDestruct "H2" as (t2) "[_ Hr2]".
    iDestruct (ghost_map_lookup with "Hl Hr1") as %HL1.
    iDestruct (ghost_map_lookup with "Hl Hr2") as %HL2.
    iPureIntro. exact (twf_uniq _ _ _ _ _ _ _ Hwf _ _ _ _ _ HL1 HL2).
  Qed.

End rehearsal.

(* ================================================================== *)
(** * 2.  What an interp-FREE mint needs to be true                    *)
(* ================================================================== *)

(* [no_own_context_alloc] and [no_ctx_parked_alloc] both fail for one
   structural reason: in the twin a context identity is a bare [nat], so
   EVERY claim about it is a fragment of some GLOBAL authority, and no
   fragment of a fixed-gname authority is allocatable from nothing.

   The real surface does not have that problem: [TsoCtx.CtxId] is
   [MkCtxId (γ : gname)] -- the identity CARRIES ITS OWN GHOST NAME.  This
   section shows that with such an identity an interp-free allocation works
   exactly as ruled:

     - allocating a never-yet-run identity is a PURE ghost step, no interp
       ([ctx_unstarted_alloc]);
     - and the token is not vacuous: the interp holding one HALF per live
       context ([roster]) turns the freshly allocated whole into precisely
       the freshness side conditions [twin_ctx_mint] / [twin_ctx_birth] ask
       for ([roster_fresh]), which are otherwise unobtainable.

   The unit payload is deliberate: the token's content IS its identity. *)
Section roster.
  Context {Σ : gFunctors} `{!ghost_varG Σ ()}.

  (* An identity that carries its own name. *)
  Notation CtxG := gname (only parsing).

  (* "ξ exists and has never been enrolled anywhere." *)
  Definition ctx_unstarted (ξ : CtxG) : iProp Σ := ghost_var ξ 1 ().
  (* the interp's half, one per live (running or parked) context *)
  Definition ctx_live (ξ : CtxG) : iProp Σ := ghost_var ξ (1/2) ().
  Definition roster (S : gset CtxG) : iProp Σ :=
    ([∗ set] ξ ∈ S, ctx_live ξ)%I.

  (* (1) FREE ALLOCATION -- no interp, no authority, no premise.  This is
     the shape a fork mint wants: fork creates an identity, and the child
     does not get [own_context] yet. *)
  Lemma ctx_unstarted_alloc : ⊢ |==> ∃ ξ : CtxG, ctx_unstarted ξ.
  Proof.
    iMod (ghost_var_alloc ()) as (γ) "H". iModIntro. by iExists γ.
  Qed.

  (* (2) AND IT CARRIES FRESHNESS.  This is the half that makes the free
     mint usable: without it, a freely allocated identity could collide
     with a live one and the mint's RUN-INJECTIVITY / PARKED-NOT-RUNNING
     premises would be unobtainable. *)
  Lemma roster_fresh (S : gset CtxG) (ξ : CtxG) :
    roster S -∗ ctx_unstarted ξ -∗ ⌜ξ ∉ S⌝.
  Proof.
    iIntros "HS Hξ".
    destruct (decide (ξ ∈ S)) as [Hin|Hnin]; last by iPureIntro.
    rewrite /roster (big_sepS_delete _ S ξ) //.
    iDestruct "HS" as "[Hhalf _]".
    rewrite /ctx_live /ctx_unstarted.
    iDestruct (ghost_var_valid_2 with "Hξ Hhalf") as %[Hv _].
    exfalso. by apply (Qp.not_add_le_l 1 (1/2)).
  Qed.

  (* (3) ENROLMENT: the mint keeps a half as its own witness and hands the
     other half to the roster, which is how the roster stays a faithful
     index of the live contexts. *)
  Lemma roster_enroll (S : gset CtxG) (ξ : CtxG) :
    roster S -∗ ctx_unstarted ξ ==∗ roster ({[ξ]} ∪ S) ∗ ctx_live ξ.
  Proof.
    iIntros "HS Hξ".
    iDestruct (roster_fresh with "HS Hξ") as %Hnin.
    rewrite /ctx_unstarted /ctx_live.
    iEval (rewrite -{1}(Qp.div_2 1)) in "Hξ".
    iDestruct "Hξ" as "[H1 H2]".
    iModIntro. iFrame "H2".
    rewrite /roster big_sepS_union; last set_solver.
    rewrite big_sepS_singleton. iFrame.
  Qed.

End roster.
