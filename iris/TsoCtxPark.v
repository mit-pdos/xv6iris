(* TsoCtxPark.v -- THE PARK BOX (tso-port.md §0.42′; tso-machine-flip.md
   A6.127 §5–§6): the four laws swtch's token exchange needs on top of
   [TsoCtx]'s public gates, and nothing else.

   THE PROBLEM THEY SOLVE.  A parked thread token [ctx_parked ξ T] carries an
   absolute stamp [T = max(K, W)] that nobody outside the token knows, so a
   resumer had no way to state the premise [T ≤ K'] of [TsoCtx.ctx_resume]
   -- [ProofSwtch:157] conjured the receipt.  The owner's ruling makes the
   token RELATIVE: it travels beside a floor on another context,
   [ctx_parked ξ T ∗ ctx_floor ξr T], and the resumer's own running token
   cashes that floor into the receipt ([TsoCtx.own_context_floor_view]).

   WHAT THE RELATUM IS.  A running context's bound is capped by its hart's
   view and a buffered store sits above it, so no running context can floor
   a fresh park (the parker's stamp covers ITS buffered stores).  The
   relatum is therefore a fresh STAMPED context -- the "park box" -- whose
   stamp is raised past the parker's for free ([ctx_parked_raise]; a
   stamped context has no hart tie), and which the scheduler makes the
   LOCK's context at its release ([WpLock.lock_finisher_in]).  From the lock
   on, the floor rides the ordinary transport ([TsoCtx.ctx_floor_dom]):
   [ctx_dom ξlock ξnew] at the acquire lands it on the winner's own context,
   and resume is [ctx_resume_floor] -- the acquire morph applied to the
   token.

   WHY ITS OWN FILE: the [TsoCtxAbsorbLb.v] precedent -- forty lines off
   [TsoCtx]'s PUBLIC unseal lemmas, needing nothing the kit does not export,
   so [TsoCtx.v] (under the whole tree) is not rebuilt. *)
From Stdlib Require Import ZArith Lia.
From stdpp Require Import gmap.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import auth.
From iris.base_logic.lib Require Import ghost_map mono_nat.
Require Import RiscvLang RiscvPtsto.
Require Import TsoMemPa TsoGhost.
Require Import TsoCtx.

Section Park.
  Context `{!riscvGS Σ}.

  (* THE BOX'S STAMP RISES AT A LOG-LENGTH RECEIPT.  A stamped context has
     no hart, so raising its stamp falsifies nothing: every clean fact of
     the box is still under the (larger) stamp, and its dirty positions
     were under the old one.  What comes out beside the box is the floor
     the link needs. *)
  Lemma ctx_parked_raise (ξ : CtxId) (T T' : nat) :
    llb loglen_name T' -∗ ctx_parked ξ T ==∗
    ctx_parked ξ (Nat.max T T') ∗ ctx_floor ξ T'.
  Proof.
    rewrite !ctx_parked_unseal /ctx_parked_def.
    iIntros "#HT' (%D & [Hb Hd] & #HT & %HDT)".
    iMod (mono_nat_own_update (Nat.max T T') with "Hb") as "[Hb #Hlb]"; first lia.
    iModIntro. iSplitL.
    - iExists D. iFrame "Hb Hd".
      iSplitR; first by iApply (llb_max with "HT HT'").
      iPureIntro. intros k Hk. have := HDT _ Hk. lia.
    - rewrite /ctx_floor /llb. iLeft.
      iApply (mono_nat_lb_own_le with "Hlb"). lia.
  Qed.

  (* PARK INTO A BOX: the parker's token parks ([TsoCtx.ctx_park], stamp
     [max(K,W)] off its own receipts) and the box's stamp is raised past it,
     leaving the link [ctx_parked ξ T ∗ ctx_floor ξb T].  Interp-free. *)
  Lemma ctx_park_box `{CID : CpuId} (ξ ξb : CtxId) (Tb : nat) :
    own_context ξ -∗ ctx_parked ξb Tb ==∗
    ∃ (T Tb' : nat), ⌜(Tb ≤ Tb')%nat⌝ ∗ ctx_parked ξb Tb' ∗
                     ctx_parked ξ T ∗ ctx_floor ξb T.
  Proof.
    iIntros "Hrun Hbox".
    iMod (ctx_park with "Hrun") as (T) "Hpk".
    iDestruct (ctx_parked_llb with "Hpk") as "[Hpk #HT]".
    iMod (ctx_parked_raise ξb Tb T with "HT Hbox") as "[Hbox #Hfl]".
    iModIntro. iExists T, (Nat.max Tb T). iFrame "Hbox Hpk Hfl". iPureIntro. lia.
  Qed.

  (* RESUME AGAINST A FLOOR: the resumer's running token turns the link's
     floor into the stable pair [hart_view_lb K ∗ ⌜T ≤ K⌝]
     ([TsoCtx.own_context_floor_view]) and [TsoCtx.ctx_resume] does the
     rest.  The resumer's token comes straight back. *)
  Lemma ctx_resume_floor `{CID : CpuId} (ξ ξr : CtxId) (T : nat) :
    own_context ξr -∗ ctx_parked ξ T -∗ ctx_floor ξr T ==∗
    own_context ξr ∗ own_context ξ.
  Proof.
    iIntros "Hrun Hpk #Hfl".
    iDestruct (own_context_floor_view ξr T with "Hrun Hfl")
      as "[Hrun (%K & #HK & %HTK)]".
    iAssert (hart_view_lb K) as "#HK'".
    { rewrite hart_view_lb_unseal /hart_view_lb_def. iExact "HK". }
    iMod (ctx_resume ξ T K HTK with "HK' Hpk") as "Hrun'".
    iModIntro. iFrame "Hrun Hrun'".
  Qed.

  (* THE FLOOR IS A TRANSPORTABLE PAYLOAD MEMBER -- [TsoCtx.ctx_floor_dom]
     as an instance, so a payload whose only context-dependence is a floor
     (the parked record's slot, [SchedCtx.proc_ctx]) is morphable by
     instance search alone. *)
  Global Instance ctx_morph_floor (lo : nat) : CtxMorph (λ ξ, ctx_floor ξ lo).
  Proof.
    iIntros (ξ ξ') "Hd #Hfl".
    iDestruct (ctx_floor_dom with "Hd Hfl") as "[Hd #Hfl']".
    iModIntro. iFrame "Hd Hfl'".
  Qed.

  (* A FRESH BOX WITH ITS STAMP ALREADY OVER A STAMPED CONTEXT'S: what the
     child-record producers (fork, userinit) mint beside a freshly
     deposited child. *)
  Lemma ctx_box_over (ξ : CtxId) (T : nat) :
    ctx_parked ξ T ==∗ ctx_parked ξ T ∗ ∃ ξb : CtxId, ctx_parked ξb T ∗ ctx_floor ξb T.
  Proof.
    iIntros "Hpk".
    iDestruct (ctx_parked_llb with "Hpk") as "[Hpk #HT]".
    iMod ctx_parked_alloc as (ξb) "Hbox".
    iMod (ctx_parked_raise ξb 0 T with "HT Hbox") as "[Hbox #Hfl]".
    iModIntro. iFrame "Hpk". iExists ξb. rewrite Nat.max_0_l. iFrame "Hbox Hfl".
  Qed.

End Park.
