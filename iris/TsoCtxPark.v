(* TsoCtxPark.v -- THE PARK BOX (tso-port.md §0.42′; tso-machine-flip.md
   A6.127 §5–§6), on main: the STATEMENTS verbatim, the bodies SC-trivial.

   THE PROBLEM THEY SOLVE.  A parked thread token [ctx_parked ξ T] carries an
   absolute stamp [T = max(K, W)] that nobody outside the token knows, so a
   resumer had no way to state the premise [T ≤ K'] of [TsoCtx.ctx_resume]
   -- [ProofSwtch] conjured the receipt (through the SC shim's
   [hart_view_lb_any]).  The owner's ruling makes the token RELATIVE: it
   travels beside a floor on another context, [ctx_parked ξ T ∗ ctx_floor ξr
   T], and the resumer's own running token cashes that floor into the
   receipt ([TsoCtx.own_context_floor_view]).

   WHAT THE RELATUM IS.  A running context's bound is capped by its hart's
   view and a buffered store sits above it, so no running context can floor
   a fresh park (the parker's stamp covers ITS buffered stores).  The
   relatum is therefore a fresh STAMPED context -- the "park box" -- whose
   stamp is raised past the parker's for free ([ctx_parked_raise]; a
   stamped context has no hart tie), and which the scheduler makes the
   LOCK's context at its release ([WpLockIn.lock_finisher_in]).  From the
   lock on, the floor rides the ordinary transport ([TsoCtx.ctx_floor_dom]):
   [ctx_dom ξlock ξnew] at the acquire lands it on the winner's own context,
   and resume is [ctx_resume_floor] -- the acquire morph applied to the
   token.

   WHAT IS TRIVIAL HERE, AND WHY.  Main is SC: [ctx_parked], [ctx_floor],
   [hart_view_lb] and [log_lb] are sealed with trivial bodies ([True], or
   [True ∨ …] for the parked token), so [ctx_parked ξ T] does not in fact
   mention [T] and every stamp arithmetic below discharges by the unseal
   lemmas.  There is no [mono_nat] update in [ctx_parked_raise] and no
   [llb_max]: the raise hands the token straight back and mints the floor
   from [ctx_floor_def].  The STATEMENTS are the T-leg's exactly, which is
   the seal principle -- at the TSO cutover the bodies are replaced and no
   consumer above this file moves.  [TsoCtxAbsorbLb.v] is the precedent for
   exactly this arrangement, down to the file's reason for existing.

   WHY ITS OWN FILE: the [TsoCtxAbsorbLb.v] precedent -- forty lines off
   [TsoCtx]'s PUBLIC unseal lemmas, needing nothing the kit does not export,
   so [TsoCtx.v] (under the whole tree) is not rebuilt.  In particular the
   T-leg's [TsoMemPa] / [TsoGhost] imports are NOT taken: they are below the
   seal and do not exist on main. *)
From Stdlib Require Import ZArith Lia.
From stdpp Require Import gmap.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import own ghost_var invariants.
Require Import RiscvLang RiscvPtsto.
Require Import TsoCtx.

Section Park.
  Context `{!riscvGS Σ}.

  (* THE BOX'S STAMP RISES AT A LOG-LENGTH RECEIPT.  A stamped context has
     no hart, so raising its stamp falsifies nothing: every clean fact of
     the box is still under the (larger) stamp, and its dirty positions
     were under the old one.  What comes out beside the box is the floor
     the link needs.  (SC: the sealed token does not mention its stamp and
     the floor is [True] -- the T-leg's [mono_nat] update and [llb_max]
     have no counterpart below.) *)
  Lemma ctx_parked_raise (ξ : CtxId) (T T' : nat) :
    log_lb T' -∗ ctx_parked ξ T ==∗
    ctx_parked ξ (Nat.max T T') ∗ ctx_floor ξ T'.
  Proof.
    rewrite !ctx_parked_unseal /ctx_parked_def
            ctx_floor_unseal /ctx_floor_def.
    iIntros "_ Hpk". iModIntro. by iFrame "Hpk".
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
     rest.  The resumer's token comes straight back.  (Main's
     [own_context_floor_view] already speaks [hart_view_lb], so the T-leg's
     [llb]-to-[hart_view_lb] re-assertion has nothing to do here.) *)
  Lemma ctx_resume_floor `{CID : CpuId} (ξ ξr : CtxId) (T : nat) :
    own_context ξr -∗ ctx_parked ξ T -∗ ctx_floor ξr T ==∗
    own_context ξr ∗ own_context ξ.
  Proof.
    iIntros "Hrun Hpk #Hfl".
    iDestruct (own_context_floor_view ξr T with "Hrun Hfl")
      as "[Hrun (%K & #HK & %HTK)]".
    iMod (ctx_resume ξ T K HTK with "HK Hpk") as "Hrun'".
    iModIntro. iFrame "Hrun Hrun'".
  Qed.

  (* THE FLOOR IS A TRANSPORTABLE PAYLOAD MEMBER -- [TsoCtx.ctx_floor_dom]
     as an instance, so a payload whose only context-dependence is a floor
     (the parked record's slot, [SchedCtx.proc_ctx]) is morphable by
     instance search alone.  Stated in main's NON-MODAL [CtxMorph] form. *)
  Global Instance ctx_morph_floor (lo : nat) : CtxMorph (Σ := Σ) (λ ξ, ctx_floor ξ lo).
  Proof.
    iIntros (ξ ξ') "Hd #Hfl".
    iDestruct (ctx_floor_dom with "Hd Hfl") as "[Hd #Hfl']".
    iFrame "Hd Hfl'".
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
