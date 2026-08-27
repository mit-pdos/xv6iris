(* TsoCtxAbsorbLb.v -- THE RECEIPT-SIDE ABSORB, and why it is a separate
   gate from [TsoCtx.ctx_absorb] (A6.68).

   A6.66 landed [TsoCtx.ctx_absorb] against the INTERP: its premise is
   [length glog <= gtv cpu_id], the at-the-top fact the AMO leaf
   establishes, and it consumes [tso_interp_at].  That is the honest gate
   for a claim made INSIDE a lock leaf -- and it is exactly why it cannot
   serve the five M2 transport sites A6.65 localised.  §0.17′'s measured
   rule cuts both ways: [own_context] is only in hand OUTSIDE a WP leaf,
   and [tso_interp_at] is only in hand INSIDE one.  A transport that needs
   both in one hand has no site.

   THE FIX IS NOT A WEAKENING: [TsoCtx.ctx_resume] already shows that a
   parked context's facts may be claimed on the strength of a RECEIPT
   alone -- [(T <= K) -> hart_view_lb K -* ctx_parked xi T ==* own_context
   xi] -- with no interp anywhere, because a stamp is a legal log position
   and a hart whose view has passed it has seen every write the record
   published.  The same evidence justifies the [ctx_dom] mint, and that is
   what this file proves.  [ctx_absorb_lb] is therefore the same law
   [ctx_absorb] is, with the interp's [length glog <= gtv cpu_id]
   replaced by the receipt it was being used to manufacture, and it is
   [tso-port.md] §0.18′'s shape on main -- where the receipt is fictional
   because SC's [ctx_dom] is vacuous, and here it is real.

   WHY ITS OWN FILE.  [TsoCtx.v] is under the whole tree; this is a
   forty-line derivation off that file's PUBLIC unseal lemmas, and it
   needs nothing the kit does not already export.  Fold it into
   [TsoCtx.v]'s gate block at cutover, beside [ctx_absorb] -- the
   [SieCapCtx.v] precedent, same reason. *)
From Stdlib Require Import ZArith Lia.
From stdpp Require Import gmap.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import auth.
From iris.base_logic.lib Require Import ghost_map mono_nat.
Require Import RiscvLang RiscvPtsto.
Require Import TsoMemPa TsoGhost.
Require Import TsoCtx.

Section AbsorbLb.
  Context `{!riscvGS Σ}.

  (* TWO RECEIPTS JOIN AT THEIR MAX -- and the join is a CASE SPLIT, not
     an algebraic op: the max IS one of the two, and [view_lb] is
     persistent, so nothing has to be combined. *)
  Lemma view_lb_max (gv gl : gname) (h : nat) (K1 K2 : nat) :
    view_lb gv gl h K1 -∗ view_lb gv gl h K2 -∗ view_lb gv gl h (Nat.max K1 K2).
  Proof.
    iIntros "H1 H2".
    destruct (Nat.le_ge_cases K1 K2) as [Hle|Hle].
    - rewrite (Nat.max_r _ _ Hle). iExact "H2".
    - rewrite (Nat.max_l _ _ Hle). iExact "H1".
  Qed.

  Lemma hart_view_lb_max `{CID : CpuId} (K1 K2 : nat) :
    hart_view_lb K1 -∗ hart_view_lb K2 -∗ hart_view_lb (Nat.max K1 K2).
  Proof.
    rewrite !hart_view_lb_unseal /hart_view_lb_def. apply view_lb_max.
  Qed.

  (* THE ACQUIRE-SIDE MINT AT A RECEIPT.  Same conclusion as
     [TsoCtx.ctx_dom_of_parked]; the source's stamp is compared with the
     claimer's own view rather than with the log length, so no interp is
     consulted and the mint is available at any ghost step where the
     running token is. *)
  Lemma ctx_dom_of_parked_lb `{CID : CpuId} (xi xi' : CtxId) (T K : nat) :
    (T <= K)%nat ->
    hart_view_lb K -∗ own_context xi' -∗ ctx_parked xi T ==∗
    own_context xi' ∗ ctx_dom xi xi' ∗ (ctx_dom xi xi' -∗ ctx_parked xi T).
  Proof.
    iIntros (HTK) "#HK Hrun Hpk".
    iEval (rewrite own_context_unseal /own_context_def) in "Hrun".
    iEval (rewrite ctx_parked_unseal /ctx_parked_def) in "Hpk".
    iDestruct "Hrun"
      as "(%B' & %K' & %W' & %D' & [Hb' Hd'] & #HK' & %HBK' & #HW' & %HDW' & #Hoks)".
    iDestruct "Hpk" as "(%D & Hat & #HT & %HDT)".
    (* raise the claimer's bound past the record's stamp; the joined
       receipt is what keeps [B <= K] true of the rebuilt token *)
    iEval (rewrite hart_view_lb_unseal /hart_view_lb_def) in "HK".
    iDestruct (view_lb_max _ _ _ K' K with "HK' HK") as "#HKj".
    iMod (mono_nat_own_update (Nat.max B' T) with "Hb'") as "[Hb' #Hlb']";
      first lia.
    iDestruct (ctx_at_halves with "Hat") as "[Hat1 Hat2]".
    iModIntro.
    rewrite own_context_unseal /own_context_def
            ctx_dom_unseal /ctx_dom_def
            ctx_parked_unseal /ctx_parked_def.
    iSplitL "Hb' Hd'".
    { iExists (Nat.max B' T), (Nat.max K' K), W', D'.
      iFrame "Hb' Hd' HKj HW'".
      iSplitR; first (iPureIntro; lia).
      iSplitR; first (iPureIntro; exact HDW').
      iApply (big_sepM_impl with "Hoks").
      iIntros "!>" (k [] Hk) "Hok". iApply (dirty_ok_mono with "Hok"). lia. }
    iSplitL "Hat1".
    { iExists T, T, (Nat.max B' T), D. iFrame "Hat1 Hlb'".
      iPureIntro. split_and!; [exact HDT | lia | lia]. }
    iIntros "(%B0 & %W0 & %B0' & %D0 & Hat0 & _)".
    iDestruct (ctx_at_agree with "Hat0 Hat2") as %[-> ->].
    iCombine "Hat0 Hat2" as "Hat". rewrite -ctx_at_halves.
    iExists D. iFrame "Hat HT". by iPureIntro.
  Qed.

  (* THE ABSORB, at a receipt.  [tso-port.md] §0.18′'s statement exactly
     -- the shape every M2 transport site was written against. *)
  Lemma ctx_absorb_lb `{CID : CpuId} (R : CtxId -> iProp Σ) `{!CtxMorph R}
      (xi xi' : CtxId) (T K : nat) :
    (T <= K)%nat ->
    own_context xi' -∗ hart_view_lb K -∗ ctx_parked xi T -∗ R xi ==∗
    own_context xi' ∗ ctx_parked xi T ∗ R xi'.
  Proof.
    iIntros (HTK) "Hrun #HK Hpk HR".
    iMod (ctx_dom_of_parked_lb xi xi' T K HTK with "HK Hrun Hpk")
      as "(Hrun & Hdom & Hback)".
    iMod (ctx_morph with "Hdom HR") as "[Hdom HR]".
    iModIntro. iFrame "Hrun HR". by iApply "Hback".
  Qed.

End AbsorbLb.
