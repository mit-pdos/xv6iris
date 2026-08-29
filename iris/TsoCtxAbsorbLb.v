(* TsoCtxAbsorbLb.v -- THE RECEIPT-SIDE ABSORB (tso-flip TsoCtxAbsorbLb.v,
   A6.68), on main: the STATEMENTS verbatim, the bodies SC-trivial.

   [TsoCtx.ctx_absorb] is the honest gate for a claim made INSIDE a lock
   leaf against the interpretation; the five M2 transport sites hold the
   running token OUTSIDE a leaf and never the interp.  [ctx_resume] already
   shows a parked context's facts may be claimed on the strength of a
   RECEIPT alone -- a stamp is a legal log position and a hart whose view
   has passed it has seen every write the record published -- and the same
   evidence justifies the [ctx_dom] mint.  [ctx_absorb_lb] is [ctx_absorb]
   with the interp's [length glog <= gtv cpu_id] replaced by the receipt it
   was being used to manufacture: exactly the shape every M2 transport site
   was written against ([tso-port.md] §0.18′).

   On main the receipt is minted by the SC shim at the AMO leaf
   ([TsoCtxShim.ctx_floor_any] -> [WpLock.lock_pay_won]) and cashed by
   [TsoCtx.own_context_floor_view]; at cutover [hart_view_lb_get] produces
   it and nothing here changes shape.  The T-leg's [view_lb_max] is below
   the seal and not stated. *)

From Stdlib Require Import ZArith Lia.
From stdpp Require Import gmap.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import own ghost_var invariants.
Require Import RiscvLang RiscvPtsto.
Require Import TsoCtx.

Section AbsorbLb.
  Context `{!riscvGS Σ}.

  (* TWO RECEIPTS JOIN AT THEIR MAX -- a case split, not an algebraic op:
     the max IS one of the two, and the receipt is persistent. *)
  Lemma hart_view_lb_max `{CID : CpuId} (K1 K2 : nat) :
    hart_view_lb (Σ := Σ) K1 -∗ hart_view_lb K2 -∗ hart_view_lb (Nat.max K1 K2).
  Proof.
    iIntros "H1 H2".
    destruct (Nat.le_ge_cases K1 K2) as [Hle|Hle].
    - rewrite (Nat.max_r _ _ Hle). iExact "H2".
    - rewrite (Nat.max_l _ _ Hle). iExact "H1".
  Qed.

  (* THE ACQUIRE-SIDE MINT AT A RECEIPT.  Same conclusion as the twin's
     [ctx_dom_of_parked]; the source's stamp is compared with the claimer's
     own view rather than with the log length, so no interp is consulted
     and the mint is available at any ghost step where the running token
     is. *)
  Lemma ctx_dom_of_parked_lb `{CID : CpuId} (xi xi' : CtxId) (T K : nat) :
    (T <= K)%nat ->
    hart_view_lb K -∗ own_context xi' -∗ ctx_parked xi T ==∗
    own_context xi' ∗ ctx_dom xi xi' ∗ (ctx_dom xi xi' -∗ ctx_parked xi T).
  Proof.
    iIntros (HTK) "#HK Hrun Hpk". iModIntro. iFrame "Hrun".
    iSplitR. { rewrite ctx_dom_unseal /ctx_dom_def. done. }
    iIntros "_". iExact "Hpk".
  Qed.

  (* THE ABSORB, at a receipt -- §0.18′'s statement exactly. *)
  Lemma ctx_absorb_lb `{CID : CpuId} (R : CtxId -> iProp Σ) `{!CtxMorph R}
      (xi xi' : CtxId) (T K : nat) :
    (T <= K)%nat ->
    own_context xi' -∗ hart_view_lb K -∗ ctx_parked xi T -∗ R xi ==∗
    own_context xi' ∗ ctx_parked xi T ∗ R xi'.
  Proof.
    iIntros (HTK) "Hrun #HK Hpk HR".
    iMod (ctx_dom_of_parked_lb xi xi' T K HTK with "HK Hrun Hpk")
      as "(Hrun & Hdom & Hback)".
    iDestruct (ctx_morph with "Hdom HR") as "[Hdom HR]".
    iModIntro. iFrame "Hrun HR". by iApply "Hback".
  Qed.
End AbsorbLb.
