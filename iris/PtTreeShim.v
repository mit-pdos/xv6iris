(* PtTreeShim.v -- TOMBSTONE (the tso-cutover branch).

   WHAT IT WAS.  Main's SC-era seam for the page-table slot tier: the
   phantom-tier equivalences [pt_slot_own PTT a dq w ⊣⊢ phys_word_pointsto
   a dq w] ([pt_slot_raw_sc], [pt_slot_own_of_raw_sc]), the generic payer
   [pt_slot_payer_sc], and the UTier re-tier [ptree_own_retier_sc].  Every
   one of those statements is FALSE at Ztso: the KTier arm's pin and the
   UTier arm's registration are real evidence there (a timestamped ledger
   element handed out once), not phantoms.

   WHERE THE HONEST FORMS LIVE: the KTier pin's producer is the boot
   telescope ([KptPublish.kptree_publish_boot] and the [KptShare] window);
   the UTier registration's producer is the walk/store tier
   ([PtTreeAdue]'s §0.46' A/D write-backs, [UptWalkPt]); the UTier
   re-tier is a real transport ([PtTreeMove]'s [CtxMorph]/[CtxMove]
   instances, along a domination or a pair of running tokens).

   THE FILE IS KEPT, EMPTY, ON PURPOSE (the TsoCtxShim precedent): a
   grep that lands here reads the history; a build error that lands on a
   [PtTreeShim.*] reference names its own seam site. *)
From Stdlib Require Import ZArith.
