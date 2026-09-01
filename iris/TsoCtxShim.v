(* TsoCtxShim.v -- TOMBSTONE.  The one-time migration shim is RETIRED
   (tso-machine-flip.md A6.86).

   WHAT IT WAS.  Before the machine flip this file stated the SC-only
   equivalences that let the sweep convert file by file:
   `ctx_pointsto ξ ⊣⊢ mem_pointsto` and its word / eslot / buf forms, plus
   the two conjured receipts `hart_view_lb_any` and `ctx_dom_sc`.  Every one
   of those statements is FALSE at Ztso, and they were deleted at the flip
   (A6.8): a `ctx_*_of_mem` cannot exist because the timestamp element is a
   `ghost_map` fragment handed out once, and a conjured view receipt is
   exactly the evidence the port exists to demand.

   HOW IT DIED, and it took three tranches:
     - the `_to_mem` (forgetting) directions became `TsoCtx`'s own
       `ctx_pointsto_forget` family -- one-way and lossy, and priced there;
     - the boot-side `_of_mem` (minting) directions became
       `BootCarve.boot_ctx_of_mem_{byte,word,word4}`, which build the honest
       cell out of the carve's own timestamp-0 receipts (A6.80/A6.81);
     - the LAST LIVE USE was `WpSconfLock.lock_claims`, which forgot the
       lock's owner cell to a raw word in order to read an ADDRESS claim off
       it and then had to cross back.  The M4 contract flip put that cell at
       the ledger tier, where it carries no mapping at all, so the invariant
       holds the two `lk_addr_claim`s explicitly and `lock_claims` became a
       peek that closes with what it opened.  Nothing to cross, nothing to
       forget, no shim (A6.84 §(1) predicted exactly this; A6.86 landed it).

   THE ONE SURVIVING LEMMA, `own_context_alloc`, is gone too: it was a
   re-export of `TsoCtx.own_context_boot` under a name that marked
   sweep-era call sites, and it had no callers left.  Note that the
   CONTEXT-FREE reading of its name is REFUTED --
   `TsoCtxRehearsal.no_own_context_alloc` -- which is why nothing should
   ever reintroduce it.

   THE FILE IS KEPT, EMPTY, ON PURPOSE.  Its rows in `_CoqProject` and in
   the dependency graph cost nothing, and a grep for `TsoCtxShim` that lands
   here reads the history instead of returning nothing.  If you are looking
   for a crossing this file used to provide, the answer is in one of the
   three bullets above; if none of them fits, the crossing you want is
   unsound. *)
From Stdlib Require Import ZArith.
