(* TsoCtxShim.v -- THE ONE-TIME MIGRATION SHIM, POST-FLIP RESIDUE.

   Before the machine flip this file stated the SC-only equivalences
   (`ctx_pointsto ξ ⊣⊢ mem_pointsto`, the word/eslot/buf forms, the
   conjured `hart_view_lb_any`/`ctx_dom_sc`).  THE MACHINE IS NOW Ztso
   (tso-machine-flip.md) and every one of those statements is FALSE, so
   they are GONE: each compile error at a former use site is one entry
   of the honest remaining worklist --
     - a `ctx_*_of/to_mem` use marks a leaf/kit boundary that needs its
       real re-proof against the log machine (the (iii) worklist);
     - a `hart_view_lb_any` use marks the M2 receipt threading
       (SpecAcquire's AMO mint, `TsoCtx.hart_view_lb_get`);
     - a `ctx_dom_sc` use marks a lock-kit transport that must be minted
       from real synchronization evidence (`TsoCtx.ctx_dom_to_parked` /
       `ctx_dom_of_parked`).

   THE ONE SURVIVOR is the sweep-era caller mint below: a conjured
   running context is still SOUND under the real construction
   ([TsoCtxTwin2.twin_run_alloc]: a context born at bound 0 with an
   empty dirty set claims nothing any hart could not honour) -- it is
   just USELESS for reading anything younger than the boot image, which
   is why each use site is still a caller whose own conversion is the
   remaining work. *)
From Stdlib Require Import ZArith Lia.
From stdpp Require Import bitvector.definitions gmap.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import dfrac.
From iris.base_logic.lib Require Import ghost_var.
Require Import SailStdpp.Values.
Require Import Riscv.rv64d_types.
Require Import RiscvModelBytes RiscvLang RiscvPtsto Ktier.
Require Import TsoCtx.

Section shim.
  Context `{!riscvGS Σ}.

  (* THE SWEEP-ERA THROWAWAY MINT (see the header).  Same mint as
     [TsoCtx.own_context_boot]; licensed here by NAME so the boot-site
     rule ("boot mints, fork mints parked, swtch exchanges") keeps its
     grep-able meaning. *)
  Lemma own_context_alloc `{CID : CpuId} : ⊢ |==> ∃ ξ : CtxId, own_context ξ.
  Proof. apply own_context_boot. Qed.
End shim.
