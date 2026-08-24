(* TsoMemsetCtx.v -- THE MIXED-TREE PROTOTYPE: one function ported to the
   context style while the rest of the tree is untouched.

   This file answers, on the real [memset]
   ([SpecMemset.wp_memset_sconf_body]), the migration question of
   claude-notes/projects/tso-port.md leg M: what does ONE converted proof
   look like mid-sweep?  Three artifacts:

   1. [wp_memset_ctx_body] -- the CONVERTED spec.  The deltas from the
      original, and there are exactly three:
        - an ambient [`{XI : CurCtx}] binder (the M1 axis, like [CpuId]);
        - [own_context cur_ctx] threaded beside [sie_cap_gpr] (STOPGAP:
          the M2 sweep puts it INSIDE the bundle in IntrDefs.v, at which
          point this conjunct disappears from spec text again);
        - the byte window stated with [ctx_pointsto ... cur_ctx].
      Everything else -- premises, registers, ktier axis, [wp_next] -- is
      character-identical.  NOTE WHAT HAPPENS AT [wp_next]: the
      continuation rebinds [CID] (memset can be preempted and resume on
      any hart) while [cur_ctx] is THE SAME ξ on both sides of it.  At SC
      that is cosmetic; under TSO it is the whole point -- the facts are
      the thread's, not the hart's, so nothing is re-proved at the
      migration.

   2. [wp_memset_ctx] -- the converted spec HOLDS in the unconverted
      tree: proved from the sealed [MS : MEMSET] parameter through the
      shim, without touching memset's own proof.  (In the real sweep the
      leaf files convert like this first, wholesale, and their proof
      TEXT does not change; this functor shows the boundary mechanics.)

   3. [wp_memset_sconf_via_ctx] -- the OLD spec re-derived from the new
      one: an unconverted CALLER loses nothing.  It mints a context on
      the spot ([own_context_alloc] -- free at SC, and exactly the move
      that stops compiling at cutover, which is what makes leftover
      unconverted callers a compile-time worklist rather than a silent
      soundness hole).

   Both directions import [TsoCtxShim]; per that file's header, the
   import is the marker of an open seam.  When memset's callers are all
   converted, artifact 3 and the shim import are deleted. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvModelBytes RiscvLang RiscvPtsto.
Require Import RegFile WpNext.
Require Import InstrBytes.
Require Import RiscvExtras.
Require Import KernelText.
Require Import CalleeSaved.
Require Import IntrDefs.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import Xv6G.
Require Import SpecMemset.
Require Import TsoCtx TsoCtxShim.
Import Defs.

(* The converted whole-function spec.  Compare [SpecMemset] side by side:
   the three deltas of the header are the only ones. *)
Definition wp_memset_ctx_body `{!riscvGS Σ, !xv6G Σ} `{GEN : GenId}
    `{CID : CpuId} `{XI : CurCtx}
    (kt ktb : ktier) `{!KtierLe ktb kt} (m0 : regfile) (n : nat) (len : nat)
    (cval : mword 64) (olds : nat -> bv 8) (b : bool) (pcur : mword 64) :=
  let a0_idx : mword 5 := mword_of_int 10 in
  let a1_idx : mword 5 := mword_of_int 11 in
  let a2_idx : mword 5 := mword_of_int 12 in
  let pcE := mword_of_int KernelSyms.memset in
  let ra0 := m0 !!! Regidx (mword_of_int 1 : mword 5) in
  let p := m0 !!! Regidx a0_idx in
  let ret_tgt := ret_pc ra0 in
  let cbyte := nth_byte (autocast (T := mword) (subrange_vec_dec cval (Z.sub (Z.mul 1 8) 1) 0) : mword 8) 0 in
  (2 <= n)%nat ->
  (Z.of_nat len < 2 ^ 32)%Z ->
  m0 !!! Regidx a1_idx = cval ->
  m0 !!! Regidx a2_idx = (mword_of_int (Z.of_nat len) : mword 64) ->
  own_context cur_ctx -∗              (* M2 folds this into [sie_cap_gpr] *)
  sie_cap_gpr kt m0 n b pcur -∗
  kernel_text -∗ pc_is pcE -∗
  ([∗ list] j ∈ seq 0 len,
     ctx_pointsto (KTR := ktb) cur_ctx (pa_add p j) (DfracOwn 1) (olds j)) -∗
  wp_next b pcur (fun (CID : CpuId) =>
    (* [CID] rebound; [cur_ctx] NOT.  The window below names the same ξ. *)
    ∀ mfin,
    own_context cur_ctx -∗
    sie_cap_gpr kt mfin n b pcur -∗
    pc_is ret_tgt -∗
    ([∗ list] j ∈ seq 0 len,
       ctx_pointsto (KTR := ktb) cur_ctx (pa_add p j) (DfracOwn 1) cbyte) -∗
    ⌜ callee_saved m0 mfin ⌝ -∗
    WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

Module MemsetCtx (MS : MEMSET).

  (* Artifact 2: the converted spec, proved in the unconverted tree. *)
  Theorem wp_memset_ctx `{!riscvGS Σ, !xv6G Σ} `{GEN : GenId}
      `{CID : CpuId} `{XI : CurCtx}
      (kt ktb : ktier) `{KLE : !KtierLe ktb kt} (m0 : regfile) (n : nat)
      (len : nat) (cval : mword 64) (olds : nat -> bv 8) (b : bool)
      (pcur : mword 64) :
    wp_memset_ctx_body kt ktb m0 n len cval olds b pcur.
  Proof.
    rewrite /wp_memset_ctx_body.
    intros Hn Hlen Ha1 Ha2.
    iIntros "Hctx Hcap Hkt Hpc Hbuf Hk".
    iDestruct (ctx_buf_to_mem with "Hbuf") as "Hbuf".
    iApply (MS.wp_memset_sconf kt ktb m0 n len cval olds b pcur
              Hn Hlen Ha1 Ha2 with "Hcap Hkt Hpc Hbuf").
    iIntros (CID' Hq mfin) "Hcap Hpc Hbuf %Hcs".
    iDestruct (ctx_buf_of_mem ktb cur_ctx with "Hbuf") as "Hbuf".
    iSpecialize ("Hk" $! CID' with "[%]"); [exact Hq|].
    iApply ("Hk" $! mfin with "Hctx Hcap Hpc Hbuf [%]"). exact Hcs.
  Qed.

  (* Artifact 3: the OLD spec from the new one -- what keeps every
     not-yet-converted caller compiling.  The mint is the SC-only move. *)
  Theorem wp_memset_sconf_via_ctx `{!riscvGS Σ, !xv6G Σ} `{GEN : GenId}
      `{CID : CpuId}
      (kt ktb : ktier) `{KLE : !KtierLe ktb kt} (m0 : regfile) (n : nat)
      (len : nat) (cval : mword 64) (olds : nat -> bv 8) (b : bool)
      (pcur : mword 64) :
    wp_memset_sconf_body kt ktb m0 n len cval olds b pcur.
  Proof.
    rewrite /wp_memset_sconf_body.
    intros Hn Hlen Ha1 Ha2.
    iIntros "Hcap Hkt Hpc Hbuf Hk".
    iMod (own_context_alloc) as (ξ) "Hctx".
    iDestruct (ctx_buf_of_mem ktb ξ with "Hbuf") as "Hbuf".
    iApply (wp_memset_ctx (XI := ξ) kt ktb m0 n len cval olds b pcur
              Hn Hlen Ha1 Ha2 with "Hctx Hcap Hkt Hpc Hbuf").
    iIntros (CID' Hq mfin) "Hctx Hcap Hpc Hbuf %Hcs".
    iDestruct (ctx_buf_to_mem with "Hbuf") as "Hbuf".
    iSpecialize ("Hk" $! CID' with "[%]"); [exact Hq|].
    iApply ("Hk" $! mfin with "Hcap Hpc Hbuf [%]"). exact Hcs.
  Qed.

End MemsetCtx.

(* Artifact 4: the round trip as a MODULE.  The converted function
   re-exports the ORIGINAL sealed interface, so every existing linker
   instantiation (LinkBalloc, LinkKvmmake, LinkIalloc, ...) could take
   the converted memset TODAY, with zero changes to any consumer: the
   sweep can convert one function at a time in ANY order. *)
Module MemsetRoundTrip (MS : MEMSET) <: MEMSET.
  Module C := MemsetCtx MS.
  Definition wp_memset_sconf := @C.wp_memset_sconf_via_ctx.
End MemsetRoundTrip.
