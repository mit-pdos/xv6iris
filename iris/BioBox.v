(* ======================================================================= *)
(*  BioBox: the bcache transit box (Phase 5, A6.142/A6.147).                *)
(*                                                                          *)
(*  The successor to [BioInv.buf_escrow]'s cell-owning invariant.  The      *)
(*  A6.147 measurement: the escrow is never OPENED in the lock-free         *)
(*  windows -- it is storage ACROSS them; every transition happens inside   *)
(*  bcache.lock or b->lock.  So the box holds ONE uniform bundle (the old   *)
(*  [buf_parked] minus the recycle token) at a PARKED context, custodied    *)
(*  by [CtxAnchor.anchor]:                                                  *)
(*                                                                          *)
(*    - deposited at bget's refcnt 0->1 bump (under bcache.lock) and at     *)
(*      brelse's park (under b->lock, before releasesleep);                 *)
(*    - withdrawn at the checkout (the acquiresleep winner, under b->lock)  *)
(*      and at brelse's refcnt 1->0 drop (under bcache.lock, folding the    *)
(*      content back into the payload's refcnt-0 arm).                      *)
(*                                                                          *)
(*  Both arms below are closed propositions (the box context ξb is BOUND),  *)
(*  so [buf_box] is fork-movable -- the whole point (§0.47').               *)
(*                                                                          *)
(*  The guard: the box body carries the deposit's [astamp]/[llb] receipt    *)
(*  persistently; a withdrawer mints its [aguard] by cashing the llb at     *)
(*  its own acquire's drained point (the A6.147-refinement export) and      *)
(*  withdraws with [anchor_withdraw].  Freshness -- the guard's generation  *)
(*  matching the box's -- is by [astamp_agree] against the body's witness.  *)
(* ======================================================================= *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import excl auth gmap frac numbers.
From iris.base_logic.lib Require Import gen_heap invariants own.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvModelBytes.
Require Import RiscvPtsto.
Require Import WpLock.
Require Import TsoMemPa TsoGhost.
Require Import TsoCtx.
Require Import TsoCtxPark.
Require Import CtxAnchor.
Require Import SleepLock.
Require Import BufOwn.
Require Import DiskPtsto.
Require Import BcacheInv.
Require Export BioDefs.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SepThread.
Require Import Xv6G.
Require Import BioInv.

Section BioBox.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !anchorG Σ}.

  (* ------------------------------------------------------------------ *)
  (*  The two box arms, as context-λs                                     *)
  (* ------------------------------------------------------------------ *)

  (* the travelling content: [BioInv.buf_parked] minus [bmid], stated at
     an explicit context.  (bmid dies with the recycle window: the
     recycler works entirely inside bcache.lock's payload now.) *)
  Definition buf_bundle (bn : bio_names) (V : bio_view Σ) (k : nat)
      (ξ : CtxId) : iProp Σ :=
    (∃ (v : bool) (dev bno : mword 32) (bs : list (bv 8)),
       ctx_word4_pointsto ξ (b_valid (bpa k)) (DfracOwn 1)
         (if v then (mword_of_int 1 : mword 32) else (mword_of_int 0 : mword 32)) ∗
       ctx_word4_pointsto ξ (b_dev (bpa k)) (DfracOwn (1/2)) dev ∗
       buf_own (XI := ξ) (bpa k) bno (mword_of_int 0 : mword 32) bs ∗
       buf_pay (XI := ξ) bn V k v dev bno bs)%I.

  (* the chain residue: what the checkout leaves behind while a
     bread..brelse chain owns the content ([BioInv.buf_chain] minus
     [bmid]).  The cell fractions ride at the box context too. *)
  Definition buf_chain_res (bn : bio_names) (k : nat) (ξ : CtxId) : iProp Σ :=
    (∃ (q : Qp) (dev bno : mword 32),
       bref_tok bn k q ∗
       ctx_word4_pointsto ξ (b_dev (bpa k)) (DfracOwn q) dev ∗
       ctx_word4_pointsto ξ (b_blockno (bpa k)) (DfracOwn q) bno ∗
       bown bn k)%I.

  (* ------------------------------------------------------------------ *)
  (*  The box                                                             *)
  (* ------------------------------------------------------------------ *)

  Definition bioxN : namespace := nroot .@ "xv6biox".

  Definition buf_box_body (bn : bio_names) (V : bio_view Σ) (k : nat) : iProp Σ :=
    (∃ (n T : nat) (ξb : CtxId),
       anchor (bn_anc bn k) n ξb T ∗
       astamp (bn_anc bn k) n T ∗
       llb loglen_name T ∗
       (buf_bundle bn V k ξb ∨ buf_chain_res bn k ξb))%I.

  Definition buf_box (bn : bio_names) (V : bio_view Σ) (k : nat) : iProp Σ :=
    inv bioxN (buf_box_body bn V k).

  (* ------------------------------------------------------------------ *)
  (*  Morphability of the arms (what deposit/withdraw transport)          *)
  (* ------------------------------------------------------------------ *)

  Global Instance buf_bundle_morph bn V k : CtxMorph (buf_bundle bn V k).
  Proof.
    rewrite /buf_bundle. apply ctx_morph_exist => v.
    apply ctx_morph_exist => dev. apply ctx_morph_exist => bno.
    apply ctx_morph_exist => bs.
    apply ctx_morph_sep; [apply ctx_morph_word4|].
    apply ctx_morph_sep; [apply ctx_morph_word4|].
    apply ctx_morph_sep.
    - rewrite /buf_own.
      apply ctx_morph_sep; [apply ctx_morph_word4|].
      apply ctx_morph_sep; [apply ctx_morph_word4|].
      apply ctx_morph_sep; [apply ctx_morph_const|].
      apply ctx_morph_big_sepL. intros i x. apply ctx_morph_pointsto.
    - rewrite /buf_pay.
      case_decide; [|apply ctx_morph_const].
      apply ctx_morph_sep; [apply ctx_morph_const|].
      destruct v.
      + apply ctx_morph_exist => bsd. apply ctx_morph_exist => d.
        apply ctx_morph_sep; [apply ctx_morph_const|].
        rewrite /bio_pay. destruct d.
        * apply ctx_morph_sep; [apply ctx_morph_const|].
          apply ctx_morph_exist => q.
          rewrite /bref.
          apply ctx_morph_sep; [apply ctx_morph_const|].
          apply ctx_morph_sep; apply ctx_morph_word4.
        * apply ctx_morph_const.
      + apply ctx_morph_const.
  Qed.

  Global Instance buf_chain_res_morph bn k : CtxMorph (buf_chain_res bn k).
  Proof.
    rewrite /buf_chain_res. apply ctx_morph_exist => q.
    apply ctx_morph_exist => dev. apply ctx_morph_exist => bno.
    apply ctx_morph_sep; [apply ctx_morph_const|].
    apply ctx_morph_sep; [apply ctx_morph_word4|].
    apply ctx_morph_sep; [apply ctx_morph_word4|].
    apply ctx_morph_const.
  Qed.

End BioBox.
