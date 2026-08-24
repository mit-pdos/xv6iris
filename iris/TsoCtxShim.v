(* TsoCtxShim.v -- THE ONE-TIME MIGRATION SHIM.  BURNED AT CUTOVER.

   The ONLY place in the tree allowed to state that a context-indexed
   fact and a plain fact are the same thing.  At SC they are
   (`TsoCtx.ctx_pointsto` ignores its index UNDER THE SEAL), and the M
   sweeps convert the tree one file at a time, so every
   converted/unconverted boundary needs the conversion stated somewhere.
   It is stated HERE and nowhere else, so that at cutover -- when
   `ctx_pointsto` becomes the TSO ledger fact and these equivalences
   become FALSE -- deleting this one file finds every remaining
   unconverted boundary as a compile error, which is the honest worklist
   of what is left.

   Consequently: a converted file may import this shim ONLY to talk to a
   not-yet-converted neighbour.  A converted file whose callers and
   callees are all converted must not import it; import of this file IS
   the tree's list of open seams (grep for TsoCtxShim).

   See claude-notes/projects/tso-port.md ("no context-irrelevance
   escapes" -- this file is the sanctioned, quarantined exception). *)
From Stdlib Require Import ZArith Lia.
From stdpp Require Import bitvector.definitions gmap.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import dfrac.
From iris.base_logic.lib Require Import ghost_var.
Require Import SailStdpp.Base SailStdpp.Values.
Require Import Riscv.rv64d_types.
Require Import RiscvModelBytes RiscvLang RiscvPtsto Ktier.
Require Import TsoCtx.

Section shim.
  Context `{!riscvGS Σ}.
  Local Transparent ctx_pointsto.

  Lemma ctx_pointsto_shim (KTR : CurKtier) (ξ : CtxId)
      (a : Arch.pa) (dq : dfrac) (v : bv 8) :
    ctx_pointsto (KTR := KTR) ξ a dq v ⊣⊢ mem_pointsto (KTR := KTR) a dq v.
  Proof. reflexivity. Qed.

  (* the two wand directions, for plain proofmode plumbing *)
  Lemma ctx_pointsto_of_mem (KTR : CurKtier) (ξ : CtxId) a dq v :
    mem_pointsto (KTR := KTR) a dq v -∗ ctx_pointsto (KTR := KTR) ξ a dq v.
  Proof. rewrite ctx_pointsto_shim. auto. Qed.

  Lemma ctx_pointsto_to_mem (KTR : CurKtier) (ξ : CtxId) a dq v :
    ctx_pointsto (KTR := KTR) ξ a dq v -∗ mem_pointsto (KTR := KTR) a dq v.
  Proof. rewrite ctx_pointsto_shim. auto. Qed.

  (* the [∗ list] window form the buffer specs trade in *)
  Lemma ctx_buf_of_mem (KTR : CurKtier) (ξ : CtxId)
      (p : Arch.pa) (len : nat) (f : nat -> bv 8) (dq : dfrac) :
    ([∗ list] j ∈ seq 0 len, mem_pointsto (KTR := KTR) (pa_add p j) dq (f j))
    -∗
    ([∗ list] j ∈ seq 0 len,
       ctx_pointsto (KTR := KTR) ξ (pa_add p j) dq (f j)).
  Proof.
    iIntros "H". iApply (big_sepL_impl with "H").
    iIntros "!>" (k j Hj) "Hb". by iApply ctx_pointsto_of_mem.
  Qed.

  Lemma ctx_buf_to_mem (KTR : CurKtier) (ξ : CtxId)
      (p : Arch.pa) (len : nat) (f : nat -> bv 8) (dq : dfrac) :
    ([∗ list] j ∈ seq 0 len,
       ctx_pointsto (KTR := KTR) ξ (pa_add p j) dq (f j))
    -∗
    ([∗ list] j ∈ seq 0 len, mem_pointsto (KTR := KTR) (pa_add p j) dq (f j)).
  Proof.
    iIntros "H". iApply (big_sepL_impl with "H").
    iIntros "!>" (k j Hj) "Hb". by iApply ctx_pointsto_to_mem.
  Qed.
End shim.
