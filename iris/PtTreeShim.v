(* PtTreeShim.v -- THE PAGE-TABLE WALK'S SC PAYER.  BURNED AT CUTOVER.
   [KptTree.ptree_translateAddr_own] and the [UptTree]/[UserPtTree]
   composers built on it thread a PAYER for the Svadu A/D write-back
   (tso-port A6.24: "the index says which ledger a slot is in; the payer
   says who may move it") and a memory-indexed currency [S].  At TSO the
   payer is a real ledger gate ([TsoCtx.ctx_store_win_ok] with the
   caller's [own_context] for a user table; the pinned store gate for the
   kernel one) and [S] carries the caller's interp bundle.  At SC the
   write is a plain [gen_heap] update, so ONE generic payer serves every
   caller at a CONSTANT currency -- this file's only export.  Like
   [TsoCtxShim], a file that imports this one is an unconverted payer
   site, and the import list is the cutover's worklist. *)
From Stdlib Require Import ZArith Lia.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes RiscvLang RiscvPtsto.
Require Import TsoCtx TsoCtxShim.
Require Import PtBytes PtTree PtTreeAdue.
Local Open Scope Z_scope.

Section PtTreeShim.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}.

  (* [pt_slot_own] is reversible to the raw word AT SC ONLY: the KTier
     arm's pin and the UTier arm's registration are both phantom. *)
  Lemma pt_slot_own_of_raw_sc (PTT : ptier) (a : Arch.pa) (dq : dfrac)
      (w : bv 64) :
    phys_word_pointsto a dq w ⊢ pt_slot_own PTT a dq w.
  Proof.
    rewrite /pt_slot_own. destruct PTT as [B|xi].
    - rewrite /kpt_slot_pin. auto.
    - rewrite TsoCtxShim.ctx_phys_word_shim. auto.
  Qed.

  (* THE UNIVERSAL SC EQUIVALENCE: a tiered slot IS the raw word until
     cutover (the KTier pin and the UTier registration are both phantom).
     Sites that read or write a slot through the va-tier bridges rewrite
     with this once, in either direction. *)
  Lemma pt_slot_raw_sc (PTT : ptier) (a : Arch.pa) (dq : dfrac) (w : bv 64) :
    pt_slot_own PTT a dq w ⊣⊢ phys_word_pointsto a dq w.
  Proof.
    iSplit.
    - iApply pt_slot_own_forget.
    - iApply pt_slot_own_of_raw_sc.
  Qed.

  (* THE GENERIC SC PAYER, at a constant currency.  Discharges the
     [ptree_translateAddr_own] payer premise for any tier and any
     ξ-constant [R]; the write is [RiscvPtsto.phys_word_pointsto_write]. *)
  Lemma pt_slot_payer_sc (PTT : ptier) (R : iProp Σ) (m : PtBytes.pamap)
      (a : Arch.pa) (w0 : mword 64) :
    ⊢ ∀ wnew : mword 64,
        ⌜pte_wb_ok w0 wnew⌝ -∗
        gen_heap_interp (hG := riscv_memGS) m -∗ R -∗
        pt_slot_own PTT a (DfracOwn 1) w0 ==∗
        gen_heap_interp (hG := riscv_memGS) (write_bytes m a 8 wnew) ∗ R ∗
        pt_slot_own PTT a (DfracOwn 1) wnew.
  Proof.
    iIntros (wnew) "%Hwb Hgh HR Hs".
    iDestruct (pt_slot_own_forget with "Hs") as "Hs".
    iMod (phys_word_pointsto_write m a w0 wnew with "Hgh Hs") as "[Hgh Hs]".
    iModIntro. iFrame "Hgh HR".
    iApply (pt_slot_own_of_raw_sc with "Hs").
  Qed.

  (* THE SC RE-TIER, page and tree: both tiers' slots are the raw word
     until cutover, so a whole table moves ledgers by rewriting.  Its one
     real consumer is the KERNEL TABLE'S PUBLICATION (ProofMain hands
     kvminit's ambient-tier tree to [KptShare.kpt_inv_alloc], whose body
     is at the context-free [KTier] -- tso-port A6.20/A6.21: an invariant
     body may not name a context).  The T-leg replaces this with the real
     publication ([KptPublish.kptree_publish]: pin mint + drain). *)
  Lemma pt_page_own_retier_sc (PTT PTT' : ptier) (dq : dfrac) (t : ptree) :
    pt_page_own_at PTT dq t ⊣⊢ pt_page_own_at PTT' dq t.
  Proof.
    rewrite /pt_page_own_at.
    apply bi.sep_proper; [reflexivity |].
    apply big_opL_proper. intros k i _.
    rewrite !pt_slot_raw_sc. reflexivity.
  Qed.

  Lemma ptree_own_retier_sc (PTT PTT' : ptier) (lvl : nat) :
    forall (dq : dfrac) (t : ptree),
      ptree_own_at PTT lvl dq t ⊣⊢ ptree_own_at PTT' lvl dq t.
  Proof.
    induction lvl as [| lvl IH]; intros dq t; cbn [ptree_own_at].
    - apply bi.sep_proper; [apply pt_page_own_retier_sc | reflexivity].
    - apply bi.sep_proper; [apply pt_page_own_retier_sc |].
      apply big_opL_proper. intros k i _.
      destruct (pt_kids t (mword_of_int i)); [apply IH | reflexivity].
  Qed.

End PtTreeShim.
