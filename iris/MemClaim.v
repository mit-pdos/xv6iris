(* ======================================================================= *)
(*  MemClaim.v -- THE PHYSICAL WINDOW AND ITS ADDRESS CLAIM.               *)
(*                                                                        *)
(*  [wordw_pointsto] (a width-indexed run of ctx bytes), the free-window   *)
(*  twin [wordw_free], and the ADDRESS CLAIM [mem_claim]/[wordw_claim]     *)
(*  every translation side-condition is derived from.  Split out of        *)
(*  WpSconfMem.v on 2026-09-03 FOR THE BUILD DAG, not for the reader: the  *)
(*  vocabulary needs nothing but the memory layer ([RiscvPtsto], [TsoCtx]) *)
(*  while WpSconfMem.v sits on top of the whole WP engine, and the         *)
(*  file-system side wants only the claim.  [IcacheInv.iref_claims] --     *)
(*  four lines naming [wordw_claim] -- was the tree's single most          *)
(*  expensive require edge: it pulled the engine (SmodeCorePt, WpIntrInv,  *)
(*  WpSmodeIntr, WpSconfMem, ...) onto the critical path in front of the   *)
(*  whole icache/fs cone, and WpSconfMem was the ONLY direct dependency of *)
(*  IcacheInv that reached the engine at all.  See                         *)
(*  claude-notes/optimization.md, [a Require between two Proof<F>.v files  *)
(*  is pure critical path].                                                *)
(*                                                                        *)
(*  WpSconfMem.v [Require Export]s this file, so every consumer that       *)
(*  reached these names through it still does; only the QUALIFIED spelling *)
(*  moved ([WpSconfMem.wordw_claim] -> [MemClaim.wordw_claim]).            *)
(* ======================================================================= *)

From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvModelBytes RiscvLang RiscvPtsto.
Require Import RiscvExtras.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import Xv6G.
Require Import TsoMemPa.
Require Import TsoCtx.

Section MemClaim.
  (* the Context block is WpSconfMem.v's, copied verbatim so every moved
     statement is generalized over exactly the section variables it was
     before; the unused ones are not generalized over at all. *)
  Context `{!riscvGS Σ}.
  Context `{!xv6G Σ}.
  Context `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}.
  Context {kt : ktier}.
  Context {p : mword 64}.

  (* TIER-INDEXED through its bytes (sp-migration phase D): the [CurKtier]
     instance argument rides along, so every ambient spelling
     [wordw_pointsto width a dq w] is unchanged and an explicit-tier one is
     [wordw_pointsto (KTR := ktd) width a dq w]. *)
  (* LEDGER MEMBERS (tso-machine-flip.md §6 amendment A6.18, ratified): the
     rehearsal-era ruling made this window RAW because the only cost of a
     ctx datum was crossing a seal for nothing.  Post-flip the S-mode data
     nodes owe [Mobl_ram_plain] on a read and the append on a write, and
     NEITHER is payable from a flat cell -- so the datum carries its ledger
     residue.  THE CONTEXT IS THE SECTION'S AMBIENT [XI], so this is an
     invisible binder: every exported statement below is textually
     unchanged, and [own_context] arrives with the [sie_cap_gpr] they all
     already take (tso-port.md §0.13': it is a conjunct of
     [IntrDefs.sie_cap]). *)
  Definition wordw_pointsto `{KTR : !CurKtier} (width : Z) (a : Arch.pa) (dq : dfrac) (w : mword (8*width)) : iProp Σ :=
    (⌜is_aligned_paddr (Physaddr a) width = true⌝ ∗
     [∗ list] j ∈ seq 0 (Z.to_nat width),
        ctx_pointsto cur_ctx (pa_add a j) dq (nth_byte w j))%I.

  (* THE PAYOFF (A6.18): the 8-byte window simply IS the ↦₈ cell now -- no
     shim, no crossing, no continuation adapter.  Kept only so the wrappers
     that named it keep compiling; it is [reflexivity] up to [Z.to_nat]. *)
  Lemma wordw8_ctx `{KTR2 : !CurKtier} (a : Arch.pa)
      (dq : dfrac) (v : mword 64) :
    wordw_pointsto (KTR := KTR2) 8 a dq v
    ⊣⊢ ctx_word_pointsto (KTR := KTR2) cur_ctx a dq v.
  Proof.
    rewrite /wordw_pointsto ctx_word_pointsto_unfold.
    by change (Z.to_nat 8) with 8%nat.
  Qed.

  (* main's siblings at 4 and 2 (main-tso-readiness A12): the windows at the
     narrower widths ARE the ctx cells, by the same unfolding *)
  Lemma wordw4_ctx `{KTR2 : !CurKtier} (a : Arch.pa)
      (dq : dfrac) (v : mword 32) :
    wordw_pointsto (KTR := KTR2) 4 a dq v
    ⊣⊢ ctx_word4_pointsto (KTR := KTR2) cur_ctx a dq v.
  Proof.
    rewrite /wordw_pointsto /TsoCtx.ctx_word4_pointsto.
    by change (Z.to_nat 4) with 4%nat.
  Qed.

  Lemma wordw2_ctx `{KTR2 : !CurKtier} (a : Arch.pa)
      (dq : dfrac) (v : mword 16) :
    wordw_pointsto (KTR := KTR2) 2 a dq v
    ⊣⊢ ctx_word2_pointsto (KTR := KTR2) cur_ctx a dq v.
  Proof.
    rewrite /wordw_pointsto /TsoCtx.ctx_word2_pointsto.
    by change (Z.to_nat 2) with 2%nat.
  Qed.

  (* THE ADDRESS CLAIM, AND WHY THE ATOMIC-UPDATE FORMS TAKE IT.
     Per node, an access TRANSLATES before it reads, and the translation
     needs the window's claim -- its [ppn], canonicality, RAM-ness and tier
     pin -- while the atomic update is opened at the READ node, several
     nodes later.  A LINEAR atomic update cannot be peeked at and put back,
     so the claim (which is persistent, and says nothing about the VALUE)
     rides beside it.  Every caller has it: an owner of the window reads it
     off the points-to ([wordw_claim_of]), and an invariant-backed caller
     off one peek-open of its (persistent) accessor. *)
  (* THE BYTE'S CLAIM: [mem_pointsto] minus the physical ownership -- the
     mapping, canonicality, RAM-ness and the tier pin.  THE ONE LEMMA every
     translation side-condition is derived from ([mem_pointsto_claim]); the
     word form below is this at byte 0 plus the word's alignment. *)
  Definition mem_claim `{KTR : !CurKtier} (a : Arch.pa) : iProp Σ :=
    (∃ ppn : mword 44,
       kmap_at (svpn_of a) ppn KP_rw ∗
       ⌜(uint a < 274877906944)%Z⌝ ∗
       ⌜addr_is_ram (pa_of ppn a)⌝ ∗
       ⌜ktier_pin cur_ktier ppn a⌝)%I.

  Global Instance mem_claim_persistent `{KTR : !CurKtier} a :
    Persistent (mem_claim a).
  Proof. apply _. Qed.

  Lemma mem_pointsto_claim `{KTR : !CurKtier} (a : Arch.pa) (dq : dfrac) (b : bv 8) :
    a ↦ₘ{dq} b -∗ mem_claim a.
  Proof.
    iIntros "Hb".
    iDestruct (TsoCtx.ctx_pointsto_forget with "Hb") as "Hb".
    iDestruct (mem_pointsto_acc with "Hb")
      as (ppn) "(#Hk & %Hcan & %Hkd0 & %Hid & _ & _)".
    iExists ppn. iFrame "Hk". done.
  Qed.

  Definition wordw_claim `{KTR : !CurKtier} (width : Z) (a : Arch.pa) : iProp Σ :=
    (⌜is_aligned_paddr (Physaddr a) width = true⌝ ∗ mem_claim a)%I.

  Global Instance wordw_claim_persistent `{KTR : !CurKtier} width a :
    Persistent (wordw_claim width a).
  Proof. apply _. Qed.

  Lemma wordw_claim_of `{KTR : !CurKtier} (width : Z) (a : Arch.pa) (dq : dfrac)
      (w : mword (8*width)) :
    0 < width ->
    wordw_pointsto width a dq w -∗ wordw_claim width a.
  Proof.
    intros Hw0. iIntros "[%Hal Hb]".
    iDestruct (big_sepL_lookup_acc _ _ 0%nat 0%nat with "Hb") as "[Hb0 _]".
    { rewrite lookup_seq_lt; [reflexivity | lia]. }
    iEval (rewrite pa_add_0) in "Hb0".
    iSplitR; [done|]. iApply (mem_pointsto_claim with "Hb0").
  Qed.

  (* main's claim readers off a ctx cell (main-tso-readiness A12): the
     address claim a leaf wants, from the window the caller holds *)

  Lemma ctx_word2_claim `{KTR2 : !CurKtier} (a : Arch.pa)
      (dq : dfrac) (w : mword 16) :
    (0 < 2)%Z ->
    ctx_word2_pointsto (KTR := KTR2) cur_ctx a dq w -∗
    wordw_claim (KTR := KTR2) 2 a.
  Proof.
    intros _.
    rewrite -(wordw2_ctx (KTR2 := KTR2)).
    iApply (wordw_claim_of (KTR := KTR2) 2 a dq w ltac:(lia)).
  Qed.

  Lemma ctx_word_claim `{KTR2 : !CurKtier} (a : Arch.pa)
      (dq : dfrac) (w : mword 64) :
    (0 < 8)%Z ->
    ctx_word_pointsto (KTR := KTR2) cur_ctx a dq w -∗
    wordw_claim (KTR := KTR2) 8 a.
  Proof.
    intros _.
    rewrite -(wordw8_ctx (KTR2 := KTR2)).
    iApply (wordw_claim_of (KTR := KTR2) 8 a dq w ltac:(lia)).
  Qed.

  (* ------------------------------------------------------------------- *)
  (* §0.26′ / A6.85: THE VISIBILITY-FREE WINDOW.  [wordw_pointsto] with    *)
  (* every byte at [TsoCtx.mem_free] -- the fraction and the timestamp     *)
  (* element, no justification.  A window in this shape may be STORED to   *)
  (* and may not be LOADED from, which is exactly a free page's contract   *)
  (* (tso-port.md §0.26′): the freer holds no value determinate at its own *)
  (* view, and does not need one.                                         *)
  (* ------------------------------------------------------------------- *)
  Definition wordw_free `{KTR : !CurKtier} (width : Z) (a : Arch.pa) : iProp Σ :=
    (⌜is_aligned_paddr (Physaddr a) width = true⌝ ∗
     [∗ list] j ∈ seq 0 (Z.to_nat width),
        TsoCtx.mem_free (pa_add a j) (DfracOwn 1))%I.

  Lemma mem_free_claim `{KTR : !CurKtier} (a : Arch.pa) (dq : dfrac) :
    TsoCtx.mem_free a dq -∗ mem_claim a.
  Proof.
    rewrite /TsoCtx.mem_free /mem_claim.
    iIntros "(%ppn & #Hk & %Hc & %Hp & Hb)".
    iDestruct (TsoCtx.phys_free_ram with "Hb") as %Hram.
    iExists ppn. iFrame "Hk". done.
  Qed.

  Lemma wordw_free_claim `{KTR : !CurKtier} (width : Z) (a : Arch.pa) :
    0 < width -> wordw_free width a -∗ wordw_claim width a.
  Proof.
    intros Hw0. iIntros "[%Hal Hb]".
    iDestruct (big_sepL_lookup_acc _ _ 0%nat 0%nat with "Hb") as "[Hb0 _]".
    { rewrite lookup_seq_lt; [reflexivity | lia]. }
    iEval (rewrite pa_add_0) in "Hb0".
    iSplitR; [done|]. iApply (mem_free_claim with "Hb0").
  Qed.

  (* the width-1 free window IS one free byte, the twin of [wordw1_byte] *)
  Lemma wordw1_free `{KTR : !CurKtier} (a : Arch.pa) :
    wordw_free 1 a ⊣⊢ TsoCtx.mem_free a (DfracOwn 1).
  Proof.
    rewrite /wordw_free. change (Z.to_nat 1) with 1%nat.
    rewrite big_sepL_singleton pa_add_0.
    iSplit; [ iIntros "[_ $]"
            | iIntros "$"; iPureIntro;
              unfold is_aligned_paddr, is_aligned_vaddr; cbn [bits_of_physaddr];
              rewrite Z.rem_1_r; reflexivity ].
  Qed.

  (* a REGISTERED window forgets to a free one, per byte *)
  Lemma wordw_pointsto_free `{KTR : !CurKtier} (width : Z) (a : Arch.pa)
      (w : mword (8*width)) :
    wordw_pointsto width a (DfracOwn 1) w ⊢ wordw_free width a.
  Proof.
    rewrite /wordw_pointsto /wordw_free. iIntros "[$ Hb]".
    iApply (big_sepL_mono with "Hb"). iIntros (k j _) "H".
    by iApply TsoCtx.ctx_pointsto_free.
  Qed.

End MemClaim.
