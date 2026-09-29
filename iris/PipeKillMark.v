(* ===================================================================== *)
(*  THE KILL/TAINT SEAM (lane KILL-TAINT).                               *)
(*                                                                       *)
(*  Two lanes closed the same arm of the pipeline application with the    *)
(*  same NAMED PREMISE                                                    *)
(*                                                                       *)
(*      Hktaint : box (forall gn, ChildTok.kill_shot gn -* app_taint)     *)
(*                                                                       *)
(*  -- CAT-PIPE for a pipe READ's -1 and ECHO-PIPE-2 for a pipe WRITE cut *)
(*  short.  This file holds the two results that retire it.              *)
(*                                                                       *)
(*  1.  THE REFUTATION.  The premise does not say that a kill taints     *)
(*      the application; it says THE APPLICATION IS TAINTED.  A shot     *)
(*      is FREELY ALLOCATABLE at a fresh generation                       *)
(*      ([ChildTok.gen_alloc] then [ChildTok.kill_pend_fire]) -- it says  *)
(*      nothing about any process that is running -- so the premise       *)
(*      implies its own conclusion outright.  Anything proved under it is *)
(*      a statement about a TAINTED era, where the claim's taint arm      *)
(*      makes the output say nothing.  This is durable-notes' vacuity     *)
(*      class: a gap premise parked as a bare forall that a caller can    *)
(*      only supply by already owning what it was meant to buy.           *)
(*                                                                       *)
(*  2.  THE HONEST ROW that replaces it.  A process INSIDE A SYSCALL      *)
(*      holds its own private block, and the block's last conjunct is the *)
(*      incarnation's MARKER ([ChildTok.taken_at], inside                 *)
(*      [SlotGen.gen_halves_priv]).  The marker refutes the spent arm of  *)
(*      <p->lock>'s killed row ([SchedCtx.kill_paid_shot_tear]), so a     *)
(*      nonzero flag read by such a process was written by a THIRD PARTY  *)
(*      -- who paid [app_taint] into the row.  The accessor here is what  *)
(*      lets piperead's and pipewrite's [killed()] call read that: the    *)
(*      pid quarter, the registration eighth AND the marker, lent         *)
(*      together off [ProcInv.proc_priv_core] and taken back.             *)
(* ===================================================================== *)
From Stdlib Require Import ZArith List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.algebra Require Import dfrac.
From iris.base_logic.lib Require Import own gen_heap.
From iris.proofmode Require Import proofmode.
Require Import SailStdpp.Base SailStdpp.Operators_mwords SailStdpp.Values.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvPtsto.
Require Import RiscvLang.
Require Import CtxIdDefs.
Require Import TsoCtx.
Require Import Xv6Cameras.
Require Import IrefSlots.
Require Import FileInvDefs.
Require Import FdSlots.
Require Import ProcGeom.
Require Import ChildTok.
Require Import SlotGen.
Require Import ProcInv.
Require Import Xv6G.
Local Open Scope Z_scope.

(* ===================================================================== *)
(*  1.  THE PREMISE TWO LANES TOOK IS THE TAINT ITSELF                    *)
(* ===================================================================== *)
Section KillTaintPremise.
  Context `{!xv6G Σ}.

  (* A kill shot at a FRESH generation costs nothing: [ChildTok.gen_alloc]
     mints a generation with its flag one-shot PENDING, and
     [ChildTok.kill_pend_fire] fires it.  Neither step touches any process,
     any proc slot or any lock. *)
  Lemma kill_shot_alloc : ⊢ |==> ∃ gn : gname, ChildTok.kill_shot gn.
  Proof using .
    iMod (ChildTok.gen_alloc (mword_of_int 0 : mword 64)
            (mword_of_int 0 : mword 32) (fun _ : Z => True)%I)
      as (gn) "[_ Hp]".
    iMod (ChildTok.kill_pend_fire with "Hp") as "#Hs".
    iModIntro. iExists gn. iExact "Hs".
  Qed.

  (* ...SO THE NAMED PREMISE IS ITS OWN CONCLUSION.  [T] is abstract, so
     this refutes the premise at [UCatPipe.pcat_round_at]'s [T] and at
     [UEchoPipe]'s [app_taint] alike. *)
  Lemma kill_taint_premise_gives_T (T : iProp Σ) :
    □ (∀ gn : gname, ChildTok.kill_shot gn -∗ T) -∗ |==> T.
  Proof using .
    iIntros "#Hk". iMod kill_shot_alloc as (gn) "#Hs".
    iModIntro. iApply ("Hk" with "Hs").
  Qed.

End KillTaintPremise.

(* ===================================================================== *)
(*  2.  THE MARKER, LENT OFF THE PRIVATE BLOCK                            *)
(* ===================================================================== *)
Section PipeKillMark.
  Context `{!riscvGS Σ}.
  Context `{XI : CurCtx}.
  Context `{ !fileG Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !irefslotG Σ, !wchG Σ}.
  Context `{GEN : GenId}.

  (* the live bundle's last conjunct, borrowed *)
  Lemma gen_halves_priv_taken (pa : mword 64) (pid : mword 32) (g : gname) :
    gen_halves_priv pa pid g -∗
    ChildTok.taken_at g ∗ (ChildTok.taken_at g -∗ gen_halves_priv pa pid g).
  Proof using .
    rewrite /gen_halves_priv. iIntros "[Hat Ht]".
    iSplitL "Ht"; [ iExact "Ht" | ]. iIntros "Ht". iFrame "Hat Ht".
  Qed.

  (* ...AND THE THREE ROWS A [killed()] CALL NEEDS AT ONCE
     ([SchedCtx.kill_paid_shot_tear]'s three arguments minus the row
     itself): the pid quarter the accessor agrees against, the
     registration eighth that says WHOSE row it is, and the marker that
     refutes the spent arm.  [ProcInv.proc_priv_core_pid_reg] is this
     without the marker; the proof is that one's, one conjunct further. *)
  Lemma proc_priv_core_pid_reg_taken (pa : mword 64) (pid : mword 32)
      (U : ustate) :
    proc_priv_core pa pid U -∗
    p_pid pa ↦₄{DfracOwn (1/4)} pid ∗
    pid_reg pid (DfracOwn qeighth) (pv_gen (us_V U)) ∗
    ChildTok.taken_at (pv_gen (us_V U)) ∗
    (p_pid pa ↦₄{DfracOwn (1/4)} pid -∗
     pid_reg pid (DfracOwn qeighth) (pv_gen (us_V U)) -∗
     ChildTok.taken_at (pv_gen (us_V U)) -∗
     proc_priv_core pa pid U).
  Proof using .
    iIntros "H". iEval (rewrite proc_priv_core_bare) in "H".
    iDestruct "H" as "(Hb & %Hlz & Hc & Hft & Hgq & Hxs & Hgh)".
    iDestruct (proc_priv_bare_pid with "Hb") as "[Hq Hbback]".
    iDestruct "Hgh" as "[Hat Ht]".
    iDestruct (gen_halves_at_reg with "Hat") as "[Hpr Hgback]".
    iSplitL "Hq"; [ iExact "Hq" | ].
    iSplitL "Hpr"; [ iExact "Hpr" | ].
    iSplitL "Ht"; [ iExact "Ht" | ].
    iIntros "Hq Hpr Ht". rewrite proc_priv_core_bare.
    iSplitL "Hbback Hq"; [ iApply ("Hbback" with "Hq") | ].
    iSplitR; [ iPureIntro; exact Hlz | ].
    iFrame "Hc Hft Hgq Hxs". rewrite /gen_halves_priv.
    iSplitL "Hgback Hpr"; [ iApply ("Hgback" with "Hpr") | iExact "Ht" ].
  Qed.

End PipeKillMark.
