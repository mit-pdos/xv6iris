(* SieCapCtx.v -- ONE lemma: peel the thread-of-control token out of a
   [sie_cap_gpr] bundle and put it back.

   WHY IT EXISTS AT ALL.  Every [TsoCtx.ctx_deposit] / [TsoCtx.ctx_absorb]
   site needs [own_context cur_ctx] -- the depositor's / absorber's
   authority over its own context, which is what bounds the moved facts'
   timestamps and which no persistent surrogate can replace
   (tso-port.md §0.15′ step (ii)).  A running kernel thread's copy of that
   token lives inside [IntrDefs.sie_cap]'s fourth conjunct, so a
   whole-function proof that already threads [sie_cap_gpr] has one -- it
   just has to get at it without losing the bundle.

   WHY IT IS ITS OWN FILE.  The peel is a six-way destructuring of
   [sie_cap] wrapped in [sie_cap_gpr_split]/[sie_cap_gpr_join], and its
   consumers are the bcache escrow's six open sites, the secondary hart's
   boot-deposit claim and the park's [own_context] threading.  It does NOT
   belong in [IntrDefs.v]: 425 files sit on that one, and this is a
   twelve-line convenience (tso-absorb-memo.md §6; tso-port.md §0.16′
   step (ii) records the same ruling for the same reason). *)

From iris.proofmode Require Import proofmode.
(* base_logic's canonical [uPredI] structure must be IMPORTED here: with
   [proofmode] alone the [-∗] in this file's statement elaborates to a bare
   [bi_car ?PROP] and does not unify with [iProp Σ]. *)
From iris.base_logic.lib Require Import ghost_var ghost_map invariants gen_heap own.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import RiscvLang RiscvPtsto.
Require Import RegFile.
Require Import StackOwn.
Require Import IntrDefs.
Require Import Xv6G.
Require Import TsoCtx.

Section SieCapCtx.
  Context `{!riscvGS Σ}.
  Context `{!xv6G Σ, !bioslotG Σ}.
  Context `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}.

  (* THE ACCESSOR.  Borrow-and-return, not a split: the bundle is
     reassembled by the closer, so the caller's [sie_cap_gpr] hypothesis is
     restored exactly (same [kt]/[m]/[avail]/[b]/[p]) and no downstream spec
     premise changes shape. *)
  Lemma sie_cap_gpr_own_ctx_acc {kt : ktier}
      (m : regfile) (avail : nat) (b : bool) (p : mword 64) :
    sie_cap_gpr kt m avail b p -∗
    own_context cur_ctx ∗ (own_context cur_ctx -∗ sie_cap_gpr kt m avail b p).
  Proof.
    iIntros "Hcg".
    iDestruct (sie_cap_gpr_split with "Hcg") as "(Hhs & Hsc & Hcap & Hfile)".
    iDestruct "Hcap" as "(Hstk & Htr & Harm & Hctx & #Htc & #Hwit)".
    iFrame "Hctx". iIntros "Hctx".
    iApply (sie_cap_gpr_join with "Hhs Hsc [Hstk Htr Harm Hctx] Hfile").
    rewrite /sie_cap. iFrame "Hstk Htr Harm Hctx Htc Hwit".
  Qed.

End SieCapCtx.
