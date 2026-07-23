(* SwtchCtx.v -- the definitional layer of the context-switch protocol:
   struct-context cell ownership, the callee-saved register image, the
   resume-pc form, the [valid_context] fixpoint, and the swtch-crossing
   configuration bundle [swconf].

   Kept free of any whole-function proof so that spec files (SpecSwtch,
   SchedCtx, SpecSched, SpecYield) depend only on definitions -- the swtch
   proof (WpSwtchSconf.v) and its decode layer (WpSwtchVc.v) sit above. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
From iris.base_logic.lib Require Import invariants ghost_var.
Require Import SailStdpp.Base SailStdpp.Operators_mwords SailStdpp.Values SailStdpp.MachineWord.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvLang RiscvPtsto.
Require Import InstrBytes.
Require Import RegFile WpGpr.
Require Import SmodeCore.
Require Import IntrDefs.
Local Open Scope Z_scope.

(* struct-context field layout: field i (0..13) holds register [ctx_regs !! i]
   at byte offset 8*i -- ra sp s0 s1 s2 .. s11. *)
Definition ctx_regs : list (mword 5) :=
  [ mword_of_int 1;  mword_of_int 2;  mword_of_int 8;  mword_of_int 9;
    mword_of_int 18; mword_of_int 19; mword_of_int 20; mword_of_int 21;
    mword_of_int 22; mword_of_int 23; mword_of_int 24; mword_of_int 25;
    mword_of_int 26; mword_of_int 27 ].

(* the callee-saved register image of a machine file, in field order. *)
Definition callee_img (m : regfile) : list (mword 64) :=
  map (fun r => m !!! Regidx r) ctx_regs.

(* the pc a [ret] to saved return address [ra] lands on (low bit cleared);
   matches wp_cret_s_zca's target expression. *)
Definition ctx_pc (ra : mword 64) : mword 64 :=
  update_vec_dec (add_vec ra (sign_extend' 64 (zeros' 12))) 0 ('b"0").

Section SwtchCtx.
  Context `{!riscvGS Σ}.
  Context `{CID : CpuId}.

  (* ================================================================== *)
  (* struct context: ownership of its 14 saved-register cells.           *)
  (* ================================================================== *)
  Fixpoint ctx_cells_at (c : mword 64) (off : Z) (vs : list (mword 64)) : iProp Σ :=
    match vs with
    | [] => emp
    | v :: rest => ((add_vec c (mword_of_int off)) ↦₈ v ∗ ctx_cells_at c (off + 8) rest)%I
    end.
  Definition ctx_cells (c : mword 64) (vs : list (mword 64)) : iProp Σ :=
    ctx_cells_at c 0 vs.

  Local Instance ctx_cells_at_timeless c off vs : Timeless (ctx_cells_at c off vs).
  Proof.
    revert off; induction vs as [|v vs IH]; intros off; simpl.
    - apply _.
    - apply bi.sep_timeless; [ | apply IH ].
      rewrite /word_pointsto /mem_pointsto. apply _.
  Qed.
  Global Instance ctx_cells_timeless c vs : Timeless (ctx_cells c vs).
  Proof. rewrite /ctx_cells. apply _. Qed.

  (* -------------------------------------------------------------------- *)
  (* valid_context sc Phi P c : the context saved at [c] admits a WP to     *)
  (* run.  It owns c's 14 saved-register cells and is the wand from (config    *)
  (* bundle [sc] + pc at c.ra + a gpr file whose callee-saved regs are c's    *)
  (* saved values, caller-saved arbitrary) to a whole-machine [WP Loop        *)
  (* {{Phi}}].  On resumption the continuation is handed, for the             *)
  (* (existentially quantified) context [cret] that resumed c,                *)
  (* [▷ valid_context sc Phi P cret] together with [P c cret tpv] -- a        *)
  (* caller-chosen THREE-place payload predicate:                             *)
  (*   [c]    the context being resumed (statically known to the resumed      *)
  (*          party, so a single chain-global P can discriminate directions   *)
  (*          -- a chain rebuilds the suspended old context at the SAME P,    *)
  (*          so per-direction P's are impossible);                           *)
  (*   [cret] the resumer's context (existential: never pin a partner);       *)
  (*   [tpv]  the RESUMER's tp register value.  [callee_img] deliberately     *)
  (*          does not pin tp (a context may in principle resume on another   *)
  (*          CPU), but the resumed code recomputes every per-CPU cell        *)
  (*          address from its own tp -- the payload is the only channel      *)
  (*          that can tie the received cells to the new file's tp, so the    *)
  (*          slot applies P at [m !!! x4] of the resumed register file.      *)
  (* [P] is fixed along the whole chain.  The S-mode configuration is         *)
  (* abstracted as the single resource [sc], so this definition does NOT      *)
  (* depend on the individual CSR parameters.  Well-defined Iris [fixpoint]   *)
  (* because the recursive occurrence is under [▷].                           *)
  (*                                                                          *)
  (* The resume wand HANDS BACK [ctx_cells c vs]: swtch only READS the         *)
  (* resumed context's cells, and the resumed party must own its own          *)
  (* context field again to ever swtch OUT again (it is what the next          *)
  (* park saves into).                                                        *)
  (* -------------------------------------------------------------------- *)
  Definition valid_context_pre
      (sc : iProp Σ) (Phi : mval -> iProp Σ)
      (P : mword 64 -d> mword 64 -d> mword 64 -d> iPropO Σ)
      (rec : mword 64 -d> iPropO Σ) : mword 64 -d> iPropO Σ := fun c =>
    (∃ vs : list (mword 64),
      ⌜length vs = 14%nat⌝ ∗
      ⌜eq_vec (access_vec_dec (ctx_pc (nth 0 vs (mword_of_int 0))) 0) ('b"0") = true⌝ ∗
      ctx_cells c vs ∗
      (∀ (m : regfile),
         ⌜callee_img m = vs⌝ -∗ sc -∗
         pc_is (ctx_pc (m !!! Regidx (mword_of_int 1))) -∗ gpr_file m -∗
         ctx_cells c vs -∗
         (∃ cret : mword 64,
            ▷ rec cret ∗ P c cret (m !!! Regidx (mword_of_int 4 : mword 5))) -∗
         WP (Loop : expr riscv_lang) {{ Phi }}))%I.

  Global Instance valid_context_pre_contractive sc Phi
      (P : mword 64 -d> mword 64 -d> mword 64 -d> iPropO Σ) :
    Contractive (valid_context_pre sc Phi P).
  Proof. solve_contractive. Qed.

  Definition valid_context (sc : iProp Σ) (Phi : mval -> iProp Σ)
      (P : mword 64 -d> mword 64 -d> mword 64 -d> iPropO Σ) : mword 64 -d> iPropO Σ :=
    fixpoint (valid_context_pre sc Phi P).

  Lemma valid_context_unfold (sc : iProp Σ) (Phi : mval -> iProp Σ)
      (P : mword 64 -d> mword 64 -d> mword 64 -d> iPropO Σ) (c : mword 64) :
    valid_context sc Phi P c ⊣⊢
      valid_context_pre sc Phi P (valid_context sc Phi P) c.
  Proof. apply (fixpoint_unfold (valid_context_pre sc Phi P) c). Qed.

End SwtchCtx.

Section Swconf.
  Context `{!riscvGS Σ, !sieG Σ}.
  Context `{CID : CpuId}.

  (* ------------------------------------------------------------------ *)
  (* The swtch-crossing configuration bundle: what a scheduler context    *)
  (* switch carries from the suspending to the resumed party.  The STACK  *)
  (* does not cross -- each coroutine's [stack_own] is captured inside     *)
  (* the continuation closure it leaves behind, and [sie_cap_gpr] is       *)
  (* rebuilt on resume from the received pieces + fresh [gpr_file]         *)
  (* (sp is pinned by [callee_img]).  [intr_count 1]: xv6 asserts          *)
  (* noff == 1 at every scheduler swtch (exactly one push_off              *)
  (* outstanding on both sides).                                           *)
  (* ------------------------------------------------------------------ *)
  Definition swconf (γ : gname) : iProp Σ :=
    (sconf γ ∗
     hart_state ↦ᵣ HART_ACTIVE tt ∗
     strans_inv ∗
     sie_arm γ ∗
     intr_count γ 1)%I.
End Swconf.
