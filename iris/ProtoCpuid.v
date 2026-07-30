(* ProtoCpuid.v -- PROTOTYPE / DEMO for the explicit-CPUID refactor.
   See claude-notes/projects/explicit-cpuid.md.

   This file validates the CONSUMER side of the new leaf shape, which is where
   essentially all of the sweep's churn lands.  It demonstrates, by compiling:

     (D1) the leaf shape itself, and how cheap a leaf's own proof is -- the
          leaf INSTANTIATES [wp_next] at the hart it lands on, which is why
          Stage 1 needs no re-proving at the leaf layer;
     (D2) the load-bearing case: interrupts-off code that reads [tp] and keeps
          using the answer -- [push_off(); c = mycpu(); ...].  At [b = false]
          the hart collapses back and the continuation is stated with NO
          binder, exactly as contracts read today;
     (D3) a [b]-GENERIC straight-line stretch (the [memmove]/[strlen] case,
          called both with interrupts on and off): no case split on [b]
          anywhere, the per-step conditional equalities just compose.

   The leaf is a section HYPOTHESIS here, stated exactly as WpSconfAlu.v will
   state it, so this file validates the shape independently of the engine
   port. *)
From Stdlib Require Import ZArith Bool Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language weakestpre lifting.
From iris.base_logic.lib Require Import gen_heap ghost_map ghost_var invariants.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExec.
Require Import RegFile HartTp WpNext WpGpr InstrBytes WpMmodeLeafBase StackOwn.
Require Import SmodeCore.
Require Import IntrDefs.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Local Open Scope Z_scope.
Import Defs.

Notation Ra5 := (mword_of_int 15 : mword 5).
Notation Rzero := (mword_of_int 0 : mword 5).

Section Proto.
  Context `{!riscvGS Σ}.
  Context `{!sieG Σ}.
  (* NOTE: no [Context `{CID : CpuId}].  The hart is a per-statement binder --
     which is what lets a lemma in THIS file be applied at a migrated hart. *)

  (* ================================================================== *)
  (* (D1) THE LEAF SHAPE, exactly as WpSconfAlu.v:422 will state it.     *)
  (*                                                                     *)
  (* Delta vs today: the lemma binder; [rd_ok rd] replacing [rd <> csp_rs1] *)
  (* IN THE SAME PREMISE SLOT (so no call site changes arity); [rget]      *)
  (* replacing [!!! Regidx] in the value premise (correct at tp too); the   *)
  (* [b] index; the [wp_next] wrapper.  Every RESOURCE keeps its spelling. *)
  (* ================================================================== *)
  Hypothesis wp_add_s_sconf :
    forall `{CID : CpuId} (Φ : mval -> iProp Σ)
      (pc : mword 64) (rd rs1 rs2 : mword 5) (wval : mword 64)
      (m : regfile) (n : nat) (b : bool),
      uint rd <> 0 ->
      rd_ok rd ->
      add_vec (rget m rs1) (rget m rs2) = wval ->
      sie_cap_gpr m n b -∗
      pc_is pc -∗
      instr pc false (RTYPE (Regidx rs2, Regidx rs1, Regidx rd, ADD)) -∗
      wp_next b (fun (CID : CpuId) =>
        sie_cap_gpr (<[Regidx rd := regval_into_reg wval]> m) n b -∗
        pc_is (add_vec_int pc 4) -∗
        WP (Loop : expr riscv_lang) {{ Φ }}) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}.

  (* ================================================================== *)
  (* (D2) INTERRUPTS OFF: read [tp], and the answer stays this cpu's.    *)
  (*                                                                     *)
  (*      add a5, zero, tp      ; a5 := cpuid   <- the tp READ           *)
  (*      add a5, a5,   a5                                               *)
  (*                                                                     *)
  (* The continuation is stated at [CID0] with no binder: at [b = false]  *)
  (* the hart provably cannot move, so [mycpu]'s answer stays valid       *)
  (* across every later instruction.  This is the case that would have    *)
  (* broken under an unconditional [∀ CID].                               *)
  (* ================================================================== *)
  Lemma demo_intr_off `{CID0 : CpuId} (Φ : mval -> iProp Σ)
      (pc : mword 64) (m : regfile) (n : nat) :
    uint Ra5 <> 0 -> rd_ok Ra5 ->
    let m1 := <[Regidx Ra5 := regval_into_reg
                 (add_vec (rget m Rzero) (cid_word_of cpu_id))]> m in
    sie_cap_gpr m n false -∗
    pc_is pc -∗
    instr pc false (RTYPE (Regidx Rtp, Regidx Rzero, Regidx Ra5, ADD)) -∗
    instr (add_vec_int pc 4) false (RTYPE (Regidx Ra5, Regidx Ra5, Regidx Ra5, ADD)) -∗
    ( sie_cap_gpr (<[Regidx Ra5 := regval_into_reg
                         (add_vec (rget m1 Ra5) (rget m1 Ra5))]> m1) n false -∗
      pc_is (add_vec_int (add_vec_int pc 4) 4) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    intros Hnz Hok m1. iIntros "Hcg Hpc Hi0 Hi4 Hcont".
    (* ---- add a5, zero, tp : the value premise is where the tp read lives.
       [rget m Rtp] IS this hart's id, by [rget_tp] -- no special leaf. ---- *)
    assert (Hv0 : add_vec (rget m Rzero) (rget m Rtp)
                  = add_vec (rget m Rzero) (cid_word_of cpu_id))
      by (by rewrite rget_tp).
    iApply (wp_add_s_sconf Φ pc Ra5 Rzero Rtp
              (add_vec (rget m Rzero) (cid_word_of cpu_id)) m n false Hnz Hok
              Hv0 with "Hcg Hpc Hi0").
    (* the whole cost of the refactor at an interrupts-off call site: *)
    rewrite wp_next_off.
    iIntros "Hcg Hpc".
    (* ---- add a5, a5, a5 : still on CID0, so [Hi4] (derived before the
       first step) is still about this hart. ---- *)
    iApply (wp_add_s_sconf Φ (add_vec_int pc 4) Ra5 Ra5 Ra5
              (add_vec (rget m1 Ra5) (rget m1 Ra5)) m1 n false Hnz Hok
              eq_refl with "Hcg Hpc Hi4").
    rewrite wp_next_off.
    iExact "Hcont".
  Qed.

  (* ================================================================== *)
  (* (D3) [b]-GENERIC: the [memmove] / [strlen] case.                    *)
  (*                                                                     *)
  (* Such a function is called both with interrupts on and off, so [b] is *)
  (* a parameter of its contract.  The point of the demo: the proof does  *)
  (* NOT case split on [b].  Each step hands back a conditional equality; *)
  (* [wp_next_trans] composes them, which is exactly what discharges the  *)
  (* function's OWN continuation at the end.                              *)
  (* ================================================================== *)
  Lemma demo_b_generic `{CID0 : CpuId} (Φ : mval -> iProp Σ)
      (pc : mword 64) (m : regfile) (n : nat) (b : bool) :
    uint Ra5 <> 0 -> rd_ok Ra5 ->
    let m1 := <[Regidx Ra5 := regval_into_reg
                 (add_vec (rget m Rzero) (rget m Rzero))]> m in
    sie_cap_gpr m n b -∗
    pc_is pc -∗
    instr pc false (RTYPE (Regidx Rzero, Regidx Rzero, Regidx Ra5, ADD)) -∗
    (* NOTE: quantified over the hart because [instr] is CID-indexed TODAY, so
       a decode fact derived before a step is useless after a migration.  The
       real fix (in the sweep) makes [instr] hart-INDEPENDENT -- it is derived
       from [kernel_text], which is already persistent global [↦ₓ□] memory, and
       its only CID dependence is the [∀ σ, mstate_interp σ -∗ ⌜…⌝] decode
       clause.  Then this binder disappears and decode facts survive a step. *)
    (∀ CID : CpuId,
        instr (add_vec_int pc 4) false (RTYPE (Regidx Ra5, Regidx Ra5, Regidx Ra5, ADD))) -∗
    wp_next b (fun (CID : CpuId) =>
      sie_cap_gpr (<[Regidx Ra5 := regval_into_reg
                         (add_vec (rget m1 Ra5) (rget m1 Ra5))]> m1) n b -∗
      pc_is (add_vec_int (add_vec_int pc 4) 4) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    intros Hnz Hok m1. iIntros "Hcg Hpc Hi0 Hi4 Hcont".
    iApply (wp_add_s_sconf Φ pc Ra5 Rzero Rzero
              (add_vec (rget m Rzero) (rget m Rzero)) m n b Hnz Hok
              eq_refl with "Hcg Hpc Hi0").
    (* step 1's continuation: a fresh hart (and hence a fresh SIE ghost, since
       the ghost is the hart's canonical [sie_gname]), plus the conditional
       equality.  NO destruct on [b]. *)
    rewrite /wp_next. iIntros (CID1 Hs1) "Hcg Hpc".
    iSpecialize ("Hi4" $! CID1).
    iApply (wp_add_s_sconf Φ (add_vec_int pc 4) Ra5 Ra5 Ra5
              (add_vec (rget m1 Ra5) (rget m1 Ra5)) m1 n b Hnz Hok
              eq_refl with "Hcg Hpc Hi4").
    iIntros (CID2 Hs2) "Hcg Hpc".
    (* discharge the function's own continuation at the hart we ended on,
       with the COMPOSED equality. *)
    iApply ("Hcont" $! CID2 with "[%] Hcg Hpc").
    wp_next_chain.
  Qed.

End Proto.
