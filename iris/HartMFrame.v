(* HartMFrame.v -- the FRAME BRIDGE for the M-mode instruction wrapper.

   The leaves hold their register state as [gpr_file m] / [pc_is pc] /
   [mmode_config dq]; the [swp] layer wants [hreg_frame rs Drw] and
   [hreg_frame_ro Df rs Dro].  Doing that conversion ONCE, here, is what
   keeps the 135 leaf statements unchanged: a leaf never sees a footprint,
   a register-file tower, or [hreg_frame].
   
   THE FOOTPRINT SPLIT, and why the GPRs have to be in it.  The wrapper
   itself ([try_step]'s prelude and tail, the fetch, the decode, the tick)
   touches NO general-purpose register -- so it is tempting to leave the
   GPRs outside [Drw] and let them ride in the caller's [R].  That fails at
   the next step down: a leaf discharges its [swp (execute i)] by
   [swp_hfrun], which needs ONE frame covering everything [execute i]
   touches -- the GPRs it reads and writes AND [nextPC] for the jumps.
   Splitting [hreg_frame _ Drw] apart and recombining it with [gpr_file] at
   each of the 135 leaves is the same conversion done 135 times.  So the
   GPRs go in [Drw] and the conversion happens here.
   
   MEASURED: the 31-way [big_sepS] split costs ~17 s (30 [big_sepS_union]
   rewrites, each with a [set_solver] disjointness side condition).  That
   is a one-time cost in this file, not a per-leaf one. *)
From Stdlib Require Import ZArith.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap ghost_map.
From iris.program_logic Require Import language weakestpre.
Require Import SailStdpp.Operators_mwords Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvLang RiscvPtsto RiscvExec HartSwp HartLift HartSpan
        RegFile WpGpr.
Local Open Scope Z_scope.

(* the 31 writable GPRs.  x0 is NOT here: [gpr_pt] at index 0 is the PURE
   fact [v = zero_reg], not a cell, because x0 is hardwired. *)
Definition mm_gpr_D : gset register :=
  {[ (R_bitvector_64 x1 : register); R_bitvector_64 x2; R_bitvector_64 x3;
     R_bitvector_64 x4; R_bitvector_64 x5; R_bitvector_64 x6;
     R_bitvector_64 x7; R_bitvector_64 x8; R_bitvector_64 x9;
     R_bitvector_64 x10; R_bitvector_64 x11; R_bitvector_64 x12;
     R_bitvector_64 x13; R_bitvector_64 x14; R_bitvector_64 x15;
     R_bitvector_64 x16; R_bitvector_64 x17; R_bitvector_64 x18;
     R_bitvector_64 x19; R_bitvector_64 x20; R_bitvector_64 x21;
     R_bitvector_64 x22; R_bitvector_64 x23; R_bitvector_64 x24;
     R_bitvector_64 x25; R_bitvector_64 x26; R_bitvector_64 x27;
     R_bitvector_64 x28; R_bitvector_64 x29; R_bitvector_64 x30;
     R_bitvector_64 x31 ]}.

Section frame.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  (* THE SPLIT.  [hreg_frame] over the 31 GPRs, as the 31 cells a leaf
     actually holds.  Stated (and proved) once; every use downstream is an
     [iApply], not a re-derivation. *)
  Lemma mm_gpr_split (rs : regstate) :
    (hreg_frame rs mm_gpr_D : iProp Σ) ⊣⊢
    ((R_bitvector_64 x1) ↦ᵣ register_lookup (R_bitvector_64 x1) rs ∗
     (R_bitvector_64 x2) ↦ᵣ register_lookup (R_bitvector_64 x2) rs ∗
     (R_bitvector_64 x3) ↦ᵣ register_lookup (R_bitvector_64 x3) rs ∗
     (R_bitvector_64 x4) ↦ᵣ register_lookup (R_bitvector_64 x4) rs ∗
     (R_bitvector_64 x5) ↦ᵣ register_lookup (R_bitvector_64 x5) rs ∗
     (R_bitvector_64 x6) ↦ᵣ register_lookup (R_bitvector_64 x6) rs ∗
     (R_bitvector_64 x7) ↦ᵣ register_lookup (R_bitvector_64 x7) rs ∗
     (R_bitvector_64 x8) ↦ᵣ register_lookup (R_bitvector_64 x8) rs ∗
     (R_bitvector_64 x9) ↦ᵣ register_lookup (R_bitvector_64 x9) rs ∗
     (R_bitvector_64 x10) ↦ᵣ register_lookup (R_bitvector_64 x10) rs ∗
     (R_bitvector_64 x11) ↦ᵣ register_lookup (R_bitvector_64 x11) rs ∗
     (R_bitvector_64 x12) ↦ᵣ register_lookup (R_bitvector_64 x12) rs ∗
     (R_bitvector_64 x13) ↦ᵣ register_lookup (R_bitvector_64 x13) rs ∗
     (R_bitvector_64 x14) ↦ᵣ register_lookup (R_bitvector_64 x14) rs ∗
     (R_bitvector_64 x15) ↦ᵣ register_lookup (R_bitvector_64 x15) rs ∗
     (R_bitvector_64 x16) ↦ᵣ register_lookup (R_bitvector_64 x16) rs ∗
     (R_bitvector_64 x17) ↦ᵣ register_lookup (R_bitvector_64 x17) rs ∗
     (R_bitvector_64 x18) ↦ᵣ register_lookup (R_bitvector_64 x18) rs ∗
     (R_bitvector_64 x19) ↦ᵣ register_lookup (R_bitvector_64 x19) rs ∗
     (R_bitvector_64 x20) ↦ᵣ register_lookup (R_bitvector_64 x20) rs ∗
     (R_bitvector_64 x21) ↦ᵣ register_lookup (R_bitvector_64 x21) rs ∗
     (R_bitvector_64 x22) ↦ᵣ register_lookup (R_bitvector_64 x22) rs ∗
     (R_bitvector_64 x23) ↦ᵣ register_lookup (R_bitvector_64 x23) rs ∗
     (R_bitvector_64 x24) ↦ᵣ register_lookup (R_bitvector_64 x24) rs ∗
     (R_bitvector_64 x25) ↦ᵣ register_lookup (R_bitvector_64 x25) rs ∗
     (R_bitvector_64 x26) ↦ᵣ register_lookup (R_bitvector_64 x26) rs ∗
     (R_bitvector_64 x27) ↦ᵣ register_lookup (R_bitvector_64 x27) rs ∗
     (R_bitvector_64 x28) ↦ᵣ register_lookup (R_bitvector_64 x28) rs ∗
     (R_bitvector_64 x29) ↦ᵣ register_lookup (R_bitvector_64 x29) rs ∗
     (R_bitvector_64 x30) ↦ᵣ register_lookup (R_bitvector_64 x30) rs ∗
     (R_bitvector_64 x31) ↦ᵣ register_lookup (R_bitvector_64 x31) rs)%I.
  Proof.
    rewrite /hreg_frame /mm_gpr_D.
    repeat (rewrite big_sepS_union; last set_solver).
    rewrite !big_sepS_singleton.
    by rewrite !bi.sep_assoc.
  Qed.

  (* the per-index reduction the [gpr_file] side needs: at a CONCRETE
     nonzero index [gpr_pt] is just the cell, and [gpr_of_Z (uint i)]
     computes.  Instant. *)
  Lemma gpr_pt_cell (i : SailStdpp.Values.mword 5) (v : SailStdpp.Values.mword 64) :
    uint i <> 0 ->
    gpr_pt (Regidx i) v ⊣⊢ ((R_bitvector_64 (gpr_of_Z (uint i))) ↦ᵣ v : iProp Σ).
  Proof.
    intros Hnz. cbv [gpr_pt].
    rewrite (proj2 (Z.eqb_neq (uint i) 0) Hnz). reflexivity.
  Qed.

End frame.
