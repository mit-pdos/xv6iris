(* UserCompute.v -- the REGISTER-ONLY retire arm.

   Safety is all that matters, so we never track register or memory
   CONTENTS: [user_inv] binds the gpr file existentially, and a compute
   step just re-establishes SOME [gpr_file g'] (the written fragment set to
   whatever the post-state holds -- no value threading).

   The fetched word is only revealed at runtime (existential page
   contents), so the arm cannot take it as a parameter; instead it takes
   an abstract per-step hypothesis [Hgpr] -- "at the pinned runtime state,
   the fetch+decode+execute yields a retire that changes ONLY nextPC, the
   TLB, and a single gpr [rd]" -- which the total classification discharges
   for each integer-compute family from [upt_fetch_instr] + the decode
   totality + that family's [_gpr] execute fact.  The arm handles the
   [u_dispatch = None] retire path: the try_step bookkeeping (tick +
   minstret bump) and the existential gpr-file / TLB re-establishment of
   [user_inv].                                                            *)
From Stdlib Require Import ZArith Bool Lia.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExec.
Require Import WpGpr.
Require Import UserPtTree UserExec.
Local Open Scope Z_scope.
Import Defs.

Section UserCompute.
  Context `{!riscvGS Σ}.
  Context `{CID : CpuId}.
  Context (C : ucfg) (pt : uptd).

  (* Peel the [rd] fragment out of an existential gpr file and hand back an
     insert-wand.  Value-agnostic: the caller reinserts whatever the
     post-state holds. *)
  Lemma gpr_file_acc (g : gmap regidx (mword 64)) (rd : mword 5) :
    (forall r : regidx, r ∈ dom g) ->
    uint rd <> 0 ->
    gpr_file g -∗
    (∃ v0 : mword 64, R_bitvector_64 (gpr_of_Z (uint rd)) ↦ᵣ v0) ∗
    (∀ v : mword 64, R_bitvector_64 (gpr_of_Z (uint rd)) ↦ᵣ v -∗
       gpr_file (<[Regidx rd := v]> g)).
  Proof.
    iIntros (Hdom Hrd) "[_ Hfmap]".
    assert (Hmd : g !! Regidx rd = Some (g !!! Regidx rd))
      by (apply lookup_lookup_total_dom; apply Hdom).
    iDestruct (big_sepM_insert_acc _ _ _ _ Hmd with "Hfmap") as "[Hrdc Hfins]".
    rewrite (gpr_pt_nz rd _ Hrd).
    iSplitL "Hrdc". { iExists _. iExact "Hrdc". }
    iIntros (v) "Hrdc".
    iSplitR.
    { iPureIntro. intro r. rewrite dom_insert_L. apply elem_of_union_r. apply Hdom. }
    iApply ("Hfins" $! v).
    rewrite (gpr_pt_nz rd _ Hrd). iExact "Hrdc".
  Qed.

  (* The abstract per-step RETIRE obligation the classification discharges
     per family.  It OWNS exactly what [run_hart_active] mutates on a
     retiring step -- the interp, the gpr file, the nextPC cell (the
     dispatch reduction sets it), [user_pt_inv] (the fetch may fill the TLB)
     and [user_cfg] (borrowed: the decode-agreement reads its cells) --
     and returns them re-established at [s_x], value-agnostically
     (existential gpr file), plus the pure facts the try_step epilogue
     needs: the run reduction, the hart still ACTIVE, and
     minstret_increment untouched.  The post-retire pc [va'] is
     EXISTENTIAL -- va+4 for base compute, va+2 for RVC, the target for
     jumps and taken branches -- the epilogue's tick lands PC := va'
     either way and [user_inv] rebinds the pc existentially.  The pure
     premises are engine-supplied (transported to the post-increment
     state the engine instantiates [σ] at); the arm keeps PC and the
     untouched CSR fragments.  [E] is the ambient mask. *)
  Definition retire_obligation (E : coPset) (σ : mstate) (va : mword 64)
      (g : gmap regidx (mword 64)) : iProp Σ :=
    (⌜u_step_pre σ va⌝ -∗
     mstate_interp σ -∗
     gpr_file g -∗
     nextPC ↦ᵣ va -∗
     user_pt_inv pt -∗
     user_cfg C -∗
     |={E}=>
       ∃ (ib : mword 32) (s_x : mstate) (g' : gmap regidx (mword 64))
         (va' : mword 64),
         ⌜exec (run_hart_active 0) σ = Some (Step_Execute (Retire_Success tt, ib), s_x)⌝ ∗
         ⌜register_lookup hart_state s_x.(sregs) = HART_ACTIVE tt⌝ ∗
         ⌜register_lookup (R_bool minstret_increment) s_x.(sregs)
            = register_lookup (R_bool minstret_increment) σ.(sregs)⌝ ∗
         ⌜register_lookup nextPC s_x.(sregs) = va'⌝ ∗
         mstate_interp s_x ∗
         gpr_file g' ∗
         nextPC ↦ᵣ va' ∗
         user_pt_inv pt ∗
         user_cfg C)%I.

End UserCompute.
