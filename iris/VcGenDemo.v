(* VcGenDemo.v -- the VCgen (VcGen.v) applied to a REAL kernel block: the
   4-instruction straight-line prologue of timerinit (0x8000001c),

       1141    c.addi  sp, -16        # sp := sp - 16
       e406    c.sdsp  ra, 8(sp)      # [sp-8]  := ra
       e022    c.sdsp  s0, 0(sp)      # [sp-16] := s0
       0800    c.addi4spn s0, sp, 16  # s0 := sp (the OLD sp)

   the same block WpTimerinit.wp_timerinit steps through by hand (four
   [iApply (wp_..._gpr ...)], ~40 lines of resource threading each).  Here
   the whole block is one [iApply wp_vc_block]:

     - the SYMBOLIC run [vc_block demo_st0 demo_prog = Some demo_st1] is
       discharged by [vm_compute] -- including the address arithmetic that
       identifies the two stores' targets with the declared footprint cells,
       and the [sp - 16 + 16 = sp] cancellation that makes the final s0 the
       OLD sp ([SX 2 0], visible SYNTACTICALLY in [demo_regs1]);
     - the [instr] decode facts come from [kernel_text] via the existing
       WpTimerinit templates (needed by ANY proof of this block);
     - no other per-instruction reasoning exists in this file.

   The lemma [wp_timerinit_prologue_vc] restates the result with ordinary
   [↦₈] pre/post-conditions (old stack words in, ra/s0 words out), i.e. the
   shape a surrounding (possibly concurrent) proof consumes. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language.
Require Import SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import SailStdpp.Base.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvExtras RiscvFetchExec WpLeafCommon WpGpr.
Require Import MinstretInv InstrBytes.
Require Import WpGprAddi WpGprLogic WpGprLui WpGprLoad WpGprStore WpGprRvc.
Require Import WpEntryNew WpSpinNew SmodeCore WpSmodeGpr WpMemsetS WpSmodeSret WpTimerinit.
Require Import VcGen.
From Kernel Require KernelSyms.
From iris.base_logic.lib Require Import invariants.
Local Open Scope Z_scope.

(* ---------------------------------------------------------------------- *)
(* The block, in the VCgen's alphabet.  The immediates are spelled exactly *)
(* as in the ti_instr9..12 decode facts (they are the decoder's output).   *)
(* ---------------------------------------------------------------------- *)
Definition demo_prog : list vinstr :=
  [ (true, Vaddi (sign_extend' 12 i9) csp_rs1 csp_rs1);
    (true, Vsd (zero_extend' 12 (concat_vec u10 ('b"000"))) ti_ra csp_rs1);
    (true, Vsd (zero_extend' 12 (concat_vec u11 ('b"000"))) ti_s0 csp_rs1);
    (true, Vaddi (caddi4spn_imm nz12) csp_rs1 ti_s0) ].

(* symbolic-variable naming convention: register xk starts as [SX k 0] (from
   [vregs_init]); 33/34 are the two old stack-word contents. *)
Definition demo_heap0 : list (sval * sval) :=
  [ (SX 2 (wrap64 (-8)),  SX 33 0);     (* [sp-8]  : old word v1 *)
    (SX 2 (wrap64 (-16)), SX 34 0) ].   (* [sp-16] : old word v2 *)

Definition demo_st0 : vstate :=
  VSt KernelSyms.timerinit vregs_init demo_heap0 [].

(* the symbolic post-state.  Note [ti_s0 ↦ SX 2 0]: the VCgen has computed
   s0 = (sp - 16) + 16 = the ORIGINAL sp, by canonical offset arithmetic. *)
Definition demo_regs1 : gmap regidx sval :=
  <[Regidx ti_s0 := SX 2 0]>
    (<[Regidx csp_rs1 := SX 2 (wrap64 (-16))]> vregs_init).
Definition demo_heap1 : list (sval * sval) :=
  [ (SX 2 (wrap64 (-8)),  SX 1 0);      (* [sp-8]  = ra *)
    (SX 2 (wrap64 (-16)), SX 8 0) ].    (* [sp-16] = s0 *)
Definition demo_st1 : vstate :=
  VSt (KernelSyms.timerinit + 8) demo_regs1 demo_heap1 [].

(* the whole symbolic execution of the block: ONE vm_compute. *)
Lemma demo_run : vc_block demo_st0 demo_prog = Some demo_st1.
Proof. vm_compute. reflexivity. Qed.

(* the valuation: symbolic variables -> this run's concrete values. *)
Definition demo_ρ (sp0 ra0 s00 v1 v2 : mword 64) : nat -> mword 64 :=
  fun n => match n with
           | 1%nat => ra0 | 2%nat => sp0 | 8%nat => s00
           | 33%nat => v1 | 34%nat => v2
           | _ => zero_reg
           end.

(* denotations of the four cells under that valuation, in caller-facing
   [add_vec_int]/plain form (pure bv algebra, proved once here). *)
Section DemoDen.
  Variable (sp0 ra0 s00 v1 v2 : mword 64).
  Let ρ := demo_ρ sp0 ra0 s00 v1 v2.

  Lemma demo_den_a1 : sval_den ρ (SX 2 (wrap64 (-8))) = add_vec_int sp0 (-8).
  Proof.
    cbn [sval_den ρ demo_ρ]. unfold add_vec_int. by rewrite mword_of_int_wrap.
  Qed.
  Lemma demo_den_a2 : sval_den ρ (SX 2 (wrap64 (-16))) = add_vec_int sp0 (-16).
  Proof.
    cbn [sval_den ρ demo_ρ]. unfold add_vec_int. by rewrite mword_of_int_wrap.
  Qed.
  Lemma demo_den_x (x : nat) :
    sval_den ρ (SX x 0) = ρ x.
  Proof. cbn [sval_den]. apply (avi0 (ρ x)). Qed.
End DemoDen.

Section VcGenDemo.
  Context `{!riscvGS Σ}.
  Context `{CID : CpuId}.

  (* the block's [instr] facts, from [kernel_text] (persistent), via the
     existing WpTimerinit decode templates. *)
  Lemma demo_block_instrs :
    kernel_text -∗ block_instrs KernelSyms.timerinit demo_prog.
  Proof.
    iIntros "#Ht". cbn [block_instrs demo_prog].
    replace (KernelSyms.timerinit + 2 + 2) with (KernelSyms.timerinit + 4) by lia.
    replace (KernelSyms.timerinit + 4 + 2) with (KernelSyms.timerinit + 6) by lia.
    iSplitR; [by iApply ti_instr9|].
    iSplitR; [by iApply ti_instr10|].
    iSplitR; [by iApply ti_instr11|].
    iSplitR; [by iApply ti_instr12|].
    done.
  Qed.

  (* The block WP with ordinary points-to pre/posts.  [gpr_file] is stated
     over [vregs_den (demo_ρ ...) vregs_init]; a caller holding an abstract
     complete file [m] converts with [vregs_den_init].  Everything below the
     denotation rewrites is ONE application of [wp_vc_block]. *)
  Lemma wp_timerinit_prologue_vc E (Φ : mval -> iProp Σ)
      (sp0 ra0 s00 v1 v2 : mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (q : Qp) :
    ↑minstretN ⊆ E ->
    pmp_all_off pmpcfg0 ->
    mmode_config (DfracOwn q) -∗
    pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
    pc_is (mword_of_int KernelSyms.timerinit) -∗
    gpr_file (vregs_den (demo_ρ sp0 ra0 s00 v1 v2) vregs_init) -∗
    kernel_text -∗
    add_vec_int sp0 (-8) ↦₈ v1 -∗
    add_vec_int sp0 (-16) ↦₈ v2 -∗
    ( mmode_config (DfracOwn q) -∗
      pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
      pc_is (mword_of_int (KernelSyms.timerinit + 8)) -∗
      gpr_file (vregs_den (demo_ρ sp0 ra0 s00 v1 v2) demo_regs1) -∗
      add_vec_int sp0 (-8) ↦₈ ra0 -∗
      add_vec_int sp0 (-16) ↦₈ s00 -∗
      WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intros HN Hpmp.
    iIntros "Hmm Hpmpc Hpc Hgpr #Ht Hw1 Hw2 Hcont".
    iDestruct (demo_block_instrs with "Ht") as "Hbi".
    (* assemble [vheap_own ρ demo_heap0] from the two stack words *)
    iAssert (vheap_own (demo_ρ sp0 ra0 s00 v1 v2) (vheap demo_st0))
      with "[Hw1 Hw2]" as "Hheap".
    { rewrite /vheap_own.
      change (vheap demo_st0) with demo_heap0. rewrite /demo_heap0.
      cbn [big_opL fst snd].
      rewrite demo_den_a1 demo_den_a2 !demo_den_x.
      cbn [demo_ρ]. iFrame "Hw1 Hw2". }
    iApply (wp_vc_block demo_prog E Φ demo_st0 demo_st1
              (demo_ρ sp0 ra0 s00 v1 v2) pmpcfg0 q HN Hpmp demo_run
              with "Hmm Hpmpc Hpc Hgpr Hbi Hheap").
    (* continuation: project the symbolic post-state back to points-to *)
    iIntros "Hmm Hpmpc Hpc Hgpr Hheap".
    iEval (rewrite /vheap_own;
           change (vheap demo_st1) with demo_heap1; rewrite /demo_heap1;
           cbn [big_opL fst snd];
           rewrite demo_den_a1 demo_den_a2 !demo_den_x;
           cbn [demo_ρ]) in "Hheap".
    iDestruct "Hheap" as "(Hw1 & Hw2 & _)".
    iApply ("Hcont" with "Hmm Hpmpc Hpc Hgpr Hw1 Hw2").
  Qed.

End VcGenDemo.
