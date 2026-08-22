(* WpSconfBtype.v -- the SIE-AGNOSTIC branch leaf layer (interrupt-sweep
   stage 5): [sconf]+[sie_cap] twins of WpSmodePtBtype.v's leaves over
   the agnostic funnel [wp_instr_s_sconf] -- since the per-node port,
   through that funnel's two BRANCH engines,
   [WpSconfEngine.wp_btype_{fall,taken}_s_sconf].

   Branches write NO general register, so [sie_cap] passes through
   UNTOUCHED (no retarget, no rd premises); a FALL-THROUGH leaf does not
   even open the bundle.  Spec cleanups made in this pass:
     - EVERY taken leaf hands the step's later out (the RVC originals
       did; the base-width ones absorbed it) -- a taken branch is a loop
       back edge, and a uniform ▷-continuation is what lets any loop
       close against the packaged leaf (a straight-line caller weakens
       with [iNext] for free);
     - EVERY taken leaf goes through the Zca-legalized jump helper, so
       only bit-0 alignment of the target is demanded (the non-zca
       originals' [bit_to_bool (access_vec_dec tgt 1) = false] premise
       is gone);
     - the config premises are gone as everywhere in the sweep.        *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExec.
Require Import InstrBytes WpGpr RegFile HartTp WpNext.
Require Import WpSconfEngine.
Require Import IntrDefs.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Import Defs.

(* THE EXEC-SIDE BRIDGES ARE GONE.  This file used to carry a [rvv] helper
   and fourteen [exec_execute_BTYPE_*_{fall,taken_zca}] lemmas, because a
   leaf's obligation was an [exec] fact about the whole instruction.  Under
   per-node stepping the obligation is an [swp] one, and it is discharged by
   [WpSconfEngine]'s two branch funnels ([wp_btype_fall_s_sconf] /
   [wp_btype_taken_s_sconf]) at a condition code the leaf names -- so the
   bridges had no consumer left and were deleted rather than carried. *)

Section WpSconfBtype.
  Context `{!riscvGS Σ}.
  Context `{!xv6G Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.
  Context {kt : ktier}.
  (* the value of [cpus[cid].proc]: a THREAD invariant, threaded through the
     bundle like the register map.  Implicit, so no call site changes. *)
  Context {p : mword 64}.

  (* ==================================================================== *)
  (* THE READ-SIDE SIDE CONDITION OF EVERY LEAF IN THIS SECTION, AND WHY IT *)
  (* IS A CLASS AND NOT A PREMISE.  Read this once; each leaf below carries *)
  (* a three-line pointer back here.                                       *)
  (*                                                                       *)
  (* A branch's only caller-varying premise is its COMPARISON, and that     *)
  (* comparison is taken on [rget m rs] -- a lookup in [tp_pin m]           *)
  (* (HartTp.v), whose value depends on the ambient hart at exactly one     *)
  (* register, rs = tp.  Today the funnel's sigma-callback is instantiated  *)
  (* at the entry hart, so the caller's comparison and the leaf's           *)
  (* obligation are spelled at the same hart.  Once that callback moves     *)
  (* inside [WpNext.wp_next] -- so that an instruction can execute on the   *)
  (* hart a trap returned to -- the obligation arrives at the REBOUND hart  *)
  (* while the caller stated its comparison at the ENTRY hart, and the two  *)
  (* agree only away from tp.  [IntrDefs.SrcOk] is that side condition.     *)
  (*                                                                       *)
  (* WHY A CLASS AND NOT A PREMISE: a branch writes NO register, so it has  *)
  (* no [rd_ok]/[ops_ok] premise slot whose meaning could be widened for    *)
  (* free -- its pure premises are exactly the [uint rs <> 0] gates and the *)
  (* comparison.  An ordinary premise would therefore change ARITY at every *)
  (* reference (~110 for the general two-register forms alone), each of     *)
  (* which would have to grow a positional [ltac:(...)] in the right place. *)
  (* An implicit instance argument shifts no positional argument, so the    *)
  (* whole family converts with ZERO call-site churn.  Nor can these use    *)
  (* [ops_ok]: its source conjuncts are guarded on [b = true], and a branch *)
  (* must decide the same way at [b = true] as at [b = false].              *)
  (*                                                                       *)
  (* MULTI-SOURCE LEAVES TAKE ONE CLASS ARGUMENT PER SOURCE.  They resolve  *)
  (* independently -- there is no combinatorial blow-up.                    *)
  (*                                                                       *)
  (* THE PREMISES STAY SPELLED [rget m rs].  Respelling them hart-free as   *)
  (* [m !!! Regidx rs] was MEASURED (on [WpSconfMem.wp_csdsp_s_sconf]) and  *)
  (* rejected: it breaks 99 consumer files, because call sites discharge    *)
  (* the comparison by rewriting with a [rget]-shaped fact they already     *)
  (* hold (WpUartgetc.v's [Hlk] is the pattern) and those rewrites then     *)
  (* have nothing to match.  So the class carries the side condition, the   *)
  (* spelling does not move, and the reconciliation happens INSIDE each     *)
  (* proof in one line via [IntrDefs.src_ok_rget_indep].                    *)
  (*                                                                       *)
  (* THAT LINE IS ALSO THE LEAF'S WIRING CHECK, so do not delete it as an   *)
  (* unused hypothesis: it names the register(s) the premise reads, so a    *)
  (* class accidentally attached to the wrong parameter fails to typecheck  *)
  (* in THIS file rather than shelving silently at a consumer's [Qed] (an   *)
  (* unresolved instance inside an [iApply] is SHELVED, not reported).      *)
  (* ==================================================================== *)

  (* ------------------------------------------------------------------- *)
  (* FALL-THROUGH leaves: [sconf]/[sie_cap] pass through untouched.       *)
  (* ------------------------------------------------------------------- *)
  Lemma wp_beq_fall_s_sconf
      (pc : mword 64) (imm : mword 13) (rs2 rs1 : mword 5) `{!SrcOk rs1} `{!SrcOk rs2}
      (m : regfile) (n : nat) (b : bool) :
    uint rs1 <> 0 -> uint rs2 <> 0 ->
    eq_vec (rget m rs1) (rget m rs2) = false ->
    sie_cap_gpr kt m n b p -∗
    pc_is pc -∗ instr pc false (BTYPE (imm, Regidx rs2, Regidx rs1, BEQ)) -∗
    wp_next b p (fun (CID : CpuId) =>
      sie_cap_gpr kt m n b p -∗
      pc_is(add_vec_int pc 4) -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    iIntros (Hrs1 Hrs2 Hcmp) "Hcg Hpc Hinstr Hcont".
    (* the class, consumed at [rs1 / rs2]: [Hcmp] lifted to its ALL-HARTS form,
       which is the one line the funnel change needs and this leaf's wiring
       check.  See the family note at the head of this section. *)
    assert (Hcmp_all : forall hh : CpuId, eq_vec (rget (CID := hh) m rs1) (rget (CID := hh) m rs2) = false)
      by (intros hh; rewrite (src_ok_rget_indep m rs1 hh CID); rewrite (src_ok_rget_indep m rs2 hh CID); exact Hcmp).
    iApply (wp_btype_fall_s_sconf pc false (imm) rs2 rs1
              (BTYPE (imm, Regidx rs2, Regidx rs1, BEQ))
              eq_vec m n b eq_refl
              with "[] Hcg Hpc Hinstr [Hcont]").
    - iIntros (hh) "Hf". iFrame "Hf". iPureIntro. exact (Hcmp_all hh).
    - iNext. iExact "Hcont".
  Qed.

  Lemma wp_bne_fall_s_sconf
      (pc : mword 64) (imm : mword 13) (rs2 rs1 : mword 5) `{!SrcOk rs1} `{!SrcOk rs2}
      (m : regfile) (n : nat) (b : bool) :
    uint rs1 <> 0 -> uint rs2 <> 0 ->
    neq_vec (rget m rs1) (rget m rs2) = false ->
    sie_cap_gpr kt m n b p -∗
    pc_is pc -∗ instr pc false (BTYPE (imm, Regidx rs2, Regidx rs1, BNE)) -∗
    wp_next b p (fun (CID : CpuId) =>
      sie_cap_gpr kt m n b p -∗
      pc_is(add_vec_int pc 4) -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    iIntros (Hrs1 Hrs2 Hcmp) "Hcg Hpc Hinstr Hcont".
    (* the class, consumed at [rs1 / rs2]: [Hcmp] lifted to its ALL-HARTS form,
       which is the one line the funnel change needs and this leaf's wiring
       check.  See the family note at the head of this section. *)
    assert (Hcmp_all : forall hh : CpuId, neq_vec (rget (CID := hh) m rs1) (rget (CID := hh) m rs2) = false)
      by (intros hh; rewrite (src_ok_rget_indep m rs1 hh CID); rewrite (src_ok_rget_indep m rs2 hh CID); exact Hcmp).
    iApply (wp_btype_fall_s_sconf pc false (imm) rs2 rs1
              (BTYPE (imm, Regidx rs2, Regidx rs1, BNE))
              neq_vec m n b eq_refl
              with "[] Hcg Hpc Hinstr [Hcont]").
    - iIntros (hh) "Hf". iFrame "Hf". iPureIntro. exact (Hcmp_all hh).
    - iNext. iExact "Hcont".
  Qed.

  Lemma wp_bltu_fall_s_sconf
      (pc : mword 64) (imm : mword 13) (rs2 rs1 : mword 5) `{!SrcOk rs1} `{!SrcOk rs2}
      (m : regfile) (n : nat) (b : bool) :
    uint rs1 <> 0 -> uint rs2 <> 0 ->
    zopz0zI_u (rget m rs1) (rget m rs2) = false ->
    sie_cap_gpr kt m n b p -∗
    pc_is pc -∗ instr pc false (BTYPE (imm, Regidx rs2, Regidx rs1, BLTU)) -∗
    wp_next b p (fun (CID : CpuId) =>
      sie_cap_gpr kt m n b p -∗
      pc_is(add_vec_int pc 4) -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    iIntros (Hrs1 Hrs2 Hcmp) "Hcg Hpc Hinstr Hcont".
    (* the class, consumed at [rs1 / rs2]: [Hcmp] lifted to its ALL-HARTS form,
       which is the one line the funnel change needs and this leaf's wiring
       check.  See the family note at the head of this section. *)
    assert (Hcmp_all : forall hh : CpuId, zopz0zI_u (rget (CID := hh) m rs1) (rget (CID := hh) m rs2) = false)
      by (intros hh; rewrite (src_ok_rget_indep m rs1 hh CID); rewrite (src_ok_rget_indep m rs2 hh CID); exact Hcmp).
    iApply (wp_btype_fall_s_sconf pc false (imm) rs2 rs1
              (BTYPE (imm, Regidx rs2, Regidx rs1, BLTU))
              zopz0zI_u m n b eq_refl
              with "[] Hcg Hpc Hinstr [Hcont]").
    - iIntros (hh) "Hf". iFrame "Hf". iPureIntro. exact (Hcmp_all hh).
    - iNext. iExact "Hcont".
  Qed.

  (* BLT-fall, the SIGNED twin of [wp_bltu_fall_s_sconf] at two general
     registers (free_desc's `i >= NUM` bound check).  The x0-specialized
     [wp_blt_x0_fall_s_sconf] below is the same leaf against zero. *)
  Lemma wp_blt_fall_s_sconf
      (pc : mword 64) (imm : mword 13) (rs2 rs1 : mword 5) `{!SrcOk rs1} `{!SrcOk rs2}
      (m : regfile) (n : nat) (b : bool) :
    uint rs1 <> 0 -> uint rs2 <> 0 ->
    zopz0zI_s (rget m rs1) (rget m rs2) = false ->
    sie_cap_gpr kt m n b p -∗
    pc_is pc -∗ instr pc false (BTYPE (imm, Regidx rs2, Regidx rs1, BLT)) -∗
    wp_next b p (fun (CID : CpuId) =>
      sie_cap_gpr kt m n b p -∗
      pc_is (add_vec_int pc 4) -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    iIntros (Hrs1 Hrs2 Hcmp) "Hcg Hpc Hinstr Hcont".
    (* the class, consumed at [rs1 / rs2]: [Hcmp] lifted to its ALL-HARTS form,
       which is the one line the funnel change needs and this leaf's wiring
       check.  See the family note at the head of this section. *)
    assert (Hcmp_all : forall hh : CpuId, zopz0zI_s (rget (CID := hh) m rs1) (rget (CID := hh) m rs2) = false)
      by (intros hh; rewrite (src_ok_rget_indep m rs1 hh CID); rewrite (src_ok_rget_indep m rs2 hh CID); exact Hcmp).
    iApply (wp_btype_fall_s_sconf pc false (imm) rs2 rs1
              (BTYPE (imm, Regidx rs2, Regidx rs1, BLT))
              zopz0zI_s m n b eq_refl
              with "[] Hcg Hpc Hinstr [Hcont]").
    - iIntros (hh) "Hf". iFrame "Hf". iPureIntro. exact (Hcmp_all hh).
    - iNext. iExact "Hcont".
  Qed.

  (* ...and the TAKEN arm of the same two-register BLT (a copy loop's back
     edge).  The general twin of [wp_blt_x0_taken_s_sconf] below. *)
  Lemma wp_blt_taken_s_sconf
      (pc : mword 64) (imm : mword 13) (rs2 rs1 : mword 5) `{!SrcOk rs1} `{!SrcOk rs2}
      (m : regfile) (n : nat) (b : bool) :
    uint rs1 <> 0 -> uint rs2 <> 0 ->
    zopz0zI_s (rget m rs1) (rget m rs2) = true ->
    eq_vec (access_vec_dec (add_vec pc (sign_extend' 64 imm)) 0) ('b"0") = true ->
    sie_cap_gpr kt m n b p -∗
    pc_is pc -∗ instr pc false (BTYPE (imm, Regidx rs2, Regidx rs1, BLT)) -∗
    ▷ wp_next b p (fun (CID : CpuId) =>
      sie_cap_gpr kt m n b p -∗
      pc_is (add_vec pc (sign_extend' 64 imm)) -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    iIntros (Hrs1 Hrs2 Hcmp Hal0) "Hcg Hpc Hinstr Hcont".
    (* the class, consumed at [rs1 / rs2]: [Hcmp] lifted to its ALL-HARTS form,
       which is the one line the funnel change needs and this leaf's wiring
       check.  See the family note at the head of this section. *)
    assert (Hcmp_all : forall hh : CpuId, zopz0zI_s (rget (CID := hh) m rs1) (rget (CID := hh) m rs2) = true)
      by (intros hh; rewrite (src_ok_rget_indep m rs1 hh CID); rewrite (src_ok_rget_indep m rs2 hh CID); exact Hcmp).
    iApply (wp_btype_taken_s_sconf pc false (imm) rs2 rs1
              (BTYPE (imm, Regidx rs2, Regidx rs1, BLT))
              zopz0zI_s m n b eq_refl
              Hal0
              with "[] Hcg Hpc Hinstr [Hcont]").
    - iIntros (hh) "Hf". iFrame "Hf". iPureIntro. exact (Hcmp_all hh).
    - iExact "Hcont".
  Qed.

  (* BGEU-fall (the freerange loop exit: no more full pages fit). *)
  Lemma wp_bgeu_fall_s_sconf
      (pc : mword 64) (imm : mword 13) (rs2 rs1 : mword 5) `{!SrcOk rs1} `{!SrcOk rs2}
      (m : regfile) (n : nat) (b : bool) :
    uint rs1 <> 0 -> uint rs2 <> 0 ->
    zopz0zKzJ_u (rget m rs1) (rget m rs2) = false ->
    sie_cap_gpr kt m n b p -∗
    pc_is pc -∗ instr pc false (BTYPE (imm, Regidx rs2, Regidx rs1, BGEU)) -∗
    wp_next b p (fun (CID : CpuId) =>
      sie_cap_gpr kt m n b p -∗
      pc_is(add_vec_int pc 4) -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    iIntros (Hrs1 Hrs2 Hcmp) "Hcg Hpc Hinstr Hcont".
    (* the class, consumed at [rs1 / rs2]: [Hcmp] lifted to its ALL-HARTS form,
       which is the one line the funnel change needs and this leaf's wiring
       check.  See the family note at the head of this section. *)
    assert (Hcmp_all : forall hh : CpuId, zopz0zKzJ_u (rget (CID := hh) m rs1) (rget (CID := hh) m rs2) = false)
      by (intros hh; rewrite (src_ok_rget_indep m rs1 hh CID); rewrite (src_ok_rget_indep m rs2 hh CID); exact Hcmp).
    iApply (wp_btype_fall_s_sconf pc false (imm) rs2 rs1
              (BTYPE (imm, Regidx rs2, Regidx rs1, BGEU))
              zopz0zKzJ_u m n b eq_refl
              with "[] Hcg Hpc Hinstr [Hcont]").
    - iIntros (hh) "Hf". iFrame "Hf". iPureIntro. exact (Hcmp_all hh).
    - iNext. iExact "Hcont".
  Qed.

  (* BLTU-taken (the freerange empty-page-list path skips the loop to the
     epilogue). *)
  Lemma wp_bltu_taken_s_sconf
      (pc : mword 64) (imm : mword 13) (rs2 rs1 : mword 5) `{!SrcOk rs1} `{!SrcOk rs2}
      (m : regfile) (n : nat) (b : bool) :
    uint rs1 <> 0 -> uint rs2 <> 0 ->
    zopz0zI_u (rget m rs1) (rget m rs2) = true ->
    eq_vec (access_vec_dec (add_vec pc (sign_extend' 64 imm)) 0) ('b"0") = true ->
    sie_cap_gpr kt m n b p -∗
    pc_is pc -∗ instr pc false (BTYPE (imm, Regidx rs2, Regidx rs1, BLTU)) -∗
    ▷ wp_next b p (fun (CID : CpuId) =>
      sie_cap_gpr kt m n b p -∗
      pc_is(add_vec pc (sign_extend' 64 imm)) -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    iIntros (Hrs1 Hrs2 Hcmp Hal0) "Hcg Hpc Hinstr Hcont".
    (* the class, consumed at [rs1 / rs2]: [Hcmp] lifted to its ALL-HARTS form,
       which is the one line the funnel change needs and this leaf's wiring
       check.  See the family note at the head of this section. *)
    assert (Hcmp_all : forall hh : CpuId, zopz0zI_u (rget (CID := hh) m rs1) (rget (CID := hh) m rs2) = true)
      by (intros hh; rewrite (src_ok_rget_indep m rs1 hh CID); rewrite (src_ok_rget_indep m rs2 hh CID); exact Hcmp).
    iApply (wp_btype_taken_s_sconf pc false (imm) rs2 rs1
              (BTYPE (imm, Regidx rs2, Regidx rs1, BLTU))
              zopz0zI_u m n b eq_refl
              Hal0
              with "[] Hcg Hpc Hinstr [Hcont]").
    - iIntros (hh) "Hf". iFrame "Hf". iPureIntro. exact (Hcmp_all hh).
    - iExact "Hcont".
  Qed.

  (* BGEU-taken (the freerange loop back-edge: another full page still fits). *)
  Lemma wp_bgeu_taken_s_sconf
      (pc : mword 64) (imm : mword 13) (rs2 rs1 : mword 5) `{!SrcOk rs1} `{!SrcOk rs2}
      (m : regfile) (n : nat) (b : bool) :
    uint rs1 <> 0 -> uint rs2 <> 0 ->
    zopz0zKzJ_u (rget m rs1) (rget m rs2) = true ->
    eq_vec (access_vec_dec (add_vec pc (sign_extend' 64 imm)) 0) ('b"0") = true ->
    sie_cap_gpr kt m n b p -∗
    pc_is pc -∗ instr pc false (BTYPE (imm, Regidx rs2, Regidx rs1, BGEU)) -∗
    ▷ wp_next b p (fun (CID : CpuId) =>
      sie_cap_gpr kt m n b p -∗
      pc_is(add_vec pc (sign_extend' 64 imm)) -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    iIntros (Hrs1 Hrs2 Hcmp Hal0) "Hcg Hpc Hinstr Hcont".
    (* the class, consumed at [rs1 / rs2]: [Hcmp] lifted to its ALL-HARTS form,
       which is the one line the funnel change needs and this leaf's wiring
       check.  See the family note at the head of this section. *)
    assert (Hcmp_all : forall hh : CpuId, zopz0zKzJ_u (rget (CID := hh) m rs1) (rget (CID := hh) m rs2) = true)
      by (intros hh; rewrite (src_ok_rget_indep m rs1 hh CID); rewrite (src_ok_rget_indep m rs2 hh CID); exact Hcmp).
    iApply (wp_btype_taken_s_sconf pc false (imm) rs2 rs1
              (BTYPE (imm, Regidx rs2, Regidx rs1, BGEU))
              zopz0zKzJ_u m n b eq_refl
              Hal0
              with "[] Hcg Hpc Hinstr [Hcont]").
    - iIntros (hh) "Hf". iFrame "Hf". iPureIntro. exact (Hcmp_all hh).
    - iExact "Hcont".
  Qed.

  (* BGE-fall / BGE-taken over TWO general registers -- the SIGNED twin of
     the [bgeu] pair above (pipewrite's / piperead's [bge s2,s4] loop guard:
     the copy is done when the signed index reaches the signed count).  The
     [_x0_] forms below are the [rs1 = x0] specializations gcc emits for
     [blez]; neither covers a general rs1. *)
  Lemma wp_bge_fall_s_sconf
      (pc : mword 64) (imm : mword 13) (rs2 rs1 : mword 5) `{!SrcOk rs1} `{!SrcOk rs2}
      (m : regfile) (n : nat) (b : bool) :
    uint rs1 <> 0 -> uint rs2 <> 0 ->
    zopz0zKzJ_s (rget m rs1) (rget m rs2) = false ->
    sie_cap_gpr kt m n b p -∗
    pc_is pc -∗ instr pc false (BTYPE (imm, Regidx rs2, Regidx rs1, BGE)) -∗
    wp_next b p (fun (CID : CpuId) =>
      sie_cap_gpr kt m n b p -∗
      pc_is(add_vec_int pc 4) -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    iIntros (Hrs1 Hrs2 Hcmp) "Hcg Hpc Hinstr Hcont".
    (* the class, consumed at [rs1 / rs2]: [Hcmp] lifted to its ALL-HARTS form,
       which is the one line the funnel change needs and this leaf's wiring
       check.  See the family note at the head of this section. *)
    assert (Hcmp_all : forall hh : CpuId, zopz0zKzJ_s (rget (CID := hh) m rs1) (rget (CID := hh) m rs2) = false)
      by (intros hh; rewrite (src_ok_rget_indep m rs1 hh CID); rewrite (src_ok_rget_indep m rs2 hh CID); exact Hcmp).
    iApply (wp_btype_fall_s_sconf pc false (imm) rs2 rs1
              (BTYPE (imm, Regidx rs2, Regidx rs1, BGE))
              zopz0zKzJ_s m n b eq_refl
              with "[] Hcg Hpc Hinstr [Hcont]").
    - iIntros (hh) "Hf". iFrame "Hf". iPureIntro. exact (Hcmp_all hh).
    - iNext. iExact "Hcont".
  Qed.

  Lemma wp_bge_taken_s_sconf
      (pc : mword 64) (imm : mword 13) (rs2 rs1 : mword 5) `{!SrcOk rs1} `{!SrcOk rs2}
      (m : regfile) (n : nat) (b : bool) :
    uint rs1 <> 0 -> uint rs2 <> 0 ->
    zopz0zKzJ_s (rget m rs1) (rget m rs2) = true ->
    eq_vec (access_vec_dec (add_vec pc (sign_extend' 64 imm)) 0) ('b"0") = true ->
    sie_cap_gpr kt m n b p -∗
    pc_is pc -∗ instr pc false (BTYPE (imm, Regidx rs2, Regidx rs1, BGE)) -∗
    ▷ wp_next b p (fun (CID : CpuId) =>
      sie_cap_gpr kt m n b p -∗
      pc_is(add_vec pc (sign_extend' 64 imm)) -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    iIntros (Hrs1 Hrs2 Hcmp Hal0) "Hcg Hpc Hinstr Hcont".
    (* the class, consumed at [rs1 / rs2]: [Hcmp] lifted to its ALL-HARTS form,
       which is the one line the funnel change needs and this leaf's wiring
       check.  See the family note at the head of this section. *)
    assert (Hcmp_all : forall hh : CpuId, zopz0zKzJ_s (rget (CID := hh) m rs1) (rget (CID := hh) m rs2) = true)
      by (intros hh; rewrite (src_ok_rget_indep m rs1 hh CID); rewrite (src_ok_rget_indep m rs2 hh CID); exact Hcmp).
    iApply (wp_btype_taken_s_sconf pc false (imm) rs2 rs1
              (BTYPE (imm, Regidx rs2, Regidx rs1, BGE))
              zopz0zKzJ_s m n b eq_refl
              Hal0
              with "[] Hcg Hpc Hinstr [Hcont]").
    - iIntros (hh) "Hf". iFrame "Hf". iPureIntro. exact (Hcmp_all hh).
    - iExact "Hcont".
  Qed.

  Lemma wp_bge_x0_fall_s_sconf
      (pc : mword 64) (imm : mword 13) (rs2 : mword 5) `{!SrcOk rs2}
      (m : regfile) (n : nat) (b : bool) :
    uint rs2 <> 0 ->
    zopz0zKzJ_s zero_reg (rget m rs2) = false ->
    sie_cap_gpr kt m n b p -∗
    pc_is pc -∗ instr pc false (BTYPE (imm, Regidx rs2, Regidx (mword_of_int 0), BGE)) -∗
    wp_next b p (fun (CID : CpuId) =>
      sie_cap_gpr kt m n b p -∗
      pc_is(add_vec_int pc 4) -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    iIntros (Hrs2 Hcmp) "Hcg Hpc Hinstr Hcont".
    (* the class, consumed at [rs2]: [Hcmp] lifted to its ALL-HARTS form,
       which is the one line the funnel change needs and this leaf's wiring
       check.  See the family note at the head of this section. *)
    assert (Hcmp_all : forall hh : CpuId, zopz0zKzJ_s zero_reg (rget (CID := hh) m rs2) = false)
      by (intros hh; rewrite (src_ok_rget_indep m rs2 hh CID); exact Hcmp).
    iApply (wp_btype_fall_s_sconf pc false (imm) rs2 (mword_of_int 0 : mword 5)
              (BTYPE (imm, Regidx rs2, Regidx (mword_of_int 0), BGE))
              zopz0zKzJ_s m n b eq_refl
              with "[] Hcg Hpc Hinstr [Hcont]").
    - iIntros (hh) "Hf".
      iDestruct (gpr_file_x0 (CID := hh) (tp_pin (CID := hh) m) (mword_of_int 0 : mword 5)
                   ltac:(vm_compute; reflexivity) with "Hf") as "[%Hx0 Hf]".
      iFrame "Hf". iPureIntro. unfold rget. rewrite Hx0. exact (Hcmp_all hh).
    - iNext. iExact "Hcont".
  Qed.

  (* BLT against x0 -- a [bltz rs1] error test (the -1 return of
     mappages / kvmmap).  x0 is not in the register file, so this is the
     x0-specialized twin of [wp_bltu_fall_s_sconf], as [wp_bge_x0_fall_s_sconf]
     is of [wp_bgeu_fall_s_sconf]. *)
  Lemma wp_blt_x0_fall_s_sconf
      (pc : mword 64) (imm : mword 13) (rs1 : mword 5) `{!SrcOk rs1}
      (m : regfile) (n : nat) (b : bool) :
    uint rs1 <> 0 ->
    zopz0zI_s (rget m rs1) zero_reg = false ->
    sie_cap_gpr kt m n b p -∗
    pc_is pc -∗ instr pc false (BTYPE (imm, Regidx (mword_of_int 0), Regidx rs1, BLT)) -∗
    wp_next b p (fun (CID : CpuId) =>
      sie_cap_gpr kt m n b p -∗
      pc_is(add_vec_int pc 4) -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    iIntros (Hrs1 Hcmp) "Hcg Hpc Hinstr Hcont".
    (* the class, consumed at [rs1]: [Hcmp] lifted to its ALL-HARTS form,
       which is the one line the funnel change needs and this leaf's wiring
       check.  See the family note at the head of this section. *)
    assert (Hcmp_all : forall hh : CpuId, zopz0zI_s (rget (CID := hh) m rs1) zero_reg = false)
      by (intros hh; rewrite (src_ok_rget_indep m rs1 hh CID); exact Hcmp).
    iApply (wp_btype_fall_s_sconf pc false (imm) (mword_of_int 0 : mword 5) rs1
              (BTYPE (imm, Regidx (mword_of_int 0), Regidx rs1, BLT))
              zopz0zI_s m n b eq_refl
              with "[] Hcg Hpc Hinstr [Hcont]").
    - iIntros (hh) "Hf".
      iDestruct (gpr_file_x0 (CID := hh) (tp_pin (CID := hh) m) (mword_of_int 0 : mword 5)
                   ltac:(vm_compute; reflexivity) with "Hf") as "[%Hx0 Hf]".
      iFrame "Hf". iPureIntro. unfold rget. rewrite Hx0. exact (Hcmp_all hh).
    - iNext. iExact "Hcont".
  Qed.

  (* ...and its TAKEN twin: the [bltz rs1] error test that DID fire (the
     [argfd(...) < 0] arm of a syscall).  x0 is not in the register file, so
     this is the x0-specialized twin of [wp_bltu_taken_s_sconf]. *)
  Lemma wp_blt_x0_taken_s_sconf
      (pc : mword 64) (imm : mword 13) (rs1 : mword 5) `{!SrcOk rs1}
      (m : regfile) (n : nat) (b : bool) :
    uint rs1 <> 0 ->
    zopz0zI_s (rget m rs1) zero_reg = true ->
    eq_vec (access_vec_dec (add_vec pc (sign_extend' 64 imm)) 0) ('b"0") = true ->
    sie_cap_gpr kt m n b p -∗
    pc_is pc -∗ instr pc false (BTYPE (imm, Regidx (mword_of_int 0), Regidx rs1, BLT)) -∗
    ▷ wp_next b p (fun (CID : CpuId) =>
      sie_cap_gpr kt m n b p -∗
      pc_is (add_vec pc (sign_extend' 64 imm)) -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    iIntros (Hrs1 Hcmp Hal0) "Hcg Hpc Hinstr Hcont".
    (* the class, consumed at [rs1]: [Hcmp] lifted to its ALL-HARTS form,
       which is the one line the funnel change needs and this leaf's wiring
       check.  See the family note at the head of this section. *)
    assert (Hcmp_all : forall hh : CpuId, zopz0zI_s (rget (CID := hh) m rs1) zero_reg = true)
      by (intros hh; rewrite (src_ok_rget_indep m rs1 hh CID); exact Hcmp).
    iApply (wp_btype_taken_s_sconf pc false (imm) (mword_of_int 0 : mword 5) rs1
              (BTYPE (imm, Regidx (mword_of_int 0), Regidx rs1, BLT))
              zopz0zI_s m n b eq_refl
              Hal0
              with "[] Hcg Hpc Hinstr [Hcont]").
    - iIntros (hh) "Hf".
      iDestruct (gpr_file_x0 (CID := hh) (tp_pin (CID := hh) m) (mword_of_int 0 : mword 5)
                   ltac:(vm_compute; reflexivity) with "Hf") as "[%Hx0 Hf]".
      iFrame "Hf". iPureIntro. unfold rget. rewrite Hx0. exact (Hcmp_all hh).
    - iExact "Hcont".
  Qed.

  (* ------------------------------------------------------------------- *)
  (* BLT against x0 in the rs1 slot -- a [bgtz rs2] test.  The MIRROR of   *)
  (* the two [wp_blt_x0_*] lemmas above, which put x0 in rs2 and so read   *)
  (* [bltz]; the operand order is the whole difference and neither can     *)
  (* serve for the other, so both pairs exist.                             *)
  (* ------------------------------------------------------------------- *)
  Lemma wp_bgtz_fall_s_sconf
      (pc : mword 64) (imm : mword 13) (rs2 : mword 5) `{!SrcOk rs2}
      (m : regfile) (n : nat) (b : bool) :
    uint rs2 <> 0 ->
    zopz0zI_s zero_reg (rget m rs2) = false ->
    sie_cap_gpr kt m n b p -∗
    pc_is pc -∗ instr pc false (BTYPE (imm, Regidx rs2, Regidx (mword_of_int 0), BLT)) -∗
    wp_next b p (fun (CID : CpuId) =>
      sie_cap_gpr kt m n b p -∗
      pc_is (add_vec_int pc 4) -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    iIntros (Hrs2 Hcmp) "Hcg Hpc Hinstr Hcont".
    (* the class, consumed at [rs2]: [Hcmp] lifted to its ALL-HARTS form,
       which is the one line the funnel change needs and this leaf's wiring
       check.  See the family note at the head of this section. *)
    assert (Hcmp_all : forall hh : CpuId, zopz0zI_s zero_reg (rget (CID := hh) m rs2) = false)
      by (intros hh; rewrite (src_ok_rget_indep m rs2 hh CID); exact Hcmp).
    iApply (wp_btype_fall_s_sconf pc false (imm) rs2 (mword_of_int 0 : mword 5)
              (BTYPE (imm, Regidx rs2, Regidx (mword_of_int 0), BLT))
              zopz0zI_s m n b eq_refl
              with "[] Hcg Hpc Hinstr [Hcont]").
    - iIntros (hh) "Hf".
      iDestruct (gpr_file_x0 (CID := hh) (tp_pin (CID := hh) m) (mword_of_int 0 : mword 5)
                   ltac:(vm_compute; reflexivity) with "Hf") as "[%Hx0 Hf]".
      iFrame "Hf". iPureIntro. unfold rget. rewrite Hx0. exact (Hcmp_all hh).
    - iNext. iExact "Hcont".
  Qed.

  Lemma wp_bgtz_taken_s_sconf
      (pc : mword 64) (imm : mword 13) (rs2 : mword 5) `{!SrcOk rs2}
      (m : regfile) (n : nat) (b : bool) :
    uint rs2 <> 0 ->
    zopz0zI_s zero_reg (rget m rs2) = true ->
    eq_vec (access_vec_dec (add_vec pc (sign_extend' 64 imm)) 0) ('b"0") = true ->
    sie_cap_gpr kt m n b p -∗
    pc_is pc -∗ instr pc false (BTYPE (imm, Regidx rs2, Regidx (mword_of_int 0), BLT)) -∗
    ▷ wp_next b p (fun (CID : CpuId) =>
      sie_cap_gpr kt m n b p -∗
      pc_is (add_vec pc (sign_extend' 64 imm)) -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    iIntros (Hrs2 Hcmp Hal0) "Hcg Hpc Hinstr Hcont".
    (* the class, consumed at [rs2]: [Hcmp] lifted to its ALL-HARTS form,
       which is the one line the funnel change needs and this leaf's wiring
       check.  See the family note at the head of this section. *)
    assert (Hcmp_all : forall hh : CpuId, zopz0zI_s zero_reg (rget (CID := hh) m rs2) = true)
      by (intros hh; rewrite (src_ok_rget_indep m rs2 hh CID); exact Hcmp).
    iApply (wp_btype_taken_s_sconf pc false (imm) rs2 (mword_of_int 0 : mword 5)
              (BTYPE (imm, Regidx rs2, Regidx (mword_of_int 0), BLT))
              zopz0zI_s m n b eq_refl
              Hal0
              with "[] Hcg Hpc Hinstr [Hcont]").
    - iIntros (hh) "Hf".
      iDestruct (gpr_file_x0 (CID := hh) (tp_pin (CID := hh) m) (mword_of_int 0 : mword 5)
                   ltac:(vm_compute; reflexivity) with "Hf") as "[%Hx0 Hf]".
      iFrame "Hf". iPureIntro. unfold rget. rewrite Hx0. exact (Hcmp_all hh).
    - iExact "Hcont".
  Qed.

  (* ------------------------------------------------------------------- *)
  (* BGE against x0 in the rs2 slot -- the [bgez rs1] "did it succeed?"    *)
  (* test (sys_pipe's [copyout(...) >= 0]).  The MIRROR of the two         *)
  (* [wp_bge_x0_*] lemmas above, which put x0 in rs1 and so read [blez];   *)
  (* the operand order is the whole difference and neither can serve for   *)
  (* the other, so both pairs exist.                                       *)
  (* ------------------------------------------------------------------- *)
  Lemma wp_bgez_fall_s_sconf
      (pc : mword 64) (imm : mword 13) (rs1 : mword 5) `{!SrcOk rs1}
      (m : regfile) (n : nat) (b : bool) :
    uint rs1 <> 0 ->
    zopz0zKzJ_s (rget m rs1) zero_reg = false ->
    sie_cap_gpr kt m n b p -∗
    pc_is pc -∗ instr pc false (BTYPE (imm, Regidx (mword_of_int 0), Regidx rs1, BGE)) -∗
    wp_next b p (fun (CID : CpuId) =>
      sie_cap_gpr kt m n b p -∗
      pc_is(add_vec_int pc 4) -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    iIntros (Hrs1 Hcmp) "Hcg Hpc Hinstr Hcont".
    (* the class, consumed at [rs1]: [Hcmp] lifted to its ALL-HARTS form,
       which is the one line the funnel change needs and this leaf's wiring
       check.  See the family note at the head of this section. *)
    assert (Hcmp_all : forall hh : CpuId, zopz0zKzJ_s (rget (CID := hh) m rs1) zero_reg = false)
      by (intros hh; rewrite (src_ok_rget_indep m rs1 hh CID); exact Hcmp).
    iApply (wp_btype_fall_s_sconf pc false (imm) (mword_of_int 0 : mword 5) rs1
              (BTYPE (imm, Regidx (mword_of_int 0), Regidx rs1, BGE))
              zopz0zKzJ_s m n b eq_refl
              with "[] Hcg Hpc Hinstr [Hcont]").
    - iIntros (hh) "Hf".
      iDestruct (gpr_file_x0 (CID := hh) (tp_pin (CID := hh) m) (mword_of_int 0 : mword 5)
                   ltac:(vm_compute; reflexivity) with "Hf") as "[%Hx0 Hf]".
      iFrame "Hf". iPureIntro. unfold rget. rewrite Hx0. exact (Hcmp_all hh).
    - iNext. iExact "Hcont".
  Qed.

  Lemma wp_bgez_taken_s_sconf
      (pc : mword 64) (imm : mword 13) (rs1 : mword 5) `{!SrcOk rs1}
      (m : regfile) (n : nat) (b : bool) :
    uint rs1 <> 0 ->
    zopz0zKzJ_s (rget m rs1) zero_reg = true ->
    eq_vec (access_vec_dec (add_vec pc (sign_extend' 64 imm)) 0) ('b"0") = true ->
    sie_cap_gpr kt m n b p -∗
    pc_is pc -∗ instr pc false (BTYPE (imm, Regidx (mword_of_int 0), Regidx rs1, BGE)) -∗
    ▷ wp_next b p (fun (CID : CpuId) =>
      sie_cap_gpr kt m n b p -∗
      pc_is (add_vec pc (sign_extend' 64 imm)) -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    iIntros (Hrs1 Hcmp Hal0) "Hcg Hpc Hinstr Hcont".
    (* the class, consumed at [rs1]: [Hcmp] lifted to its ALL-HARTS form,
       which is the one line the funnel change needs and this leaf's wiring
       check.  See the family note at the head of this section. *)
    assert (Hcmp_all : forall hh : CpuId, zopz0zKzJ_s (rget (CID := hh) m rs1) zero_reg = true)
      by (intros hh; rewrite (src_ok_rget_indep m rs1 hh CID); exact Hcmp).
    iApply (wp_btype_taken_s_sconf pc false (imm) (mword_of_int 0 : mword 5) rs1
              (BTYPE (imm, Regidx (mword_of_int 0), Regidx rs1, BGE))
              zopz0zKzJ_s m n b eq_refl
              Hal0
              with "[] Hcg Hpc Hinstr [Hcont]").
    - iIntros (hh) "Hf".
      iDestruct (gpr_file_x0 (CID := hh) (tp_pin (CID := hh) m) (mword_of_int 0 : mword 5)
                   ltac:(vm_compute; reflexivity) with "Hf") as "[%Hx0 Hf]".
      iFrame "Hf". iPureIntro. unfold rget. rewrite Hx0. exact (Hcmp_all hh).
    - iExact "Hcont".
  Qed.

  (* BGE against x0 in the rs1 slot -- a [blez rs2] loop-guard (printint's
     [while (--i >= 0)]).  The taken twin of [wp_bge_x0_fall_s_sconf]. *)
  Lemma wp_bge_x0_taken_s_sconf
      (pc : mword 64) (imm : mword 13) (rs2 : mword 5) `{!SrcOk rs2}
      (m : regfile) (n : nat) (b : bool) :
    uint rs2 <> 0 ->
    zopz0zKzJ_s zero_reg (rget m rs2) = true ->
    eq_vec (access_vec_dec (add_vec pc (sign_extend' 64 imm)) 0) ('b"0") = true ->
    sie_cap_gpr kt m n b p -∗
    pc_is pc -∗ instr pc false (BTYPE (imm, Regidx rs2, Regidx (mword_of_int 0), BGE)) -∗
    ▷ wp_next b p (fun (CID : CpuId) =>
      sie_cap_gpr kt m n b p -∗
      pc_is (add_vec pc (sign_extend' 64 imm)) -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    iIntros (Hrs2 Hcmp Hal0) "Hcg Hpc Hinstr Hcont".
    (* the class, consumed at [rs2]: [Hcmp] lifted to its ALL-HARTS form,
       which is the one line the funnel change needs and this leaf's wiring
       check.  See the family note at the head of this section. *)
    assert (Hcmp_all : forall hh : CpuId, zopz0zKzJ_s zero_reg (rget (CID := hh) m rs2) = true)
      by (intros hh; rewrite (src_ok_rget_indep m rs2 hh CID); exact Hcmp).
    iApply (wp_btype_taken_s_sconf pc false (imm) rs2 (mword_of_int 0 : mword 5)
              (BTYPE (imm, Regidx rs2, Regidx (mword_of_int 0), BGE))
              zopz0zKzJ_s m n b eq_refl
              Hal0
              with "[] Hcg Hpc Hinstr [Hcont]").
    - iIntros (hh) "Hf".
      iDestruct (gpr_file_x0 (CID := hh) (tp_pin (CID := hh) m) (mword_of_int 0 : mword 5)
                   ltac:(vm_compute; reflexivity) with "Hf") as "[%Hx0 Hf]".
      iFrame "Hf". iPureIntro. unfold rget. rewrite Hx0. exact (Hcmp_all hh).
    - iExact "Hcont".
  Qed.

  (* THE SIDE CONDITION ARRIVES BY INSTANCE RESOLUTION, NOT AS A PREMISE --
     see [IntrDefs.SrcOk].  A branch leaf's only caller-varying premise is the
     COMPARISON below, and that comparison is taken on [rget m rd1], a lookup
     in [tp_pin m]: its value depends on the ambient hart at exactly one
     register, rd1 = tp.  When the funnel's σ-callback moves inside [wp_next]
     the branch's obligation is discharged at the hart the trap returned to
     while the caller stated its comparison at the entry hart.  A branch writes
     no register, so there is no [rd_ok]/[ops_ok] slot to widen here and an
     ordinary premise would shift the three positional arguments below at ~110
     references.  The implicit [`{!SrcOk rd1}] costs no slot.

     THE PREMISE STAYS SPELLED [rget m rd1], at the entry hart.  Respelling it
     hart-free as [m !!! Regidx rd1] was MEASURED and rejected: call sites
     discharge it by rewriting with a [rget]-shaped fact they already hold
     (WpUartgetc.v's [Hlk] is the pattern), and the same respelling on
     [WpSconfMem.wp_csdsp_s_sconf] broke 99 consumer files for the same reason.
     So the class carries the side condition and the spelling does not move;
     what the class buys is the ALL-HARTS form of the premise, derived once in
     the proof below. *)
  Lemma wp_cbeqz_fall_s_sconf
      (pc : mword 64) (imm8 : mword 8) (rs : cregidx) (rd1 : mword 5)
      `{!SrcOk rd1}
      (m : regfile) (n : nat) (b : bool) :
    creg2reg_idx rs = Regidx rd1 ->
    uint rd1 <> 0 ->
    eq_vec (rget m rd1) zero_reg = false ->
    sie_cap_gpr kt m n b p -∗
    pc_is pc -∗
    instr pc true (BTYPE (sign_extend' 13 (concat_vec imm8 ('b"0")), zreg, creg2reg_idx rs, BEQ)) -∗
    wp_next b p (fun (CID : CpuId) =>
      sie_cap_gpr kt m n b p -∗
      pc_is(add_vec_int pc 2) -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    iIntros (Hrs Hrd1 Hcmp) "Hcg Hpc Hinstr Hcont".
    (* THE CLASS, CONSUMED.  [Hcmp] is the caller's comparison, taken at the
       ENTRY hart; the σ-obligation below is discharged at whatever hart the
       callback was instantiated at, and the two agree only away from tp.
       [src_ok_rget_indep] is [HartTp.rget_hart_indep] under the class, so this
       one line lifts the premise to the ALL-HARTS form and the endgame never
       names the hart the comparison was taken at.  Today the callback is still
       the entry hart, so [Hcmp_all CID] is what gets used; the funnel change
       that moves the callback inside [wp_next] instantiates it at the rebound
       hart instead and NOTHING ELSE in this proof moves -- which is the whole
       point of paying for the class now.
       (At a VARIABLE [rd1] this is not a conversion: the pin's [bool_decide]
       cannot reduce, so without the class [Hcmp_all] has no proof.) *)
    assert (Hcmp_all : forall hh : CpuId, eq_vec (rget (CID := hh) m rd1) zero_reg = false)
      by (intros hh; rewrite (src_ok_rget_indep m rd1 hh CID); exact Hcmp).
    assert (Hred : execute (BTYPE (sign_extend' 13 (concat_vec imm8 ('b"0")), zreg, creg2reg_idx rs, BEQ))
                   = btype_body (sign_extend' 13 (concat_vec imm8 ('b"0"))) (zero_extend' 5 ('b"00") : mword 5) rd1 eq_vec)
      by (rewrite Hrs; reflexivity).
    iApply (wp_btype_fall_s_sconf pc true (sign_extend' 13 (concat_vec imm8 ('b"0"))) (zero_extend' 5 ('b"00") : mword 5) rd1
              (BTYPE (sign_extend' 13 (concat_vec imm8 ('b"0")), zreg, creg2reg_idx rs, BEQ))
              eq_vec m n b Hred
              with "[] Hcg Hpc Hinstr [Hcont]").
    - iIntros (hh) "Hf".
      iDestruct (gpr_file_x0 (CID := hh) (tp_pin (CID := hh) m) (zero_extend' 5 ('b"00") : mword 5)
                   ltac:(vm_compute; reflexivity) with "Hf") as "[%Hx0 Hf]".
      iFrame "Hf". iPureIntro. unfold rget. rewrite Hx0. exact (Hcmp_all hh).
    - iNext. iExact "Hcont".
  Qed.

  (* WHAT AN [SrcOk] FAILURE LOOKS LIKE, so nobody has to rediscover it.  A
     converted leaf applied with the thread pointer in the source slot has no
     instance, and resolution says so AT THE APPLICATION, naming both the
     lemma and the register.  Uncommenting the probe below gives, verbatim
     (the line number is wherever the [pose proof] ends up):

       File "./WpSconfBtype.v", line 1293, characters 16-37:
       Error: Cannot infer the implicit parameter SrcOk0 of
       wp_cbeqz_fall_s_sconf whose type is "SrcOk Rtp" (no type class
       instance found) in environment:
       Σ : gFunctors
       riscvGS0 : riscvGS Σ
       sieG0 : sieG Σ
       GEN : GenId
       CID : CpuId
       p, pc : mword 64
       imm8 : mword 8
       m : regfile
       n : nat
       b : bool

     (An [exact]-shaped application reports the same thing as
     [Error: Could not find an instance for "SrcOk Rtp"].)  Either way it is a
     legible resolution failure at the call site -- not a deferred obligation,
     not a silent success.  That is the intended behaviour: a c.beqz on tp
     would make the comparison depend on which hart the σ-callback was
     instantiated at, and there is no proof of it.  Nothing in the tree does
     this -- [rd1] here comes from a [cregidx], which encodes x8..x15 only --
     so the register is not even reachable through this leaf; the probe has to
     forge it.

  Lemma cbeqz_tp_probe (pc : mword 64) (imm8 : mword 8)
      (m : regfile) (n : nat) (b : bool) : True.
  Proof.
    pose proof (wp_cbeqz_fall_s_sconf pc imm8 (Cregidx (mword_of_int 4)) Rtp m n b).
    exact I.
  Qed.
  *)

  Lemma wp_cbnez_fall_s_sconf
      (pc : mword 64) (imm8 : mword 8) (rs : cregidx) (rd1 : mword 5) `{!SrcOk rd1}
      (m : regfile) (n : nat) (b : bool) :
    creg2reg_idx rs = Regidx rd1 ->
    uint rd1 <> 0 ->
    neq_vec (rget m rd1) zero_reg = false ->
    sie_cap_gpr kt m n b p -∗
    pc_is pc -∗
    instr pc true (BTYPE (sign_extend' 13 (concat_vec imm8 ('b"0")), zreg, creg2reg_idx rs, BNE)) -∗
    wp_next b p (fun (CID : CpuId) =>
      sie_cap_gpr kt m n b p -∗
      pc_is(add_vec_int pc 2) -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    iIntros (Hrs Hrd1 Hcmp) "Hcg Hpc Hinstr Hcont".
    (* the class, consumed at [rd1]: [Hcmp] lifted to its ALL-HARTS form,
       which is the one line the funnel change needs and this leaf's wiring
       check.  See the family note at the head of this section. *)
    assert (Hcmp_all : forall hh : CpuId, neq_vec (rget (CID := hh) m rd1) zero_reg = false)
      by (intros hh; rewrite (src_ok_rget_indep m rd1 hh CID); exact Hcmp).
    assert (Hred : execute (BTYPE (sign_extend' 13 (concat_vec imm8 ('b"0")), zreg, creg2reg_idx rs, BNE))
                   = btype_body (sign_extend' 13 (concat_vec imm8 ('b"0"))) (zero_extend' 5 ('b"00") : mword 5) rd1 neq_vec)
      by (rewrite Hrs; reflexivity).
    iApply (wp_btype_fall_s_sconf pc true (sign_extend' 13 (concat_vec imm8 ('b"0"))) (zero_extend' 5 ('b"00") : mword 5) rd1
              (BTYPE (sign_extend' 13 (concat_vec imm8 ('b"0")), zreg, creg2reg_idx rs, BNE))
              neq_vec m n b Hred
              with "[] Hcg Hpc Hinstr [Hcont]").
    - iIntros (hh) "Hf".
      iDestruct (gpr_file_x0 (CID := hh) (tp_pin (CID := hh) m) (zero_extend' 5 ('b"00") : mword 5)
                   ltac:(vm_compute; reflexivity) with "Hf") as "[%Hx0 Hf]".
      iFrame "Hf". iPureIntro. unfold rget. rewrite Hx0. exact (Hcmp_all hh).
    - iNext. iExact "Hcont".
  Qed.

  (* ------------------------------------------------------------------- *)
  (* TAKEN leaves: the continuation is UNDER A LATER (the step's own),    *)
  (* so a loop's Löb IH can be discharged here; straight-line callers     *)
  (* weaken with [iNext].  All four go through the Zca jump helper, so    *)
  (* only bit-0 alignment of the target is demanded.                      *)
  (* ------------------------------------------------------------------- *)
  Lemma wp_beq_taken_s_sconf
      (pc : mword 64) (imm : mword 13) (rs2 rs1 : mword 5) `{!SrcOk rs1} `{!SrcOk rs2}
      (m : regfile) (n : nat) (b : bool) :
    uint rs1 <> 0 -> uint rs2 <> 0 ->
    eq_vec (rget m rs1) (rget m rs2) = true ->
    eq_vec (access_vec_dec (add_vec pc (sign_extend' 64 imm)) 0) ('b"0") = true ->
    sie_cap_gpr kt m n b p -∗
    pc_is pc -∗ instr pc false (BTYPE (imm, Regidx rs2, Regidx rs1, BEQ)) -∗
    ▷ wp_next b p (fun (CID : CpuId) =>
      sie_cap_gpr kt m n b p -∗
      pc_is(add_vec pc (sign_extend' 64 imm)) -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    iIntros (Hrs1 Hrs2 Hcmp Hal0) "Hcg Hpc Hinstr Hcont".
    (* the class, consumed at [rs1 / rs2]: [Hcmp] lifted to its ALL-HARTS form,
       which is the one line the funnel change needs and this leaf's wiring
       check.  See the family note at the head of this section. *)
    assert (Hcmp_all : forall hh : CpuId, eq_vec (rget (CID := hh) m rs1) (rget (CID := hh) m rs2) = true)
      by (intros hh; rewrite (src_ok_rget_indep m rs1 hh CID); rewrite (src_ok_rget_indep m rs2 hh CID); exact Hcmp).
    iApply (wp_btype_taken_s_sconf pc false (imm) rs2 rs1
              (BTYPE (imm, Regidx rs2, Regidx rs1, BEQ))
              eq_vec m n b eq_refl
              Hal0
              with "[] Hcg Hpc Hinstr [Hcont]").
    - iIntros (hh) "Hf". iFrame "Hf". iPureIntro. exact (Hcmp_all hh).
    - iExact "Hcont".
  Qed.

  Lemma wp_bne_taken_s_sconf
      (pc : mword 64) (imm : mword 13) (rs2 rs1 : mword 5) `{!SrcOk rs1} `{!SrcOk rs2}
      (m : regfile) (n : nat) (b : bool) :
    uint rs1 <> 0 -> uint rs2 <> 0 ->
    neq_vec (rget m rs1) (rget m rs2) = true ->
    eq_vec (access_vec_dec (add_vec pc (sign_extend' 64 imm)) 0) ('b"0") = true ->
    sie_cap_gpr kt m n b p -∗
    pc_is pc -∗ instr pc false (BTYPE (imm, Regidx rs2, Regidx rs1, BNE)) -∗
    ▷ wp_next b p (fun (CID : CpuId) =>
      sie_cap_gpr kt m n b p -∗
      pc_is(add_vec pc (sign_extend' 64 imm)) -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    iIntros (Hrs1 Hrs2 Hcmp Hal0) "Hcg Hpc Hinstr Hcont".
    (* the class, consumed at [rs1 / rs2]: [Hcmp] lifted to its ALL-HARTS form,
       which is the one line the funnel change needs and this leaf's wiring
       check.  See the family note at the head of this section. *)
    assert (Hcmp_all : forall hh : CpuId, neq_vec (rget (CID := hh) m rs1) (rget (CID := hh) m rs2) = true)
      by (intros hh; rewrite (src_ok_rget_indep m rs1 hh CID); rewrite (src_ok_rget_indep m rs2 hh CID); exact Hcmp).
    iApply (wp_btype_taken_s_sconf pc false (imm) rs2 rs1
              (BTYPE (imm, Regidx rs2, Regidx rs1, BNE))
              neq_vec m n b eq_refl
              Hal0
              with "[] Hcg Hpc Hinstr [Hcont]").
    - iIntros (hh) "Hf". iFrame "Hf". iPureIntro. exact (Hcmp_all hh).
    - iExact "Hcont".
  Qed.

  Lemma wp_cbeqz_taken_s_sconf
      (pc : mword 64) (imm8 : mword 8) (rs : cregidx) (rd1 : mword 5) `{!SrcOk rd1}
      (m : regfile) (n : nat) (b : bool) :
    let imm : mword 13 := sign_extend' 13 (concat_vec imm8 ('b"0")) in
    creg2reg_idx rs = Regidx rd1 ->
    uint rd1 <> 0 ->
    eq_vec (rget m rd1) zero_reg = true ->
    eq_vec (access_vec_dec (add_vec pc (sign_extend' 64 imm)) 0) ('b"0") = true ->
    sie_cap_gpr kt m n b p -∗
    pc_is pc -∗ instr pc true (BTYPE (imm, zreg, creg2reg_idx rs, BEQ)) -∗
    ▷ wp_next b p (fun (CID : CpuId) =>
      sie_cap_gpr kt m n b p -∗
      pc_is(add_vec pc (sign_extend' 64 imm)) -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros imm.
    iIntros (Hrs Hrd1 Hcmp Hal0) "Hcg Hpc Hinstr Hcont".
    (* the class, consumed at [rd1]: [Hcmp] lifted to its ALL-HARTS form,
       which is the one line the funnel change needs and this leaf's wiring
       check.  See the family note at the head of this section. *)
    assert (Hcmp_all : forall hh : CpuId, eq_vec (rget (CID := hh) m rd1) zero_reg = true)
      by (intros hh; rewrite (src_ok_rget_indep m rd1 hh CID); exact Hcmp).
    assert (Hred : execute (BTYPE (imm, zreg, creg2reg_idx rs, BEQ))
                   = btype_body (imm) (zero_extend' 5 ('b"00") : mword 5) rd1 eq_vec)
      by (rewrite Hrs; reflexivity).
    iApply (wp_btype_taken_s_sconf pc true (imm) (zero_extend' 5 ('b"00") : mword 5) rd1
              (BTYPE (imm, zreg, creg2reg_idx rs, BEQ))
              eq_vec m n b Hred
              Hal0
              with "[] Hcg Hpc Hinstr [Hcont]").
    - iIntros (hh) "Hf".
      iDestruct (gpr_file_x0 (CID := hh) (tp_pin (CID := hh) m) (zero_extend' 5 ('b"00") : mword 5)
                   ltac:(vm_compute; reflexivity) with "Hf") as "[%Hx0 Hf]".
      iFrame "Hf". iPureIntro. unfold rget. rewrite Hx0. exact (Hcmp_all hh).
    - iExact "Hcont".
  Qed.

  Lemma wp_cbnez_taken_s_sconf
      (pc : mword 64) (imm8 : mword 8) (rs : cregidx) (rd1 : mword 5) `{!SrcOk rd1}
      (m : regfile) (n : nat) (b : bool) :
    let imm : mword 13 := sign_extend' 13 (concat_vec imm8 ('b"0")) in
    creg2reg_idx rs = Regidx rd1 ->
    uint rd1 <> 0 ->
    neq_vec (rget m rd1) zero_reg = true ->
    eq_vec (access_vec_dec (add_vec pc (sign_extend' 64 imm)) 0) ('b"0") = true ->
    sie_cap_gpr kt m n b p -∗
    pc_is pc -∗ instr pc true (BTYPE (imm, zreg, creg2reg_idx rs, BNE)) -∗
    ▷ wp_next b p (fun (CID : CpuId) =>
      sie_cap_gpr kt m n b p -∗
      pc_is(add_vec pc (sign_extend' 64 imm)) -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros imm.
    iIntros (Hrs Hrd1 Hcmp Hal0) "Hcg Hpc Hinstr Hcont".
    (* the class, consumed at [rd1]: [Hcmp] lifted to its ALL-HARTS form,
       which is the one line the funnel change needs and this leaf's wiring
       check.  See the family note at the head of this section. *)
    assert (Hcmp_all : forall hh : CpuId, neq_vec (rget (CID := hh) m rd1) zero_reg = true)
      by (intros hh; rewrite (src_ok_rget_indep m rd1 hh CID); exact Hcmp).
    assert (Hred : execute (BTYPE (imm, zreg, creg2reg_idx rs, BNE))
                   = btype_body (imm) (zero_extend' 5 ('b"00") : mword 5) rd1 neq_vec)
      by (rewrite Hrs; reflexivity).
    iApply (wp_btype_taken_s_sconf pc true (imm) (zero_extend' 5 ('b"00") : mword 5) rd1
              (BTYPE (imm, zreg, creg2reg_idx rs, BNE))
              neq_vec m n b Hred
              Hal0
              with "[] Hcg Hpc Hinstr [Hcont]").
    - iIntros (hh) "Hf".
      iDestruct (gpr_file_x0 (CID := hh) (tp_pin (CID := hh) m) (zero_extend' 5 ('b"00") : mword 5)
                   ltac:(vm_compute; reflexivity) with "Hf") as "[%Hx0 Hf]".
      iFrame "Hf". iPureIntro. unfold rget. rewrite Hx0. exact (Hcmp_all hh).
    - iExact "Hcont".
  Qed.


  (* beqz (x0) TAKEN: the 4-byte twin of [wp_cbeqz_taken_s_sconf].  Only the
     instruction width differs -- the branch target's 2-alignment is what Zca
     licenses, and that is a fact about the TARGET, not about the size of the
     branch. *)
  Lemma wp_beqz_x0_taken_s_sconf
      (pc : mword 64) (imm : mword 13) (rs1 : mword 5) `{!SrcOk rs1}
      (m : regfile) (n : nat) (b : bool) :
    uint rs1 <> 0 ->
    eq_vec (rget m rs1) zero_reg = true ->
    eq_vec (access_vec_dec (add_vec pc (sign_extend' 64 imm)) 0) ('b"0") = true ->
    sie_cap_gpr kt m n b p -∗
    pc_is pc -∗ instr pc false (BTYPE (imm, zreg, Regidx rs1, BEQ)) -∗
    ▷ wp_next b p (fun (CID : CpuId) =>
      sie_cap_gpr kt m n b p -∗
      pc_is(add_vec pc (sign_extend' 64 imm)) -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    iIntros (Hrs1 Hcmp Hal0) "Hcg Hpc Hinstr Hcont".
    (* the class, consumed at [rs1]: [Hcmp] lifted to its ALL-HARTS form,
       which is the one line the funnel change needs and this leaf's wiring
       check.  See the family note at the head of this section. *)
    assert (Hcmp_all : forall hh : CpuId, eq_vec (rget (CID := hh) m rs1) zero_reg = true)
      by (intros hh; rewrite (src_ok_rget_indep m rs1 hh CID); exact Hcmp).
    iApply (wp_btype_taken_s_sconf pc false (imm) (zero_extend' 5 ('b"00") : mword 5) rs1
              (BTYPE (imm, zreg, Regidx rs1, BEQ))
              eq_vec m n b eq_refl
              Hal0
              with "[] Hcg Hpc Hinstr [Hcont]").
    - iIntros (hh) "Hf".
      iDestruct (gpr_file_x0 (CID := hh) (tp_pin (CID := hh) m) (zero_extend' 5 ('b"00") : mword 5)
                   ltac:(vm_compute; reflexivity) with "Hf") as "[%Hx0 Hf]".
      iFrame "Hf". iPureIntro. unfold rget. rewrite Hx0. exact (Hcmp_all hh).
    - iExact "Hcont".
  Qed.

  (* beqz (x0) fall-through -- moved here from ProofWalk.v. *)
  Lemma wp_beqz_x0_fall_s_sconf
      (pc : mword 64) (imm : mword 13) (rs1 : mword 5) `{!SrcOk rs1}
      (m : regfile) (n : nat) (b : bool) :
    uint rs1 <> 0 ->
    eq_vec (rget m rs1) zero_reg = false ->
    sie_cap_gpr kt m n b p -∗
    pc_is pc -∗ instr pc false (BTYPE (imm, zreg, Regidx rs1, BEQ)) -∗
    wp_next b p (fun (CID : CpuId) =>
      sie_cap_gpr kt m n b p -∗
      pc_is(add_vec_int pc 4) -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    iIntros (Hrs1 Hcmp) "Hcg Hpc Hinstr Hcont".
    (* the class, consumed at [rs1]: [Hcmp] lifted to its ALL-HARTS form,
       which is the one line the funnel change needs and this leaf's wiring
       check.  See the family note at the head of this section. *)
    assert (Hcmp_all : forall hh : CpuId, eq_vec (rget (CID := hh) m rs1) zero_reg = false)
      by (intros hh; rewrite (src_ok_rget_indep m rs1 hh CID); exact Hcmp).
    iApply (wp_btype_fall_s_sconf pc false (imm) (zero_extend' 5 ('b"00") : mword 5) rs1
              (BTYPE (imm, zreg, Regidx rs1, BEQ))
              eq_vec m n b eq_refl
              with "[] Hcg Hpc Hinstr [Hcont]").
    - iIntros (hh) "Hf".
      iDestruct (gpr_file_x0 (CID := hh) (tp_pin (CID := hh) m) (zero_extend' 5 ('b"00") : mword 5)
                   ltac:(vm_compute; reflexivity) with "Hf") as "[%Hx0 Hf]".
      iFrame "Hf". iPureIntro. unfold rget. rewrite Hx0. exact (Hcmp_all hh).
    - iNext. iExact "Hcont".
  Qed.

  (* bnez (x0 as rs2), the uncompressed form -- the back-edge of printk's %p
     hex loop, whose counter is a full-width [addiw].  The [zreg] twins of
     [wp_bne_taken]/[wp_bne_fall]: with rs2 = x0 the model reads no second
     register, so the [uint rs2 <> 0] side condition of those cannot be met. *)
  Lemma wp_bnez_x0_taken_s_sconf
      (pc : mword 64) (imm : mword 13) (rs1 : mword 5) `{!SrcOk rs1}
      (m : regfile) (n : nat) (b : bool) :
    uint rs1 <> 0 ->
    neq_vec (rget m rs1) zero_reg = true ->
    eq_vec (access_vec_dec (add_vec pc (sign_extend' 64 imm)) 0) ('b"0") = true ->
    sie_cap_gpr kt m n b p -∗
    pc_is pc -∗ instr pc false (BTYPE (imm, zreg, Regidx rs1, BNE)) -∗
    ▷ wp_next b p (fun (CID : CpuId) =>
      sie_cap_gpr kt m n b p -∗
      pc_is(add_vec pc (sign_extend' 64 imm)) -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    iIntros (Hrs1 Hcmp Hal0) "Hcg Hpc Hinstr Hcont".
    (* the class, consumed at [rs1]: [Hcmp] lifted to its ALL-HARTS form,
       which is the one line the funnel change needs and this leaf's wiring
       check.  See the family note at the head of this section. *)
    assert (Hcmp_all : forall hh : CpuId, neq_vec (rget (CID := hh) m rs1) zero_reg = true)
      by (intros hh; rewrite (src_ok_rget_indep m rs1 hh CID); exact Hcmp).
    iApply (wp_btype_taken_s_sconf pc false (imm) (zero_extend' 5 ('b"00") : mword 5) rs1
              (BTYPE (imm, zreg, Regidx rs1, BNE))
              neq_vec m n b eq_refl
              Hal0
              with "[] Hcg Hpc Hinstr [Hcont]").
    - iIntros (hh) "Hf".
      iDestruct (gpr_file_x0 (CID := hh) (tp_pin (CID := hh) m) (zero_extend' 5 ('b"00") : mword 5)
                   ltac:(vm_compute; reflexivity) with "Hf") as "[%Hx0 Hf]".
      iFrame "Hf". iPureIntro. unfold rget. rewrite Hx0. exact (Hcmp_all hh).
    - iExact "Hcont".
  Qed.

  Lemma wp_bnez_x0_fall_s_sconf
      (pc : mword 64) (imm : mword 13) (rs1 : mword 5) `{!SrcOk rs1}
      (m : regfile) (n : nat) (b : bool) :
    uint rs1 <> 0 ->
    neq_vec (rget m rs1) zero_reg = false ->
    sie_cap_gpr kt m n b p -∗
    pc_is pc -∗ instr pc false (BTYPE (imm, zreg, Regidx rs1, BNE)) -∗
    wp_next b p (fun (CID : CpuId) =>
      sie_cap_gpr kt m n b p -∗
      pc_is(add_vec_int pc 4) -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    iIntros (Hrs1 Hcmp) "Hcg Hpc Hinstr Hcont".
    (* the class, consumed at [rs1]: [Hcmp] lifted to its ALL-HARTS form,
       which is the one line the funnel change needs and this leaf's wiring
       check.  See the family note at the head of this section. *)
    assert (Hcmp_all : forall hh : CpuId, neq_vec (rget (CID := hh) m rs1) zero_reg = false)
      by (intros hh; rewrite (src_ok_rget_indep m rs1 hh CID); exact Hcmp).
    iApply (wp_btype_fall_s_sconf pc false (imm) (zero_extend' 5 ('b"00") : mword 5) rs1
              (BTYPE (imm, zreg, Regidx rs1, BNE))
              neq_vec m n b eq_refl
              with "[] Hcg Hpc Hinstr [Hcont]").
    - iIntros (hh) "Hf".
      iDestruct (gpr_file_x0 (CID := hh) (tp_pin (CID := hh) m) (zero_extend' 5 ('b"00") : mword 5)
                   ltac:(vm_compute; reflexivity) with "Hf") as "[%Hx0 Hf]".
      iFrame "Hf". iPureIntro. unfold rget. rewrite Hx0. exact (Hcmp_all hh).
    - iNext. iExact "Hcont".
  Qed.

  (* ------------------------------------------------------------------- *)
  (* [SrcOk] SMOKE TEST -- see IntrDefs.v's checker block for why this is  *)
  (* repeated per file: an unresolved [SrcOk] inside an [iApply] is        *)
  (* SHELVED, so a hint this file cannot see would surface only as some    *)
  (* consumer's "Attempt to save an incomplete proof".  These two lines    *)
  (* make that failure happen HERE.  x9/x15 (s1/a5) are the registers the  *)
  (* branch leaves above are actually applied at; the [cregidx]-sourced    *)
  (* c.beqz/c.bnez leaves can only ever see x8..x15.                       *)
  (* ------------------------------------------------------------------- *)
  Definition btype_srcok_pos_s1 : SrcOk (mword_of_int 9 : mword 5) := _.
  Definition btype_srcok_pos_a5 : SrcOk (mword_of_int 15 : mword 5) := _.
  Fail Definition btype_srcok_neg : SrcOk Rtp := _.

End WpSconfBtype.
