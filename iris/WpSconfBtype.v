(* WpSconfBtype.v -- the SIE-AGNOSTIC branch leaf layer (interrupt-sweep
   stage 5): [sconf]+[sie_cap] twins of WpSmodePtBtype.v's leaves over
   the agnostic funnel [wp_instr_s_sconf].

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
Require Import RiscvLang RiscvPtsto RiscvExec RiscvTryStep RiscvFetchExec.
Require Import InstrBytes ExecCommon WpGpr RegFile HartTp WpNext.
Require Import SmodeCore.
Require Import IntrDefs WpSmodeIntr.
Require Import IntrDefs.
Import Defs.

(* ---- Local helpers (copies: WpSmodePtBtype's are Local) ---- *)
Local Definition rvv (r : mword 5) (s : mstate) : mword 64 :=
    if Z.eqb (uint r) 0 then zero_reg
    else register_lookup (R_bitvector_64 (gpr_of_Z (uint r))) s.(sregs).

Local Lemma exec_BTYPE_cmp_BNE (rs2 rs1 : mword 5) s :
    exec (Defs.bind (rX_bits (Regidx rs1))
            (fun w2 => Defs.bind (rX_bits (Regidx rs2))
               (fun w3 => returnM (neq_vec w2 w3)))) s
      = Some (neq_vec (rvv rs1 s) (rvv rs2 s), s).
  Proof.
    unfold rvv.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_rX_bits_gpr rs1 s)).
    rewrite (exec_bind_Some _ _ _ _ _ (exec_rX_bits_gpr rs2 s)).
    apply exec_returnM.
  Qed.

Local Lemma exec_BTYPE_cmp_BEQ (rs2 rs1 : mword 5) s :
    exec (Defs.bind (rX_bits (Regidx rs1))
            (fun w2 => Defs.bind (rX_bits (Regidx rs2))
               (fun w3 => returnM (eq_vec w2 w3)))) s
      = Some (eq_vec (rvv rs1 s) (rvv rs2 s), s).
  Proof.
    unfold rvv.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_rX_bits_gpr rs1 s)).
    rewrite (exec_bind_Some _ _ _ _ _ (exec_rX_bits_gpr rs2 s)).
    apply exec_returnM.
  Qed.

Local Lemma exec_BTYPE_cmp_BGE (rs2 rs1 : mword 5) s :
  exec (Defs.bind (rX_bits (Regidx rs1))
          (fun w2 => Defs.bind (rX_bits (Regidx rs2))
             (fun w3 => returnM (zopz0zKzJ_s w2 w3)))) s
    = Some (zopz0zKzJ_s (rvv rs1 s) (rvv rs2 s), s).
Proof.
  unfold rvv.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_rX_bits_gpr rs1 s)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_rX_bits_gpr rs2 s)).
  apply exec_returnM.
Qed.

Local Lemma exec_execute_BTYPE_BEQ_fall (imm : mword 13) (rs2 rs1 : mword 5) s :
    eq_vec (rvv rs1 s) (rvv rs2 s) = false ->
    exec (execute (BTYPE (imm, Regidx rs2, Regidx rs1, BEQ))) s
      = Some (RETIRE_SUCCESS, s).
  Proof.
    intro Hfall.
    unfold execute. cbn match. unfold execute_BTYPE.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_BTYPE_cmp_BEQ rs2 rs1 s)).
    rewrite Hfall. apply exec_returnM.
  Qed.

Local Lemma exec_execute_BTYPE_BNE_fall (imm : mword 13) (rs2 rs1 : mword 5) s :
    neq_vec (rvv rs1 s) (rvv rs2 s) = false ->
    exec (execute (BTYPE (imm, Regidx rs2, Regidx rs1, BNE))) s
      = Some (RETIRE_SUCCESS, s).
  Proof.
    intro Hfall.
    unfold execute. cbn match. unfold execute_BTYPE.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_BTYPE_cmp_BNE rs2 rs1 s)).
    rewrite Hfall. apply exec_returnM.
  Qed.

Local Lemma exec_execute_BTYPE_BGE_fall (imm : mword 13) (rs2 rs1 : mword 5) s :
  zopz0zKzJ_s (rvv rs1 s) (rvv rs2 s) = false ->
  exec (execute (BTYPE (imm, Regidx rs2, Regidx rs1, BGE))) s
    = Some (RETIRE_SUCCESS, s).
Proof.
  intro Hfall.
  unfold execute. cbn match. unfold execute_BTYPE.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_BTYPE_cmp_BGE rs2 rs1 s)).
  rewrite Hfall. apply exec_returnM.
Qed.

Local Lemma exec_BTYPE_cmp_BLTU (rs2 rs1 : mword 5) s :
  exec (Defs.bind (rX_bits (Regidx rs1))
          (fun w2 => Defs.bind (rX_bits (Regidx rs2))
             (fun w3 => returnM (zopz0zI_u w2 w3)))) s
    = Some (zopz0zI_u (rvv rs1 s) (rvv rs2 s), s).
Proof.
  unfold rvv.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_rX_bits_gpr rs1 s)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_rX_bits_gpr rs2 s)).
  apply exec_returnM.
Qed.

Local Lemma exec_execute_BTYPE_BLTU_fall (imm : mword 13) (rs2 rs1 : mword 5) s :
  zopz0zI_u (rvv rs1 s) (rvv rs2 s) = false ->
  exec (execute (BTYPE (imm, Regidx rs2, Regidx rs1, BLTU))) s
    = Some (RETIRE_SUCCESS, s).
Proof.
  intro Hfall.
  unfold execute. cbn match. unfold execute_BTYPE.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_BTYPE_cmp_BLTU rs2 rs1 s)).
  rewrite Hfall. apply exec_returnM.
Qed.

Local Lemma exec_BTYPE_cmp_BLT (rs2 rs1 : mword 5) s :
  exec (Defs.bind (rX_bits (Regidx rs1))
          (fun w2 => Defs.bind (rX_bits (Regidx rs2))
             (fun w3 => returnM (zopz0zI_s w2 w3)))) s
    = Some (zopz0zI_s (rvv rs1 s) (rvv rs2 s), s).
Proof.
  unfold rvv.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_rX_bits_gpr rs1 s)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_rX_bits_gpr rs2 s)).
  apply exec_returnM.
Qed.

Local Lemma exec_execute_BTYPE_BLT_fall (imm : mword 13) (rs2 rs1 : mword 5) s :
  zopz0zI_s (rvv rs1 s) (rvv rs2 s) = false ->
  exec (execute (BTYPE (imm, Regidx rs2, Regidx rs1, BLT))) s
    = Some (RETIRE_SUCCESS, s).
Proof.
  intro Hfall.
  unfold execute. cbn match. unfold execute_BTYPE.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_BTYPE_cmp_BLT rs2 rs1 s)).
  rewrite Hfall. apply exec_returnM.
Qed.

Local Lemma exec_BTYPE_cmp_BGEU (rs2 rs1 : mword 5) s :
  exec (Defs.bind (rX_bits (Regidx rs1))
          (fun w2 => Defs.bind (rX_bits (Regidx rs2))
             (fun w3 => returnM (zopz0zKzJ_u w2 w3)))) s
    = Some (zopz0zKzJ_u (rvv rs1 s) (rvv rs2 s), s).
Proof.
  unfold rvv.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_rX_bits_gpr rs1 s)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_rX_bits_gpr rs2 s)).
  apply exec_returnM.
Qed.

Local Lemma exec_execute_BTYPE_BGEU_fall (imm : mword 13) (rs2 rs1 : mword 5) s :
  zopz0zKzJ_u (rvv rs1 s) (rvv rs2 s) = false ->
  exec (execute (BTYPE (imm, Regidx rs2, Regidx rs1, BGEU))) s
    = Some (RETIRE_SUCCESS, s).
Proof.
  intro Hfall.
  unfold execute. cbn match. unfold execute_BTYPE.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_BTYPE_cmp_BGEU rs2 rs1 s)).
  rewrite Hfall. apply exec_returnM.
Qed.


Local Lemma exec_execute_BTYPE_BEQ_taken_zca (imm : mword 13) (rs2 rs1 : mword 5) s :
    eq_vec (rvv rs1 s) (rvv rs2 s) = true ->
    eq_vec (access_vec_dec (add_vec (register_lookup PC s.(sregs)) (sign_extend' 64 imm)) 0) ('b"0") = true ->
    exec (currentlyEnabled Ext_Zca) s = Some (true, s) ->
    exec (execute (BTYPE (imm, Regidx rs2, Regidx rs1, BEQ))) s
      = Some (RETIRE_SUCCESS,
              set_reg s nextPC (add_vec (register_lookup PC s.(sregs)) (sign_extend' 64 imm))).
  Proof.
    intros Htaken Halign Hzca.
    unfold execute. cbn match. unfold execute_BTYPE.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_BTYPE_cmp_BEQ rs2 rs1 s)).
    rewrite Htaken.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg PC s)).
    exact (exec_jump_to_zca _ s Halign Hzca).
  Qed.

Local Lemma exec_execute_BTYPE_BNE_taken_zca (imm : mword 13) (rs2 rs1 : mword 5) s :
    neq_vec (rvv rs1 s) (rvv rs2 s) = true ->
    eq_vec (access_vec_dec (add_vec (register_lookup PC s.(sregs)) (sign_extend' 64 imm)) 0) ('b"0") = true ->
    exec (currentlyEnabled Ext_Zca) s = Some (true, s) ->
    exec (execute (BTYPE (imm, Regidx rs2, Regidx rs1, BNE))) s
      = Some (RETIRE_SUCCESS,
              set_reg s nextPC (add_vec (register_lookup PC s.(sregs)) (sign_extend' 64 imm))).
  Proof.
    intros Htaken Halign Hzca.
    unfold execute. cbn match. unfold execute_BTYPE.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_BTYPE_cmp_BNE rs2 rs1 s)).
    rewrite Htaken.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg PC s)).
    exact (exec_jump_to_zca _ s Halign Hzca).
  Qed.

Local Lemma exec_execute_BTYPE_BLTU_taken_zca (imm : mword 13) (rs2 rs1 : mword 5) s :
    zopz0zI_u (rvv rs1 s) (rvv rs2 s) = true ->
    eq_vec (access_vec_dec (add_vec (register_lookup PC s.(sregs)) (sign_extend' 64 imm)) 0) ('b"0") = true ->
    exec (currentlyEnabled Ext_Zca) s = Some (true, s) ->
    exec (execute (BTYPE (imm, Regidx rs2, Regidx rs1, BLTU))) s
      = Some (RETIRE_SUCCESS,
              set_reg s nextPC (add_vec (register_lookup PC s.(sregs)) (sign_extend' 64 imm))).
  Proof.
    intros Htaken Halign Hzca.
    unfold execute. cbn match. unfold execute_BTYPE.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_BTYPE_cmp_BLTU rs2 rs1 s)).
    rewrite Htaken.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg PC s)).
    exact (exec_jump_to_zca _ s Halign Hzca).
  Qed.

Local Lemma exec_execute_BTYPE_BLT_taken_zca (imm : mword 13) (rs2 rs1 : mword 5) s :
    zopz0zI_s (rvv rs1 s) (rvv rs2 s) = true ->
    eq_vec (access_vec_dec (add_vec (register_lookup PC s.(sregs)) (sign_extend' 64 imm)) 0) ('b"0") = true ->
    exec (currentlyEnabled Ext_Zca) s = Some (true, s) ->
    exec (execute (BTYPE (imm, Regidx rs2, Regidx rs1, BLT))) s
      = Some (RETIRE_SUCCESS,
              set_reg s nextPC (add_vec (register_lookup PC s.(sregs)) (sign_extend' 64 imm))).
  Proof.
    intros Htaken Halign Hzca.
    unfold execute. cbn match. unfold execute_BTYPE.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_BTYPE_cmp_BLT rs2 rs1 s)).
    rewrite Htaken.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg PC s)).
    exact (exec_jump_to_zca _ s Halign Hzca).
  Qed.

Local Lemma exec_execute_BTYPE_BGE_taken_zca (imm : mword 13) (rs2 rs1 : mword 5) s :
    zopz0zKzJ_s (rvv rs1 s) (rvv rs2 s) = true ->
    eq_vec (access_vec_dec (add_vec (register_lookup PC s.(sregs)) (sign_extend' 64 imm)) 0) ('b"0") = true ->
    exec (currentlyEnabled Ext_Zca) s = Some (true, s) ->
    exec (execute (BTYPE (imm, Regidx rs2, Regidx rs1, BGE))) s
      = Some (RETIRE_SUCCESS,
              set_reg s nextPC (add_vec (register_lookup PC s.(sregs)) (sign_extend' 64 imm))).
  Proof.
    intros Htaken Halign Hzca.
    unfold execute. cbn match. unfold execute_BTYPE.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_BTYPE_cmp_BGE rs2 rs1 s)).
    rewrite Htaken.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg PC s)).
    exact (exec_jump_to_zca _ s Halign Hzca).
  Qed.

Local Lemma exec_execute_BTYPE_BGEU_taken_zca (imm : mword 13) (rs2 rs1 : mword 5) s :
    zopz0zKzJ_u (rvv rs1 s) (rvv rs2 s) = true ->
    eq_vec (access_vec_dec (add_vec (register_lookup PC s.(sregs)) (sign_extend' 64 imm)) 0) ('b"0") = true ->
    exec (currentlyEnabled Ext_Zca) s = Some (true, s) ->
    exec (execute (BTYPE (imm, Regidx rs2, Regidx rs1, BGEU))) s
      = Some (RETIRE_SUCCESS,
              set_reg s nextPC (add_vec (register_lookup PC s.(sregs)) (sign_extend' 64 imm))).
  Proof.
    intros Htaken Halign Hzca.
    unfold execute. cbn match. unfold execute_BTYPE.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_BTYPE_cmp_BGEU rs2 rs1 s)).
    rewrite Htaken.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg PC s)).
    exact (exec_jump_to_zca _ s Halign Hzca).
  Qed.

Section WpSconfBtype.
  Context `{!riscvGS Σ}.
  Context `{!sieG Σ}.
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
    iApply (wp_instr_s_sconf m n b pc false
              (BTYPE (imm, Regidx rs2, Regidx rs1, BEQ))
              with "Hcg Hpc Hinstr").
    (* FREE THE NAME [CID] FOR THE REBOUND HART.  A section variable is an
       ordinary context entry inside a proof, so [rename] moves it aside --
       and the STATEMENT never sees that, so the 184 call sites that name this
       tier's harts as [(CID := ...)] keep working.  Introducing the new hart
       under a different name instead would force a [(CID := ...)] annotation on
       every hart-indexed term the body writes out ([tp_pin m], [rget m rs]);
       with the rename the body below is UNCHANGED. *)
    rename CID into CID0.
    iIntros (CID Hs σ Hpceq) "Hsc Hcap Hfile Hnpc [Hreg Hmem]".
    iMod (reg_update (CID := CID) _ nextPC _ (add_vec_int pc 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s_pc := set_reg σ nextPC (add_vec_int pc 4)).
    iDestruct (gpr_file_lookup_acc (tp_pin (CID := CID) m) (Regidx rs1) with "Hfile") as "[Hrac Hfb_rs1]".
    iDestruct (gpr_pt_value (CID := CID) rs1 (tp_pin (CID := CID) m (Regidx rs1)) s_pc with "Hreg Hrac") as %Lva.
    iDestruct ("Hfb_rs1" with "Hrac") as "Hfile".
    iDestruct (gpr_file_lookup_acc (tp_pin (CID := CID) m) (Regidx rs2) with "Hfile") as "[Hrbc Hfb_rs2]".
    iDestruct (gpr_pt_value (CID := CID) rs2 (tp_pin (CID := CID) m (Regidx rs2)) s_pc with "Hreg Hrbc") as %Lvb.
    iDestruct ("Hfb_rs2" with "Hrbc") as "Hfile".
    iModIntro. iExists s_pc.
    iSplitR.
    { iPureIntro. rewrite Hpceq. fold s_pc.
      apply exec_execute_BTYPE_BEQ_fall. unfold rvv. rewrite Lva Lvb. exact (Hcmp_all CID). }
    iSplitL "Hreg Hmem". { unfold s_pc; rewrite ?sregs_set_reg ?mem_set_reg. iFrame "Hreg Hmem". }
    iIntros "Hhs' Hpc'".
    assert (Lnpc : register_lookup nextPC s_pc.(sregs) = add_vec_int pc 4)
      by (unfold s_pc; rewrite register_lookup_set; reflexivity).
    iEval (rewrite Lnpc) in "Hpc'".
    iDestruct (sie_cap_gpr_join (CID := CID) with "Hhs' Hsc Hcap Hfile") as "Hcg".
    iApply ("Hcont" $! CID with "[] Hcg [$Hpc' $Hnpc]").
    iPureIntro. exact Hs.
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
    iApply (wp_instr_s_sconf m n b pc false
              (BTYPE (imm, Regidx rs2, Regidx rs1, BNE))
              with "Hcg Hpc Hinstr").
    (* FREE THE NAME [CID] FOR THE REBOUND HART.  A section variable is an
       ordinary context entry inside a proof, so [rename] moves it aside --
       and the STATEMENT never sees that, so the 184 call sites that name this
       tier's harts as [(CID := ...)] keep working.  Introducing the new hart
       under a different name instead would force a [(CID := ...)] annotation on
       every hart-indexed term the body writes out ([tp_pin m], [rget m rs]);
       with the rename the body below is UNCHANGED. *)
    rename CID into CID0.
    iIntros (CID Hs σ Hpceq) "Hsc Hcap Hfile Hnpc [Hreg Hmem]".
    iMod (reg_update (CID := CID) _ nextPC _ (add_vec_int pc 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s_pc := set_reg σ nextPC (add_vec_int pc 4)).
    iDestruct (gpr_file_lookup_acc (tp_pin (CID := CID) m) (Regidx rs1) with "Hfile") as "[Hrac Hfb_rs1]".
    iDestruct (gpr_pt_value (CID := CID) rs1 (tp_pin (CID := CID) m (Regidx rs1)) s_pc with "Hreg Hrac") as %Lva.
    iDestruct ("Hfb_rs1" with "Hrac") as "Hfile".
    iDestruct (gpr_file_lookup_acc (tp_pin (CID := CID) m) (Regidx rs2) with "Hfile") as "[Hrbc Hfb_rs2]".
    iDestruct (gpr_pt_value (CID := CID) rs2 (tp_pin (CID := CID) m (Regidx rs2)) s_pc with "Hreg Hrbc") as %Lvb.
    iDestruct ("Hfb_rs2" with "Hrbc") as "Hfile".
    iModIntro. iExists s_pc.
    iSplitR.
    { iPureIntro. rewrite Hpceq. fold s_pc.
      apply exec_execute_BTYPE_BNE_fall. unfold rvv. rewrite Lva Lvb. exact (Hcmp_all CID). }
    iSplitL "Hreg Hmem". { unfold s_pc; rewrite ?sregs_set_reg ?mem_set_reg. iFrame "Hreg Hmem". }
    iIntros "Hhs' Hpc'".
    assert (Lnpc : register_lookup nextPC s_pc.(sregs) = add_vec_int pc 4)
      by (unfold s_pc; rewrite register_lookup_set; reflexivity).
    iEval (rewrite Lnpc) in "Hpc'".
    iDestruct (sie_cap_gpr_join (CID := CID) with "Hhs' Hsc Hcap Hfile") as "Hcg".
    iApply ("Hcont" $! CID with "[] Hcg [$Hpc' $Hnpc]").
    iPureIntro. exact Hs.
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
    iApply (wp_instr_s_sconf m n b pc false
              (BTYPE (imm, Regidx rs2, Regidx rs1, BLTU))
              with "Hcg Hpc Hinstr").
    (* FREE THE NAME [CID] FOR THE REBOUND HART.  A section variable is an
       ordinary context entry inside a proof, so [rename] moves it aside --
       and the STATEMENT never sees that, so the 184 call sites that name this
       tier's harts as [(CID := ...)] keep working.  Introducing the new hart
       under a different name instead would force a [(CID := ...)] annotation on
       every hart-indexed term the body writes out ([tp_pin m], [rget m rs]);
       with the rename the body below is UNCHANGED. *)
    rename CID into CID0.
    iIntros (CID Hs σ Hpceq) "Hsc Hcap Hfile Hnpc [Hreg Hmem]".
    iMod (reg_update (CID := CID) _ nextPC _ (add_vec_int pc 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s_pc := set_reg σ nextPC (add_vec_int pc 4)).
    iDestruct (gpr_file_lookup_acc (tp_pin (CID := CID) m) (Regidx rs1) with "Hfile") as "[Hrac Hfb_rs1]".
    iDestruct (gpr_pt_value (CID := CID) rs1 (tp_pin (CID := CID) m (Regidx rs1)) s_pc with "Hreg Hrac") as %Lva.
    iDestruct ("Hfb_rs1" with "Hrac") as "Hfile".
    iDestruct (gpr_file_lookup_acc (tp_pin (CID := CID) m) (Regidx rs2) with "Hfile") as "[Hrbc Hfb_rs2]".
    iDestruct (gpr_pt_value (CID := CID) rs2 (tp_pin (CID := CID) m (Regidx rs2)) s_pc with "Hreg Hrbc") as %Lvb.
    iDestruct ("Hfb_rs2" with "Hrbc") as "Hfile".
    iModIntro. iExists s_pc.
    iSplitR.
    { iPureIntro. rewrite Hpceq. fold s_pc.
      apply exec_execute_BTYPE_BLTU_fall. unfold rvv. rewrite Lva Lvb. exact (Hcmp_all CID). }
    iSplitL "Hreg Hmem". { unfold s_pc; rewrite ?sregs_set_reg ?mem_set_reg. iFrame "Hreg Hmem". }
    iIntros "Hhs' Hpc'".
    assert (Lnpc : register_lookup nextPC s_pc.(sregs) = add_vec_int pc 4)
      by (unfold s_pc; rewrite register_lookup_set; reflexivity).
    iEval (rewrite Lnpc) in "Hpc'".
    iDestruct (sie_cap_gpr_join (CID := CID) with "Hhs' Hsc Hcap Hfile") as "Hcg".
    iApply ("Hcont" $! CID with "[] Hcg [$Hpc' $Hnpc]").
    iPureIntro. exact Hs.
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
    iApply (wp_instr_s_sconf m n b pc false
              (BTYPE (imm, Regidx rs2, Regidx rs1, BLT))
              with "Hcg Hpc Hinstr").
    (* FREE THE NAME [CID] FOR THE REBOUND HART.  A section variable is an
       ordinary context entry inside a proof, so [rename] moves it aside --
       and the STATEMENT never sees that, so the 184 call sites that name this
       tier's harts as [(CID := ...)] keep working.  Introducing the new hart
       under a different name instead would force a [(CID := ...)] annotation on
       every hart-indexed term the body writes out ([tp_pin m], [rget m rs]);
       with the rename the body below is UNCHANGED. *)
    rename CID into CID0.
    iIntros (CID Hs σ Hpceq) "Hsc Hcap Hfile Hnpc [Hreg Hmem]".
    iMod (reg_update (CID := CID) _ nextPC _ (add_vec_int pc 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s_pc := set_reg σ nextPC (add_vec_int pc 4)).
    iDestruct (gpr_file_lookup_acc (tp_pin (CID := CID) m) (Regidx rs1) with "Hfile") as "[Hrac Hfb_rs1]".
    iDestruct (gpr_pt_value (CID := CID) rs1 (tp_pin (CID := CID) m (Regidx rs1)) s_pc with "Hreg Hrac") as %Lva.
    iDestruct ("Hfb_rs1" with "Hrac") as "Hfile".
    iDestruct (gpr_file_lookup_acc (tp_pin (CID := CID) m) (Regidx rs2) with "Hfile") as "[Hrbc Hfb_rs2]".
    iDestruct (gpr_pt_value (CID := CID) rs2 (tp_pin (CID := CID) m (Regidx rs2)) s_pc with "Hreg Hrbc") as %Lvb.
    iDestruct ("Hfb_rs2" with "Hrbc") as "Hfile".
    iModIntro. iExists s_pc.
    iSplitR.
    { iPureIntro. rewrite Hpceq. fold s_pc.
      apply exec_execute_BTYPE_BLT_fall. unfold rvv. rewrite Lva Lvb. exact (Hcmp_all CID). }
    iSplitL "Hreg Hmem". { unfold s_pc; rewrite ?sregs_set_reg ?mem_set_reg. iFrame "Hreg Hmem". }
    iIntros "Hhs' Hpc'".
    assert (Lnpc : register_lookup nextPC s_pc.(sregs) = add_vec_int pc 4)
      by (unfold s_pc; rewrite register_lookup_set; reflexivity).
    iEval (rewrite Lnpc) in "Hpc'".
    iDestruct (sie_cap_gpr_join (CID := CID) with "Hhs' Hsc Hcap Hfile") as "Hcg".
    iApply ("Hcont" $! CID with "[] Hcg [$Hpc' $Hnpc]").
    iPureIntro. exact Hs.
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
    iApply (wp_instr_s_sconf m n b pc false
              (BTYPE (imm, Regidx rs2, Regidx rs1, BLT))
              with "Hcg Hpc Hinstr").
    (* FREE THE NAME [CID] FOR THE REBOUND HART.  A section variable is an
       ordinary context entry inside a proof, so [rename] moves it aside --
       and the STATEMENT never sees that, so the 184 call sites that name this
       tier's harts as [(CID := ...)] keep working.  Introducing the new hart
       under a different name instead would force a [(CID := ...)] annotation on
       every hart-indexed term the body writes out ([tp_pin m], [rget m rs]);
       with the rename the body below is UNCHANGED. *)
    rename CID into CID0.
    iIntros (CID Hs σ Hpceq) "Hsc Hcap Hfile Hnpc [Hreg Hmem]".
    iDestruct "Hsc" as "[#Hhw Hsc2]".
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & #Hsenv & %HmisaS & %HmisaC &
        %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np & %HmisaA & %Hmisa_val0 & %Hmseccfg_val0 & #Hkmapb)".
    iDestruct (reg_valid_dq (CID := CID) with "Hreg Hmisa") as %Lmisa.
    iMod (reg_update (CID := CID) _ nextPC _ (add_vec_int pc 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s_pc := set_reg σ nextPC (add_vec_int pc 4)).
    assert (Hpcv : register_lookup PC s_pc.(sregs) = pc).
    { unfold s_pc; rewrite ?sregs_set_reg.
      rewrite irrelevant_register_set; [ exact Hpceq | vm_compute; reflexivity ]. }
    iDestruct (gpr_file_lookup_acc (tp_pin (CID := CID) m) (Regidx rs1) with "Hfile") as "[Hrac Hfb_rs1]".
    iDestruct (gpr_pt_value (CID := CID) rs1 (tp_pin (CID := CID) m (Regidx rs1)) s_pc with "Hreg Hrac") as %Lva.
    iDestruct ("Hfb_rs1" with "Hrac") as "Hfile".
    iDestruct (gpr_file_lookup_acc (tp_pin (CID := CID) m) (Regidx rs2) with "Hfile") as "[Hrbc Hfb_rs2]".
    iDestruct (gpr_pt_value (CID := CID) rs2 (tp_pin (CID := CID) m (Regidx rs2)) s_pc with "Hreg Hrbc") as %Lvb.
    iDestruct ("Hfb_rs2" with "Hrbc") as "Hfile".
    iMod (reg_update (CID := CID) _ nextPC _ (add_vec pc (sign_extend' 64 imm)) with "Hreg Hnpc") as "[Hreg Hnpc]".
    iModIntro.
    iExists (set_reg s_pc nextPC (add_vec pc (sign_extend' 64 imm))).
    iSplitR.
    { iPureIntro. rewrite Hpceq. fold s_pc.
      assert (Htk : zopz0zI_s (rvv rs1 s_pc) (rvv rs2 s_pc) = true)
        by (unfold rvv; rewrite Lva Lvb; exact (Hcmp_all CID)).
      assert (HzcaS : eq_vec (_get_Misa_C (register_lookup misa s_pc.(sregs))) ('b"1") = true).
      { unfold s_pc; rewrite ?sregs_set_reg.
        rewrite irrelevant_register_set; [ rewrite Lmisa; exact HmisaC | vm_compute; reflexivity ]. }
      epose proof (exec_execute_BTYPE_BLT_taken_zca imm rs2 rs1 s_pc Htk) as Hred.
      rewrite Hpcv in Hred. exact (Hred Hal0 (exec_currentlyEnabled_Zca s_pc HzcaS)). }
    iSplitL "Hreg Hmem". { unfold s_pc; rewrite ?sregs_set_reg ?mem_set_reg. iFrame "Hreg Hmem". }
    iIntros "Hhs' Hpc'".
    assert (Lnpc : register_lookup nextPC
             (set_reg s_pc nextPC (add_vec pc (sign_extend' 64 imm))).(sregs)
             = add_vec pc (sign_extend' 64 imm))
      by (rewrite ?sregs_set_reg; rewrite register_lookup_set; reflexivity).
    iEval (rewrite Lnpc) in "Hpc'".
    iNext.
    iDestruct (sie_cap_gpr_join (CID := CID) with "Hhs' [$Hhw $Hsc2] Hcap Hfile") as "Hcg".
    iApply ("Hcont" $! CID with "[] Hcg [$Hpc' $Hnpc]").
    iPureIntro. exact Hs.
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
    iApply (wp_instr_s_sconf m n b pc false
              (BTYPE (imm, Regidx rs2, Regidx rs1, BGEU))
              with "Hcg Hpc Hinstr").
    (* FREE THE NAME [CID] FOR THE REBOUND HART.  A section variable is an
       ordinary context entry inside a proof, so [rename] moves it aside --
       and the STATEMENT never sees that, so the 184 call sites that name this
       tier's harts as [(CID := ...)] keep working.  Introducing the new hart
       under a different name instead would force a [(CID := ...)] annotation on
       every hart-indexed term the body writes out ([tp_pin m], [rget m rs]);
       with the rename the body below is UNCHANGED. *)
    rename CID into CID0.
    iIntros (CID Hs σ Hpceq) "Hsc Hcap Hfile Hnpc [Hreg Hmem]".
    iMod (reg_update (CID := CID) _ nextPC _ (add_vec_int pc 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s_pc := set_reg σ nextPC (add_vec_int pc 4)).
    iDestruct (gpr_file_lookup_acc (tp_pin (CID := CID) m) (Regidx rs1) with "Hfile") as "[Hrac Hfb_rs1]".
    iDestruct (gpr_pt_value (CID := CID) rs1 (tp_pin (CID := CID) m (Regidx rs1)) s_pc with "Hreg Hrac") as %Lva.
    iDestruct ("Hfb_rs1" with "Hrac") as "Hfile".
    iDestruct (gpr_file_lookup_acc (tp_pin (CID := CID) m) (Regidx rs2) with "Hfile") as "[Hrbc Hfb_rs2]".
    iDestruct (gpr_pt_value (CID := CID) rs2 (tp_pin (CID := CID) m (Regidx rs2)) s_pc with "Hreg Hrbc") as %Lvb.
    iDestruct ("Hfb_rs2" with "Hrbc") as "Hfile".
    iModIntro. iExists s_pc.
    iSplitR.
    { iPureIntro. rewrite Hpceq. fold s_pc.
      apply exec_execute_BTYPE_BGEU_fall. unfold rvv. rewrite Lva Lvb. exact (Hcmp_all CID). }
    iSplitL "Hreg Hmem". { unfold s_pc; rewrite ?sregs_set_reg ?mem_set_reg. iFrame "Hreg Hmem". }
    iIntros "Hhs' Hpc'".
    assert (Lnpc : register_lookup nextPC s_pc.(sregs) = add_vec_int pc 4)
      by (unfold s_pc; rewrite register_lookup_set; reflexivity).
    iEval (rewrite Lnpc) in "Hpc'".
    iDestruct (sie_cap_gpr_join (CID := CID) with "Hhs' Hsc Hcap Hfile") as "Hcg".
    iApply ("Hcont" $! CID with "[] Hcg [$Hpc' $Hnpc]").
    iPureIntro. exact Hs.
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
    iApply (wp_instr_s_sconf m n b pc false
              (BTYPE (imm, Regidx rs2, Regidx rs1, BLTU))
              with "Hcg Hpc Hinstr").
    (* FREE THE NAME [CID] FOR THE REBOUND HART.  A section variable is an
       ordinary context entry inside a proof, so [rename] moves it aside --
       and the STATEMENT never sees that, so the 184 call sites that name this
       tier's harts as [(CID := ...)] keep working.  Introducing the new hart
       under a different name instead would force a [(CID := ...)] annotation on
       every hart-indexed term the body writes out ([tp_pin m], [rget m rs]);
       with the rename the body below is UNCHANGED. *)
    rename CID into CID0.
    iIntros (CID Hs σ Hpceq) "Hsc Hcap Hfile Hnpc [Hreg Hmem]".
    iDestruct "Hsc" as "[#Hhw Hsc2]".
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & #Hsenv & %HmisaS & %HmisaC &
        %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np & %HmisaA & %Hmisa_val0 & %Hmseccfg_val0 & #Hkmapb)".
    iDestruct (reg_valid_dq (CID := CID) with "Hreg Hmisa") as %Lmisa.
    iMod (reg_update (CID := CID) _ nextPC _ (add_vec_int pc 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s_pc := set_reg σ nextPC (add_vec_int pc 4)).
    assert (Hpcv : register_lookup PC s_pc.(sregs) = pc).
    { unfold s_pc; rewrite ?sregs_set_reg.
      rewrite irrelevant_register_set; [ exact Hpceq | vm_compute; reflexivity ]. }
    iDestruct (gpr_file_lookup_acc (tp_pin (CID := CID) m) (Regidx rs1) with "Hfile") as "[Hrac Hfb_rs1]".
    iDestruct (gpr_pt_value (CID := CID) rs1 (tp_pin (CID := CID) m (Regidx rs1)) s_pc with "Hreg Hrac") as %Lva.
    iDestruct ("Hfb_rs1" with "Hrac") as "Hfile".
    iDestruct (gpr_file_lookup_acc (tp_pin (CID := CID) m) (Regidx rs2) with "Hfile") as "[Hrbc Hfb_rs2]".
    iDestruct (gpr_pt_value (CID := CID) rs2 (tp_pin (CID := CID) m (Regidx rs2)) s_pc with "Hreg Hrbc") as %Lvb.
    iDestruct ("Hfb_rs2" with "Hrbc") as "Hfile".
    iMod (reg_update (CID := CID) _ nextPC _ (add_vec pc (sign_extend' 64 imm)) with "Hreg Hnpc") as "[Hreg Hnpc]".
    iModIntro.
    iExists (set_reg s_pc nextPC (add_vec pc (sign_extend' 64 imm))).
    iSplitR.
    { iPureIntro. rewrite Hpceq. fold s_pc.
      assert (Htk : zopz0zI_u (rvv rs1 s_pc) (rvv rs2 s_pc) = true)
        by (unfold rvv; rewrite Lva Lvb; exact (Hcmp_all CID)).
      assert (HzcaS : eq_vec (_get_Misa_C (register_lookup misa s_pc.(sregs))) ('b"1") = true).
      { unfold s_pc; rewrite ?sregs_set_reg.
        rewrite irrelevant_register_set; [ rewrite Lmisa; exact HmisaC | vm_compute; reflexivity ]. }
      epose proof (exec_execute_BTYPE_BLTU_taken_zca imm rs2 rs1 s_pc Htk) as Hred.
      rewrite Hpcv in Hred. exact (Hred Hal0 (exec_currentlyEnabled_Zca s_pc HzcaS)). }
    iSplitL "Hreg Hmem". { unfold s_pc; rewrite ?sregs_set_reg ?mem_set_reg. iFrame "Hreg Hmem". }
    iIntros "Hhs' Hpc'".
    assert (Lnpc : register_lookup nextPC
             (set_reg s_pc nextPC (add_vec pc (sign_extend' 64 imm))).(sregs)
             = add_vec pc (sign_extend' 64 imm))
      by (rewrite ?sregs_set_reg; rewrite register_lookup_set; reflexivity).
    iEval (rewrite Lnpc) in "Hpc'".
    iNext.
    iDestruct (sie_cap_gpr_join (CID := CID) with "Hhs' [$Hhw $Hsc2] Hcap Hfile") as "Hcg".
    iApply ("Hcont" $! CID with "[] Hcg [$Hpc' $Hnpc]").
    iPureIntro. exact Hs.
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
    iApply (wp_instr_s_sconf m n b pc false
              (BTYPE (imm, Regidx rs2, Regidx rs1, BGEU))
              with "Hcg Hpc Hinstr").
    (* FREE THE NAME [CID] FOR THE REBOUND HART.  A section variable is an
       ordinary context entry inside a proof, so [rename] moves it aside --
       and the STATEMENT never sees that, so the 184 call sites that name this
       tier's harts as [(CID := ...)] keep working.  Introducing the new hart
       under a different name instead would force a [(CID := ...)] annotation on
       every hart-indexed term the body writes out ([tp_pin m], [rget m rs]);
       with the rename the body below is UNCHANGED. *)
    rename CID into CID0.
    iIntros (CID Hs σ Hpceq) "Hsc Hcap Hfile Hnpc [Hreg Hmem]".
    iDestruct "Hsc" as "[#Hhw Hsc2]".
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & #Hsenv & %HmisaS & %HmisaC &
        %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np & %HmisaA & %Hmisa_val0 & %Hmseccfg_val0 & #Hkmapb)".
    iDestruct (reg_valid_dq (CID := CID) with "Hreg Hmisa") as %Lmisa.
    iMod (reg_update (CID := CID) _ nextPC _ (add_vec_int pc 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s_pc := set_reg σ nextPC (add_vec_int pc 4)).
    assert (Hpcv : register_lookup PC s_pc.(sregs) = pc).
    { unfold s_pc; rewrite ?sregs_set_reg.
      rewrite irrelevant_register_set; [ exact Hpceq | vm_compute; reflexivity ]. }
    iDestruct (gpr_file_lookup_acc (tp_pin (CID := CID) m) (Regidx rs1) with "Hfile") as "[Hrac Hfb_rs1]".
    iDestruct (gpr_pt_value (CID := CID) rs1 (tp_pin (CID := CID) m (Regidx rs1)) s_pc with "Hreg Hrac") as %Lva.
    iDestruct ("Hfb_rs1" with "Hrac") as "Hfile".
    iDestruct (gpr_file_lookup_acc (tp_pin (CID := CID) m) (Regidx rs2) with "Hfile") as "[Hrbc Hfb_rs2]".
    iDestruct (gpr_pt_value (CID := CID) rs2 (tp_pin (CID := CID) m (Regidx rs2)) s_pc with "Hreg Hrbc") as %Lvb.
    iDestruct ("Hfb_rs2" with "Hrbc") as "Hfile".
    iMod (reg_update (CID := CID) _ nextPC _ (add_vec pc (sign_extend' 64 imm)) with "Hreg Hnpc") as "[Hreg Hnpc]".
    iModIntro.
    iExists (set_reg s_pc nextPC (add_vec pc (sign_extend' 64 imm))).
    iSplitR.
    { iPureIntro. rewrite Hpceq. fold s_pc.
      assert (Htk : zopz0zKzJ_u (rvv rs1 s_pc) (rvv rs2 s_pc) = true)
        by (unfold rvv; rewrite Lva Lvb; exact (Hcmp_all CID)).
      assert (HzcaS : eq_vec (_get_Misa_C (register_lookup misa s_pc.(sregs))) ('b"1") = true).
      { unfold s_pc; rewrite ?sregs_set_reg.
        rewrite irrelevant_register_set; [ rewrite Lmisa; exact HmisaC | vm_compute; reflexivity ]. }
      epose proof (exec_execute_BTYPE_BGEU_taken_zca imm rs2 rs1 s_pc Htk) as Hred.
      rewrite Hpcv in Hred. exact (Hred Hal0 (exec_currentlyEnabled_Zca s_pc HzcaS)). }
    iSplitL "Hreg Hmem". { unfold s_pc; rewrite ?sregs_set_reg ?mem_set_reg. iFrame "Hreg Hmem". }
    iIntros "Hhs' Hpc'".
    assert (Lnpc : register_lookup nextPC
             (set_reg s_pc nextPC (add_vec pc (sign_extend' 64 imm))).(sregs)
             = add_vec pc (sign_extend' 64 imm))
      by (rewrite ?sregs_set_reg; rewrite register_lookup_set; reflexivity).
    iEval (rewrite Lnpc) in "Hpc'".
    iNext.
    iDestruct (sie_cap_gpr_join (CID := CID) with "Hhs' [$Hhw $Hsc2] Hcap Hfile") as "Hcg".
    iApply ("Hcont" $! CID with "[] Hcg [$Hpc' $Hnpc]").
    iPureIntro. exact Hs.
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
    iApply (wp_instr_s_sconf m n b pc false
              (BTYPE (imm, Regidx rs2, Regidx rs1, BGE))
              with "Hcg Hpc Hinstr").
    (* FREE THE NAME [CID] FOR THE REBOUND HART.  A section variable is an
       ordinary context entry inside a proof, so [rename] moves it aside --
       and the STATEMENT never sees that, so the 184 call sites that name this
       tier's harts as [(CID := ...)] keep working.  Introducing the new hart
       under a different name instead would force a [(CID := ...)] annotation on
       every hart-indexed term the body writes out ([tp_pin m], [rget m rs]);
       with the rename the body below is UNCHANGED. *)
    rename CID into CID0.
    iIntros (CID Hs σ Hpceq) "Hsc Hcap Hfile Hnpc [Hreg Hmem]".
    iMod (reg_update (CID := CID) _ nextPC _ (add_vec_int pc 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s_pc := set_reg σ nextPC (add_vec_int pc 4)).
    iDestruct (gpr_file_lookup_acc (tp_pin (CID := CID) m) (Regidx rs1) with "Hfile") as "[Hrac Hfb_rs1]".
    iDestruct (gpr_pt_value (CID := CID) rs1 (tp_pin (CID := CID) m (Regidx rs1)) s_pc with "Hreg Hrac") as %Lva.
    iDestruct ("Hfb_rs1" with "Hrac") as "Hfile".
    iDestruct (gpr_file_lookup_acc (tp_pin (CID := CID) m) (Regidx rs2) with "Hfile") as "[Hrbc Hfb_rs2]".
    iDestruct (gpr_pt_value (CID := CID) rs2 (tp_pin (CID := CID) m (Regidx rs2)) s_pc with "Hreg Hrbc") as %Lvb.
    iDestruct ("Hfb_rs2" with "Hrbc") as "Hfile".
    iModIntro. iExists s_pc.
    iSplitR.
    { iPureIntro. rewrite Hpceq. fold s_pc.
      apply exec_execute_BTYPE_BGE_fall. unfold rvv. rewrite Lva Lvb. exact (Hcmp_all CID). }
    iSplitL "Hreg Hmem". { unfold s_pc; rewrite ?sregs_set_reg ?mem_set_reg. iFrame "Hreg Hmem". }
    iIntros "Hhs' Hpc'".
    assert (Lnpc : register_lookup nextPC s_pc.(sregs) = add_vec_int pc 4)
      by (unfold s_pc; rewrite register_lookup_set; reflexivity).
    iEval (rewrite Lnpc) in "Hpc'".
    iDestruct (sie_cap_gpr_join (CID := CID) with "Hhs' Hsc Hcap Hfile") as "Hcg".
    iApply ("Hcont" $! CID with "[] Hcg [$Hpc' $Hnpc]").
    iPureIntro. exact Hs.
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
    iApply (wp_instr_s_sconf m n b pc false
              (BTYPE (imm, Regidx rs2, Regidx rs1, BGE))
              with "Hcg Hpc Hinstr").
    (* FREE THE NAME [CID] FOR THE REBOUND HART.  A section variable is an
       ordinary context entry inside a proof, so [rename] moves it aside --
       and the STATEMENT never sees that, so the 184 call sites that name this
       tier's harts as [(CID := ...)] keep working.  Introducing the new hart
       under a different name instead would force a [(CID := ...)] annotation on
       every hart-indexed term the body writes out ([tp_pin m], [rget m rs]);
       with the rename the body below is UNCHANGED. *)
    rename CID into CID0.
    iIntros (CID Hs σ Hpceq) "Hsc Hcap Hfile Hnpc [Hreg Hmem]".
    iDestruct "Hsc" as "[#Hhw Hsc2]".
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & #Hsenv & %HmisaS & %HmisaC &
        %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np & %HmisaA & %Hmisa_val0 & %Hmseccfg_val0 & #Hkmapb)".
    iDestruct (reg_valid_dq (CID := CID) with "Hreg Hmisa") as %Lmisa.
    iMod (reg_update (CID := CID) _ nextPC _ (add_vec_int pc 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s_pc := set_reg σ nextPC (add_vec_int pc 4)).
    assert (Hpcv : register_lookup PC s_pc.(sregs) = pc).
    { unfold s_pc; rewrite ?sregs_set_reg.
      rewrite irrelevant_register_set; [ exact Hpceq | vm_compute; reflexivity ]. }
    iDestruct (gpr_file_lookup_acc (tp_pin (CID := CID) m) (Regidx rs1) with "Hfile") as "[Hrac Hfb_rs1]".
    iDestruct (gpr_pt_value (CID := CID) rs1 (tp_pin (CID := CID) m (Regidx rs1)) s_pc with "Hreg Hrac") as %Lva.
    iDestruct ("Hfb_rs1" with "Hrac") as "Hfile".
    iDestruct (gpr_file_lookup_acc (tp_pin (CID := CID) m) (Regidx rs2) with "Hfile") as "[Hrbc Hfb_rs2]".
    iDestruct (gpr_pt_value (CID := CID) rs2 (tp_pin (CID := CID) m (Regidx rs2)) s_pc with "Hreg Hrbc") as %Lvb.
    iDestruct ("Hfb_rs2" with "Hrbc") as "Hfile".
    iMod (reg_update (CID := CID) _ nextPC _ (add_vec pc (sign_extend' 64 imm)) with "Hreg Hnpc") as "[Hreg Hnpc]".
    iModIntro.
    iExists (set_reg s_pc nextPC (add_vec pc (sign_extend' 64 imm))).
    iSplitR.
    { iPureIntro. rewrite Hpceq. fold s_pc.
      assert (Htk : zopz0zKzJ_s (rvv rs1 s_pc) (rvv rs2 s_pc) = true)
        by (unfold rvv; rewrite Lva Lvb; exact (Hcmp_all CID)).
      assert (HzcaS : eq_vec (_get_Misa_C (register_lookup misa s_pc.(sregs))) ('b"1") = true).
      { unfold s_pc; rewrite ?sregs_set_reg.
        rewrite irrelevant_register_set; [ rewrite Lmisa; exact HmisaC | vm_compute; reflexivity ]. }
      epose proof (exec_execute_BTYPE_BGE_taken_zca imm rs2 rs1 s_pc Htk) as Hred.
      rewrite Hpcv in Hred. exact (Hred Hal0 (exec_currentlyEnabled_Zca s_pc HzcaS)). }
    iSplitL "Hreg Hmem". { unfold s_pc; rewrite ?sregs_set_reg ?mem_set_reg. iFrame "Hreg Hmem". }
    iIntros "Hhs' Hpc'".
    assert (Lnpc : register_lookup nextPC
             (set_reg s_pc nextPC (add_vec pc (sign_extend' 64 imm))).(sregs)
             = add_vec pc (sign_extend' 64 imm))
      by (rewrite ?sregs_set_reg; rewrite register_lookup_set; reflexivity).
    iEval (rewrite Lnpc) in "Hpc'".
    iNext.
    iDestruct (sie_cap_gpr_join (CID := CID) with "Hhs' [$Hhw $Hsc2] Hcap Hfile") as "Hcg".
    iApply ("Hcont" $! CID with "[] Hcg [$Hpc' $Hnpc]").
    iPureIntro. exact Hs.
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
    iApply (wp_instr_s_sconf m n b pc false
              (BTYPE (imm, Regidx rs2, Regidx (mword_of_int 0), BGE))
              with "Hcg Hpc Hinstr").
    (* FREE THE NAME [CID] FOR THE REBOUND HART.  A section variable is an
       ordinary context entry inside a proof, so [rename] moves it aside --
       and the STATEMENT never sees that, so the 184 call sites that name this
       tier's harts as [(CID := ...)] keep working.  Introducing the new hart
       under a different name instead would force a [(CID := ...)] annotation on
       every hart-indexed term the body writes out ([tp_pin m], [rget m rs]);
       with the rename the body below is UNCHANGED. *)
    rename CID into CID0.
    iIntros (CID Hs σ Hpceq) "Hsc Hcap Hfile Hnpc [Hreg Hmem]".
    iMod (reg_update (CID := CID) _ nextPC _ (add_vec_int pc 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s_pc := set_reg σ nextPC (add_vec_int pc 4)).
    iDestruct (gpr_file_lookup_acc (tp_pin (CID := CID) m) (Regidx rs2) with "Hfile") as "[Hrbc Hfb_rs2]".
    iDestruct (gpr_pt_value (CID := CID) rs2 (tp_pin (CID := CID) m (Regidx rs2)) s_pc with "Hreg Hrbc") as %Lvb.
    iDestruct ("Hfb_rs2" with "Hrbc") as "Hfile".
    iModIntro. iExists s_pc.
    iSplitR.
    { iPureIntro. rewrite Hpceq. fold s_pc.
      apply exec_execute_BTYPE_BGE_fall. unfold rvv. rewrite Lvb.
      replace (Z.eqb (uint (mword_of_int 0 : mword 5)) 0) with true
        by (vm_compute; reflexivity).
      cbn match. exact (Hcmp_all CID). }
    iSplitL "Hreg Hmem". { unfold s_pc; rewrite ?sregs_set_reg ?mem_set_reg. iFrame "Hreg Hmem". }
    iIntros "Hhs' Hpc'".
    assert (Lnpc : register_lookup nextPC s_pc.(sregs) = add_vec_int pc 4)
      by (unfold s_pc; rewrite register_lookup_set; reflexivity).
    iEval (rewrite Lnpc) in "Hpc'".
    iDestruct (sie_cap_gpr_join (CID := CID) with "Hhs' Hsc Hcap Hfile") as "Hcg".
    iApply ("Hcont" $! CID with "[] Hcg [$Hpc' $Hnpc]").
    iPureIntro. exact Hs.
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
    iApply (wp_instr_s_sconf m n b pc false
              (BTYPE (imm, Regidx (mword_of_int 0), Regidx rs1, BLT))
              with "Hcg Hpc Hinstr").
    (* FREE THE NAME [CID] FOR THE REBOUND HART.  A section variable is an
       ordinary context entry inside a proof, so [rename] moves it aside --
       and the STATEMENT never sees that, so the 184 call sites that name this
       tier's harts as [(CID := ...)] keep working.  Introducing the new hart
       under a different name instead would force a [(CID := ...)] annotation on
       every hart-indexed term the body writes out ([tp_pin m], [rget m rs]);
       with the rename the body below is UNCHANGED. *)
    rename CID into CID0.
    iIntros (CID Hs σ Hpceq) "Hsc Hcap Hfile Hnpc [Hreg Hmem]".
    iMod (reg_update (CID := CID) _ nextPC _ (add_vec_int pc 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s_pc := set_reg σ nextPC (add_vec_int pc 4)).
    iDestruct (gpr_file_lookup_acc (tp_pin (CID := CID) m) (Regidx rs1) with "Hfile") as "[Hrac Hfb_rs1]".
    iDestruct (gpr_pt_value (CID := CID) rs1 (tp_pin (CID := CID) m (Regidx rs1)) s_pc with "Hreg Hrac") as %Lva.
    iDestruct ("Hfb_rs1" with "Hrac") as "Hfile".
    iModIntro. iExists s_pc.
    iSplitR.
    { iPureIntro. rewrite Hpceq. fold s_pc.
      apply exec_execute_BTYPE_BLT_fall. unfold rvv. rewrite Lva.
      replace (Z.eqb (uint (mword_of_int 0 : mword 5)) 0) with true
        by (vm_compute; reflexivity).
      cbn match. exact (Hcmp_all CID). }
    iSplitL "Hreg Hmem". { unfold s_pc; rewrite ?sregs_set_reg ?mem_set_reg. iFrame "Hreg Hmem". }
    iIntros "Hhs' Hpc'".
    assert (Lnpc : register_lookup nextPC s_pc.(sregs) = add_vec_int pc 4)
      by (unfold s_pc; rewrite register_lookup_set; reflexivity).
    iEval (rewrite Lnpc) in "Hpc'".
    iDestruct (sie_cap_gpr_join (CID := CID) with "Hhs' Hsc Hcap Hfile") as "Hcg".
    iApply ("Hcont" $! CID with "[] Hcg [$Hpc' $Hnpc]").
    iPureIntro. exact Hs.
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
    iApply (wp_instr_s_sconf m n b pc false
              (BTYPE (imm, Regidx (mword_of_int 0), Regidx rs1, BLT))
              with "Hcg Hpc Hinstr").
    (* FREE THE NAME [CID] FOR THE REBOUND HART.  A section variable is an
       ordinary context entry inside a proof, so [rename] moves it aside --
       and the STATEMENT never sees that, so the 184 call sites that name this
       tier's harts as [(CID := ...)] keep working.  Introducing the new hart
       under a different name instead would force a [(CID := ...)] annotation on
       every hart-indexed term the body writes out ([tp_pin m], [rget m rs]);
       with the rename the body below is UNCHANGED. *)
    rename CID into CID0.
    iIntros (CID Hs σ Hpceq) "Hsc Hcap Hfile Hnpc [Hreg Hmem]".
    iDestruct "Hsc" as "[#Hhw Hsc2]".
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & #Hsenv & %HmisaS & %HmisaC &
        %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np & %HmisaA & %Hmisa_val0 & %Hmseccfg_val0 & #Hkmapb)".
    iDestruct (reg_valid_dq (CID := CID) with "Hreg Hmisa") as %Lmisa.
    iMod (reg_update (CID := CID) _ nextPC _ (add_vec_int pc 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s_pc := set_reg σ nextPC (add_vec_int pc 4)).
    assert (Hpcv : register_lookup PC s_pc.(sregs) = pc).
    { unfold s_pc; rewrite ?sregs_set_reg.
      rewrite irrelevant_register_set; [ exact Hpceq | vm_compute; reflexivity ]. }
    iDestruct (gpr_file_lookup_acc (tp_pin (CID := CID) m) (Regidx rs1) with "Hfile") as "[Hrac Hfb_rs1]".
    iDestruct (gpr_pt_value (CID := CID) rs1 (tp_pin (CID := CID) m (Regidx rs1)) s_pc with "Hreg Hrac") as %Lva.
    iDestruct ("Hfb_rs1" with "Hrac") as "Hfile".
    iMod (reg_update (CID := CID) _ nextPC _ (add_vec pc (sign_extend' 64 imm)) with "Hreg Hnpc") as "[Hreg Hnpc]".
    iModIntro.
    iExists (set_reg s_pc nextPC (add_vec pc (sign_extend' 64 imm))).
    iSplitR.
    { iPureIntro. rewrite Hpceq. fold s_pc.
      assert (Htk : zopz0zI_s (rvv rs1 s_pc) (rvv (mword_of_int 0 : mword 5) s_pc) = true).
      { unfold rvv. rewrite Lva.
        replace (Z.eqb (uint (mword_of_int 0 : mword 5)) 0) with true
          by (vm_compute; reflexivity).
        cbn match. exact (Hcmp_all CID). }
      assert (HzcaS : eq_vec (_get_Misa_C (register_lookup misa s_pc.(sregs))) ('b"1") = true).
      { unfold s_pc; rewrite ?sregs_set_reg.
        rewrite irrelevant_register_set; [ rewrite Lmisa; exact HmisaC | vm_compute; reflexivity ]. }
      epose proof (exec_execute_BTYPE_BLT_taken_zca imm (mword_of_int 0) rs1 s_pc Htk) as Hred.
      rewrite Hpcv in Hred. exact (Hred Hal0 (exec_currentlyEnabled_Zca s_pc HzcaS)). }
    iSplitL "Hreg Hmem". { unfold s_pc; rewrite ?sregs_set_reg ?mem_set_reg. iFrame "Hreg Hmem". }
    iIntros "Hhs' Hpc'".
    assert (Lnpc : register_lookup nextPC
             (set_reg s_pc nextPC (add_vec pc (sign_extend' 64 imm))).(sregs)
             = add_vec pc (sign_extend' 64 imm))
      by (rewrite ?sregs_set_reg; rewrite register_lookup_set; reflexivity).
    iEval (rewrite Lnpc) in "Hpc'".
    iNext.
    iDestruct (sie_cap_gpr_join (CID := CID) with "Hhs' [$Hhw $Hsc2] Hcap Hfile") as "Hcg".
    iApply ("Hcont" $! CID with "[] Hcg [$Hpc' $Hnpc]").
    iPureIntro. exact Hs.
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
    iApply (wp_instr_s_sconf m n b pc false
              (BTYPE (imm, Regidx rs2, Regidx (mword_of_int 0), BLT))
              with "Hcg Hpc Hinstr").
    (* FREE THE NAME [CID] FOR THE REBOUND HART.  A section variable is an
       ordinary context entry inside a proof, so [rename] moves it aside --
       and the STATEMENT never sees that, so the 184 call sites that name this
       tier's harts as [(CID := ...)] keep working.  Introducing the new hart
       under a different name instead would force a [(CID := ...)] annotation on
       every hart-indexed term the body writes out ([tp_pin m], [rget m rs]);
       with the rename the body below is UNCHANGED. *)
    rename CID into CID0.
    iIntros (CID Hs σ Hpceq) "Hsc Hcap Hfile Hnpc [Hreg Hmem]".
    iMod (reg_update (CID := CID) _ nextPC _ (add_vec_int pc 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s_pc := set_reg σ nextPC (add_vec_int pc 4)).
    iDestruct (gpr_file_lookup_acc (tp_pin (CID := CID) m) (Regidx rs2) with "Hfile") as "[Hrbc Hfb_rs2]".
    iDestruct (gpr_pt_value (CID := CID) rs2 (tp_pin (CID := CID) m (Regidx rs2)) s_pc with "Hreg Hrbc") as %Lvb.
    iDestruct ("Hfb_rs2" with "Hrbc") as "Hfile".
    iModIntro. iExists s_pc.
    iSplitR.
    { iPureIntro. rewrite Hpceq. fold s_pc.
      apply exec_execute_BTYPE_BLT_fall.
      unfold rvv. rewrite Lvb.
      replace (Z.eqb (uint (mword_of_int 0 : mword 5)) 0) with true
        by (vm_compute; reflexivity).
      cbn match. exact (Hcmp_all CID). }
    iSplitL "Hreg Hmem". { unfold s_pc; rewrite ?sregs_set_reg ?mem_set_reg. iFrame "Hreg Hmem". }
    iIntros "Hhs' Hpc'".
    assert (Lnpc : register_lookup nextPC s_pc.(sregs) = add_vec_int pc 4)
      by (unfold s_pc; rewrite register_lookup_set; reflexivity).
    iEval (rewrite Lnpc) in "Hpc'".
    iDestruct (sie_cap_gpr_join (CID := CID) with "Hhs' Hsc Hcap Hfile") as "Hcg".
    iApply ("Hcont" $! CID with "[] Hcg [$Hpc' $Hnpc]").
    iPureIntro. exact Hs.
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
    iApply (wp_instr_s_sconf m n b pc false
              (BTYPE (imm, Regidx rs2, Regidx (mword_of_int 0), BLT))
              with "Hcg Hpc Hinstr").
    (* FREE THE NAME [CID] FOR THE REBOUND HART.  A section variable is an
       ordinary context entry inside a proof, so [rename] moves it aside --
       and the STATEMENT never sees that, so the 184 call sites that name this
       tier's harts as [(CID := ...)] keep working.  Introducing the new hart
       under a different name instead would force a [(CID := ...)] annotation on
       every hart-indexed term the body writes out ([tp_pin m], [rget m rs]);
       with the rename the body below is UNCHANGED. *)
    rename CID into CID0.
    iIntros (CID Hs σ Hpceq) "Hsc Hcap Hfile Hnpc [Hreg Hmem]".
    iDestruct "Hsc" as "[#Hhw Hsc2]".
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & #Hsenv & %HmisaS & %HmisaC &
        %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np & %HmisaA & %Hmisa_val0 & %Hmseccfg_val0 & #Hkmapb)".
    iDestruct (reg_valid_dq (CID := CID) with "Hreg Hmisa") as %Lmisa.
    iMod (reg_update (CID := CID) _ nextPC _ (add_vec_int pc 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s_pc := set_reg σ nextPC (add_vec_int pc 4)).
    assert (Hpcv : register_lookup PC s_pc.(sregs) = pc).
    { unfold s_pc; rewrite ?sregs_set_reg.
      rewrite irrelevant_register_set; [ exact Hpceq | vm_compute; reflexivity ]. }
    iDestruct (gpr_file_lookup_acc (tp_pin (CID := CID) m) (Regidx rs2) with "Hfile") as "[Hrbc Hfb_rs2]".
    iDestruct (gpr_pt_value (CID := CID) rs2 (tp_pin (CID := CID) m (Regidx rs2)) s_pc with "Hreg Hrbc") as %Lvb.
    iDestruct ("Hfb_rs2" with "Hrbc") as "Hfile".
    iMod (reg_update (CID := CID) _ nextPC _ (add_vec pc (sign_extend' 64 imm)) with "Hreg Hnpc") as "[Hreg Hnpc]".
    iModIntro.
    iExists (set_reg s_pc nextPC (add_vec pc (sign_extend' 64 imm))).
    iSplitR.
    { iPureIntro. rewrite Hpceq. fold s_pc.
      assert (Htk : zopz0zI_s (rvv (mword_of_int 0 : mword 5) s_pc)
                              (rvv rs2 s_pc) = true).
      { unfold rvv. rewrite Lvb.
        replace (Z.eqb (uint (mword_of_int 0 : mword 5)) 0) with true
          by (vm_compute; reflexivity).
        cbn match. exact (Hcmp_all CID). }
      assert (HzcaS : eq_vec (_get_Misa_C (register_lookup misa s_pc.(sregs))) ('b"1") = true).
      { unfold s_pc; rewrite ?sregs_set_reg.
        rewrite irrelevant_register_set; [ rewrite Lmisa; exact HmisaC | vm_compute; reflexivity ]. }
      epose proof (exec_execute_BTYPE_BLT_taken_zca imm rs2
                     (mword_of_int 0 : mword 5) s_pc Htk) as Hred.
      rewrite Hpcv in Hred. exact (Hred Hal0 (exec_currentlyEnabled_Zca s_pc HzcaS)). }
    iSplitL "Hreg Hmem". { unfold s_pc; rewrite ?sregs_set_reg ?mem_set_reg. iFrame "Hreg Hmem". }
    iIntros "Hhs' Hpc'".
    assert (Lnpc : register_lookup nextPC
             (set_reg s_pc nextPC (add_vec pc (sign_extend' 64 imm))).(sregs)
             = add_vec pc (sign_extend' 64 imm))
      by (rewrite ?sregs_set_reg; rewrite register_lookup_set; reflexivity).
    iEval (rewrite Lnpc) in "Hpc'".
    iNext.
    iDestruct (sie_cap_gpr_join (CID := CID) with "Hhs' [$Hhw $Hsc2] Hcap Hfile") as "Hcg".
    iApply ("Hcont" $! CID with "[] Hcg [$Hpc' $Hnpc]").
    iPureIntro. exact Hs.
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
    iApply (wp_instr_s_sconf m n b pc false
              (BTYPE (imm, Regidx (mword_of_int 0), Regidx rs1, BGE))
              with "Hcg Hpc Hinstr").
    (* FREE THE NAME [CID] FOR THE REBOUND HART.  A section variable is an
       ordinary context entry inside a proof, so [rename] moves it aside --
       and the STATEMENT never sees that, so the 184 call sites that name this
       tier's harts as [(CID := ...)] keep working.  Introducing the new hart
       under a different name instead would force a [(CID := ...)] annotation on
       every hart-indexed term the body writes out ([tp_pin m], [rget m rs]);
       with the rename the body below is UNCHANGED. *)
    rename CID into CID0.
    iIntros (CID Hs σ Hpceq) "Hsc Hcap Hfile Hnpc [Hreg Hmem]".
    iMod (reg_update (CID := CID) _ nextPC _ (add_vec_int pc 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s_pc := set_reg σ nextPC (add_vec_int pc 4)).
    iDestruct (gpr_file_lookup_acc (tp_pin (CID := CID) m) (Regidx rs1) with "Hfile") as "[Hrac Hfb_rs1]".
    iDestruct (gpr_pt_value (CID := CID) rs1 (tp_pin (CID := CID) m (Regidx rs1)) s_pc with "Hreg Hrac") as %Lva.
    iDestruct ("Hfb_rs1" with "Hrac") as "Hfile".
    iModIntro. iExists s_pc.
    iSplitR.
    { iPureIntro. rewrite Hpceq. fold s_pc.
      apply exec_execute_BTYPE_BGE_fall. unfold rvv. rewrite Lva.
      replace (Z.eqb (uint (mword_of_int 0 : mword 5)) 0) with true
        by (vm_compute; reflexivity).
      cbn match. exact (Hcmp_all CID). }
    iSplitL "Hreg Hmem". { unfold s_pc; rewrite ?sregs_set_reg ?mem_set_reg. iFrame "Hreg Hmem". }
    iIntros "Hhs' Hpc'".
    assert (Lnpc : register_lookup nextPC s_pc.(sregs) = add_vec_int pc 4)
      by (unfold s_pc; rewrite register_lookup_set; reflexivity).
    iEval (rewrite Lnpc) in "Hpc'".
    iDestruct (sie_cap_gpr_join (CID := CID) with "Hhs' Hsc Hcap Hfile") as "Hcg".
    iApply ("Hcont" $! CID with "[] Hcg [$Hpc' $Hnpc]").
    iPureIntro. exact Hs.
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
    iApply (wp_instr_s_sconf m n b pc false
              (BTYPE (imm, Regidx (mword_of_int 0), Regidx rs1, BGE))
              with "Hcg Hpc Hinstr").
    (* FREE THE NAME [CID] FOR THE REBOUND HART.  A section variable is an
       ordinary context entry inside a proof, so [rename] moves it aside --
       and the STATEMENT never sees that, so the 184 call sites that name this
       tier's harts as [(CID := ...)] keep working.  Introducing the new hart
       under a different name instead would force a [(CID := ...)] annotation on
       every hart-indexed term the body writes out ([tp_pin m], [rget m rs]);
       with the rename the body below is UNCHANGED. *)
    rename CID into CID0.
    iIntros (CID Hs σ Hpceq) "Hsc Hcap Hfile Hnpc [Hreg Hmem]".
    iDestruct "Hsc" as "[#Hhw Hsc2]".
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & #Hsenv & %HmisaS & %HmisaC &
        %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np & %HmisaA & %Hmisa_val0 & %Hmseccfg_val0 & #Hkmapb)".
    iDestruct (reg_valid_dq (CID := CID) with "Hreg Hmisa") as %Lmisa.
    iMod (reg_update (CID := CID) _ nextPC _ (add_vec_int pc 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s_pc := set_reg σ nextPC (add_vec_int pc 4)).
    assert (Hpcv : register_lookup PC s_pc.(sregs) = pc).
    { unfold s_pc; rewrite ?sregs_set_reg.
      rewrite irrelevant_register_set; [ exact Hpceq | vm_compute; reflexivity ]. }
    iDestruct (gpr_file_lookup_acc (tp_pin (CID := CID) m) (Regidx rs1) with "Hfile") as "[Hrac Hfb_rs1]".
    iDestruct (gpr_pt_value (CID := CID) rs1 (tp_pin (CID := CID) m (Regidx rs1)) s_pc with "Hreg Hrac") as %Lva.
    iDestruct ("Hfb_rs1" with "Hrac") as "Hfile".
    iMod (reg_update (CID := CID) _ nextPC _ (add_vec pc (sign_extend' 64 imm)) with "Hreg Hnpc") as "[Hreg Hnpc]".
    iModIntro.
    iExists (set_reg s_pc nextPC (add_vec pc (sign_extend' 64 imm))).
    iSplitR.
    { iPureIntro. rewrite Hpceq. fold s_pc.
      assert (Htk : zopz0zKzJ_s (rvv rs1 s_pc) (rvv (mword_of_int 0 : mword 5) s_pc) = true).
      { unfold rvv. rewrite Lva.
        replace (Z.eqb (uint (mword_of_int 0 : mword 5)) 0) with true
          by (vm_compute; reflexivity).
        cbn match. exact (Hcmp_all CID). }
      assert (HzcaS : eq_vec (_get_Misa_C (register_lookup misa s_pc.(sregs))) ('b"1") = true).
      { unfold s_pc; rewrite ?sregs_set_reg.
        rewrite irrelevant_register_set; [ rewrite Lmisa; exact HmisaC | vm_compute; reflexivity ]. }
      epose proof (exec_execute_BTYPE_BGE_taken_zca imm (mword_of_int 0) rs1 s_pc Htk) as Hred.
      rewrite Hpcv in Hred. exact (Hred Hal0 (exec_currentlyEnabled_Zca s_pc HzcaS)). }
    iSplitL "Hreg Hmem". { unfold s_pc; rewrite ?sregs_set_reg ?mem_set_reg. iFrame "Hreg Hmem". }
    iIntros "Hhs' Hpc'".
    assert (Lnpc : register_lookup nextPC
             (set_reg s_pc nextPC (add_vec pc (sign_extend' 64 imm))).(sregs)
             = add_vec pc (sign_extend' 64 imm))
      by (rewrite ?sregs_set_reg; rewrite register_lookup_set; reflexivity).
    iEval (rewrite Lnpc) in "Hpc'".
    iNext.
    iDestruct (sie_cap_gpr_join (CID := CID) with "Hhs' [$Hhw $Hsc2] Hcap Hfile") as "Hcg".
    iApply ("Hcont" $! CID with "[] Hcg [$Hpc' $Hnpc]").
    iPureIntro. exact Hs.
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
    iApply (wp_instr_s_sconf m n b pc false
              (BTYPE (imm, Regidx rs2, Regidx (mword_of_int 0), BGE))
              with "Hcg Hpc Hinstr").
    (* FREE THE NAME [CID] FOR THE REBOUND HART.  A section variable is an
       ordinary context entry inside a proof, so [rename] moves it aside --
       and the STATEMENT never sees that, so the 184 call sites that name this
       tier's harts as [(CID := ...)] keep working.  Introducing the new hart
       under a different name instead would force a [(CID := ...)] annotation on
       every hart-indexed term the body writes out ([tp_pin m], [rget m rs]);
       with the rename the body below is UNCHANGED. *)
    rename CID into CID0.
    iIntros (CID Hs σ Hpceq) "Hsc Hcap Hfile Hnpc [Hreg Hmem]".
    iDestruct "Hsc" as "[#Hhw Hsc2]".
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & #Hsenv & %HmisaS & %HmisaC &
        %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np & %HmisaA & %Hmisa_val0 & %Hmseccfg_val0 & #Hkmapb)".
    iDestruct (reg_valid_dq (CID := CID) with "Hreg Hmisa") as %Lmisa.
    iMod (reg_update (CID := CID) _ nextPC _ (add_vec_int pc 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s_pc := set_reg σ nextPC (add_vec_int pc 4)).
    assert (Hpcv : register_lookup PC s_pc.(sregs) = pc).
    { unfold s_pc; rewrite ?sregs_set_reg.
      rewrite irrelevant_register_set; [ exact Hpceq | vm_compute; reflexivity ]. }
    iDestruct (gpr_file_lookup_acc (tp_pin (CID := CID) m) (Regidx rs2) with "Hfile") as "[Hrbc Hfb_rs2]".
    iDestruct (gpr_pt_value (CID := CID) rs2 (tp_pin (CID := CID) m (Regidx rs2)) s_pc with "Hreg Hrbc") as %Lvb.
    iDestruct ("Hfb_rs2" with "Hrbc") as "Hfile".
    iMod (reg_update (CID := CID) _ nextPC _ (add_vec pc (sign_extend' 64 imm)) with "Hreg Hnpc") as "[Hreg Hnpc]".
    iModIntro.
    iExists (set_reg s_pc nextPC (add_vec pc (sign_extend' 64 imm))).
    iSplitR.
    { iPureIntro. rewrite Hpceq. fold s_pc.
      assert (Htk : zopz0zKzJ_s (rvv (mword_of_int 0 : mword 5) s_pc) (rvv rs2 s_pc) = true).
      { unfold rvv. rewrite Lvb.
        replace (Z.eqb (uint (mword_of_int 0 : mword 5)) 0) with true
          by (vm_compute; reflexivity).
        cbn match. exact (Hcmp_all CID). }
      assert (HzcaS : eq_vec (_get_Misa_C (register_lookup misa s_pc.(sregs))) ('b"1") = true).
      { unfold s_pc; rewrite ?sregs_set_reg.
        rewrite irrelevant_register_set; [ rewrite Lmisa; exact HmisaC | vm_compute; reflexivity ]. }
      epose proof (exec_execute_BTYPE_BGE_taken_zca imm rs2 (mword_of_int 0) s_pc Htk) as Hred.
      rewrite Hpcv in Hred. exact (Hred Hal0 (exec_currentlyEnabled_Zca s_pc HzcaS)). }
    iSplitL "Hreg Hmem". { unfold s_pc; rewrite ?sregs_set_reg ?mem_set_reg. iFrame "Hreg Hmem". }
    iIntros "Hhs' Hpc'".
    assert (Lnpc : register_lookup nextPC
             (set_reg s_pc nextPC (add_vec pc (sign_extend' 64 imm))).(sregs)
             = add_vec pc (sign_extend' 64 imm))
      by (rewrite ?sregs_set_reg; rewrite register_lookup_set; reflexivity).
    iEval (rewrite Lnpc) in "Hpc'".
    iNext.
    iDestruct (sie_cap_gpr_join (CID := CID) with "Hhs' [$Hhw $Hsc2] Hcap Hfile") as "Hcg".
    iApply ("Hcont" $! CID with "[] Hcg [$Hpc' $Hnpc]").
    iPureIntro. exact Hs.
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
    iApply (wp_instr_s_sconf m n b pc true
              (BTYPE (sign_extend' 13 (concat_vec imm8 ('b"0")), zreg, creg2reg_idx rs, BEQ))
              with "Hcg Hpc Hinstr").
    (* FREE THE NAME [CID] FOR THE REBOUND HART.  A section variable is an
       ordinary context entry inside a proof, so [rename] moves it aside --
       and the STATEMENT never sees that, so the 184 call sites that name this
       tier's harts as [(CID := ...)] keep working.  Introducing the new hart
       under a different name instead would force a [(CID := ...)] annotation on
       every hart-indexed term the body writes out ([tp_pin m], [rget m rs]);
       with the rename the body below is UNCHANGED. *)
    rename CID into CID0.
    iIntros (CID Hs σ Hpceq) "Hsc Hcap Hfile Hnpc [Hreg Hmem]".
    iMod (reg_update (CID := CID) _ nextPC _ (add_vec_int pc 2) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s_pc := set_reg σ nextPC (add_vec_int pc 2)).
    iDestruct (gpr_file_lookup_acc (tp_pin (CID := CID) m) (Regidx rd1) with "Hfile") as "[Hrac Hfb_rd1]".
    iDestruct (gpr_pt_value (CID := CID) rd1 (tp_pin (CID := CID) m (Regidx rd1)) s_pc with "Hreg Hrac") as %Lva.
    iDestruct ("Hfb_rd1" with "Hrac") as "Hfile".
    iModIntro. iExists s_pc.
    iSplitR.
    { iPureIntro. rewrite Hpceq. fold s_pc. rewrite Hrs.
      change zreg with (Regidx (zero_extend' 5 ('b"00") : mword 5)).
      apply exec_execute_BTYPE_BEQ_fall. unfold rvv.
      rewrite Lva.
      replace (Z.eqb (uint (zero_extend' 5 ('b"00") : mword 5)) 0) with true
        by (vm_compute; reflexivity).
      (* the ambient hart is the one the callback was instantiated at *)
      cbn match. exact (Hcmp_all CID). }
    iSplitL "Hreg Hmem". { unfold s_pc; rewrite ?sregs_set_reg ?mem_set_reg. iFrame "Hreg Hmem". }
    iIntros "Hhs' Hpc'".
    assert (Lnpc : register_lookup nextPC s_pc.(sregs) = add_vec_int pc 2)
      by (unfold s_pc; rewrite register_lookup_set; reflexivity).
    iEval (rewrite Lnpc) in "Hpc'".
    iDestruct (sie_cap_gpr_join (CID := CID) with "Hhs' Hsc Hcap Hfile") as "Hcg".
    iApply ("Hcont" $! CID with "[] Hcg [$Hpc' $Hnpc]").
    iPureIntro. exact Hs.
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
    iApply (wp_instr_s_sconf m n b pc true
              (BTYPE (sign_extend' 13 (concat_vec imm8 ('b"0")), zreg, creg2reg_idx rs, BNE))
              with "Hcg Hpc Hinstr").
    (* FREE THE NAME [CID] FOR THE REBOUND HART.  A section variable is an
       ordinary context entry inside a proof, so [rename] moves it aside --
       and the STATEMENT never sees that, so the 184 call sites that name this
       tier's harts as [(CID := ...)] keep working.  Introducing the new hart
       under a different name instead would force a [(CID := ...)] annotation on
       every hart-indexed term the body writes out ([tp_pin m], [rget m rs]);
       with the rename the body below is UNCHANGED. *)
    rename CID into CID0.
    iIntros (CID Hs σ Hpceq) "Hsc Hcap Hfile Hnpc [Hreg Hmem]".
    iMod (reg_update (CID := CID) _ nextPC _ (add_vec_int pc 2) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s_pc := set_reg σ nextPC (add_vec_int pc 2)).
    iDestruct (gpr_file_lookup_acc (tp_pin (CID := CID) m) (Regidx rd1) with "Hfile") as "[Hrac Hfb_rd1]".
    iDestruct (gpr_pt_value (CID := CID) rd1 (tp_pin (CID := CID) m (Regidx rd1)) s_pc with "Hreg Hrac") as %Lva.
    iDestruct ("Hfb_rd1" with "Hrac") as "Hfile".
    iModIntro. iExists s_pc.
    iSplitR.
    { iPureIntro. rewrite Hpceq. fold s_pc. rewrite Hrs.
      change zreg with (Regidx (zero_extend' 5 ('b"00") : mword 5)).
      apply exec_execute_BTYPE_BNE_fall. unfold rvv.
      rewrite Lva.
      replace (Z.eqb (uint (zero_extend' 5 ('b"00") : mword 5)) 0) with true
        by (vm_compute; reflexivity).
      cbn match. exact (Hcmp_all CID). }
    iSplitL "Hreg Hmem". { unfold s_pc; rewrite ?sregs_set_reg ?mem_set_reg. iFrame "Hreg Hmem". }
    iIntros "Hhs' Hpc'".
    assert (Lnpc : register_lookup nextPC s_pc.(sregs) = add_vec_int pc 2)
      by (unfold s_pc; rewrite register_lookup_set; reflexivity).
    iEval (rewrite Lnpc) in "Hpc'".
    iDestruct (sie_cap_gpr_join (CID := CID) with "Hhs' Hsc Hcap Hfile") as "Hcg".
    iApply ("Hcont" $! CID with "[] Hcg [$Hpc' $Hnpc]").
    iPureIntro. exact Hs.
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
    iApply (wp_instr_s_sconf m n b pc false
              (BTYPE (imm, Regidx rs2, Regidx rs1, BEQ))
              with "Hcg Hpc Hinstr").
    (* FREE THE NAME [CID] FOR THE REBOUND HART.  A section variable is an
       ordinary context entry inside a proof, so [rename] moves it aside --
       and the STATEMENT never sees that, so the 184 call sites that name this
       tier's harts as [(CID := ...)] keep working.  Introducing the new hart
       under a different name instead would force a [(CID := ...)] annotation on
       every hart-indexed term the body writes out ([tp_pin m], [rget m rs]);
       with the rename the body below is UNCHANGED. *)
    rename CID into CID0.
    iIntros (CID Hs σ Hpceq) "Hsc Hcap Hfile Hnpc [Hreg Hmem]".
    iDestruct "Hsc" as "[#Hhw Hsc2]".
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & #Hsenv & %HmisaS & %HmisaC &
        %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np & %HmisaA & %Hmisa_val0 & %Hmseccfg_val0 & #Hkmapb)".
    iDestruct (reg_valid_dq (CID := CID) with "Hreg Hmisa") as %Lmisa.
    iMod (reg_update (CID := CID) _ nextPC _ (add_vec_int pc 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s_pc := set_reg σ nextPC (add_vec_int pc 4)).
    assert (Hpcv : register_lookup PC s_pc.(sregs) = pc).
    { unfold s_pc; rewrite ?sregs_set_reg.
      rewrite irrelevant_register_set; [ exact Hpceq | vm_compute; reflexivity ]. }
    iDestruct (gpr_file_lookup_acc (tp_pin (CID := CID) m) (Regidx rs1) with "Hfile") as "[Hrac Hfb_rs1]".
    iDestruct (gpr_pt_value (CID := CID) rs1 (tp_pin (CID := CID) m (Regidx rs1)) s_pc with "Hreg Hrac") as %Lva.
    iDestruct ("Hfb_rs1" with "Hrac") as "Hfile".
    iDestruct (gpr_file_lookup_acc (tp_pin (CID := CID) m) (Regidx rs2) with "Hfile") as "[Hrbc Hfb_rs2]".
    iDestruct (gpr_pt_value (CID := CID) rs2 (tp_pin (CID := CID) m (Regidx rs2)) s_pc with "Hreg Hrbc") as %Lvb.
    iDestruct ("Hfb_rs2" with "Hrbc") as "Hfile".
    iMod (reg_update (CID := CID) _ nextPC _ (add_vec pc (sign_extend' 64 imm)) with "Hreg Hnpc") as "[Hreg Hnpc]".
    iModIntro.
    iExists (set_reg s_pc nextPC (add_vec pc (sign_extend' 64 imm))).
    iSplitR.
    { iPureIntro. rewrite Hpceq. fold s_pc.
      assert (Htk : eq_vec (rvv rs1 s_pc) (rvv rs2 s_pc) = true)
        by (unfold rvv; rewrite Lva Lvb; exact (Hcmp_all CID)).
      assert (HzcaS : eq_vec (_get_Misa_C (register_lookup misa s_pc.(sregs))) ('b"1") = true).
      { unfold s_pc; rewrite ?sregs_set_reg.
        rewrite irrelevant_register_set; [ rewrite Lmisa; exact HmisaC | vm_compute; reflexivity ]. }
      epose proof (exec_execute_BTYPE_BEQ_taken_zca imm rs2 rs1 s_pc Htk) as Hred.
      rewrite Hpcv in Hred. exact (Hred Hal0 (exec_currentlyEnabled_Zca s_pc HzcaS)). }
    iSplitL "Hreg Hmem". { unfold s_pc; rewrite ?sregs_set_reg ?mem_set_reg. iFrame "Hreg Hmem". }
    iIntros "Hhs' Hpc'".
    assert (Lnpc : register_lookup nextPC
             (set_reg s_pc nextPC (add_vec pc (sign_extend' 64 imm))).(sregs)
             = add_vec pc (sign_extend' 64 imm))
      by (rewrite ?sregs_set_reg; rewrite register_lookup_set; reflexivity).
    iEval (rewrite Lnpc) in "Hpc'".
    iNext.
    iDestruct (sie_cap_gpr_join (CID := CID) with "Hhs' [$Hhw $Hsc2] Hcap Hfile") as "Hcg".
    iApply ("Hcont" $! CID with "[] Hcg [$Hpc' $Hnpc]").
    iPureIntro. exact Hs.
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
    iApply (wp_instr_s_sconf m n b pc false
              (BTYPE (imm, Regidx rs2, Regidx rs1, BNE))
              with "Hcg Hpc Hinstr").
    (* FREE THE NAME [CID] FOR THE REBOUND HART.  A section variable is an
       ordinary context entry inside a proof, so [rename] moves it aside --
       and the STATEMENT never sees that, so the 184 call sites that name this
       tier's harts as [(CID := ...)] keep working.  Introducing the new hart
       under a different name instead would force a [(CID := ...)] annotation on
       every hart-indexed term the body writes out ([tp_pin m], [rget m rs]);
       with the rename the body below is UNCHANGED. *)
    rename CID into CID0.
    iIntros (CID Hs σ Hpceq) "Hsc Hcap Hfile Hnpc [Hreg Hmem]".
    iDestruct "Hsc" as "[#Hhw Hsc2]".
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & #Hsenv & %HmisaS & %HmisaC &
        %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np & %HmisaA & %Hmisa_val0 & %Hmseccfg_val0 & #Hkmapb)".
    iDestruct (reg_valid_dq (CID := CID) with "Hreg Hmisa") as %Lmisa.
    iMod (reg_update (CID := CID) _ nextPC _ (add_vec_int pc 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s_pc := set_reg σ nextPC (add_vec_int pc 4)).
    assert (Hpcv : register_lookup PC s_pc.(sregs) = pc).
    { unfold s_pc; rewrite ?sregs_set_reg.
      rewrite irrelevant_register_set; [ exact Hpceq | vm_compute; reflexivity ]. }
    iDestruct (gpr_file_lookup_acc (tp_pin (CID := CID) m) (Regidx rs1) with "Hfile") as "[Hrac Hfb_rs1]".
    iDestruct (gpr_pt_value (CID := CID) rs1 (tp_pin (CID := CID) m (Regidx rs1)) s_pc with "Hreg Hrac") as %Lva.
    iDestruct ("Hfb_rs1" with "Hrac") as "Hfile".
    iDestruct (gpr_file_lookup_acc (tp_pin (CID := CID) m) (Regidx rs2) with "Hfile") as "[Hrbc Hfb_rs2]".
    iDestruct (gpr_pt_value (CID := CID) rs2 (tp_pin (CID := CID) m (Regidx rs2)) s_pc with "Hreg Hrbc") as %Lvb.
    iDestruct ("Hfb_rs2" with "Hrbc") as "Hfile".
    iMod (reg_update (CID := CID) _ nextPC _ (add_vec pc (sign_extend' 64 imm)) with "Hreg Hnpc") as "[Hreg Hnpc]".
    iModIntro.
    iExists (set_reg s_pc nextPC (add_vec pc (sign_extend' 64 imm))).
    iSplitR.
    { iPureIntro. rewrite Hpceq. fold s_pc.
      assert (Htk : neq_vec (rvv rs1 s_pc) (rvv rs2 s_pc) = true)
        by (unfold rvv; rewrite Lva Lvb; exact (Hcmp_all CID)).
      assert (HzcaS : eq_vec (_get_Misa_C (register_lookup misa s_pc.(sregs))) ('b"1") = true).
      { unfold s_pc; rewrite ?sregs_set_reg.
        rewrite irrelevant_register_set; [ rewrite Lmisa; exact HmisaC | vm_compute; reflexivity ]. }
      epose proof (exec_execute_BTYPE_BNE_taken_zca imm rs2 rs1 s_pc Htk) as Hred.
      rewrite Hpcv in Hred. exact (Hred Hal0 (exec_currentlyEnabled_Zca s_pc HzcaS)). }
    iSplitL "Hreg Hmem". { unfold s_pc; rewrite ?sregs_set_reg ?mem_set_reg. iFrame "Hreg Hmem". }
    iIntros "Hhs' Hpc'".
    assert (Lnpc : register_lookup nextPC
             (set_reg s_pc nextPC (add_vec pc (sign_extend' 64 imm))).(sregs)
             = add_vec pc (sign_extend' 64 imm))
      by (rewrite ?sregs_set_reg; rewrite register_lookup_set; reflexivity).
    iEval (rewrite Lnpc) in "Hpc'".
    iNext.
    iDestruct (sie_cap_gpr_join (CID := CID) with "Hhs' [$Hhw $Hsc2] Hcap Hfile") as "Hcg".
    iApply ("Hcont" $! CID with "[] Hcg [$Hpc' $Hnpc]").
    iPureIntro. exact Hs.
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
    iApply (wp_instr_s_sconf m n b pc true
              (BTYPE (imm, zreg, creg2reg_idx rs, BEQ))
              with "Hcg Hpc Hinstr").
    (* FREE THE NAME [CID] FOR THE REBOUND HART.  A section variable is an
       ordinary context entry inside a proof, so [rename] moves it aside --
       and the STATEMENT never sees that, so the 184 call sites that name this
       tier's harts as [(CID := ...)] keep working.  Introducing the new hart
       under a different name instead would force a [(CID := ...)] annotation on
       every hart-indexed term the body writes out ([tp_pin m], [rget m rs]);
       with the rename the body below is UNCHANGED. *)
    rename CID into CID0.
    iIntros (CID Hs σ Hpceq) "Hsc Hcap Hfile Hnpc [Hreg Hmem]".
    iDestruct "Hsc" as "[#Hhw Hsc2]".
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & #Hsenv & %HmisaS & %HmisaC &
        %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np & %HmisaA & %Hmisa_val0 & %Hmseccfg_val0 & #Hkmapb)".
    iDestruct (reg_valid_dq (CID := CID) with "Hreg Hmisa") as %Lmisa.
    iMod (reg_update (CID := CID) _ nextPC _ (add_vec_int pc 2) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s_pc := set_reg σ nextPC (add_vec_int pc 2)).
    assert (Hpcv : register_lookup PC s_pc.(sregs) = pc).
    { unfold s_pc; rewrite ?sregs_set_reg.
      rewrite irrelevant_register_set; [ exact Hpceq | vm_compute; reflexivity ]. }
    iDestruct (gpr_file_lookup_acc (tp_pin (CID := CID) m) (Regidx rd1) with "Hfile") as "[Hrac Hfb_rd1]".
    iDestruct (gpr_pt_value (CID := CID) rd1 (tp_pin (CID := CID) m (Regidx rd1)) s_pc with "Hreg Hrac") as %Lva.
    iDestruct ("Hfb_rd1" with "Hrac") as "Hfile".
    iMod (reg_update (CID := CID) _ nextPC _ (add_vec pc (sign_extend' 64 imm)) with "Hreg Hnpc") as "[Hreg Hnpc]".
    iModIntro.
    iExists (set_reg s_pc nextPC (add_vec pc (sign_extend' 64 imm))).
    iSplitR.
    { iPureIntro. rewrite Hpceq. fold s_pc. rewrite Hrs.
      change zreg with (Regidx (zero_extend' 5 ('b"00") : mword 5)).
      assert (Htk : eq_vec (rvv rd1 s_pc) (rvv (zero_extend' 5 ('b"00") : mword 5) s_pc) = true).
      { unfold rvv. rewrite Lva.
        replace (Z.eqb (uint (zero_extend' 5 ('b"00") : mword 5)) 0) with true
          by (vm_compute; reflexivity).
        cbn match. exact (Hcmp_all CID). }
      assert (HzcaS : eq_vec (_get_Misa_C (register_lookup misa s_pc.(sregs))) ('b"1") = true).
      { unfold s_pc; rewrite ?sregs_set_reg.
        rewrite irrelevant_register_set; [ rewrite Lmisa; exact HmisaC | vm_compute; reflexivity ]. }
      epose proof (exec_execute_BTYPE_BEQ_taken_zca imm (zero_extend' 5 ('b"00")) rd1 s_pc Htk) as Hred.
      rewrite Hpcv in Hred. exact (Hred Hal0 (exec_currentlyEnabled_Zca s_pc HzcaS)). }
    iSplitL "Hreg Hmem". { unfold s_pc; rewrite ?sregs_set_reg ?mem_set_reg. iFrame "Hreg Hmem". }
    iIntros "Hhs' Hpc'".
    assert (Lnpc : register_lookup nextPC
                     (set_reg s_pc nextPC (add_vec pc (sign_extend' 64 imm))).(sregs)
                   = add_vec pc (sign_extend' 64 imm))
      by (rewrite register_lookup_set; reflexivity).
    iEval (rewrite Lnpc) in "Hpc'".
    iNext.
    iDestruct (sie_cap_gpr_join (CID := CID) with "Hhs' [$Hhw $Hsc2] Hcap Hfile") as "Hcg".
    iApply ("Hcont" $! CID with "[] Hcg [$Hpc' $Hnpc]").
    iPureIntro. exact Hs.
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
    iApply (wp_instr_s_sconf m n b pc true
              (BTYPE (imm, zreg, creg2reg_idx rs, BNE))
              with "Hcg Hpc Hinstr").
    (* FREE THE NAME [CID] FOR THE REBOUND HART.  A section variable is an
       ordinary context entry inside a proof, so [rename] moves it aside --
       and the STATEMENT never sees that, so the 184 call sites that name this
       tier's harts as [(CID := ...)] keep working.  Introducing the new hart
       under a different name instead would force a [(CID := ...)] annotation on
       every hart-indexed term the body writes out ([tp_pin m], [rget m rs]);
       with the rename the body below is UNCHANGED. *)
    rename CID into CID0.
    iIntros (CID Hs σ Hpceq) "Hsc Hcap Hfile Hnpc [Hreg Hmem]".
    iDestruct "Hsc" as "[#Hhw Hsc2]".
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & #Hsenv & %HmisaS & %HmisaC &
        %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np & %HmisaA & %Hmisa_val0 & %Hmseccfg_val0 & #Hkmapb)".
    iDestruct (reg_valid_dq (CID := CID) with "Hreg Hmisa") as %Lmisa.
    iMod (reg_update (CID := CID) _ nextPC _ (add_vec_int pc 2) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s_pc := set_reg σ nextPC (add_vec_int pc 2)).
    assert (Hpcv : register_lookup PC s_pc.(sregs) = pc).
    { unfold s_pc; rewrite ?sregs_set_reg.
      rewrite irrelevant_register_set; [ exact Hpceq | vm_compute; reflexivity ]. }
    iDestruct (gpr_file_lookup_acc (tp_pin (CID := CID) m) (Regidx rd1) with "Hfile") as "[Hrac Hfb_rd1]".
    iDestruct (gpr_pt_value (CID := CID) rd1 (tp_pin (CID := CID) m (Regidx rd1)) s_pc with "Hreg Hrac") as %Lva.
    iDestruct ("Hfb_rd1" with "Hrac") as "Hfile".
    iMod (reg_update (CID := CID) _ nextPC _ (add_vec pc (sign_extend' 64 imm)) with "Hreg Hnpc") as "[Hreg Hnpc]".
    iModIntro.
    iExists (set_reg s_pc nextPC (add_vec pc (sign_extend' 64 imm))).
    iSplitR.
    { iPureIntro. rewrite Hpceq. fold s_pc. rewrite Hrs.
      change zreg with (Regidx (zero_extend' 5 ('b"00") : mword 5)).
      assert (Htk : neq_vec (rvv rd1 s_pc) (rvv (zero_extend' 5 ('b"00") : mword 5) s_pc) = true).
      { unfold rvv. rewrite Lva.
        replace (Z.eqb (uint (zero_extend' 5 ('b"00") : mword 5)) 0) with true
          by (vm_compute; reflexivity).
        cbn match. exact (Hcmp_all CID). }
      assert (HzcaS : eq_vec (_get_Misa_C (register_lookup misa s_pc.(sregs))) ('b"1") = true).
      { unfold s_pc; rewrite ?sregs_set_reg.
        rewrite irrelevant_register_set; [ rewrite Lmisa; exact HmisaC | vm_compute; reflexivity ]. }
      epose proof (exec_execute_BTYPE_BNE_taken_zca imm (zero_extend' 5 ('b"00")) rd1 s_pc Htk) as Hred.
      rewrite Hpcv in Hred. exact (Hred Hal0 (exec_currentlyEnabled_Zca s_pc HzcaS)). }
    iSplitL "Hreg Hmem". { unfold s_pc; rewrite ?sregs_set_reg ?mem_set_reg. iFrame "Hreg Hmem". }
    iIntros "Hhs' Hpc'".
    assert (Lnpc : register_lookup nextPC
                     (set_reg s_pc nextPC (add_vec pc (sign_extend' 64 imm))).(sregs)
                   = add_vec pc (sign_extend' 64 imm))
      by (rewrite register_lookup_set; reflexivity).
    iEval (rewrite Lnpc) in "Hpc'".
    iNext.
    iDestruct (sie_cap_gpr_join (CID := CID) with "Hhs' [$Hhw $Hsc2] Hcap Hfile") as "Hcg".
    iApply ("Hcont" $! CID with "[] Hcg [$Hpc' $Hnpc]").
    iPureIntro. exact Hs.
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
    iApply (wp_instr_s_sconf m n b pc false
              (BTYPE (imm, zreg, Regidx rs1, BEQ))
              with "Hcg Hpc Hinstr").
    (* FREE THE NAME [CID] FOR THE REBOUND HART.  A section variable is an
       ordinary context entry inside a proof, so [rename] moves it aside --
       and the STATEMENT never sees that, so the 184 call sites that name this
       tier's harts as [(CID := ...)] keep working.  Introducing the new hart
       under a different name instead would force a [(CID := ...)] annotation on
       every hart-indexed term the body writes out ([tp_pin m], [rget m rs]);
       with the rename the body below is UNCHANGED. *)
    rename CID into CID0.
    iIntros (CID Hs σ Hpceq) "Hsc Hcap Hfile Hnpc [Hreg Hmem]".
    iDestruct "Hsc" as "[#Hhw Hsc2]".
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & #Hsenv & %HmisaS & %HmisaC &
        %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np & %HmisaA & %Hmisa_val0 & %Hmseccfg_val0 & #Hkmapb)".
    iDestruct (reg_valid_dq (CID := CID) with "Hreg Hmisa") as %Lmisa.
    iMod (reg_update (CID := CID) _ nextPC _ (add_vec_int pc 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s_pc := set_reg σ nextPC (add_vec_int pc 4)).
    assert (Hpcv : register_lookup PC s_pc.(sregs) = pc).
    { unfold s_pc; rewrite ?sregs_set_reg.
      rewrite irrelevant_register_set; [ exact Hpceq | vm_compute; reflexivity ]. }
    iDestruct (gpr_file_lookup_acc (tp_pin (CID := CID) m) (Regidx rs1) with "Hfile") as "[Hrac Hfb_rs1]".
    iDestruct (gpr_pt_value (CID := CID) rs1 (tp_pin (CID := CID) m (Regidx rs1)) s_pc with "Hreg Hrac") as %Lva.
    iDestruct ("Hfb_rs1" with "Hrac") as "Hfile".
    iMod (reg_update (CID := CID) _ nextPC _ (add_vec pc (sign_extend' 64 imm)) with "Hreg Hnpc") as "[Hreg Hnpc]".
    iModIntro.
    iExists (set_reg s_pc nextPC (add_vec pc (sign_extend' 64 imm))).
    iSplitR.
    { iPureIntro. rewrite Hpceq. fold s_pc.
      change zreg with (Regidx (zero_extend' 5 ('b"00") : mword 5)).
      assert (Htk : eq_vec (rvv rs1 s_pc) (rvv (zero_extend' 5 ('b"00") : mword 5) s_pc) = true).
      { unfold rvv. rewrite Lva.
        replace (Z.eqb (uint (zero_extend' 5 ('b"00") : mword 5)) 0) with true
          by (vm_compute; reflexivity).
        cbn match. exact (Hcmp_all CID). }
      assert (HzcaS : eq_vec (_get_Misa_C (register_lookup misa s_pc.(sregs))) ('b"1") = true).
      { unfold s_pc; rewrite ?sregs_set_reg.
        rewrite irrelevant_register_set; [ rewrite Lmisa; exact HmisaC | vm_compute; reflexivity ]. }
      epose proof (exec_execute_BTYPE_BEQ_taken_zca imm (zero_extend' 5 ('b"00")) rs1 s_pc Htk) as Hred.
      rewrite Hpcv in Hred. exact (Hred Hal0 (exec_currentlyEnabled_Zca s_pc HzcaS)). }
    iSplitL "Hreg Hmem". { unfold s_pc; rewrite ?sregs_set_reg ?mem_set_reg. iFrame "Hreg Hmem". }
    iIntros "Hhs' Hpc'".
    assert (Lnpc : register_lookup nextPC
                     (set_reg s_pc nextPC (add_vec pc (sign_extend' 64 imm))).(sregs)
                   = add_vec pc (sign_extend' 64 imm))
      by (rewrite register_lookup_set; reflexivity).
    iEval (rewrite Lnpc) in "Hpc'".
    iNext.
    iDestruct (sie_cap_gpr_join (CID := CID) with "Hhs' [$Hhw $Hsc2] Hcap Hfile") as "Hcg".
    iApply ("Hcont" $! CID with "[] Hcg [$Hpc' $Hnpc]").
    iPureIntro. exact Hs.
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
    iApply (wp_instr_s_sconf m n b pc false
              (BTYPE (imm, zreg, Regidx rs1, BEQ))
              with "Hcg Hpc Hinstr").
    (* FREE THE NAME [CID] FOR THE REBOUND HART.  A section variable is an
       ordinary context entry inside a proof, so [rename] moves it aside --
       and the STATEMENT never sees that, so the 184 call sites that name this
       tier's harts as [(CID := ...)] keep working.  Introducing the new hart
       under a different name instead would force a [(CID := ...)] annotation on
       every hart-indexed term the body writes out ([tp_pin m], [rget m rs]);
       with the rename the body below is UNCHANGED. *)
    rename CID into CID0.
    iIntros (CID Hs σ Hpceq) "Hsc Hcap [%Hdom Hfmap] Hnpc [Hreg Hmem]".
    assert (Hma : rf_to_gmap (tp_pin (CID := CID) m) !! Regidx rs1 = Some (tp_pin (CID := CID) m !!! Regidx rs1))
      by (rewrite rf_lookup; apply rf_to_gmap_lookup).
    iMod (reg_update (CID := CID) _ nextPC _ (add_vec_int pc 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s_pc := set_reg σ nextPC (add_vec_int pc 4)).
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hma with "Hfmap") as "[Hrac Hfba]".
    iDestruct (gpr_pt_value (CID := CID) rs1 (tp_pin (CID := CID) m !!! Regidx rs1) s_pc with "Hreg Hrac") as %Lva.
    iDestruct ("Hfba" with "Hrac") as "Hfmap".
    iModIntro. iExists s_pc.
    iSplitR.
    { iPureIntro. rewrite Hpceq. fold s_pc.
      change zreg with (Regidx (mword_of_int 0 : mword 5)).
      apply exec_execute_BTYPE_BEQ_fall. unfold rvv. rewrite Lva.
      replace (Z.eqb (uint (mword_of_int 0 : mword 5)) 0) with true
        by (vm_compute; reflexivity).
      cbn match. exact (Hcmp_all CID). }
    iSplitL "Hreg Hmem". { unfold s_pc; rewrite ?sregs_set_reg ?mem_set_reg. iFrame "Hreg Hmem". }
    iIntros "Hhs' Hpc'".
    assert (Lnpc : register_lookup nextPC s_pc.(sregs) = add_vec_int pc 4)
      by (unfold s_pc; rewrite register_lookup_set; reflexivity).
    iEval (rewrite Lnpc) in "Hpc'".
    iAssert (gpr_file (CID := CID) (tp_pin (CID := CID) m)) with "[Hfmap]" as "Hfile".
    { iSplitR; [iPureIntro; exact Hdom | iExact "Hfmap"]. }
    iDestruct (sie_cap_gpr_join (CID := CID) with "Hhs' Hsc Hcap Hfile") as "Hcg'".
    iApply ("Hcont" $! CID with "[] Hcg' [$Hpc' $Hnpc]").
    iPureIntro. exact Hs.
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
    iApply (wp_instr_s_sconf m n b pc false
              (BTYPE (imm, zreg, Regidx rs1, BNE))
              with "Hcg Hpc Hinstr").
    (* FREE THE NAME [CID] FOR THE REBOUND HART.  A section variable is an
       ordinary context entry inside a proof, so [rename] moves it aside --
       and the STATEMENT never sees that, so the 184 call sites that name this
       tier's harts as [(CID := ...)] keep working.  Introducing the new hart
       under a different name instead would force a [(CID := ...)] annotation on
       every hart-indexed term the body writes out ([tp_pin m], [rget m rs]);
       with the rename the body below is UNCHANGED. *)
    rename CID into CID0.
    iIntros (CID Hs σ Hpceq) "Hsc Hcap Hfile Hnpc [Hreg Hmem]".
    iDestruct "Hsc" as "[#Hhw Hsc2]".
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & #Hsenv & %HmisaS & %HmisaC &
        %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np & %HmisaA & %Hmisa_val0 & %Hmseccfg_val0 & #Hkmapb)".
    iDestruct (reg_valid_dq (CID := CID) with "Hreg Hmisa") as %Lmisa.
    iMod (reg_update (CID := CID) _ nextPC _ (add_vec_int pc 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s_pc := set_reg σ nextPC (add_vec_int pc 4)).
    assert (Hpcv : register_lookup PC s_pc.(sregs) = pc).
    { unfold s_pc; rewrite ?sregs_set_reg.
      rewrite irrelevant_register_set; [ exact Hpceq | vm_compute; reflexivity ]. }
    iDestruct (gpr_file_lookup_acc (tp_pin (CID := CID) m) (Regidx rs1) with "Hfile") as "[Hrac Hfb_rs1]".
    iDestruct (gpr_pt_value (CID := CID) rs1 (tp_pin (CID := CID) m (Regidx rs1)) s_pc with "Hreg Hrac") as %Lva.
    iDestruct ("Hfb_rs1" with "Hrac") as "Hfile".
    iMod (reg_update (CID := CID) _ nextPC _ (add_vec pc (sign_extend' 64 imm)) with "Hreg Hnpc") as "[Hreg Hnpc]".
    iModIntro.
    iExists (set_reg s_pc nextPC (add_vec pc (sign_extend' 64 imm))).
    iSplitR.
    { iPureIntro. rewrite Hpceq. fold s_pc.
      change zreg with (Regidx (zero_extend' 5 ('b"00") : mword 5)).
      assert (Htk : neq_vec (rvv rs1 s_pc) (rvv (zero_extend' 5 ('b"00") : mword 5) s_pc) = true).
      { unfold rvv. rewrite Lva.
        replace (Z.eqb (uint (zero_extend' 5 ('b"00") : mword 5)) 0) with true
          by (vm_compute; reflexivity).
        cbn match. exact (Hcmp_all CID). }
      assert (HzcaS : eq_vec (_get_Misa_C (register_lookup misa s_pc.(sregs))) ('b"1") = true).
      { unfold s_pc; rewrite ?sregs_set_reg.
        rewrite irrelevant_register_set; [ rewrite Lmisa; exact HmisaC | vm_compute; reflexivity ]. }
      epose proof (exec_execute_BTYPE_BNE_taken_zca imm (zero_extend' 5 ('b"00")) rs1 s_pc Htk) as Hred.
      rewrite Hpcv in Hred. exact (Hred Hal0 (exec_currentlyEnabled_Zca s_pc HzcaS)). }
    iSplitL "Hreg Hmem". { unfold s_pc; rewrite ?sregs_set_reg ?mem_set_reg. iFrame "Hreg Hmem". }
    iIntros "Hhs' Hpc'".
    assert (Lnpc : register_lookup nextPC
                     (set_reg s_pc nextPC (add_vec pc (sign_extend' 64 imm))).(sregs)
                   = add_vec pc (sign_extend' 64 imm))
      by (rewrite register_lookup_set; reflexivity).
    iEval (rewrite Lnpc) in "Hpc'".
    iNext.
    iDestruct (sie_cap_gpr_join (CID := CID) with "Hhs' [$Hhw $Hsc2] Hcap Hfile") as "Hcg".
    iApply ("Hcont" $! CID with "[] Hcg [$Hpc' $Hnpc]").
    iPureIntro. exact Hs.
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
    iApply (wp_instr_s_sconf m n b pc false
              (BTYPE (imm, zreg, Regidx rs1, BNE))
              with "Hcg Hpc Hinstr").
    (* FREE THE NAME [CID] FOR THE REBOUND HART.  A section variable is an
       ordinary context entry inside a proof, so [rename] moves it aside --
       and the STATEMENT never sees that, so the 184 call sites that name this
       tier's harts as [(CID := ...)] keep working.  Introducing the new hart
       under a different name instead would force a [(CID := ...)] annotation on
       every hart-indexed term the body writes out ([tp_pin m], [rget m rs]);
       with the rename the body below is UNCHANGED. *)
    rename CID into CID0.
    iIntros (CID Hs σ Hpceq) "Hsc Hcap [%Hdom Hfmap] Hnpc [Hreg Hmem]".
    assert (Hma : rf_to_gmap (tp_pin (CID := CID) m) !! Regidx rs1 = Some (tp_pin (CID := CID) m !!! Regidx rs1))
      by (rewrite rf_lookup; apply rf_to_gmap_lookup).
    iMod (reg_update (CID := CID) _ nextPC _ (add_vec_int pc 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s_pc := set_reg σ nextPC (add_vec_int pc 4)).
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hma with "Hfmap") as "[Hrac Hfba]".
    iDestruct (gpr_pt_value (CID := CID) rs1 (tp_pin (CID := CID) m !!! Regidx rs1) s_pc with "Hreg Hrac") as %Lva.
    iDestruct ("Hfba" with "Hrac") as "Hfmap".
    iModIntro. iExists s_pc.
    iSplitR.
    { iPureIntro. rewrite Hpceq. fold s_pc.
      change zreg with (Regidx (mword_of_int 0 : mword 5)).
      apply exec_execute_BTYPE_BNE_fall. unfold rvv. rewrite Lva.
      replace (Z.eqb (uint (mword_of_int 0 : mword 5)) 0) with true
        by (vm_compute; reflexivity).
      cbn match. exact (Hcmp_all CID). }
    iSplitL "Hreg Hmem". { unfold s_pc; rewrite ?sregs_set_reg ?mem_set_reg. iFrame "Hreg Hmem". }
    iIntros "Hhs' Hpc'".
    assert (Lnpc : register_lookup nextPC s_pc.(sregs) = add_vec_int pc 4)
      by (unfold s_pc; rewrite register_lookup_set; reflexivity).
    iEval (rewrite Lnpc) in "Hpc'".
    iAssert (gpr_file (CID := CID) (tp_pin (CID := CID) m)) with "[Hfmap]" as "Hfile".
    { iSplitR; [iPureIntro; exact Hdom | iExact "Hfmap"]. }
    iDestruct (sie_cap_gpr_join (CID := CID) with "Hhs' Hsc Hcap Hfile") as "Hcg'".
    iApply ("Hcont" $! CID with "[] Hcg' [$Hpc' $Hnpc]").
    iPureIntro. exact Hs.
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
