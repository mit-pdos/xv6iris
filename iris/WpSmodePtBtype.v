(* S-mode Btype (branch) leaf lemmas over the generalized page-table
   invariant [tlb_inv_pt] (ptree abstraction, Svadu/ADUE).
   Ports of the WpSmodeBtype leaves. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvTryStep RiscvFetchExec.
Require Import MinstretInv InstrBytes ExecCommon WpGpr RegFile.
Require Import SRegime.
Require Import SmodeCore.
Require Import WpSmodePtFetch.
Require Import HartSwp WpSmodePtEngine.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Require Import TsoCtx.
Import Defs.

(* ---- Local helpers copied from WpSmodeBtype.v ---- *)
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

(* helper: exec_BTYPE_cmp_BEQ *)
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

(* helper: exec_execute_BTYPE_BNE_fall *)
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

(* helper: exec_execute_BTYPE_BEQ_fall *)
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

(* helper: exec_BTYPE_cmp_BGE *)

(* helper: exec_BTYPE_cmp_BLTU *)

(* helper: exec_execute_BTYPE_BLTU_fall *)

(* helper: exec_execute_BTYPE_BEQ_taken *)

(* helper: exec_execute_BTYPE_BGE_fall *)

(* helper: exec_execute_BTYPE_BNE_taken *)


(* helper: exec_execute_BTYPE_BNE_taken_zca *)
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

(* helper: exec_execute_BTYPE_BEQ_taken_zca *)
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


Section WpSmodePtBtype.
  Context `{!riscvGS Σ, !xv6G Σ}.
  Context `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}.

  (* ==================================================================== *)
  (* THE TWO BRANCH ENGINES, per node.  A branch is the one instruction    *)
  (* family that writes NO gpr: the fall-through arm is two register reads *)
  (* and a [Ret], and the taken arm adds a PC read and a nextPC write.     *)
  (* Both walks live in [WpSconfEngine] already (they are privilege- and   *)
  (* bundle-free); what is here is the regime wrapper around them, with    *)
  (* the instruction and its comparison as parameters, so each of the four *)
  (* leaves below is one [iApply].                                        *)
  (* ==================================================================== *)
  Lemma wp_btype_fall_s_r (R : s_regime)
      (pc : mword 64) (imm : mword 13) (rs2 rs1 : mword 5) (m : regfile)
      (i : instruction)
      (cmp : mword 64 -> mword 64 -> bool)
      (mstatus0 mie_v mdv0 menvcfg0 : mword 64) {dq : dfrac} :
    eq_vec (_get_Mstatus_SIE mstatus0) ('b"1") = false ->
    eq_vec (_get_Mstatus_MPRV mstatus0) ('b"1") = false ->
    _get_Mstatus_SXL mstatus0 = 'b"10" ->
    and_vec mie_v (not_vec mdv0) = zeros' 64 ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    menvcfg0 = MENVCFG_S ->
    execute i = sb_btype_body imm rs2 rs1 cmp ->
    cmp (m !!! Regidx rs1) (m !!! Regidx rs2) = false ->
    hw_config -∗ minstret_inv -∗
    hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ{ dq } Supervisor -∗ mstatus ↦ᵣ{ dq } mstatus0 -∗
    mie ↦ᵣ{ dq } mie_v -∗ mideleg ↦ᵣ{ dq } mdv0 -∗ menvcfg ↦ᵣ{ dq } menvcfg0 -∗
    sr_inv R -∗
    pc_is pc -∗ gpr_file m -∗ instr pc false i -∗
    ( hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
      cur_privilege ↦ᵣ{ dq } Supervisor -∗ mstatus ↦ᵣ{ dq } mstatus0 -∗
      mie ↦ᵣ{ dq } mie_v -∗ mideleg ↦ᵣ{ dq } mdv0 -∗ menvcfg ↦ᵣ{ dq } menvcfg0 -∗
      sr_inv R -∗
      pc_is (add_vec_int pc 4) -∗ gpr_file m -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    iIntros (HSIE HMPRV HSXL Hmm HPBMTE Hmenvval0 Hred Hcmp)
      "#Hhw #Hminv Hhs Hpriv Hms Hmie Hmdl Hmenv Hinv Hpc Hfile Hinstr Hcont".
    iDestruct (hw_config_cert with "Hhw") as "#Hcert".
    iApply (wp_instr_s_config_folded R pc false i mstatus0 mie_v mdv0 menvcfg0
              mie_v menvcfg0
              (fun npc ms1 mdv1 => (⌜npc = add_vec_int pc 4⌝ ∗
                 ⌜ms1 = mstatus0⌝ ∗ ⌜mdv1 = mdv0⌝ ∗ gpr_file m)%I)
              (dq := dq) HSIE HMPRV HSXL Hmm HPBMTE Hmenvval0
              with "Hhw Hminv Hhs Hpriv Hms Hmie Hmdl Hmenv Hinv Hpc Hinstr
                    [Hfile] [Hcont]").
    - iIntros "Hpriv Hms Hmie Hmdl Hmenv Hslot Hclk HPC HnPC Hresv".
      iApply (swp_mono with "[Hmie Hmdl Hclk HPC HnPC Hpriv Hms Hmenv Hslot
                              Hresv] [Hfile]").
      2:{ iApply (swp_sb_BTYPE_fall imm rs2 rs1 m (execute i) cmp Hred
                    Hcmp with "Hcert Hfile"). }
      iIntros (e) "(-> & Hfile)".
      iSplitR; [done|].
      iFrame "Hpriv Hmie Hmenv Hslot Hclk".
      iSplitR "Hresv"; [| iExact "Hresv"].
      iExists mstatus0, mdv0, (add_vec_int pc 4).
      iFrame "Hms Hmdl HPC HnPC".
      iSplitR; [done|]. iSplitR; [done|]. iSplitR; [done|]. iExact "Hfile".
    - iNext. iIntros (npc ms1 mdv1)
        "Hhs Hpriv Hms Hmie Hmdl Hmenv Hinv Hpc (-> & -> & -> & Hfile)".
      iApply ("Hcont" with "Hhs Hpriv Hms Hmie Hmdl Hmenv Hinv Hpc Hfile").
  Qed.

  Lemma wp_btype_taken_s_r (R : s_regime)
      (pc : mword 64) (imm : mword 13) (rs2 rs1 : mword 5) (m : regfile)
      (i : instruction)
      (cmp : mword 64 -> mword 64 -> bool)
      (mstatus0 mie_v mdv0 menvcfg0 : mword 64) {dq : dfrac} :
    eq_vec (_get_Mstatus_SIE mstatus0) ('b"1") = false ->
    eq_vec (_get_Mstatus_MPRV mstatus0) ('b"1") = false ->
    _get_Mstatus_SXL mstatus0 = 'b"10" ->
    and_vec mie_v (not_vec mdv0) = zeros' 64 ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    menvcfg0 = MENVCFG_S ->
    execute i = sb_btype_body imm rs2 rs1 cmp ->
    cmp (m !!! Regidx rs1) (m !!! Regidx rs2) = true ->
    eq_vec (access_vec_dec (add_vec pc (sign_extend' 64 imm)) 0) ('b"0") = true ->
    hw_config -∗ minstret_inv -∗
    hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ{ dq } Supervisor -∗ mstatus ↦ᵣ{ dq } mstatus0 -∗
    mie ↦ᵣ{ dq } mie_v -∗ mideleg ↦ᵣ{ dq } mdv0 -∗ menvcfg ↦ᵣ{ dq } menvcfg0 -∗
    sr_inv R -∗
    pc_is pc -∗ gpr_file m -∗ instr pc false i -∗
    ( hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
      cur_privilege ↦ᵣ{ dq } Supervisor -∗ mstatus ↦ᵣ{ dq } mstatus0 -∗
      mie ↦ᵣ{ dq } mie_v -∗ mideleg ↦ᵣ{ dq } mdv0 -∗ menvcfg ↦ᵣ{ dq } menvcfg0 -∗
      sr_inv R -∗
      pc_is (add_vec pc (sign_extend' 64 imm)) -∗ gpr_file m -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    iIntros (HSIE HMPRV HSXL Hmm HPBMTE Hmenvval0 Hred Hcmp Hal0)
      "#Hhw #Hminv Hhs Hpriv Hms Hmie Hmdl Hmenv Hinv Hpc Hfile Hinstr Hcont".
    iDestruct (hw_config_cert with "Hhw") as "#Hcert".
    iDestruct (sb_hw_config_misa with "Hhw") as "#Hmisa".
    iApply (wp_instr_s_config_folded R pc false i mstatus0 mie_v mdv0 menvcfg0
              mie_v menvcfg0
              (fun npc ms1 mdv1 =>
                 (⌜npc = add_vec pc (sign_extend' 64 imm)⌝ ∗
                  ⌜ms1 = mstatus0⌝ ∗ ⌜mdv1 = mdv0⌝ ∗ gpr_file m)%I)
              (dq := dq) HSIE HMPRV HSXL Hmm HPBMTE Hmenvval0
              with "Hhw Hminv Hhs Hpriv Hms Hmie Hmdl Hmenv Hinv Hpc Hinstr
                    [Hfile] [Hcont]").
    - iIntros "Hpriv Hms Hmie Hmdl Hmenv Hslot Hclk HPC HnPC Hresv".
      iApply (swp_mono with "[Hmie Hmdl Hclk Hpriv Hms Hmenv Hslot Hresv]
                             [Hfile HPC HnPC]").
      2:{ iApply (swp_sb_BTYPE_taken imm rs2 rs1 m (execute i) pc
                    (add_vec_int pc 4) cmp Hred Hcmp Hal0
                    with "Hcert Hfile HPC HnPC Hmisa"). }
      iIntros (e) "(-> & Hfile & HPC & HnPC & _)".
      iSplitR; [done|].
      iFrame "Hpriv Hmie Hmenv Hslot Hclk".
      iSplitR "Hresv"; [| iExact "Hresv"].
      iExists mstatus0, mdv0, (add_vec pc (sign_extend' 64 imm)).
      iFrame "Hms Hmdl HPC HnPC".
      iSplitR; [done|]. iSplitR; [done|]. iSplitR; [done|]. iExact "Hfile".
    - iNext. iIntros (npc ms1 mdv1)
        "Hhs Hpriv Hms Hmie Hmdl Hmenv Hinv Hpc (-> & -> & -> & Hfile)".
      iApply ("Hcont" with "Hhs Hpriv Hms Hmie Hmdl Hmenv Hinv Hpc Hfile").
  Qed.

  Lemma wp_beq_fall_s_config_r (R : s_regime)
      (pc : mword 64) (imm : mword 13) (rs2 rs1 : mword 5)
      (m : regfile)
      (mstatus0 mie_v mdv0 menvcfg0 : mword 64)
      {dq : dfrac} :
    eq_vec (_get_Mstatus_SIE mstatus0) ('b"1") = false ->
    eq_vec (_get_Mstatus_MPRV mstatus0) ('b"1") = false ->
    _get_Mstatus_SXL mstatus0 = 'b"10" ->
    and_vec mie_v (not_vec mdv0) = zeros' 64 ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    menvcfg0 = MENVCFG_S ->
    uint rs1 <> 0 -> uint rs2 <> 0 ->
    eq_vec (m !!! Regidx rs1) (m !!! Regidx rs2) = false ->
    hw_config -∗ minstret_inv -∗
    hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ{ dq } Supervisor -∗ mstatus ↦ᵣ{ dq } mstatus0 -∗
    mie ↦ᵣ{ dq } mie_v -∗ mideleg ↦ᵣ{ dq } mdv0 -∗ menvcfg ↦ᵣ{ dq } menvcfg0 -∗
    sr_inv R -∗
    pc_is pc -∗ gpr_file m -∗ instr pc false (BTYPE (imm, Regidx rs2, Regidx rs1, BEQ)) -∗
    ( hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
      cur_privilege ↦ᵣ{ dq } Supervisor -∗ mstatus ↦ᵣ{ dq } mstatus0 -∗
      mie ↦ᵣ{ dq } mie_v -∗ mideleg ↦ᵣ{ dq } mdv0 -∗ menvcfg ↦ᵣ{ dq } menvcfg0 -∗
      sr_inv R -∗
      pc_is (add_vec_int pc 4) -∗ gpr_file m -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    iIntros (HSIE HMPRV HSXL Hmm HPBMTE Hmenvval0 Hrs1 Hrs2 Hcmp).
    iApply (wp_btype_fall_s_r R pc imm rs2 rs1 m
              (BTYPE (imm, Regidx rs2, Regidx rs1, BEQ)) eq_vec
              mstatus0 mie_v mdv0 menvcfg0 (dq := dq)
              HSIE HMPRV HSXL Hmm HPBMTE Hmenvval0 eq_refl Hcmp).
  Qed.


  Lemma wp_beq_fall_s_config_scfg_r (R : s_regime) (γ : gname)
      (pc : mword 64) (imm : mword 13) (rs2 rs1 : mword 5)
      (m : regfile) {dq : dfrac} :
    uint rs1 <> 0 -> uint rs2 <> 0 ->
    eq_vec (m !!! Regidx rs1) (m !!! Regidx rs2) = false ->
    smode_config γ dq -∗ sr_inv R -∗
    pc_is pc -∗ gpr_file m -∗ instr pc false (BTYPE (imm, Regidx rs2, Regidx rs1, BEQ)) -∗
    ( smode_config γ dq -∗ sr_inv R -∗
      pc_is (add_vec_int pc 4) -∗ gpr_file m -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    iIntros (Hrs1 Hrs2 Hcmp) "Hsm Htlbinv Hpc Hgpr Hinstr Hcont".
    iDestruct (smode_config_unbundle with "Hsm") as
      "(#Hhw & #Hinv & Hhs & Hpriv & Hmst & Hmieb & Hmenvb)".
    iDestruct "Hmst" as (mstatus0) "(Hms & Hsie & %HSIE & %HMPRV & %HSXL & %HMXR & %Hleg)".
    iDestruct "Hmieb" as (mie_v mdv0) "(Hmie & Hmdl & %Hmm)".
    iDestruct "Hmenvb" as (menvcfg0) "(Hmenv & %HPBMTE & %Hpmm & %Hlpe & %Hfiom & %Hmenvval0)".
    iApply (wp_beq_fall_s_config_r R pc imm rs2 rs1 m mstatus0 mie_v mdv0 menvcfg0 (dq:=dq)
 HSIE HMPRV HSXL Hmm HPBMTE Hmenvval0 Hrs1 Hrs2 Hcmp
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hgpr Hinstr").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hgpr".
    iDestruct (smode_config_rebuild γ dq mstatus0 mie_v mdv0 menvcfg0
                 HSIE HMPRV HSXL HMXR Hleg Hmm HPBMTE Hpmm Hlpe Hfiom Hmenvval0
                 with "Hhw Hinv Hhs Hpriv Hms Hsie Hmie Hmdl Hmenv") as "Hsm".
    iApply ("Hcont" with "Hsm Htlbinv Hpc Hgpr").
  Qed.


  Lemma wp_beq_taken_s_config_r (R : s_regime)
      (pc : mword 64) (imm : mword 13) (rs2 rs1 : mword 5)
      (m : regfile)
      (mstatus0 mie_v mdv0 menvcfg0 : mword 64)
      {dq : dfrac} :
    eq_vec (_get_Mstatus_SIE mstatus0) ('b"1") = false ->
    eq_vec (_get_Mstatus_MPRV mstatus0) ('b"1") = false ->
    _get_Mstatus_SXL mstatus0 = 'b"10" ->
    and_vec mie_v (not_vec mdv0) = zeros' 64 ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    menvcfg0 = MENVCFG_S ->
    uint rs1 <> 0 -> uint rs2 <> 0 ->
    eq_vec (m !!! Regidx rs1) (m !!! Regidx rs2) = true ->
    (* only 2-alignment of the target is required: the C extension (Zca,
       derived internally from misa.C) legalizes a bit1 = 1 branch target. *)
    eq_vec (access_vec_dec (add_vec pc (sign_extend' 64 imm)) 0) ('b"0") = true ->
    hw_config -∗ minstret_inv -∗
    hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ{ dq } Supervisor -∗ mstatus ↦ᵣ{ dq } mstatus0 -∗
    mie ↦ᵣ{ dq } mie_v -∗ mideleg ↦ᵣ{ dq } mdv0 -∗ menvcfg ↦ᵣ{ dq } menvcfg0 -∗
    sr_inv R -∗
    pc_is pc -∗ gpr_file m -∗ instr pc false (BTYPE (imm, Regidx rs2, Regidx rs1, BEQ)) -∗
    ( hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
      cur_privilege ↦ᵣ{ dq } Supervisor -∗ mstatus ↦ᵣ{ dq } mstatus0 -∗
      mie ↦ᵣ{ dq } mie_v -∗ mideleg ↦ᵣ{ dq } mdv0 -∗ menvcfg ↦ᵣ{ dq } menvcfg0 -∗
      sr_inv R -∗
      pc_is (add_vec pc (sign_extend' 64 imm)) -∗ gpr_file m -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    iIntros (HSIE HMPRV HSXL Hmm HPBMTE Hmenvval0 Hrs1 Hrs2 Hcmp Hal0).
    iApply (wp_btype_taken_s_r R pc imm rs2 rs1 m
              (BTYPE (imm, Regidx rs2, Regidx rs1, BEQ)) eq_vec
              mstatus0 mie_v mdv0 menvcfg0 (dq := dq)
              HSIE HMPRV HSXL Hmm HPBMTE Hmenvval0 eq_refl Hcmp Hal0).
  Qed.


  Lemma wp_beq_taken_s_config_scfg_r (R : s_regime) (γ : gname)
      (pc : mword 64) (imm : mword 13) (rs2 rs1 : mword 5)
      (m : regfile) {dq : dfrac} :
    uint rs1 <> 0 -> uint rs2 <> 0 ->
    eq_vec (m !!! Regidx rs1) (m !!! Regidx rs2) = true ->
    eq_vec (access_vec_dec (add_vec pc (sign_extend' 64 imm)) 0) ('b"0") = true ->
    smode_config γ dq -∗ sr_inv R -∗
    pc_is pc -∗ gpr_file m -∗ instr pc false (BTYPE (imm, Regidx rs2, Regidx rs1, BEQ)) -∗
    ( smode_config γ dq -∗ sr_inv R -∗
      pc_is (add_vec pc (sign_extend' 64 imm)) -∗ gpr_file m -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    iIntros (Hrs1 Hrs2 Hcmp Hal) "Hsm Htlbinv Hpc Hgpr Hinstr Hcont".
    iDestruct (smode_config_unbundle with "Hsm") as
      "(#Hhw & #Hinv & Hhs & Hpriv & Hmst & Hmieb & Hmenvb)".
    iDestruct "Hmst" as (mstatus0) "(Hms & Hsie & %HSIE & %HMPRV & %HSXL & %HMXR & %Hleg)".
    iDestruct "Hmieb" as (mie_v mdv0) "(Hmie & Hmdl & %Hmm)".
    iDestruct "Hmenvb" as (menvcfg0) "(Hmenv & %HPBMTE & %Hpmm & %Hlpe & %Hfiom & %Hmenvval0)".
    iApply (wp_beq_taken_s_config_r R pc imm rs2 rs1 m mstatus0 mie_v mdv0 menvcfg0 (dq:=dq)
 HSIE HMPRV HSXL Hmm HPBMTE Hmenvval0 Hrs1 Hrs2 Hcmp Hal
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hgpr Hinstr").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hgpr".
    iDestruct (smode_config_rebuild γ dq mstatus0 mie_v mdv0 menvcfg0
                 HSIE HMPRV HSXL HMXR Hleg Hmm HPBMTE Hpmm Hlpe Hfiom Hmenvval0
                 with "Hhw Hinv Hhs Hpriv Hms Hsie Hmie Hmdl Hmenv") as "Hsm".
    iApply ("Hcont" with "Hsm Htlbinv Hpc Hgpr").
  Qed.


  (* beq rs1, x0 (beqz) FALL-THROUGH: the x0 side reads zero_reg; the
     catalog spells the rs2 slot [zreg] *)


  Lemma wp_bne_fall_s_config_r (R : s_regime)
      (pc : mword 64) (imm : mword 13) (rs2 rs1 : mword 5)
      (m : regfile)
      (mstatus0 mie_v mdv0 menvcfg0 : mword 64)
      {dq : dfrac} :
    eq_vec (_get_Mstatus_SIE mstatus0) ('b"1") = false ->
    eq_vec (_get_Mstatus_MPRV mstatus0) ('b"1") = false ->
    _get_Mstatus_SXL mstatus0 = 'b"10" ->
    and_vec mie_v (not_vec mdv0) = zeros' 64 ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    menvcfg0 = MENVCFG_S ->
    uint rs1 <> 0 -> uint rs2 <> 0 ->
    neq_vec (m !!! Regidx rs1) (m !!! Regidx rs2) = false ->
    hw_config -∗ minstret_inv -∗
    hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ{ dq } Supervisor -∗ mstatus ↦ᵣ{ dq } mstatus0 -∗
    mie ↦ᵣ{ dq } mie_v -∗ mideleg ↦ᵣ{ dq } mdv0 -∗ menvcfg ↦ᵣ{ dq } menvcfg0 -∗
    sr_inv R -∗
    pc_is pc -∗ gpr_file m -∗ instr pc false (BTYPE (imm, Regidx rs2, Regidx rs1, BNE)) -∗
    ( hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
      cur_privilege ↦ᵣ{ dq } Supervisor -∗ mstatus ↦ᵣ{ dq } mstatus0 -∗
      mie ↦ᵣ{ dq } mie_v -∗ mideleg ↦ᵣ{ dq } mdv0 -∗ menvcfg ↦ᵣ{ dq } menvcfg0 -∗
      sr_inv R -∗
      pc_is (add_vec_int pc 4) -∗ gpr_file m -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    iIntros (HSIE HMPRV HSXL Hmm HPBMTE Hmenvval0 Hrs1 Hrs2 Hcmp).
    iApply (wp_btype_fall_s_r R pc imm rs2 rs1 m
              (BTYPE (imm, Regidx rs2, Regidx rs1, BNE)) neq_vec
              mstatus0 mie_v mdv0 menvcfg0 (dq := dq)
              HSIE HMPRV HSXL Hmm HPBMTE Hmenvval0 eq_refl Hcmp).
  Qed.


  Lemma wp_bne_fall_s_config_scfg_r (R : s_regime) (γ : gname)
      (pc : mword 64) (imm : mword 13) (rs2 rs1 : mword 5)
      (m : regfile) {dq : dfrac} :
    uint rs1 <> 0 -> uint rs2 <> 0 ->
    neq_vec (m !!! Regidx rs1) (m !!! Regidx rs2) = false ->
    smode_config γ dq -∗ sr_inv R -∗
    pc_is pc -∗ gpr_file m -∗ instr pc false (BTYPE (imm, Regidx rs2, Regidx rs1, BNE)) -∗
    ( smode_config γ dq -∗ sr_inv R -∗
      pc_is (add_vec_int pc 4) -∗ gpr_file m -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    iIntros (Hrs1 Hrs2 Hcmp) "Hsm Htlbinv Hpc Hgpr Hinstr Hcont".
    iDestruct (smode_config_unbundle with "Hsm") as
      "(#Hhw & #Hinv & Hhs & Hpriv & Hmst & Hmieb & Hmenvb)".
    iDestruct "Hmst" as (mstatus0) "(Hms & Hsie & %HSIE & %HMPRV & %HSXL & %HMXR & %Hleg)".
    iDestruct "Hmieb" as (mie_v mdv0) "(Hmie & Hmdl & %Hmm)".
    iDestruct "Hmenvb" as (menvcfg0) "(Hmenv & %HPBMTE & %Hpmm & %Hlpe & %Hfiom & %Hmenvval0)".
    iApply (wp_bne_fall_s_config_r R pc imm rs2 rs1 m mstatus0 mie_v mdv0 menvcfg0 (dq:=dq)
 HSIE HMPRV HSXL Hmm HPBMTE Hmenvval0 Hrs1 Hrs2 Hcmp
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hgpr Hinstr").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hgpr".
    iDestruct (smode_config_rebuild γ dq mstatus0 mie_v mdv0 menvcfg0
                 HSIE HMPRV HSXL HMXR Hleg Hmm HPBMTE Hpmm Hlpe Hfiom Hmenvval0
                 with "Hhw Hinv Hhs Hpriv Hms Hsie Hmie Hmdl Hmenv") as "Hsm".
    iApply ("Hcont" with "Hsm Htlbinv Hpc Hgpr").
  Qed.


  Lemma wp_bne_taken_s_config_r (R : s_regime)
      (pc : mword 64) (imm : mword 13) (rs2 rs1 : mword 5)
      (m : regfile)
      (mstatus0 mie_v mdv0 menvcfg0 : mword 64)
      {dq : dfrac} :
    eq_vec (_get_Mstatus_SIE mstatus0) ('b"1") = false ->
    eq_vec (_get_Mstatus_MPRV mstatus0) ('b"1") = false ->
    _get_Mstatus_SXL mstatus0 = 'b"10" ->
    and_vec mie_v (not_vec mdv0) = zeros' 64 ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    menvcfg0 = MENVCFG_S ->
    uint rs1 <> 0 -> uint rs2 <> 0 ->
    neq_vec (m !!! Regidx rs1) (m !!! Regidx rs2) = true ->
    (* only 2-alignment of the target is required: the C extension (Zca,
       derived internally from misa.C) legalizes a bit1 = 1 branch target. *)
    eq_vec (access_vec_dec (add_vec pc (sign_extend' 64 imm)) 0) ('b"0") = true ->
    hw_config -∗ minstret_inv -∗
    hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ{ dq } Supervisor -∗ mstatus ↦ᵣ{ dq } mstatus0 -∗
    mie ↦ᵣ{ dq } mie_v -∗ mideleg ↦ᵣ{ dq } mdv0 -∗ menvcfg ↦ᵣ{ dq } menvcfg0 -∗
    sr_inv R -∗
    pc_is pc -∗ gpr_file m -∗ instr pc false (BTYPE (imm, Regidx rs2, Regidx rs1, BNE)) -∗
    ( hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
      cur_privilege ↦ᵣ{ dq } Supervisor -∗ mstatus ↦ᵣ{ dq } mstatus0 -∗
      mie ↦ᵣ{ dq } mie_v -∗ mideleg ↦ᵣ{ dq } mdv0 -∗ menvcfg ↦ᵣ{ dq } menvcfg0 -∗
      sr_inv R -∗
      pc_is (add_vec pc (sign_extend' 64 imm)) -∗ gpr_file m -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    iIntros (HSIE HMPRV HSXL Hmm HPBMTE Hmenvval0 Hrs1 Hrs2 Hcmp Hal0).
    iApply (wp_btype_taken_s_r R pc imm rs2 rs1 m
              (BTYPE (imm, Regidx rs2, Regidx rs1, BNE)) neq_vec
              mstatus0 mie_v mdv0 menvcfg0 (dq := dq)
              HSIE HMPRV HSXL Hmm HPBMTE Hmenvval0 eq_refl Hcmp Hal0).
  Qed.


  Lemma wp_bne_taken_s_config_scfg_r (R : s_regime) (γ : gname)
      (pc : mword 64) (imm : mword 13) (rs2 rs1 : mword 5)
      (m : regfile) {dq : dfrac} :
    uint rs1 <> 0 -> uint rs2 <> 0 ->
    neq_vec (m !!! Regidx rs1) (m !!! Regidx rs2) = true ->
    eq_vec (access_vec_dec (add_vec pc (sign_extend' 64 imm)) 0) ('b"0") = true ->
    smode_config γ dq -∗ sr_inv R -∗
    pc_is pc -∗ gpr_file m -∗ instr pc false (BTYPE (imm, Regidx rs2, Regidx rs1, BNE)) -∗
    ( smode_config γ dq -∗ sr_inv R -∗
      pc_is (add_vec pc (sign_extend' 64 imm)) -∗ gpr_file m -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    iIntros (Hrs1 Hrs2 Hcmp Hal) "Hsm Htlbinv Hpc Hgpr Hinstr Hcont".
    iDestruct (smode_config_unbundle with "Hsm") as
      "(#Hhw & #Hinv & Hhs & Hpriv & Hmst & Hmieb & Hmenvb)".
    iDestruct "Hmst" as (mstatus0) "(Hms & Hsie & %HSIE & %HMPRV & %HSXL & %HMXR & %Hleg)".
    iDestruct "Hmieb" as (mie_v mdv0) "(Hmie & Hmdl & %Hmm)".
    iDestruct "Hmenvb" as (menvcfg0) "(Hmenv & %HPBMTE & %Hpmm & %Hlpe & %Hfiom & %Hmenvval0)".
    iApply (wp_bne_taken_s_config_r R pc imm rs2 rs1 m mstatus0 mie_v mdv0 menvcfg0 (dq:=dq)
 HSIE HMPRV HSXL Hmm HPBMTE Hmenvval0 Hrs1 Hrs2 Hcmp Hal
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hgpr Hinstr").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hgpr".
    iDestruct (smode_config_rebuild γ dq mstatus0 mie_v mdv0 menvcfg0
                 HSIE HMPRV HSXL HMXR Hleg Hmm HPBMTE Hpmm Hlpe Hfiom Hmenvval0
                 with "Hhw Hinv Hhs Hpriv Hms Hsie Hmie Hmdl Hmenv") as "Hsm".
    iApply ("Hcont" with "Hsm Htlbinv Hpc Hgpr").
  Qed.


End WpSmodePtBtype.
