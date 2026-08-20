(* S-mode control-flow / CSR / fence / sret leaf lemmas over the generalized
   page-table invariant [tlb_inv_pt] (ptree abstraction, Svadu/ADUE).
   Ports of the WpSmodeFence/Jal/Jalr/Csr/Sret leaves. *)
From Stdlib Require Import ZArith Lia List FunctionalExtensionality.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
From iris.base_logic.lib Require Import ghost_var invariants.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvTryStep RiscvFetchExec.
Require Import MinstretInv InstrBytes ExecCommon WpGpr.
Require Import SRegime.
Require Import KptShare.
Require Import SmodeCore WpMmodeLeafBase.
Require Import MstatusBits.
Require Import WpSmodePtFetch.
Require Import HartSwp WpSmodePtEngine.
Require Import RegFile.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Import Defs.

(* helper: exec_execute_JAL_gpr_zca *)
Local Lemma exec_execute_JAL_gpr_zca (imm : mword 21) (rd : mword 5) s :
  uint rd <> 0 ->
  eq_vec (access_vec_dec (add_vec (register_lookup PC s.(sregs)) (sign_extend' 64 imm)) 0) ('b"0") = true ->
  exec (currentlyEnabled Ext_Zca) s = Some (true, s) ->
  exec (execute_JAL imm (Regidx rd)) s
  = Some (RETIRE_SUCCESS,
          set_reg (set_reg s nextPC (add_vec (register_lookup PC s.(sregs)) (sign_extend' 64 imm)))
                  (R_bitvector_64 (gpr_of_Z (uint rd)))
                  (regval_into_reg (register_lookup nextPC s.(sregs)))).
Proof.
  intros Hrd Halign Hzca.
  unfold execute_JAL, get_next_pc.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg nextPC s)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg PC s)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_jump_to_zca _ s Halign Hzca)).
  cbn match.
  match goal with |- context[Defs.bind0 ?wx _] =>
    assert (Hwx : exec wx (set_reg s nextPC (add_vec (register_lookup PC s.(sregs)) (sign_extend' 64 imm)))
                  = Some (tt, set_reg (set_reg s nextPC (add_vec (register_lookup PC s.(sregs)) (sign_extend' 64 imm)))
                                (R_bitvector_64 (gpr_of_Z (uint rd)))
                                (regval_into_reg (register_lookup nextPC s.(sregs)))))
  end.
  { rewrite (exec_wX_bits_gpr rd (register_lookup nextPC s.(sregs)) _).
    replace (Z.eqb (uint rd) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrd).
    reflexivity. }
  rewrite (exec_bind0_Some _ _ _ _ _ Hwx).
  apply exec_returnm.
Qed.


(* ---- Local helpers copied from WpSmodeCsr.v ---- *)

(* helper: exec_csr_id_write_callback_sstatus *)

(* helper: exec_hartSupports_H *)

(* helper: exec_hartSupports_Sv32 *)

(* helper: exec_have_nominal_privLevel *)

(* helper: exec_lowest_supported_privLevel *)

(* helper: exec_read_CSR_sstatus *)

(* helper: exec_virtual_memory_supported *)

(* helper: register_set_bv64_id *)

(* helper: exec_currentlyEnabled_H_false *)

(* helper: exec_legalize_mstatus *)

(* helper: exec_legalize_sstatus *)

(* helper: exec_write_CSR_sstatus *)

(* helper: exec_check_CSR_priv_sstatus_S *)

(* helper: exec_check_CSR_sstatus_S *)

(* helper: exec_check_CSR_result_sstatus_S *)

(* helper: exec_execute_csrr_sstatus *)

(* helper: exec_execute_csrrci_sstatus *)


(* pure FENCE helpers (relocated from the deleted WpSmodeFence.v) *)
Lemma exec_sail_barrier (b : Arch.barrier) s :
  exec (sail_barrier b) s = Some (tt, s).
Proof. reflexivity. Qed.

Lemma exec_is_fiom_active_S (menvcfg0 : mword 64) s :
  register_lookup cur_privilege s.(sregs) = Supervisor ->
  register_lookup menvcfg s.(sregs) = menvcfg0 ->
  exec (is_fiom_active tt) s
    = Some (eq_vec (_get_MEnvcfg_FIOM menvcfg0) ('b"1"), s).
Proof.
  intros Hcp Hmenv. unfold is_fiom_active.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg cur_privilege s)).
  rewrite Hcp. cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg menvcfg s)).
  rewrite Hmenv. apply exec_returnM.
Qed.


(* A FENCE is state-preserving at EVERY pred/succ pair: the model's whole
   pred/succ dispatch is an if-tree whose every arm is a [sail_barrier]
   (a no-op in the functional interpreter) or a bare [returnM tt].  So the
   S-mode exec fact is generic in [fm]/[pred]/[succ]/[rs]/[rd] -- which is
   what makes ONE leaf serve both [__sync_lock_release]'s `fence rw,w` and
   [__sync_synchronize]'s `fence rw,rw`.  (The User-mode twin, proved the
   same way, is [UserExecFacts.exec_execute_FENCE_total_U].)               *)
Lemma exec_execute_FENCE_S (menvcfg0 : mword 64)
    (fm pred succ : mword 4) (rs rd : regidx) s :
  register_lookup cur_privilege s.(sregs) = Supervisor ->
  register_lookup menvcfg s.(sregs) = menvcfg0 ->
  eq_vec (_get_MEnvcfg_FIOM menvcfg0) ('b"1") = false ->
  exec (execute (FENCE (fm, pred, succ, rs, rd))) s
    = Some (RETIRE_SUCCESS, s).
Proof.
  intros Hcp Hmenv Hfiom.
  change (execute (FENCE (fm, pred, succ, rs, rd)))
    with (execute_FENCE fm pred succ rs rd).
  unfold execute_FENCE.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_is_fiom_active_S menvcfg0 s Hcp Hmenv)).
  rewrite Hfiom.
  cbn beta. cbv zeta. cbn match.
  erewrite exec_bind0_Some.
  2:{ repeat match goal with
             | |- exec (if ?b then _ else _) _ = _ => destruct b
             | |- exec (returnM (if ?b then _ else _)) _ = _ => destruct b
             end;
      first [ apply (exec_sail_barrier _ s) | apply exec_returnM ]. }
  apply exec_returnM.
Qed.

(* [fence.i] is state-preserving unconditionally: [execute_FENCEI] is a single
   [sail_barrier] (a no-op in the functional interpreter) and a [returnM].  It
   needs no privilege or menvcfg hypothesis at all -- unlike [FENCE], whose
   FIOM dispatch does.  (The User-mode twin is
   [UserExecFacts.exec_execute_FENCEI_U]; re-proved here rather than imported,
   so an S-mode WP file does not depend on the user-execution layer.) *)
Lemma exec_execute_FENCEI_S (imm : mword 12) (rs rd : regidx) s :
  exec (execute (FENCEI (imm, rs, rd))) s = Some (RETIRE_SUCCESS, s).
Proof.
  destruct rs as [i1]; destruct rd as [ird].
  change (execute (FENCEI (imm, Regidx i1, Regidx ird)))
    with (execute_FENCEI imm (Regidx i1) (Regidx ird)).
  unfold execute_FENCEI.
  rewrite (exec_bind0_Some _ _ _ _ _ (exec_sail_barrier _ s)).
  apply exec_returnM.
Qed.

Section WpSmodePtCtl.
  Context `{!riscvGS Σ, !xv6G Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  (* ---- from WpSmodeFence.v ---- *)


  (* ---- from WpSmodeJal.v ---- *)


  Lemma wp_jal_gpr_s_zca_r (R : s_regime) (γ : gname)
      (pc : mword 64) (rd : mword 5) (imm : mword 21)
      (m : regfile)
      (q : Qp) :
    uint rd <> 0 ->
    eq_vec (access_vec_dec (add_vec pc (sign_extend' 64 imm)) 0) ('b"0") = true ->
    smode_config γ (DfracOwn q) -∗
    sr_inv R -∗
    pc_is pc -∗
    gpr_file m -∗
    instr pc false (JAL (imm, Regidx rd)) -∗
    ( smode_config γ (DfracOwn q) -∗
      sr_inv R -∗
      pc_is (add_vec pc (sign_extend' 64 imm)) -∗
      gpr_file (<[Regidx rd := regval_into_reg (add_vec_int pc 4)]> m) -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    iIntros (Hrd Hal0) "Hsm Hinv Hpc Hfile Hinstr Hcont".
    iDestruct (smode_config_unbundle with "Hsm")
      as "(#Hhw & #Hminv & Hhs & Hpriv & Hmst & Hmieb & Hmenvb)".
    iDestruct "Hmst" as (mstatus0)
      "(Hms & Hsie & %HSIE & %HMPRV & %HSXL & %HMXR & %Hleg)".
    iDestruct "Hmieb" as (mie_v mdv0) "(Hmie & Hmdl & %Hmm)".
    iDestruct "Hmenvb" as (menvcfg0)
      "(Hmenv & %HPBMTE & %Hpmm & %Hlpe & %Hfiom & %Hmenvval0)".
    iDestruct (hw_config_cert with "Hhw") as "#Hcert".
    iDestruct (sb_hw_config_misa with "Hhw") as "#Hmisa".
    iApply (wp_instr_s_config_folded R pc false (JAL (imm, Regidx rd))
              mstatus0 mie_v mdv0 menvcfg0 mie_v menvcfg0
              (fun npc ms1 mdv1 =>
                 (⌜npc = add_vec pc (sign_extend' 64 imm)⌝ ∗
                  ⌜ms1 = mstatus0⌝ ∗ ⌜mdv1 = mdv0⌝ ∗
                  gpr_file (<[Regidx rd
                              := regval_into_reg (add_vec_int pc 4)]> m))%I)
              (dq := DfracOwn q) HSIE HMPRV HSXL Hmm HPBMTE Hmenvval0
              with "Hhw Hminv Hhs Hpriv Hms Hmie Hmdl Hmenv Hinv Hpc Hinstr
                    [Hfile] [Hcont Hsie]").
    - iIntros "Hpriv Hms Hmie Hmdl Hmenv Hslot Hclk HPC HnPC Hresv".
      iApply (swp_mono with "[Hmie Hmdl Hclk Hpriv Hms Hmenv Hslot Hresv]
                             [Hfile HPC HnPC]").
      2:{ iApply (swp_cj_JAL imm rd m pc (add_vec_int pc 4) Hrd Hal0
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
      iApply ("Hcont" with
                "[Hhs Hpriv Hms Hsie Hmie Hmdl Hmenv] Hinv Hpc Hfile").
      iApply (smode_config_rebuild γ (DfracOwn q) mstatus0 mie_v mdv0 menvcfg0
                HSIE HMPRV HSXL HMXR Hleg Hmm HPBMTE Hpmm Hlpe Hfiom Hmenvval0
                with "Hhw Hminv Hhs Hpriv Hms Hsie Hmie Hmdl Hmenv").
  Qed.

  Lemma wp_jal_gpr_s_zca_pt (root_ppn : mword 44) (γ : gname)
      (pc : mword 64) (rd : mword 5) (imm : mword 21)
      (m : regfile)
      (q : Qp) :
    uint rd <> 0 ->
    eq_vec (access_vec_dec (add_vec pc (sign_extend' 64 imm)) 0) ('b"0") = true ->
    smode_config γ (DfracOwn q) -∗
    tlb_res_pt root_ppn -∗
    pc_is pc -∗
    gpr_file m -∗
    instr pc false (JAL (imm, Regidx rd)) -∗
    ( smode_config γ (DfracOwn q) -∗
      tlb_res_pt root_ppn -∗
      pc_is (add_vec pc (sign_extend' 64 imm)) -∗
      gpr_file (<[Regidx rd := regval_into_reg (add_vec_int pc 4)]> m) -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
    Proof.
    exact (wp_jal_gpr_s_zca_r (kpt_share_regime root_ppn) γ pc rd imm m q).
  Qed.

  (* ---- from WpSmodeJalr.v ---- *)


  Lemma wp_cret_s_zca_r_later (R : s_regime)
      (pc : mword 64) (ra : mword 5)
      (m : regfile)
      (mstatus0 mie_v mdv0 menvcfg0 : mword 64)
      {dq : dfrac} :
    let tgt := ret_pc (m !!! Regidx ra) in
    eq_vec (_get_Mstatus_SIE mstatus0) ('b"1") = false ->
    eq_vec (_get_Mstatus_MPRV mstatus0) ('b"1") = false ->
    _get_Mstatus_SXL mstatus0 = 'b"10" ->
    and_vec mie_v (not_vec mdv0) = zeros' 64 ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    menvcfg0 = MENVCFG_S ->
    uint ra <> 0 ->
    bool_bit_backwards (_get_MEnvcfg_LPE menvcfg0) = false ->
    hw_config -∗
    minstret_inv -∗
    hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ{ dq } Supervisor -∗
    mstatus ↦ᵣ{ dq } mstatus0 -∗
    mie ↦ᵣ{ dq } mie_v -∗
    mideleg ↦ᵣ{ dq } mdv0 -∗
    menvcfg ↦ᵣ{ dq } menvcfg0 -∗
    sr_inv R -∗
    pc_is pc -∗
    gpr_file m -∗
    instr pc true (JALR (zeros' 12, Regidx ra, zreg)) -∗
    ( ▷ ( hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
      cur_privilege ↦ᵣ{ dq } Supervisor -∗
      mstatus ↦ᵣ{ dq } mstatus0 -∗
      mie ↦ᵣ{ dq } mie_v -∗
      mideleg ↦ᵣ{ dq } mdv0 -∗
      menvcfg ↦ᵣ{ dq } menvcfg0 -∗
      sr_inv R -∗
      pc_is tgt -∗
      gpr_file m -∗
      WP (Loop : expr riscv_lang))) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros tgt HSIE HMPRV HSXL Hmm HPBMTE Hmenvval0 Hra Hlpe.
    subst tgt.
    iIntros "#Hhw #Hminv Hhs Hpriv Hms Hmie Hmdl Hmenv Hinv Hpc Hfile Hinstr
             Hcont".
    iDestruct (hw_config_cert with "Hhw") as "#Hcert".
    iDestruct (sb_hw_config_misa with "Hhw") as "#Hmisa".
    subst menvcfg0.
    iApply (wp_instr_s_config_folded R pc true
              (JALR (zeros' 12, Regidx ra, zreg))
              mstatus0 mie_v mdv0 MENVCFG_S mie_v MENVCFG_S
              (fun npc ms1 mdv1 =>
                 (⌜npc = ret_pc (m !!! Regidx ra)⌝ ∗
                  ⌜ms1 = mstatus0⌝ ∗ ⌜mdv1 = mdv0⌝ ∗ gpr_file m)%I)
              (dq := dq) HSIE HMPRV HSXL Hmm HPBMTE eq_refl
              with "Hhw Hminv Hhs Hpriv Hms Hmie Hmdl Hmenv Hinv Hpc Hinstr
                    [Hfile] [Hcont]").
    - iIntros "Hpriv Hms Hmie Hmdl Hmenv Hslot Hclk HPC HnPC Hresv".
      iApply (swp_mono with "[Hmie Hmdl Hclk Hms Hslot Hresv HPC]
                             [Hfile HnPC Hpriv Hmenv]").
      2:{ iApply (swp_cj_JALR_ret dq ra (zero_extend' 5 ('b"00")) m
                    (add_vec_int pc 2) ltac:(vm_compute; reflexivity)
                    with "Hcert Hfile HnPC Hpriv Hmenv Hmisa"). }
      iIntros (e) "(-> & Hfile & HnPC & Hpriv & Hmenv & _)".
      iSplitR; [done|].
      iFrame "Hpriv Hmie Hmenv Hslot Hclk".
      iSplitR "Hresv"; [| iExact "Hresv"].
      iExists mstatus0, mdv0, (ret_pc (m !!! Regidx ra)).
      iFrame "Hms Hmdl HPC HnPC".
      iSplitR; [done|]. iSplitR; [done|]. iSplitR; [done|]. iExact "Hfile".
    - iNext. iIntros (npc ms1 mdv1)
        "Hhs Hpriv Hms Hmie Hmdl Hmenv Hinv Hpc (-> & -> & -> & Hfile)".
      iApply ("Hcont" with "Hhs Hpriv Hms Hmie Hmdl Hmenv Hinv Hpc Hfile").
  Qed.

  Lemma wp_cret_s_zca_r (R : s_regime)
      (pc : mword 64) (ra : mword 5)
      (m : regfile)
      (mstatus0 mie_v mdv0 menvcfg0 : mword 64)
      {dq : dfrac} :
    let tgt := ret_pc (m !!! Regidx ra) in
    eq_vec (_get_Mstatus_SIE mstatus0) ('b"1") = false ->
    eq_vec (_get_Mstatus_MPRV mstatus0) ('b"1") = false ->
    _get_Mstatus_SXL mstatus0 = 'b"10" ->
    and_vec mie_v (not_vec mdv0) = zeros' 64 ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    menvcfg0 = MENVCFG_S ->
    uint ra <> 0 ->
    bool_bit_backwards (_get_MEnvcfg_LPE menvcfg0) = false ->
    hw_config -∗
    minstret_inv -∗
    hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ{ dq } Supervisor -∗
    mstatus ↦ᵣ{ dq } mstatus0 -∗
    mie ↦ᵣ{ dq } mie_v -∗
    mideleg ↦ᵣ{ dq } mdv0 -∗
    menvcfg ↦ᵣ{ dq } menvcfg0 -∗
    sr_inv R -∗
    pc_is pc -∗
    gpr_file m -∗
    instr pc true (JALR (zeros' 12, Regidx ra, zreg)) -∗
    ( hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
      cur_privilege ↦ᵣ{ dq } Supervisor -∗
      mstatus ↦ᵣ{ dq } mstatus0 -∗
      mie ↦ᵣ{ dq } mie_v -∗
      mideleg ↦ᵣ{ dq } mdv0 -∗
      menvcfg ↦ᵣ{ dq } menvcfg0 -∗
      sr_inv R -∗
      pc_is tgt -∗
      gpr_file m -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros tgt HSIE HMPRV HSXL Hmm HPBMTE Hmenvval0 Hra Hlpe.
    iIntros "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hinstr Hcont".
    iApply (wp_cret_s_zca_r_later R pc ra m mstatus0 mie_v mdv0 menvcfg0
              HSIE HMPRV HSXL Hmm HPBMTE Hmenvval0 Hra Hlpe
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hinstr [Hcont]").
    iNext. iExact "Hcont".
  Qed.


  (* ---- from WpSmodeCsr.v ---- *)


  (* ---- from WpSmodeSret.v ---- *)

  Lemma wp_sret_gpr_r (R : s_regime)
      (pc : mword 64)
      (mstatus0 mie_v mdv0 menvcfg0 sepc0 : mword 64)
      (m : regfile)
      :
    (* S-mode config facts *)
    eq_vec (_get_Mstatus_SIE mstatus0) ('b"1") = false ->
    eq_vec (_get_Mstatus_MPRV mstatus0) ('b"1") = false ->
    _get_Mstatus_SXL mstatus0 = 'b"10" ->
    and_vec mie_v (not_vec mdv0) = zeros' 64 ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    menvcfg0 = MENVCFG_S ->
    (* fetch: page-table geometry (SRET is a 4-byte F_Base) *)
    (* the walk's PTE read *)
    (* SRET-specific premises *)
    eq_vec (_get_Mstatus_TSR mstatus0) ('b"1") = false ->
    sret_newpriv mstatus0 = Supervisor ->
    _get_MEnvcfg_LPE menvcfg0 = ('b"0") ->
    hw_config -∗
    minstret_inv -∗
    hart_state ↦ᵣ HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ Supervisor -∗
    mstatus ↦ᵣ mstatus0 -∗
    mie ↦ᵣ mie_v -∗
    mideleg ↦ᵣ mdv0 -∗
    menvcfg ↦ᵣ menvcfg0 -∗
    sr_inv R -∗
    sepc ↦ᵣ sepc0 -∗
    pc_is pc -∗
    gpr_file m -∗
    instr pc false (SRET tt) -∗
    ( hart_state ↦ᵣ HART_ACTIVE tt -∗
      cur_privilege ↦ᵣ Supervisor -∗
      mstatus ↦ᵣ sret_ms5 mstatus0 -∗
      mie ↦ᵣ mie_v -∗
      mideleg ↦ᵣ mdv0 -∗
      menvcfg ↦ᵣ menvcfg0 -∗
      sr_inv R -∗
      sepc ↦ᵣ sepc0 -∗
      pc_is (ret_pc sepc0) -∗
      gpr_file m -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    iIntros (HSIE HMPRV HSXL Hmm HPBMTE Hmenvval0 HTSR Hsup Hlpe0)
      "#Hhw #Hminv Hhs Hpriv Hms Hmie Hmdl Hmenv Hinv Hsepc Hpc Hfile Hinstr
       Hcont".
    iDestruct (hw_config_cert with "Hhw") as "#Hcert".
    iDestruct (sb_hw_config_misa with "Hhw") as "#Hmisa".
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(_ & _ & _ & _ & #Help & _ & _ & _ & _ & _ & _ & _ & _ & %Help_np & _)".
    rewrite (mword1_not_lp elp0 Help_np).
    iApply (wp_instr_s_config_folded R pc false (SRET tt)
              mstatus0 mie_v mdv0 menvcfg0 mie_v menvcfg0
              (fun npc ms1 mdv1 =>
                 (⌜npc = ret_pc sepc0⌝ ∗ ⌜ms1 = sret_ms5 mstatus0⌝ ∗
                  ⌜mdv1 = mdv0⌝ ∗ gpr_file m ∗ sepc ↦ᵣ sepc0)%I)
              (dq := DfracOwn 1) HSIE HMPRV HSXL Hmm HPBMTE Hmenvval0
              with "Hhw Hminv Hhs Hpriv Hms Hmie Hmdl Hmenv Hinv Hpc Hinstr
                    [Hsepc Hfile] [Hcont]").
    - iIntros "Hpriv Hms Hmie Hmdl Hmenv Hslot Hclk HPC HnPC Hresv".
      iDestruct (sret_frames_in mstatus0 Supervisor (add_vec_int pc 4)
                   menvcfg0 sepc0
                   with "Hms Hpriv HnPC Hmisa Hmenv Hsepc") as "[Hrw Hro]".
      iApply (swp_mono with "[Hmie Hmdl Hclk Hslot Hresv HPC Hfile]
                             [Hrw Hro]").
      2:{ iApply (swp_execute_SRET_S mstatus0 (add_vec_int pc 4) menvcfg0
                    sepc0 HTSR Hsup Hlpe0 with "Hcert Help Hrw Hro"). }
      iIntros (e) "(-> & Hrw & Hro)".
      iDestruct (sret_frames_out (sret_ms5 mstatus0) Supervisor
                   (ret_pc sepc0) menvcfg0 sepc0 with "[$Hrw $Hro]")
        as "(Hms & Hpriv & HnPC & _ & Hmenv & Hsepc)".
      iSplitR; [done|].
      iFrame "Hpriv Hmie Hmenv Hslot Hclk".
      iSplitR "Hresv"; [| iExact "Hresv"].
      iExists (sret_ms5 mstatus0), mdv0, (ret_pc sepc0).
      iFrame "Hms Hmdl HPC HnPC".
      iSplitR; [done|]. iSplitR; [done|]. iSplitR; [done|].
      iFrame "Hfile Hsepc".
    - iNext. iIntros (npc ms1 mdv1)
        "Hhs Hpriv Hms Hmie Hmdl Hmenv Hinv Hpc
         (-> & -> & -> & Hfile & Hsepc)".
      iApply ("Hcont" with "Hhs Hpriv Hms Hmie Hmdl Hmenv Hinv Hsepc Hpc
                            Hfile").
  Qed.

  Lemma wp_sret_gpr_pt (root_ppn : mword 44)
      (pc : mword 64)
      (mstatus0 mie_v mdv0 menvcfg0 sepc0 : mword 64)
      (m : regfile)
      :
    (* S-mode config facts *)
    eq_vec (_get_Mstatus_SIE mstatus0) ('b"1") = false ->
    eq_vec (_get_Mstatus_MPRV mstatus0) ('b"1") = false ->
    _get_Mstatus_SXL mstatus0 = 'b"10" ->
    and_vec mie_v (not_vec mdv0) = zeros' 64 ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    menvcfg0 = MENVCFG_S ->
    (* fetch: page-table geometry (SRET is a 4-byte F_Base) *)
    (* the walk's PTE read *)
    (* SRET-specific premises *)
    eq_vec (_get_Mstatus_TSR mstatus0) ('b"1") = false ->
    sret_newpriv mstatus0 = Supervisor ->
    _get_MEnvcfg_LPE menvcfg0 = ('b"0") ->
    hw_config -∗
    minstret_inv -∗
    hart_state ↦ᵣ HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ Supervisor -∗
    mstatus ↦ᵣ mstatus0 -∗
    mie ↦ᵣ mie_v -∗
    mideleg ↦ᵣ mdv0 -∗
    menvcfg ↦ᵣ menvcfg0 -∗
    tlb_res_pt root_ppn -∗
    sepc ↦ᵣ sepc0 -∗
    pc_is pc -∗
    gpr_file m -∗
    instr pc false (SRET tt) -∗
    ( hart_state ↦ᵣ HART_ACTIVE tt -∗
      cur_privilege ↦ᵣ Supervisor -∗
      mstatus ↦ᵣ sret_ms5 mstatus0 -∗
      mie ↦ᵣ mie_v -∗
      mideleg ↦ᵣ mdv0 -∗
      menvcfg ↦ᵣ menvcfg0 -∗
      tlb_res_pt root_ppn -∗
      sepc ↦ᵣ sepc0 -∗
      pc_is (ret_pc sepc0) -∗
      gpr_file m -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
    Proof.
    exact (wp_sret_gpr_r (kpt_share_regime root_ppn) pc mstatus0 mie_v mdv0 menvcfg0 sepc0 m).
  Qed.

End WpSmodePtCtl.
