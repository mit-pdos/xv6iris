(* WpPushOffCsr.v -- S-mode csrrci-on-sstatus (interrupt disable) instruction lemma
   
   [noff]/[intena] accesses.  Built by cloning wp_cldsp_gpr_s / wp_csdsp_gpr_s
   (WpSmodeGpr.v, 8-byte, sp-relative) with the base register generalized and
   the access width changed 8 -> 4. *)
From Stdlib Require Import Eqdep_dec ZArith Lia List FunctionalExtensionality.
From stdpp Require Import gmap list list_monad bitvector.definitions bitvector.tactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap invariants.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import RiscvModelBytes.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvExtras RiscvTryStep RiscvFetchExec.
Require Import MinstretInv InstrBytes.
Require Import WpAdd WpFetch WpLoad WpDecode WpLeafCommon WpEntry WpEntryNew WpAuipc.
Require Import WpGpr WpGprAddi WpGprRvc WpGprShift WpGprJalr WpGprStore WpGprLogic WpGprAuipc.
Require Import SmodeCore WpSmodeGpr WpMemsetS.
Require Import WpGprCsrwCommon WpGprCsrwA WpGprCsrrCommon WpIntrBits.
From Kernel Require KernelInstrs.
From Kernel Require KernelSyms.
Local Open Scope Z_scope.
Import Defs.

(* ====================================================================== *)
(* csrrci a5,sstatus,2  (= csrrc a5,sstatus,imm5 with imm5<>0 -> CSRReadWrite)*)
(* at Supervisor, running with SIE ALREADY 0 (interrupt-disable idempotent).*)
(* ====================================================================== *)

Definition csr_sstatus : mword 12 := Ox"100".

(* RDVAL: the S-visible read of an mstatus value, as read_CSR(0x100) returns. *)
Definition sstatus_read (ms : mword 64) : mword 64 :=
  subrange_vec_dec (lower_mstatus ms) (Z.sub xlen 1) 0.

(* The value csrrc writes back: the read value with the imm-selected bits
   cleared (bit 1 = SIE for imm5 = 2). *)
Definition sstatus_write_val (ms : mword 64) (imm5 : mword 5) : mword 64 :=
  and_vec (sstatus_read ms) (not_vec (zero_extend' 64 imm5)).

(* The mstatus value the model computes after write_CSR(0x100, v): legalize the
   S-status-lifted new value.  Matches [mstatus_legalized] from WpGprCsrwA. *)
Definition legalize_sstatus_val (m v : mword 64) : mword 64 :=
  mstatus_legalized m (lift_sstatus m (Mk_Sstatus (zero_extend' 64 v))).

(* ---- set a bitvector-64 register to the value it already holds = no-op ---- *)
Lemma register_set_bv64_id (r : register_bitvector_64) (rs : regstate) :
  register_set (R_bitvector_64 r) (register_lookup (R_bitvector_64 r) rs) rs = rs.
Proof.
  destruct rs. unfold register_set, register_lookup. cbn.
  f_equal. apply functional_extensionality. intro r'.
  destruct (register_bitvector_64_beq r' r) eqn:E.
  - apply register_bitvector_64_beq_iff in E. subst r'. reflexivity.
  - reflexivity.
Qed.

(* ---- Ext_H is not supported: hartSupports / currentlyEnabled reduce false ---- *)
Lemma exec_hartSupports_H s : exec (hartSupports Ext_H) s = Some (false, s).
Proof.
  unfold hartSupports. destruct (Defs.Zwf_guarded _).
  cbn [_rec_hartSupports]. unfold Defs.assert_exp'.
  replace (Z.geb (hartSupports_measure Ext_H) 0) with true by reflexivity.
  cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM eq_refl s)).
  apply exec_returnM.
Qed.

Lemma exec_currentlyEnabled_H_false s : exec (currentlyEnabled Ext_H) s = Some (false, s).
Proof.
  unfold currentlyEnabled. destruct (Defs.Zwf_guarded _).
  cbn [_rec_currentlyEnabled]. unfold Defs.assert_exp'.
  replace (Z.geb (currentlyEnabled_measure Ext_H) 0) with true by reflexivity.
  cbn match. rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM eq_refl s)). cbn match.
  rewrite (exec_and_boolM_Some _ _ _ _ _ (exec_hartSupports_H s)). reflexivity.
Qed.

(* ---- check_CSR path for sstatus at Supervisor / CSRReadWrite ---- *)
Lemma exec_check_CSR_priv_sstatus_S s :
  exec (check_CSR_priv csr_sstatus Supervisor) s = Some (true, s).
Proof.
  unfold check_CSR_priv.
  assert (Hp : exec (privLevel_to_CSR_privbits Supervisor) s = Some ('b"01" : mword 2, s)).
  { unfold privLevel_to_CSR_privbits.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_currentlyEnabled_H_false s)). apply exec_returnM. }
  rewrite (exec_bind_Some _ _ _ _ _ Hp). rewrite exec_returnM.
  replace (zopz0zKzJ_u ('b"01" : mword 2) (csrPriv csr_sstatus)) with true
    by (vm_compute; reflexivity).
  reflexivity.
Qed.

Lemma exec_check_CSR_sstatus_S s :
  eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (check_CSR csr_sstatus Supervisor CSRReadWrite) s = Some (true, s).
Proof.
  intro HS. unfold check_CSR.
  rewrite (exec_and_boolM_Some _ _ _ _ _ (exec_check_CSR_priv_sstatus_S s)). cbn match.
  assert (HA : exec (returnM (check_CSR_access csr_sstatus CSRReadWrite) : M bool) s
               = Some (true, s)).
  { rewrite exec_returnM.
    replace (check_CSR_access csr_sstatus CSRReadWrite) with true by (vm_compute; reflexivity).
    reflexivity. }
  rewrite (exec_and_boolM_Some _ _ _ _ _ HA). cbn match.
  assert (Hacc : exec (is_CSR_accessible csr_sstatus Supervisor CSRReadWrite) s = Some (true, s)).
  { unfold is_CSR_accessible. skip_csr_false_clauses.
    replace (eq_vec csr_sstatus (Ox"100")) with true by (vm_compute; reflexivity). cbn match.
    rewrite (exec_currentlyEnabled_S s). rewrite HS. reflexivity. }
  rewrite (exec_and_boolM_Some _ _ _ _ _ Hacc). cbn match.
  unfold stateen_allows_CSR_access. cbn match. skip_csr_false_clauses.
  apply exec_returnM.
Qed.

Lemma exec_check_CSR_result_sstatus_S s :
  eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (check_CSR_result csr_sstatus Supervisor CSRReadWrite) s = Some (CSR_Check_OK tt, s).
Proof.
  intro HS. unfold check_CSR_result.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_check_CSR_sstatus_S s HS)). cbn match.
  apply exec_returnM.
Qed.

(* ---- read_CSR / legalize / write_CSR for sstatus ---- *)
Lemma exec_read_CSR_sstatus s :
  exec (read_CSR csr_sstatus) s
    = Some (sstatus_read (register_lookup mstatus s.(sregs)), s).
Proof.
  unfold read_CSR. skip_csr_false_clauses.
  replace (eq_vec csr_sstatus (Ox"100")) with true by (vm_compute; reflexivity). cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mstatus s)).
  unfold sstatus_read. apply exec_returnM.
Qed.

Lemma exec_legalize_sstatus (m v : mword 64) s :
  eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1") = true ->
  eq_vec (_get_Misa_U (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (legalize_sstatus m v) s = Some (legalize_sstatus_val m v, s).
Proof.
  intros HS HU. unfold legalize_sstatus, legalize_sstatus_val.
  apply (exec_legalize_mstatus m (lift_sstatus m (Mk_Sstatus (zero_extend' 64 v))) s HS HU).
Qed.

Lemma exec_write_CSR_sstatus (v : mword 64) s :
  eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1") = true ->
  eq_vec (_get_Misa_U (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (write_CSR csr_sstatus v) s
    = Some (Ok (subrange_vec_dec
                  (lower_mstatus (legalize_sstatus_val (register_lookup mstatus s.(sregs)) v))
                  (Z.sub xlen 1) 0),
            set_reg s mstatus (legalize_sstatus_val (register_lookup mstatus s.(sregs)) v)).
Proof.
  intros HS HU. unfold write_CSR. skip_csr_false_clauses.
  replace (eq_vec csr_sstatus (Ox"100")) with true by (vm_compute; reflexivity). cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mstatus s)).
  rewrite (exec_bind_Some _ _ _ _ _
             (exec_legalize_sstatus (register_lookup mstatus s.(sregs)) v s HS HU)).
  rewrite (exec_bind0_Some _ _ _ _ _ (exec_write_reg mstatus _ s)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mstatus _)).
  rewrite register_lookup_set.
  apply exec_returnM.
Qed.

Lemma exec_csr_id_write_callback_sstatus (d : mword 64) s :
  exec (csr_id_write_callback csr_sstatus d) s = Some (tt, s).
Proof.
  assert (H : csr_id_write_callback csr_sstatus d = returnM tt) by (vm_compute; reflexivity).
  rewrite H. apply exec_returnM.
Qed.

(* ---- the full csrrci-on-sstatus execute, with SIE-idempotence collapse ---- *)
Lemma exec_execute_csrrci_sstatus (imm5 rd : mword 5) (m : mword 64) s :
  register_lookup cur_privilege s.(sregs) = Supervisor ->
  register_lookup mstatus s.(sregs) = m ->
  eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1") = true ->
  eq_vec (_get_Misa_U (register_lookup misa s.(sregs))) ('b"1") = true ->
  eq_vec imm5 (zeros' 5) = false ->
  uint rd <> 0 ->
  legalize_sstatus_val m (sstatus_write_val m imm5) = m ->
  exec (execute (CSRImm (csr_sstatus, imm5, Regidx rd, CSRRC))) s
    = Some (RETIRE_SUCCESS,
            set_reg s (R_bitvector_64 (gpr_of_Z (uint rd))) (regval_into_reg (sstatus_read m))).
Proof.
  intros Hpriv Hm HS HU Himm Hrd Hcollapse.
  change (execute (CSRImm (csr_sstatus, imm5, Regidx rd, CSRRC)))
    with (execute_CSRImm csr_sstatus imm5 (Regidx rd) CSRRC).
  unfold execute_CSRImm.
  rewrite Himm.
  (* access_type = CSRReadWrite *)
  cbn match.
  unfold doCSR.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg cur_privilege s)). rewrite Hpriv.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_check_CSR_result_sstatus_S s HS)). cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg cur_privilege s)). rewrite Hpriv.
  unfold ext_check_CSR. cbn match.
  replace (generic_neq CSRReadWrite CSRWrite) with true by (vm_compute; reflexivity). cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_CSR_sstatus s)). rewrite Hm.
  replace (eq_vec csr_sstatus (Ox"344")) with false by (vm_compute; reflexivity).
  replace (eq_vec csr_sstatus (Ox"144")) with false by (vm_compute; reflexivity). cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM (sstatus_read m) s)).
  replace (generic_eq CSRReadWrite CSRRead) with false by (vm_compute; reflexivity). cbn match.
  (* write path: write_val = and_vec read_val (not_vec (zext imm5)) = sstatus_write_val m imm5 *)
  assert (Hid : set_reg s mstatus m = s).
  { unfold set_reg. rewrite <- Hm.
    rewrite (register_set_bv64_id mstatus s.(sregs)).
    destruct s; reflexivity. }
  assert (Hwrite : exec (write_CSR csr_sstatus (sstatus_write_val m imm5)) s
                   = Some (Ok (subrange_vec_dec (lower_mstatus m) (Z.sub xlen 1) 0), s)).
  { rewrite (exec_write_CSR_sstatus (sstatus_write_val m imm5) s HS HU).
    rewrite Hm. rewrite Hcollapse. rewrite Hid. reflexivity. }
  change (and_vec (sstatus_read m) (not_vec (zero_extend' 64 imm5)))
    with (sstatus_write_val m imm5).
  rewrite (exec_bind_Some _ _ _ _ _ Hwrite). cbn beta match.
  (* [>>] is left-associative: (wX >> callback) >> returnM.  Peel inner first. *)
  assert (Hwc : exec (wX_bits (Regidx rd) (sstatus_read m) >>
                      csr_id_write_callback csr_sstatus
                        (subrange_vec_dec (lower_mstatus m) (Z.sub xlen 1) 0)) s
                = Some (tt, set_reg s (R_bitvector_64 (gpr_of_Z (uint rd)))
                              (regval_into_reg (sstatus_read m)))).
  { rewrite (exec_bind0_Some _ _ _ _ _ (exec_wX_bits_gpr rd (sstatus_read m) s)).
    replace (Z.eqb (uint rd) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrd).
    apply (exec_csr_id_write_callback_sstatus
             (subrange_vec_dec (lower_mstatus m) (Z.sub xlen 1) 0) _). }
  rewrite (exec_bind0_Some _ _ _ _ _ Hwc).
  apply exec_returnM.
Qed.

(* ---- bit-extraction: bit 1 (SIE) of the read S-status = machine SIE ----
   [lower_mstatus]'s OUTERMOST field-update is [_update_Sstatus_SIE _ (SIE ms)]
   at bit 1; every inner update touches a strictly higher bit, so reading bit 1
   sees exactly the written SIE value.  We only unfold the outer update and use
   a single-update access lemma -- unfolding the whole 11-update tower makes the
   testbit search diverge. *)
Lemma access1_update_subrange11 (v : mword 64) (x : mword 1) :
  access_vec_dec (update_subrange_vec_dec v 1 1 x) 1 = x.
Proof.
  unfold access_vec_dec, access_mword_dec. mw_prep; tb1.
Qed.

Lemma sstatus_read_SIE (ms : mword 64) :
  access_vec_dec (sstatus_read ms) 1 = _get_Mstatus_SIE ms.
Proof.
  unfold sstatus_read. rewrite subrange64_id.
  unfold lower_mstatus, _update_Sstatus_SIE. cbn zeta.
  apply access1_update_subrange11.
Qed.

Section WpPushOffCsr.
  Context `{!riscvGS Σ}.
  Context `{CID : CpuId}.

  (* ---- csrrci rd,sstatus,imm5 at Supervisor, SIE already 0 (idempotent) ----
     4-byte instruction: PC advances +4; needs fetch geom at pc and pc+2.
     mstatus is UNCHANGED (the [Hcollapse] premise witnesses that legalizing the
     read-back S-status onto mstatus0 gives mstatus0 -- true because clearing an
     already-0 SIE is a no-op, so the write puts back exactly the S-bits read). *)
  Lemma wp_csrrci_sstatus_s (root_ppn : mword 44) E (Φ : mval -> iProp Σ)
      (pc : mword 64) (rd imm5 : mword 5)
      (m : gmap regidx (mword 64))
      (mstatus0 mie_v mdv0 menvcfg0 : mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (pmpaddr00 : type_of_register pmpaddr_n)
      (region_pte : PMA_Region) {dq : dfrac} :
    ↑minstretN ⊆ E ->
    eq_vec (_get_Mstatus_SIE mstatus0) ('b"1") = false ->
    eq_vec (_get_Mstatus_MPRV mstatus0) ('b"1") = false ->
    _get_Mstatus_SXL mstatus0 = 'b"10" ->
    and_vec mie_v (not_vec mdv0) = zeros' 64 ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    kv_fetch_geom pc -> kv_fetch_geom (add_vec_int pc 2) ->
    pmp_tor0_sfetch_all pmpcfg0 pmpaddr00 pc ->
    pmp_tor0_pte_read pmpcfg0 pmpaddr00 (pte_paddr root_ppn) ->
    (forall pmar0, pma_allows_all pmar0 ->
       matching_pma_region pmar0 (Physaddr (pte_paddr root_ppn)) 8 = Some region_pte /\
       (override_PMA (PMA_Region_attributes region_pte) PBMT_PMA).(PMA_supports_pte_read) = true) ->
    is_aligned_paddr (Physaddr (pte_paddr root_ppn)) 8 = true ->
    uint rd <> 0 ->
    eq_vec imm5 (zeros' 5) = false ->
    legalize_sstatus_val mstatus0 (sstatus_write_val mstatus0 imm5) = mstatus0 ->
    hw_config -∗ minstret_inv -∗
    hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ{ dq } Supervisor -∗ mstatus ↦ᵣ{ dq } mstatus0 -∗
    mie ↦ᵣ{ dq } mie_v -∗ mideleg ↦ᵣ{ dq } mdv0 -∗ menvcfg ↦ᵣ{ dq } menvcfg0 -∗
    pmpcfg_n ↦ᵣ{ dq } pmpcfg0 -∗ pmpaddr_n ↦ᵣ{ dq } pmpaddr00 -∗ tlb_inv root_ppn -∗
    pc_is pc -∗ gpr_file m -∗
    instr pc false (CSRImm (csr_sstatus, imm5, Regidx rd, CSRRC)) -∗
    ( hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
      cur_privilege ↦ᵣ{ dq } Supervisor -∗ mstatus ↦ᵣ{ dq } mstatus0 -∗
      mie ↦ᵣ{ dq } mie_v -∗ mideleg ↦ᵣ{ dq } mdv0 -∗ menvcfg ↦ᵣ{ dq } menvcfg0 -∗
      pmpcfg_n ↦ᵣ{ dq } pmpcfg0 -∗ pmpaddr_n ↦ᵣ{ dq } pmpaddr00 -∗ tlb_inv root_ppn -∗
      pc_is (add_vec_int pc 4) -∗
      gpr_file (<[Regidx rd := regval_into_reg (sstatus_read mstatus0)]> m) -∗
      WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    iIntros (HN HSIE HMPRV HSXL Hmm HPBMTE Hgeom Hgeom2 Hpmp Hpmpp Hpteregion Halignp Hrd Himm5 Hcollapse)
      "#Hhw #Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv
       [Hpc Hnpc] [%Hdom Hfmap] Hinstr Hcont".
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & %HmisaS & %HmisaC & %HmisaU & %HmisaM &
        %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np & %HmisaA)".
    iApply (wp_instr_s_config_tlbinv root_ppn E Φ pc false
              (CSRImm (csr_sstatus, imm5, Regidx rd, CSRRC))
              mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 region_pte
              HN HSIE HMPRV HSXL Hmm HPBMTE Hgeom (fun _ => Hgeom2) Hpmp Hpmpp Hpteregion Halignp
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hinstr").
    iIntros (σ Hpceq satp0 tlbvec_f Hmode Hasid Hppn Hconsf)
      "Hpriv Hsatp Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlb Hpbytes Hsi".
    iDestruct "Hsi" as "[Hreg Hmem]".
    iDestruct (reg_valid_dq with "Hreg Hpriv") as %Lpriv.
    iDestruct (reg_valid_dq with "Hreg Hms") as %Lms.
    iDestruct (reg_valid_dq with "Hreg Hmisa") as %Lmisa.
    assert (Hmd : m !! Regidx rd = Some (m !!! Regidx rd))
      by (apply lookup_lookup_total_dom; apply Hdom).
    iMod (reg_update _ nextPC _ (add_vec_int pc 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s_pc := set_reg σ nextPC (add_vec_int pc 4)).
    assert (Lnpc0 : register_lookup nextPC s_pc.(sregs) = add_vec_int pc 4)
      by (unfold s_pc; rewrite register_lookup_set; reflexivity).
    assert (Lpriv_spc : register_lookup cur_privilege s_pc.(sregs) = Supervisor).
    { unfold s_pc, set_reg; cbn [sregs].
      rewrite irrelevant_register_set; [ exact Lpriv | vm_compute; reflexivity ]. }
    assert (Lms_spc : register_lookup mstatus s_pc.(sregs) = mstatus0).
    { unfold s_pc, set_reg; cbn [sregs].
      rewrite irrelevant_register_set; [ exact Lms | vm_compute; reflexivity ]. }
    assert (Lmisa_spc : register_lookup misa s_pc.(sregs) = misa0).
    { unfold s_pc, set_reg; cbn [sregs].
      rewrite irrelevant_register_set; [ exact Lmisa | vm_compute; reflexivity ]. }
    iDestruct (big_sepM_insert_acc _ _ _ _ Hmd with "Hfmap") as "[Hrdc Hfins]".
    rewrite (gpr_pt_nz rd _ Hrd).
    iMod (reg_update _ (R_bitvector_64 (gpr_of_Z (uint rd))) _
            (regval_into_reg (sstatus_read mstatus0)) with "Hreg Hrdc") as "[Hreg Hrdc]".
    iDestruct ("Hfins" $! (regval_into_reg (sstatus_read mstatus0)) with "[Hrdc]") as "Hfmap".
    { rewrite (gpr_pt_nz rd _ Hrd). iExact "Hrdc". }
    iModIntro.
    iExists (set_reg s_pc (R_bitvector_64 (gpr_of_Z (uint rd)))
               (regval_into_reg (sstatus_read mstatus0))).
    iSplitR.
    { iPureIntro. rewrite Hpceq. fold s_pc.
      apply (exec_execute_csrrci_sstatus imm5 rd mstatus0 s_pc
               Lpriv_spc Lms_spc
               ltac:(rewrite Lmisa_spc; exact HmisaS)
               ltac:(rewrite Lmisa_spc; exact HmisaU)
               Himm5 Hrd Hcollapse). }
    iSplitL "Hreg Hmem".
    { unfold s_pc, set_reg; cbn [sregs mem]. iFrame "Hreg Hmem". }
    iIntros "Hhs' Hpc'".
    assert (Lnpc : register_lookup nextPC
             (set_reg s_pc (R_bitvector_64 (gpr_of_Z (uint rd)))
                (regval_into_reg (sstatus_read mstatus0))).(sregs)
             = add_vec_int pc 4)
      by (tmig; exact Lnpc0).
    iEval (rewrite Lnpc) in "Hpc'".
    iApply ("Hcont" with "Hhs' Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa [Hsatp Htlb Hpbytes]
                          [$Hpc' $Hnpc] [Hfmap]").
    { iApply (tlb_inv_close root_ppn satp0 tlbvec_f Hmode Hasid Hppn Hconsf
                with "Hsatp Htlb Hpbytes"). }
    iSplitR.
    { iPureIntro. intro r. rewrite dom_insert_L. apply elem_of_union_r. apply Hdom. }
    iExact "Hfmap".
  Qed.

End WpPushOffCsr.
