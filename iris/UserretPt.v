(* UserretPt.v -- the userret trapframe-load leaf over [utlb_inv_pt]
   (the tlb_inv_pt-style port of WpUserretTop's wp_uld):
   - pa-GENERIC state-generic width-8 LOAD towers (the WpSmodePtLeaves
     towers with the translate output page an explicit [pa] -- the
     trapframe leaf maps TRAPFRAME+off to the trapframe page, not the
     identity);
   - [wp_uld_pt]: ld rd, imm(a0) via the user table's TRAPFRAME leaf,
     through the absorption theorem -- no walk-PTE plumbing, no TLB
     hit/walk split. *)
From Stdlib Require Import ZArith Bool Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
From iris.base_logic.lib Require Import gen_heap ghost_map ghost_var invariants.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvModelBytes RiscvLang RiscvPtsto RiscvExec RiscvTryStep RiscvFetchExec RiscvExtras.
Require Import MinstretInv InstrBytes.
Require Import WpLoad ExecCommon WpGpr WpMmodeLeafBase.
Require Import SmodePte Pt4kWalk TrampPt.
Require Import SmodeCorePt WpSmodeGpr UptTree.
Require Import TrampStepPt.
Require Import UserretDefs MstatusBits WpDecode WpGprMret.
Require Import RegFile.
Require Import Riscv.rv64d_types Riscv.rv64d.
From Kernel Require KernelSyms.
Require Import MemAccessGen.
Local Open Scope Z_scope.
Import Defs.

Section RWSwalkPtPa.
Variable a : mword 64.
Variable v : mword (8*8).
Variable region : PMA_Region.
Variable s s' : mstate.
Variable pa : mword 64.
Hypothesis Halign : is_aligned_vaddr (Virtaddr a) 8 = true.
Hypothesis Hcp' : register_lookup cur_privilege s'.(sregs) = Supervisor.
Hypothesis Hmprv' : eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s'.(sregs))) ('b"1") = false.
Variable md : SATPMode.
Hypothesis Hcps : register_lookup cur_privilege s.(sregs) = Supervisor.
Hypothesis Hmprvs : eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s.(sregs))) ('b"1") = false.
Hypothesis Htm : exec (translationMode Supervisor) s = Some (md, s).
Hypothesis Htr : exec (translateAddr (Virtaddr a) (Load Data)) s
                 = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), s').
Hypothesis HA : pmpAddrMatchType_encdec_backwards
    (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s'.(sregs)) 0)) = TOR.
Hypothesis Hord : zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s'.(sregs)) 0) = false.
Hypothesis Hrange : pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
    (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s'.(sregs)) 0)) 4)
    (uint pa) (uint (to_bits 64 8)) = PMP_Match.
Hypothesis HR : eq_vec (_get_Pmpcfg_ent_R (vec_access_dec (register_lookup pmpcfg_n s'.(sregs)) 0)) ('b"1") = true.
Hypothesis Hmatch : matching_pma_region (register_lookup pma_regions s'.(sregs)) (Physaddr pa) 8 = Some region.
Hypothesis Hpalign : is_aligned_paddr (Physaddr pa) 8 = true.
Hypothesis Hread : (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_readable) = true.
Hypothesis Hc : exec (within_clint (Physaddr pa) 8) s' = Some (false, s').
Hypothesis Hsig : exec (within_sig (Physaddr pa) 8) s' = Some (false, s').
Hypothesis Hh : exec (within_htif_readable (Physaddr pa) 8) s' = Some (false, s').
Hypothesis Hdev : dev_addr pa = false.
Hypothesis Hbytes : forall j : nat, (N.of_nat j < 8)%N -> s'.(mem) !! (pa_add pa j) = Some (nth_byte v j).

Lemma exec_vmem_read_addr_8_S_walk_pa_pt :
  exec (vmem_read_addr (Virtaddr a) 8 (Load Data) false false false) s
    = Some (Ok v, s').
Proof.
  assert (Heff : exec (effectivePrivilege (Load Data) (register_lookup mstatus s.(sregs))
                         (register_lookup cur_privilege s.(sregs))) s = Some (Supervisor, s)).
  { rewrite Hcps. apply exec_effectivePrivilege_load_S. exact Hmprvs. }
  apply (exec_vmem_read_addr_aligned_load 8 a pa v Supervisor md s s'
           ltac:(right; right; right; reflexivity) Halign Heff Htm).
  apply (exec_translate_and_read_value_g 8 a pa PBMT_PMA v s s' s' Htr).
  exact (exec_mem_read_load_S PBMT_PMA pa region v (register_lookup mstatus s'.(sregs)) s'
           HA Hord Hrange HR Hmatch Hpalign Hread Hc Hsig Hh Hdev Hbytes eq_refl Hmprv' Hcp').
Qed.
End RWSwalkPtPa.

Section RWgSwalkPtPa.
Variable rs1 : mword 5.
Variable offset : mword 64.
Variable v : mword (8*8).
Variable region : PMA_Region.
Variable satp0 : mword 64.
Variable s s' : mstate.
Variable pa : mword 64.
Let ea := add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                   else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs)) offset.
Let a8 := sign_extend' 64 (subrange_vec_dec ea (xlen - 0 - 1) 0).
Hypothesis Hcp : register_lookup cur_privilege s.(sregs) = Supervisor.
Hypothesis HSXL : _get_Mstatus_SXL (register_lookup mstatus s.(sregs)) = 'b"10".
Hypothesis Hsatp : register_lookup satp s.(sregs) = satp0.
Hypothesis Hmode : _get_Satp64_Mode (Mk_Satp64 satp0) = ('b"1000" : mword 4).
Hypothesis Hmprv : eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s.(sregs))) ('b"1") = false.
Hypothesis Hmxr : eq_vec (_get_Mstatus_MXR (register_lookup mstatus s.(sregs))) ('b"0") = true.
Hypothesis Hpmm : pmm_mode_backwards (_get_MEnvcfg_PMM (register_lookup menvcfg s.(sregs))) = PMM_Disabled.
Hypothesis Halign : is_aligned_vaddr (Virtaddr a8) 8 = true.
Hypothesis Htr : exec (translateAddr (Virtaddr a8) (Load Data)) s
                 = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), s').
Hypothesis Hcp' : register_lookup cur_privilege s'.(sregs) = Supervisor.
Hypothesis Hmprv' : eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s'.(sregs))) ('b"1") = false.
Hypothesis HA : pmpAddrMatchType_encdec_backwards
    (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s'.(sregs)) 0)) = TOR.
Hypothesis Hord : zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s'.(sregs)) 0) = false.
Hypothesis Hrange : pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
    (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s'.(sregs)) 0)) 4)
    (uint pa) (uint (to_bits 64 8)) = PMP_Match.
Hypothesis HR : eq_vec (_get_Pmpcfg_ent_R (vec_access_dec (register_lookup pmpcfg_n s'.(sregs)) 0)) ('b"1") = true.
Hypothesis Hmatch : matching_pma_region (register_lookup pma_regions s'.(sregs)) (Physaddr pa) 8 = Some region.
Hypothesis Hpalign : is_aligned_paddr (Physaddr pa) 8 = true.
Hypothesis Hread : (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_readable) = true.
Hypothesis Hc : exec (within_clint (Physaddr pa) 8) s' = Some (false, s').
Hypothesis Hsig : exec (within_sig (Physaddr pa) 8) s' = Some (false, s').
Hypothesis Hh : exec (within_htif_readable (Physaddr pa) 8) s' = Some (false, s').
Hypothesis Hdev : dev_addr pa = false.
Hypothesis Hbytes : forall j : nat, (N.of_nat j < 8)%N -> s'.(mem) !! (pa_add pa j) = Some (nth_byte v j).

Lemma exec_vmem_read_8_gpr_S_walk_pa_pt :
  exec (vmem_read (Regidx rs1) offset 8 (Load Data) false false false) s = Some (Ok v, s').
Proof.
  unfold vmem_read. rewrite exec_catch_early_return.
  assert (Hgta : exec (get_transformed_data_addr (Regidx rs1) offset (Load Data) 8) s
                 = Some (Ext_DataAddr_OK (Virtaddr a8), s)).
  { unfold get_transformed_data_addr.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_ext_data_get_addr_gpr rs1 offset (Load Data) 8 s)).
    cbn match.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_transform_effective_address_load_S ea satp0 s Hcp HSXL Hsatp Hmode Hmprv Hmxr Hpmm)).
    apply exec_returnM. }
  rewrite (execR_liftR_seq _ _ _ _ _ Hgta).
  cbn match.
  rewrite (execR_bind_Some _ _ _ _ _ (execR_returnR_fwd (Virtaddr a8) s)).
  rewrite execR_liftR.
  assert (Htmv : exec (translationMode Supervisor) s = Some (Sv39, s))
    by exact (exec_translationMode_S_sv39 satp0 s HSXL Hsatp Hmode).
  rewrite (exec_vmem_read_addr_8_S_walk_pa_pt a8 v region s s' pa Halign Hcp' Hmprv'
             Sv39 Hcp Hmprv Htmv Htr HA Hord Hrange HR Hmatch Hpalign Hread Hc Hsig Hh Hdev Hbytes).
  reflexivity.
Qed.
End RWgSwalkPtPa.

Section ExecLoadGSwalkPtPa.
Variable rs1 rd : mword 5.
Variable imm : mword 12.
Variable v : mword (8*8).
Variable region : PMA_Region.
Variable satp0 : mword 64.
Variable s s' : mstate.
Variable pa : mword 64.
Let offset := sign_extend' 64 imm.
Let ea := add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                   else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs)) offset.
Let a8 := sign_extend' 64 (subrange_vec_dec ea (xlen - 0 - 1) 0).
Hypothesis Hrd : uint rd <> 0.
Hypothesis Hcp : register_lookup cur_privilege s.(sregs) = Supervisor.
Hypothesis HSXL : _get_Mstatus_SXL (register_lookup mstatus s.(sregs)) = 'b"10".
Hypothesis Hsatp : register_lookup satp s.(sregs) = satp0.
Hypothesis Hmode : _get_Satp64_Mode (Mk_Satp64 satp0) = ('b"1000" : mword 4).
Hypothesis Hmprv : eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s.(sregs))) ('b"1") = false.
Hypothesis Hmxr : eq_vec (_get_Mstatus_MXR (register_lookup mstatus s.(sregs))) ('b"0") = true.
Hypothesis Hpmm : pmm_mode_backwards (_get_MEnvcfg_PMM (register_lookup menvcfg s.(sregs))) = PMM_Disabled.
Hypothesis Halign : is_aligned_vaddr (Virtaddr a8) 8 = true.
Hypothesis Htr : exec (translateAddr (Virtaddr a8) (Load Data)) s
                 = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), s').
Hypothesis Hcp' : register_lookup cur_privilege s'.(sregs) = Supervisor.
Hypothesis Hmprv' : eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s'.(sregs))) ('b"1") = false.
Hypothesis HA : pmpAddrMatchType_encdec_backwards
    (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s'.(sregs)) 0)) = TOR.
Hypothesis Hord : zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s'.(sregs)) 0) = false.
Hypothesis Hrange : pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
    (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s'.(sregs)) 0)) 4)
    (uint pa) (uint (to_bits 64 8)) = PMP_Match.
Hypothesis HR : eq_vec (_get_Pmpcfg_ent_R (vec_access_dec (register_lookup pmpcfg_n s'.(sregs)) 0)) ('b"1") = true.
Hypothesis Hmatch : matching_pma_region (register_lookup pma_regions s'.(sregs)) (Physaddr pa) 8 = Some region.
Hypothesis Hpalign : is_aligned_paddr (Physaddr pa) 8 = true.
Hypothesis Hread : (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_readable) = true.
Hypothesis Hc : exec (within_clint (Physaddr pa) 8) s' = Some (false, s').
Hypothesis Hsig : exec (within_sig (Physaddr pa) 8) s' = Some (false, s').
Hypothesis Hh : exec (within_htif_readable (Physaddr pa) 8) s' = Some (false, s').
Hypothesis Hdev : dev_addr pa = false.
Hypothesis Hbytes : forall j : nat, (N.of_nat j < 8)%N -> s'.(mem) !! (pa_add pa j) = Some (nth_byte v j).

Lemma exec_execute_LOAD_8_gpr_S_walk_pa_pt :
  exec (execute (LOAD (imm, Regidx rs1, Regidx rd, false, 8))) s
    = Some (RETIRE_SUCCESS,
            set_reg s' (R_bitvector_64 (gpr_of_Z (uint rd))) (regval_into_reg (extend_value false v))).
Proof.
  change (execute (LOAD (imm, Regidx rs1, Regidx rd, false, 8)))
    with (execute_LOAD imm (Regidx rs1) (Regidx rd) false 8).
  unfold execute_LOAD.
  replace (8 <=? xlen_bytes) with true by (vm_compute; reflexivity).
  assert (Hass : exec (assert_exp' true "extensions/I/base_insts.sail:289.28-289.29" : M (true = true)) s = Some (@eq_refl bool true, s)) by reflexivity.
  rewrite (exec_bind_Some _ _ _ _ _ Hass).
  rewrite (exec_bind_Some _ _ _ _ _
    (exec_vmem_read_8_gpr_S_walk_pa_pt rs1 offset v region satp0 s s' pa Hcp HSXL Hsatp Hmode Hmprv Hmxr Hpmm Halign
       Htr Hcp' Hmprv' HA Hord Hrange HR Hmatch Hpalign Hread Hc Hsig Hh Hdev Hbytes)).
  cbn match.
  assert (Hw : exec (wX_bits (Regidx rd) (extend_value false v)) s'
               = Some (tt, set_reg s' (R_bitvector_64 (gpr_of_Z (uint rd)))
                              (regval_into_reg (extend_value false v)))).
  { rewrite (exec_wX_bits_gpr rd (extend_value false v) s').
    rewrite (proj2 (Z.eqb_neq (uint rd) 0) Hrd). reflexivity. }
  rewrite (exec_bind0_Some _ _ _ _ _ Hw).
  apply exec_returnM.
Qed.
End ExecLoadGSwalkPtPa.

(* the kernel TLB's trampoline slot after any kernel-consistent history:
   empty, a non-matching (hash-63, non-trampoline) entry, or the kernel
   table's own trampoline entry (an A/D variant of [pte_tramp], with the
   cached walk path = the kernel tree's).  Feeds the userret satp-switch:
   the stale hit after [csrw satp] lands on the SAME physical page. *)

Lemma tfcat_unsigned (tfp : mword 44) (x : mword 12) :
  bv_unsigned (zero_extend' 64 (concat_vec tfp x)) = bv_unsigned tfp * 4096 + bv_unsigned x.
Proof.
  pose proof (bv_unsigned_in_range _ x) as Hx. unfold bv_modulus in Hx.
  change (Z.of_N (MachineWord.MachineWord.Z_idx 12)) with 12 in Hx.
  unfold zero_extend', concat_vec.
  cbv [Operators_mwords.zero_extend Operators_mwords.extz_vec
       Operators_mwords.word_binop Operators_mwords.with_word' to_word get_word
       SailStdpp.Values.with_word autocast].
  cbn.
  destruct (Z.eq_dec (Z.of_N (44 + 12)) (44 + 12)) as [e | ne]; [| exfalso; exact (ne eq_refl)].
  rewrite (TypeCasts.cast_Z_refl (H := e)).
  unfold to_word_idx. rewrite MachineWord.MachineWord.cast_idx_refl.
  unfold MachineWord.MachineWord.zero_extend, MachineWord.MachineWord.concat, Values.to_word.
  erewrite bv_zero_extend_unsigned by (cbn; lia).
  erewrite bv_concat_unsigned by (cbn; lia).
  change (Z.of_N (MachineWord.MachineWord.Z_idx 12)) with 12.
  erewrite Z.shiftl_mul_pow2 by lia.
  change (2 ^ 12) with 4096.
  apply Z_lor_disjoint_add.
  change 4096 with (2 ^ 12).
  apply Z_land_shift_low; [lia |].
  change (2 ^ 12) with 4096.
  pose proof (bv_unsigned_in_range _ x) as Hx2.
  change (MachineWord.MachineWord.Z_idx 12) with 12%N in Hx2.
  unfold bv_modulus in Hx2.
  change (Z.of_N 12%N) with 12 in Hx2.
  change (2 ^ 12) with 4096 in Hx2.
  lia.
Qed.

Lemma tfcat_aligned8 (tfp : mword 44) (x : mword 12) :
  bv_unsigned x `mod` 8 = 0 ->
  is_aligned_paddr (Physaddr (zero_extend' 64 (concat_vec tfp x))) 8 = true.
Proof.
  intro Hx8. unfold is_aligned_paddr. apply Z.eqb_eq.
  rewrite uint_unsigned.
  rewrite tfcat_unsigned.
  rewrite Z.rem_mod_nonneg; [| | lia].
  - rewrite Zplus_mod. rewrite Hx8.
    replace (bv_unsigned tfp * 4096) with ((bv_unsigned tfp * 512) * 8) by lia.
    rewrite Z_mod_mult. reflexivity.
  - pose proof (bv_unsigned_in_range _ tfp) as Ht. unfold bv_modulus in Ht.
    pose proof (bv_unsigned_in_range _ x) as Hx. unfold bv_modulus in Hx.
    nia.
Qed.

Section WpUldPt.
  Context `{!riscvGS Σ, !sieG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  (* ld rd, imm(a0) inside userret: instruction on the TRAMPOLINE page,
     data through the user table's TRAPFRAME leaf.  All the walk-PTE cell
     plumbing and the TLB hit/walk split of the old [wp_uld] are gone --
     the absorption theorem handles the data translation, the invariant
     absorbs whatever the walk did. *)
  Lemma wp_uld_pt (uroot tfp : mword 44) (um : gmap (mword 27) (mword 64))
      (off immz : Z) (rd : mword 5) (is_rvc : bool)
      (m : regfile) (v : bv 64)
      (mstatus0 mie_v mdv0 menvcfg0 : mword 64) {dq dqm : dfrac} :
    let va := uva off in
    let pa := upa off in
    let imm : mword 12 := mword_of_int immz in
    let iva : mword 64 := mword_of_int (TRAPFRAME + immz) in
    let tfpa : mword 64 := zero_extend' 64 (concat_vec tfp
        (subrange_vec_dec (bits_of_virtaddr (Virtaddr iva)) (Z.sub pagesize_bits 1) 0)) in
    uint rd <> 0 ->
    eq_vec (_get_Mstatus_SIE mstatus0) ('b"1") = false ->
    eq_vec (_get_Mstatus_MPRV mstatus0) ('b"1") = false ->
    _get_Mstatus_SXL mstatus0 = 'b"10" ->
    and_vec mie_v (not_vec mdv0) = zeros' 64 ->
    eq_vec (_get_Mstatus_MXR mstatus0) ('b"0") = true ->
    pmm_mode_backwards (_get_MEnvcfg_PMM menvcfg0) = PMM_Disabled ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    menvcfg0 = MENVCFG_S ->
    (* GPR: a0 holds TRAPFRAME *)
    m !!! Regidx (mword_of_int 10) = mword_of_int TRAPFRAME ->
    (* fetch va/pa geometry (vm_compute per instruction) *)
    neq_vec (bits_of_virtaddr (Virtaddr va))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false ->
    svpn_of va = tramp_vpn ->
    zero_extend' 64 (concat_vec tramp_ppn
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub pagesize_bits 1) 0)) = pa ->
    neq_vec (bits_of_virtaddr (Virtaddr (add_vec_int va 2)))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr (add_vec_int va 2))) (Z.sub 39 1) 0)) = false ->
    svpn_of (add_vec_int va 2) = tramp_vpn ->
    zero_extend' 64 (concat_vec tramp_ppn
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr (add_vec_int va 2))) (Z.sub pagesize_bits 1) 0)) = add_vec_int pa 2 ->
    is_aligned_vaddr (Virtaddr va) 2 = true ->
    is_aligned_vaddr (Virtaddr pa) 4 = is_aligned_vaddr (Virtaddr va) 4 ->
    is_aligned_paddr (Physaddr pa) 2 = true ->
    is_aligned_paddr (Physaddr (add_vec_int pa 2)) 2 = true ->
    (is_aligned_vaddr (Virtaddr va) 4 = true -> is_aligned_paddr (Physaddr pa) 4 = true) ->
    (* data va geometry (vm_compute per instruction) *)
    add_vec (mword_of_int TRAPFRAME) (sign_extend' 64 imm) = iva ->
    neq_vec (bits_of_virtaddr (Virtaddr iva))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr iva)) (Z.sub 39 1) 0)) = false ->
    svpn_of iva = tf_vpn ->
    is_aligned_vaddr (Virtaddr iva) 8 = true ->
    bv_unsigned (subrange_vec_dec (bits_of_virtaddr (Virtaddr iva)) (Z.sub pagesize_bits 1) 0) `mod` 8 = 0 ->
    hw_config -∗
    minstret_inv -∗
    hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ{ dq } Supervisor -∗
    mstatus ↦ᵣ{ dq } mstatus0 -∗
    mie ↦ᵣ{ dq } mie_v -∗
    mideleg ↦ᵣ{ dq } mdv0 -∗
    menvcfg ↦ᵣ{ dq } menvcfg0 -∗
    utlb_inv_pt uroot tfp um -∗
    pc_is va -∗
    gpr_file m -∗
    instr pa is_rvc (LOAD (imm, Regidx (mword_of_int 10), Regidx rd, false, 8)) -∗
    tfpa ↦ₚ₈{ dqm } v -∗
    ( hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
      cur_privilege ↦ᵣ{ dq } Supervisor -∗
      mstatus ↦ᵣ{ dq } mstatus0 -∗
      mie ↦ᵣ{ dq } mie_v -∗
      mideleg ↦ᵣ{ dq } mdv0 -∗
      menvcfg ↦ᵣ{ dq } menvcfg0 -∗
      utlb_inv_pt uroot tfp um -∗
      pc_is (add_vec_int va (if is_rvc then 2 else 4)) -∗
      gpr_file (<[Regidx rd := regval_into_reg v]> m) -∗
      tfpa ↦ₚ₈{ dqm } v -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros va pa imm iva tfpa Hrd HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmenvval0 Ha0
      Hcanon Hvpn Hident Hcanon2 Hvpn2 Hident2 Hva2 Hpa4va4 Hpa2al Hpa2al2 Hpa4al
      Heva Hcanond Hvpnd Halignd Hmod8.
    iIntros "#Hhw #Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hutlb
             [Hpc Hnpc] [%Hdom Hfmap] Hinstr Hbw Hcont".
    iDestruct (phys_word_pointsto_ram with "Hbw") as %Hram_tf.
    iDestruct (phys_word_pointsto_ram7 with "Hbw") as %Hram_tf7.
    iDestruct "Hbw" as "[%Hbal Hbytes]".
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & #Hsenv & %HmisaS & %HmisaC &
        %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np & %HmisaA & %Hmisa_val0 & %Hmseccfg_val0 & #Hkmapb)".
    destruct (pma_all_ram Hpma_all tfpa 8
                 (pma_access_ram _ _ _ Hram_tf Hram_tf7 (pma_width_ok 8 eq_refl eq_refl) eq_refl eq_refl)) as (region_ld & Hmatch_ld0 & _ & Hread_ld & _).
    iApply (wp_instr_u_pt uroot tfp um va pa is_rvc
              (LOAD (imm, Regidx (mword_of_int 10), Regidx rd, false, 8))
              mstatus0 mie_v mdv0 menvcfg0 dq
 HSIE HMPRV HSXL Hmm HPBMTE Hmenvval0
              Hcanon Hvpn Hident Hcanon2 Hvpn2 Hident2 Hva2 Hpa4va4 Hpa2al Hpa2al2 Hpa4al
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hutlb Hpc Hinstr").
    iIntros (σ Hpceq)
      "Hpriv Hms Hmie Hmdl Hmenv Hutlb Hsi".
    iDestruct "Hsi" as "[Hreg [Hmem Hdev]]".
    (* peel the satp value and the PMP facts, then reassemble *)
    iDestruct "Hutlb" as (usatp tlbvec1 t1)
      "(Hsatp & %Hmode & %Hasid & %Hppn & Htlb & %Htlbok & %Hspec & %Hwf & %Hpmawimpl & Ht & Hpmp)".
    iDestruct "Hpmp" as (pmpcfg0 pmpaddr00)
      "(Hpc0 & Hpa0 & %HA0 & %Hord0 & %HX & %HW & %HR & %Hcov)".
    iDestruct (reg_valid_dq with "Hreg Hsatp") as %Lsatp.
    iDestruct (reg_valid_dq with "Hreg Hpc0")  as %Lpmpc.
    iDestruct (reg_valid_dq with "Hreg Hpa0")  as %Lpmpaddr.
    iAssert (utlb_inv_pt uroot tfp um) with "[Hsatp Htlb Ht Hpc0 Hpa0]" as "Hutlb".
    { iExists usatp, tlbvec1, t1. iFrame "Hsatp Htlb Ht".
      iSplit; [iPureIntro; exact Hmode |].
      iSplit; [iPureIntro; exact Hasid |].
      iSplit; [iPureIntro; exact Hppn |].
      iSplit; [iPureIntro; exact Htlbok |].
      iSplit; [iPureIntro; exact Hspec |].
      iSplit; [iPureIntro; exact Hwf |].
      iSplit; [iPureIntro; exact Hpmawimpl |].
      iExists pmpcfg0, pmpaddr00. iFrame "Hpc0 Hpa0". iPureIntro. tauto. }
    iDestruct (reg_valid_dq with "Hreg Hpriv") as %Lpriv.
    iDestruct (reg_valid_dq with "Hreg Hms")   as %Lms.
    iDestruct (reg_valid_dq with "Hreg Hmenv") as %Lmenv.
    iDestruct (reg_valid_dq with "Hreg Hpma")  as %Lpma.
    iDestruct (reg_valid_dq with "Hreg Hhtif") as %Lhtif.
    iDestruct (reg_valid_dq with "Hreg Hmisa") as %Lmisa.
    assert (Hma0v : m (Regidx (mword_of_int 10 : mword 5)) = mword_of_int TRAPFRAME)
      by exact Ha0.
    iAssert (⌜addr_is_ram tfpa⌝)%I as %Hrampa.
    { iDestruct (big_sepL_lookup _ _ 0%nat 0%nat with "Hbytes") as "Hb0".
      { rewrite lookup_seq_lt; [reflexivity | lia]. }
      iDestruct (phys_ram with "Hb0") as %Hr0. rewrite pa_add_0 in Hr0. iPureIntro. exact Hr0. }
    iAssert (⌜addr_is_ram (pa_add tfpa 7)⌝)%I as %Hrampa7.
    { iDestruct (big_sepL_lookup _ _ 7%nat 7%nat with "Hbytes") as "Hb7".
      { rewrite lookup_seq_lt; [reflexivity | lia]. }
      iDestruct (phys_ram with "Hb7") as %Hr. iPureIntro. exact Hr. }
    assert (Hlo : (ram_base <= uint tfpa)%Z) by (destruct Hrampa as [Hl _]; exact Hl).
    assert (Hfit : (uint tfpa + 8 <= ram_base + ram_size)%Z).
    { assert (Hnw : (uint tfpa + Z.of_nat 7 < 18446744073709551616)%Z).
      { destruct Hrampa as [_ Hh]. unfold ram_base, ram_size in Hh. change (Z.of_nat 7) with 7. lia. }
      pose proof (uint_pa_add tfpa 7 Hnw) as Heq.
      destruct Hrampa7 as [_ Hhi7]. rewrite Heq in Hhi7. change (Z.of_nat 7) with 7 in Hhi7.
      unfold ram_base, ram_size in *. lia. }
    pose proof (ram_pmp_match_w tfpa (vec_access_dec pmpaddr00 0) 8 ltac:(lia) ltac:(vm_compute; reflexivity) Hlo Hfit Hcov) as Hrange_ld.
    pose proof (tfcat_aligned8 tfp _ Hmod8) as Hpalign8.
    iMod (reg_update _ nextPC _ (add_vec_int va (if is_rvc then 2 else 4)) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s_pc := set_reg σ nextPC (add_vec_int va (if is_rvc then 2 else 4))).
    iDestruct (big_sepM_lookup_acc _ _ _ _ (rf_to_gmap_lookup m (Regidx (mword_of_int 10 : mword 5))) with "Hfmap") as "[Hspc Hfb1]".
    iDestruct (gpr_pt_value (mword_of_int 10) (m (Regidx (mword_of_int 10 : mword 5))) s_pc with "Hreg Hspc") as %Lva.
    iDestruct ("Hfb1" with "Hspc") as "Hfmap".
    assert (Lpriv_pc : register_lookup cur_privilege s_pc.(sregs) = Supervisor)
      by (unfold s_pc; tmig; exact Lpriv).
    assert (Lms_pc : register_lookup mstatus s_pc.(sregs) = mstatus0)
      by (unfold s_pc; tmig; exact Lms).
    assert (Lsatp_pc : register_lookup satp s_pc.(sregs) = usatp)
      by (unfold s_pc; tmig; exact Lsatp).
    assert (Lmenv_pc : register_lookup menvcfg s_pc.(sregs) = menvcfg0)
      by (unfold s_pc; tmig; exact Lmenv).
    assert (Lpma_pc : register_lookup pma_regions s_pc.(sregs) = pmar0)
      by (unfold s_pc; tmig; exact Lpma).
    assert (Lhtif_pc : register_lookup htif_tohost_base s_pc.(sregs) = None)
      by (unfold s_pc; tmig; exact Lhtif).
    assert (Lmisa_pc : register_lookup misa s_pc.(sregs) = misa0)
      by (unfold s_pc; tmig; exact Lmisa).
    assert (Lpmpc_pc : register_lookup pmpcfg_n s_pc.(sregs) = pmpcfg0)
      by (unfold s_pc; tmig; exact Lpmpc).
    assert (Lpmpaddr_pc : register_lookup pmpaddr_n s_pc.(sregs) = pmpaddr00)
      by (unfold s_pc; tmig; exact Lpmpaddr).
    assert (Lmisa_pc' : register_lookup misa s_pc.(sregs) = MISA_C)
      by (rewrite Lmisa_pc; exact Hmisa_val0).
    assert (Lmenv_pc' : register_lookup menvcfg s_pc.(sregs) = MENVCFG_S)
      by (rewrite Lmenv_pc; exact Hmenvval0).
    assert (LSXL_pc : _get_Mstatus_SXL (register_lookup mstatus s_pc.(sregs)) = 'b"10")
      by (rewrite Lms_pc; exact HSXL).
    assert (Lpma_pc' : pma_allows_all (register_lookup pma_regions s_pc.(sregs)))
      by (rewrite Lpma_pc; exact Hpma_all).
    assert (Hif : (if Z.eqb (uint (mword_of_int 10 : mword 5)) 0 then zero_reg
                   else register_lookup (R_bitvector_64 (gpr_of_Z (uint (mword_of_int 10 : mword 5)))) s_pc.(sregs))
                  = mword_of_int TRAPFRAME).
    { rewrite Lva. exact Hma0v. }
    (* the vmem level hands back the value itself now, so the retire's
       [extend_value] is just the sign-extension identity at width 8 *)
    assert (Hev : extend_value (n := 8 * 8) false v = v).
    { unfold extend_value. apply sign_extend'_id. }
    (* the trapframe data translate through the absorption theorem *)
    iMod (utlb_inv_pt_translateAddr_tf_load uroot tfp um iva tfpa s_pc
            Hvpnd Hcanond eq_refl
            Lmisa_pc' Lmenv_pc' Lhtif_pc Lpriv_pc LSXL_pc
            (exec_effectivePrivilege_load_S (register_lookup mstatus s_pc.(sregs)) s_pc
               ltac:(rewrite Lms_pc; exact HMPRV))
            (exec_is_shadow_stack_load s_pc)
            Lpma_pc' with "Hreg Hmem Hutlb")
      as (s_tr) "(%Htr0 & %Hmdevtr & %Hshtr & Hreg & Hmem & Hutlb)".
    pose proof (pt_regs_preserved _ _ Hshtr) as Hprestr.
    assert (Lpriv_tr : register_lookup cur_privilege s_tr.(sregs) = Supervisor)
      by (rewrite (Hprestr cur_privilege ltac:(vm_compute; reflexivity)); exact Lpriv_pc).
    assert (Lms_tr : register_lookup mstatus s_tr.(sregs) = mstatus0)
      by (rewrite (Hprestr mstatus ltac:(vm_compute; reflexivity)); exact Lms_pc).
    assert (Lpmpc_tr : register_lookup pmpcfg_n s_tr.(sregs) = pmpcfg0)
      by (rewrite (Hprestr pmpcfg_n ltac:(vm_compute; reflexivity)); exact Lpmpc_pc).
    assert (Lpmpaddr_tr : register_lookup pmpaddr_n s_tr.(sregs) = pmpaddr00)
      by (rewrite (Hprestr pmpaddr_n ltac:(vm_compute; reflexivity)); exact Lpmpaddr_pc).
    assert (Lpma_tr : register_lookup pma_regions s_tr.(sregs) = pmar0)
      by (rewrite (Hprestr pma_regions ltac:(vm_compute; reflexivity)); exact Lpma_pc).
    assert (Lhtif_tr : register_lookup htif_tohost_base s_tr.(sregs) = None)
      by (rewrite (Hprestr htif_tohost_base ltac:(vm_compute; reflexivity)); exact Lhtif_pc).
    iAssert (⌜forall j : nat, (N.of_nat j < 8)%N ->
              s_tr.(mem) !! (pa_add tfpa j) = Some (nth_byte v j)⌝)%I as %Hbytesf_tr.
    { iIntros (j Hj). assert (Hj' : (j < 8)%nat) by lia.
      iDestruct (big_sepL_lookup _ _ j j with "Hbytes") as "Hbj".
      { rewrite lookup_seq_lt; [reflexivity | exact Hj']. }
      iDestruct (phys_valid with "Hmem Hbj") as %Hmj. iPureIntro. exact Hmj. }
    pose proof (within_clint_false tfpa 8 s_tr (addr_is_ram_not_in_clint _ Hrampa) ltac:(lia)) as Hwc.
    pose proof (within_sig_false tfpa 8 s_tr (addr_is_ram_not_in_sig _ Hrampa) ltac:(lia)) as Hws.
    pose proof (within_htif_false tfpa 8 s_tr Lhtif_tr) as Hwh.
    assert (Hload : exec (execute (LOAD (imm, Regidx (mword_of_int 10), Regidx rd, false, 8))) s_pc
                    = Some (RETIRE_SUCCESS,
                            set_reg s_tr (R_bitvector_64 (gpr_of_Z (uint rd)))
                              (regval_into_reg v))).
    { rewrite <- Hev.
      apply (exec_execute_LOAD_8_gpr_S_walk_pa_pt (mword_of_int 10) rd imm v region_ld usatp s_pc s_tr tfpa Hrd
               Lpriv_pc ltac:(rewrite Lms_pc; exact HSXL) Lsatp_pc Hmode
               ltac:(rewrite Lms_pc; exact HMPRV) ltac:(rewrite Lms_pc; exact HMXR)
               ltac:(rewrite Lmenv_pc; exact Hpmm)
               ltac:(rewrite Hif subrange_id sign_extend'_id Heva; exact Halignd)
               ltac:(rewrite Hif subrange_id sign_extend'_id Heva; exact Htr0)
               Lpriv_tr ltac:(rewrite Lms_tr; exact HMPRV)
               ltac:(rewrite Lpmpc_tr; exact HA0) ltac:(rewrite Lpmpaddr_tr; exact Hord0)
               ltac:(rewrite Lpmpaddr_tr; exact Hrange_ld) ltac:(rewrite Lpmpc_tr; exact HR)
               ltac:(rewrite Lpma_tr; exact Hmatch_ld0)
               Hpalign8
               Hread_ld ltac:(apply Hwc)
               ltac:(apply Hws)
               ltac:(apply Hwh)
               ltac:(exact (addr_is_ram_not_dev _ Hrampa))
               ltac:(exact Hbytesf_tr)). }
    iDestruct (big_sepM_insert_acc _ _ _ _ (rf_to_gmap_lookup m (Regidx rd)) with "Hfmap") as "[Hrdc Hfins]".
    rewrite (gpr_pt_nz rd _ Hrd).
    iMod (reg_update _ (R_bitvector_64 (gpr_of_Z (uint rd))) _ (regval_into_reg v)
            with "Hreg Hrdc") as "[Hreg Hrdc]".
    iDestruct ("Hfins" $! (regval_into_reg v) with "[Hrdc]") as "Hfmap".
    { rewrite (gpr_pt_nz rd _ Hrd). iExact "Hrdc". }
    iEval (rewrite -(rf_to_gmap_upd m (Regidx rd) (regval_into_reg v))) in "Hfmap".
    iModIntro.
    iExists (set_reg s_tr (R_bitvector_64 (gpr_of_Z (uint rd))) (regval_into_reg v)).
    iSplitR.
    { iPureIntro. rewrite Hpceq. fold s_pc. exact Hload. }
    iSplitL "Hreg Hmem Hdev".
    { unfold set_reg; cbn [sregs mem mdev].
      rewrite Hmdevtr. unfold s_pc, set_reg; cbn [mdev].
      iFrame "Hreg Hmem Hdev". }
    iIntros "Hhs' Hpc'".
    assert (Lnpc : register_lookup nextPC
             (set_reg s_tr (R_bitvector_64 (gpr_of_Z (uint rd))) (regval_into_reg v)).(sregs)
             = add_vec_int va (if is_rvc then 2 else 4)).
    { unfold set_reg at 1; cbn [sregs]. tmig.
      rewrite (Hprestr nextPC ltac:(vm_compute; reflexivity)).
      unfold s_pc; cbn [sregs]. rewrite register_lookup_set. reflexivity. }
    iEval (rewrite Lnpc) in "Hpc'".
    iDestruct (phys_word_pointsto_intro tfpa dqm v Hpalign8 with "Hbytes") as "Hbytes".
    iApply ("Hcont" with "Hhs' Hpriv Hms Hmie Hmdl Hmenv Hutlb
                          [$Hpc' $Hnpc] [Hfmap] Hbytes").
    iSplitR.
    { iPureIntro. apply rf_to_gmap_dom. }
    iExact "Hfmap".
  Qed.

End WpUldPt.

(* ===================================================================== *)
(* sret to USER mode: pure execute reductions.                                 *)
(* ===================================================================== *)

(* get_xLPE at User with senvcfg = 0 and menvcfg = MENVCFG_S: reads
   senvcfg/menvcfg/senvcfg (via read_senvcfg); the LPE bit of the
   SSE-merged senvcfg is 0. *)
Lemma exec_get_xLPE_U (sz : mstate) :
  eq_vec (_get_Misa_S (register_lookup misa sz.(sregs))) ('b"1") = true ->
  register_lookup senvcfg sz.(sregs) = mword_of_int 0 ->
  register_lookup menvcfg sz.(sregs) = MENVCFG_S ->
  exec (get_xLPE User) sz = Some (false, sz).
Proof.
  intros HS Hsenv Hmenv.
  unfold get_xLPE. destruct (Defs.Zwf_guarded _).
  cbn [_rec_get_xLPE]. unfold Defs.assert_exp'.
  replace (Z.geb 2 0) with true by reflexivity.
  cbn match. rewrite (exec_bind_Some _ _ _ _ _ (exec_returnm eq_refl sz)). cbn match.
  match goal with |- context[_rec_currentlyEnabled Ext_S ?k ?a] =>
    assert (HrecS : exec (_rec_currentlyEnabled Ext_S k a) sz
                    = Some (eq_vec (_get_Misa_S (register_lookup misa sz.(sregs))) ('b"1"), sz)) end.
  { match goal with |- context[_rec_currentlyEnabled Ext_S ?k ?a] => destruct a end.
    cbn [_rec_currentlyEnabled]. unfold Defs.assert_exp'.
    match goal with |- context[Z.geb ?kk 0] => change (Z.geb kk 0) with true end.
    cbn match. rewrite (exec_bind_Some _ _ _ _ _ (exec_returnm eq_refl sz)). cbn match.
    rewrite (exec_and_boolM_Some _ _ _ _ _ (exec_hartSupports_S sz)). cbn match.
    rewrite (exec_and_boolM_Some _ _ sz
               (eq_vec (_get_Misa_S (register_lookup misa sz.(sregs))) ('b"1")) sz).
    - destruct (eq_vec (_get_Misa_S (register_lookup misa sz.(sregs))) ('b"1")) eqn:?.
      + match goal with |- context[_rec_currentlyEnabled Ext_Zicsr ?k2 ?a2] =>
          exact (exec_rec_cE_Zicsr_any k2 a2 sz ltac:(reflexivity)) end.
      + reflexivity.
    - rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg misa sz)). apply exec_returnM. }
  rewrite (exec_bind_Some _ _ _ _ _ HrecS).
  rewrite HS. cbv iota.
  (* read_senvcfg: senvcfg, menvcfg, senvcfg -- all pinned *)
  unfold read_senvcfg.
  assert (Hrs : exec (Defs.bind (Defs.read_reg senvcfg)
           (fun w0 => Defs.bind (Defs.read_reg menvcfg)
              (fun w1 => Defs.bind (Defs.read_reg senvcfg)
                 (fun w2 => returnM (_update_SEnvcfg_SSE w0
                              (and_vec (_get_MEnvcfg_SSE w1) (_get_SEnvcfg_SSE w2))))))) sz
         = Some (_update_SEnvcfg_SSE (mword_of_int 0)
                   (and_vec (_get_MEnvcfg_SSE MENVCFG_S)
                            (_get_SEnvcfg_SSE (mword_of_int 0))), sz)).
  { rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg senvcfg sz)).
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg menvcfg sz)).
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg senvcfg sz)).
    rewrite Hsenv. rewrite Hmenv. apply exec_returnM. }
  rewrite (exec_bind_Some _ _ _ _ _ Hrs).
  match goal with |- context[bool_bit_backwards ?b] =>
    replace (bool_bit_backwards b) with false by (vm_compute; reflexivity) end.
  apply exec_returnM.
Qed.

(* The SRET execute reduction (verbatim WpSmodeSret's [ExecSRET] tower)
   with the [get_xLPE] premise ALSO carrying the senvcfg and misa lookups
   of the intermediate state -- [get_xLPE User] reads both. *)
Section ExecSRETU.
  Context (s : mstate) (lpe : bool) (menvcfg0 : mword 64).
  Let ms0 := register_lookup mstatus s.(sregs).
  Let ms1 := update_subrange_vec_dec ms0 1 1 (_get_Mstatus_SPIE ms0).
  Let ms2 := update_subrange_vec_dec ms1 5 5 ('b"1").
  Let newpriv : Privilege := if eq_vec (_get_Mstatus_SPP ms2) ('b"1") then Supervisor else User.
  Let ms3 := update_subrange_vec_dec ms2 8 8 ('b"0").
  Let ms4 := update_subrange_vec_dec ms3 17 17 ('b"0").
  Let ms5 := update_subrange_vec_dec ms4 23 23 (landing_pad_bits_backwards NO_LP_EXPECTED).
  Let elpv := if lpe then _get_Mstatus_SPELP ms4 else landing_pad_bits_backwards NO_LP_EXPECTED.
  Let tgt := ret_pc (register_lookup sepc s.(sregs)).
  Let sF := set_reg (set_reg (set_reg (set_reg (set_reg
              (set_reg (set_reg (set_reg s mstatus ms1) mstatus ms2)
                       cur_privilege newpriv) mstatus ms3) mstatus ms4)
              mstatus ms5) elp elpv) nextPC tgt.

  Hypothesis Hpriv : register_lookup cur_privilege s.(sregs) = Supervisor.
  Hypothesis HS : eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1") = true.
  Hypothesis HTSR : eq_vec (_get_Mstatus_TSR ms0) ('b"1") = false.
  Hypothesis Hmc : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true.
  Hypothesis Hmenv : register_lookup menvcfg s.(sregs) = menvcfg0.
  Hypothesis Hlpe : forall sz : mstate,
      register_lookup menvcfg sz.(sregs) = menvcfg0 ->
      register_lookup senvcfg sz.(sregs) = register_lookup senvcfg s.(sregs) ->
      register_lookup misa sz.(sregs) = register_lookup misa s.(sregs) ->
      exec (get_xLPE newpriv) sz = Some (lpe, sz).

  Lemma exec_execute_SRET_menvU : exec (execute (SRET tt)) s = Some (RETIRE_SUCCESS, sF).
  Proof using All.
    change (execute (SRET tt)) with (execute_SRET tt).
    unfold execute_SRET.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg cur_privilege s)).
    rewrite Hpriv. cbn match.
    assert (Harm1 : exec (Defs.bind (currentlyEnabled Ext_S)
                          (fun w1 : bool => returnM (Riscv.rv64d.not w1))) s = Some (false, s)).
    { rewrite (exec_bind_Some _ _ _ _ _ (exec_currentlyEnabled_S s)). rewrite HS.
      cbn [Riscv.rv64d.not negb]. apply exec_returnM. }
    assert (Hguard : exec (or_boolM (Defs.bind (currentlyEnabled Ext_S)
                            (fun w1 : bool => returnM (Riscv.rv64d.not w1)))
                          (Defs.bind (Defs.read_reg mstatus)
                            (fun w2 : mword 64 => returnM (eq_vec (_get_Mstatus_TSR w2) ('b"1"))))) s
                    = Some (false, s)).
    { unfold or_boolM. rewrite (exec_bind_Some _ _ _ _ _ Harm1). cbn match.
      rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mstatus s)). rewrite HTSR. apply exec_returnM. }
    rewrite (exec_bind_Some _ _ _ _ _ Hguard). cbn match.
    change (ext_check_xret_priv Supervisor) with true. cbn [Riscv.rv64d.not negb]. cbn match.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg cur_privilege s)).
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mstatus s)).
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mstatus s)).
    set (s1 := set_reg s mstatus ms1).
    rewrite (exec_bind0_Some _ _ _ _ _ (exec_write_reg mstatus ms1 s)).
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mstatus s1)).
    replace (register_lookup mstatus s1.(sregs)) with ms1
      by (subst s1; rewrite register_lookup_set; reflexivity).
    set (s2 := set_reg s1 mstatus ms2).
    rewrite (exec_bind0_Some _ _ _ _ _ (exec_write_reg mstatus ms2 s1)).
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mstatus s2)).
    replace (register_lookup mstatus s2.(sregs)) with ms2
      by (subst s2; rewrite register_lookup_set; reflexivity).
    set (s3 := set_reg s2 cur_privilege newpriv).
    rewrite (exec_bind0_Some _ _ _ _ _ (exec_write_reg cur_privilege newpriv s2)).
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mstatus s3)).
    replace (register_lookup mstatus s3.(sregs)) with ms2
      by (subst s3; rewrite irrelevant_register_set; [subst s2; rewrite register_lookup_set; reflexivity | vm_compute; reflexivity]).
    set (s4 := set_reg s3 mstatus ms3).
    rewrite (exec_bind0_Some _ _ _ _ _ (exec_write_reg mstatus ms3 s3)).
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg cur_privilege s4)).
    replace (register_lookup cur_privilege s4.(sregs)) with newpriv
      by (subst s4; rewrite irrelevant_register_set; [subst s3; rewrite register_lookup_set; reflexivity | vm_compute; reflexivity]).
    assert (Hnpm : generic_neq newpriv Machine = true)
      by (unfold newpriv; destruct (eq_vec (_get_Mstatus_SPP ms2) ('b"1")); reflexivity).
    rewrite Hnpm. cbn match.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mstatus s4)).
    replace (register_lookup mstatus s4.(sregs)) with ms3
      by (subst s4; rewrite register_lookup_set; reflexivity).
    set (s5 := set_reg s4 mstatus ms4).
    rewrite (exec_bind0_Some _ _ _ _ _ (exec_write_reg mstatus ms4 s4)).
    set (s6 := set_reg s5 mstatus ms5).
    set (s7 := set_reg s6 elp elpv).
    assert (HL6 : register_lookup menvcfg s6.(sregs) = menvcfg0).
    { subst s6 s5 s4 s3 s2 s1.
      repeat (rewrite irrelevant_register_set; [| vm_compute; reflexivity]).
      exact Hmenv. }
    assert (HL6s : register_lookup senvcfg s6.(sregs) = register_lookup senvcfg s.(sregs)).
    { subst s6 s5 s4 s3 s2 s1.
      repeat (rewrite irrelevant_register_set; [| vm_compute; reflexivity]).
      reflexivity. }
    assert (HL6m : register_lookup misa s6.(sregs) = register_lookup misa s.(sregs)).
    { subst s6 s5 s4 s3 s2 s1.
      repeat (rewrite irrelevant_register_set; [| vm_compute; reflexivity]).
      reflexivity. }
    rewrite (exec_bind_Some _ _ _ _ _
      (_ : exec (Defs.bind0 (Defs.bind (Defs.read_reg cur_privilege)
                   (fun w12 : Privilege => zicfilp_restore_elp_on_xret sRET w12))
                (Defs.read_reg mstatus)) s5 = Some (ms5, s7))).
    2:{ rewrite (exec_bind0_Some _ _ _ _ _
          (_ : exec (Defs.bind (Defs.read_reg cur_privilege)
                  (fun w12 : Privilege => zicfilp_restore_elp_on_xret sRET w12)) s5
               = Some (tt, s7))).
        2:{ rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg cur_privilege s5)).
            replace (register_lookup cur_privilege s5.(sregs)) with newpriv
              by (subst s5 s4 s3; rewrite irrelevant_register_set; [|vm_compute; reflexivity];
                  rewrite irrelevant_register_set; [|vm_compute; reflexivity];
                  rewrite register_lookup_set; reflexivity).
            unfold zicfilp_restore_elp_on_xret. cbn match.
            rewrite (exec_bind_Some _ _ _ _ _
              (_ : exec (Defs.bind (Defs.read_reg mstatus)
                     (fun w0 : mword 64 => Defs.bind (Defs.read_reg mstatus)
                        (fun w1 : mword 64 => Defs.bind0
                          (Defs.write_reg mstatus (update_subrange_vec_dec w1 23 23
                             (landing_pad_bits_backwards NO_LP_EXPECTED)))
                          (returnM (_get_Mstatus_SPELP w0))))) s5
                   = Some (_get_Mstatus_SPELP ms4, s6))).
            2:{ rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mstatus s5)).
                replace (register_lookup mstatus s5.(sregs)) with ms4
                  by (subst s5; rewrite register_lookup_set; reflexivity).
                rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mstatus s5)).
                replace (register_lookup mstatus s5.(sregs)) with ms4
                  by (subst s5; rewrite register_lookup_set; reflexivity).
                rewrite (exec_bind0_Some _ _ _ _ _ (exec_write_reg mstatus ms5 s5)).
                apply exec_returnm. }
            rewrite (exec_bind_Some _ _ _ _ _ (Hlpe s6 HL6 HL6s HL6m)).
            rewrite (exec_write_reg elp elpv s6). reflexivity. }
        rewrite (exec_read_reg mstatus s7).
        replace (register_lookup mstatus s7.(sregs)) with ms5
          by (subst s7 s6; rewrite irrelevant_register_set; [|vm_compute; reflexivity];
              rewrite register_lookup_set; reflexivity).
        reflexivity. }
    rewrite (exec_bind_Some _ _ _ _ _
      (_ : exec (Defs.bind0 (Defs.bind0 (long_csr_write_callback "mstatus" "mstatush" ms5) _)
                   (prepare_xret_target Supervisor)) s7 = Some (tgt, s7))).
    2:{ rewrite (exec_bind0_Some _ _ _ _ _
          (_ : exec (Defs.bind0 (long_csr_write_callback "mstatus" "mstatush" ms5) _)
                 s7 = Some (tt, s7))).
        2:{ rewrite (exec_bind0_Some _ _ _ _ _
              (_ : exec (long_csr_write_callback "mstatus" "mstatush" ms5) s7 = Some (tt, s7))).
            2:{ apply exec_long_csr_write_mstatus. }
            replace (get_config_print_exception tt) with false by reflexivity.
            cbn match. apply exec_returnm. }
        unfold prepare_xret_target, get_xepc. cbn match.
        rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg sepc s7)).
        replace (register_lookup sepc s7.(sregs)) with (register_lookup sepc s.(sregs))
          by (subst s7 s6 s5 s4 s3 s2 s1;
              repeat (rewrite irrelevant_register_set; [|vm_compute; reflexivity]); reflexivity).
        unfold align_pc.
        rewrite (exec_bind_Some _ _ _ _ _
          (_ : exec (currentlyEnabled Ext_Zca) s7 = Some (true, s7))).
        2:{ apply exec_currentlyEnabled_Zca.
            subst s7 s6 s5 s4 s3 s2 s1.
            repeat (rewrite irrelevant_register_set; [|vm_compute; reflexivity]). exact Hmc. }
        cbn match. apply exec_returnM. }
    rewrite (exec_bind0_Some _ _ _ _ _ (exec_set_next_pc tgt s7)).
    apply exec_returnm.
  Qed.
End ExecSRETU.


Section WpUaluUsretPt.
  Context `{!riscvGS Σ, !sieG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Lemma wp_ualu_pt (uroot tfp : mword 44) (um : gmap (mword 27) (mword 64))
      (off : Z) (is_rvc : bool) (ast : instruction)
      (m : regfile) (a0v vnew : mword 64)
      (vf : mstate -> mword 64)
      (mstatus0 mie_v mdv0 menvcfg0 : mword 64) {dq : dfrac} :
    let va := uva off in
    let pa := upa off in
    (* S-mode config facts *)
    eq_vec (_get_Mstatus_SIE mstatus0) ('b"1") = false ->
    eq_vec (_get_Mstatus_MPRV mstatus0) ('b"1") = false ->
    _get_Mstatus_SXL mstatus0 = 'b"10" ->
    and_vec mie_v (not_vec mdv0) = zeros' 64 ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    menvcfg0 = MENVCFG_S ->
    (* the execute: a0 := vf s *)
    (forall s : mstate,
       exec (execute ast) s
       = Some (RETIRE_SUCCESS,
               if Z.eqb (uint (mword_of_int 10 : mword 5)) 0 then s
               else set_reg s (R_bitvector_64 (gpr_of_Z (uint (mword_of_int 10 : mword 5))))
                      (regval_into_reg (vf s)))) ->
    (* the value, given a0's current contents *)
    (forall s : mstate,
       register_lookup (R_bitvector_64 (gpr_of_Z (uint (mword_of_int 10 : mword 5)))) s.(sregs) = a0v ->
       vf s = vnew) ->
    (* GPR: a0's current contents *)
    m !!! Regidx (mword_of_int 10) = a0v ->
    (* fetch va/pa geometry (vm_compute per instruction) *)
    neq_vec (bits_of_virtaddr (Virtaddr va))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = tramp_vpn ->
    zero_extend' 64 (concat_vec tramp_ppn
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub pagesize_bits 1) 0)) = pa ->
    neq_vec (bits_of_virtaddr (Virtaddr (add_vec_int va 2)))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr (add_vec_int va 2))) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr (add_vec_int va 2))) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = tramp_vpn ->
    zero_extend' 64 (concat_vec tramp_ppn
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr (add_vec_int va 2))) (Z.sub pagesize_bits 1) 0)) = add_vec_int pa 2 ->
    is_aligned_vaddr (Virtaddr va) 2 = true ->
    is_aligned_vaddr (Virtaddr pa) 4 = is_aligned_vaddr (Virtaddr va) 4 ->
    is_aligned_paddr (Physaddr pa) 2 = true ->
    is_aligned_paddr (Physaddr (add_vec_int pa 2)) 2 = true ->
    (is_aligned_vaddr (Virtaddr va) 4 = true -> is_aligned_paddr (Physaddr pa) 4 = true) ->
    hw_config -∗
    minstret_inv -∗
    hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ{ dq } Supervisor -∗
    mstatus ↦ᵣ{ dq } mstatus0 -∗
    mie ↦ᵣ{ dq } mie_v -∗
    mideleg ↦ᵣ{ dq } mdv0 -∗
    menvcfg ↦ᵣ{ dq } menvcfg0 -∗
    utlb_inv_pt uroot tfp um -∗
    pc_is va -∗
    gpr_file m -∗
    instr pa is_rvc ast -∗
    ( hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
      cur_privilege ↦ᵣ{ dq } Supervisor -∗
      mstatus ↦ᵣ{ dq } mstatus0 -∗
      mie ↦ᵣ{ dq } mie_v -∗
      mideleg ↦ᵣ{ dq } mdv0 -∗
      menvcfg ↦ᵣ{ dq } menvcfg0 -∗
      utlb_inv_pt uroot tfp um -∗
      pc_is (add_vec_int va (if is_rvc then 2 else 4)) -∗
      gpr_file (<[Regidx (mword_of_int 10) := regval_into_reg vnew]> m) -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros va pa HSIE HMPRV HSXL Hmm HPBMTE Hmenvval0 Hexec Hval Ha0
      Hcanon Hvpn Hident Hcanon2 Hvpn2 Hident2 Hva2 Hpa4va4 Hpa2al Hpa2al2 Hpa4al.
    iIntros "#Hhw #Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hutlb [Hpc Hnpc] [%Hdom Hfmap] Hinstr Hcont".
    iApply (wp_instr_u_pt uroot tfp um va pa is_rvc ast
              mstatus0 mie_v mdv0 menvcfg0 dq
 HSIE HMPRV HSXL Hmm HPBMTE Hmenvval0
              Hcanon Hvpn Hident Hcanon2 Hvpn2 Hident2 Hva2 Hpa4va4 Hpa2al Hpa2al2 Hpa4al
             
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hutlb Hpc Hinstr").
    iIntros (σ Hpceq)
      "Hpriv Hms Hmie Hmdl Hmenv Hutlb Hsi".
    iDestruct "Hsi" as "[Hreg Hmem]".
    assert (Hrd10 : uint (mword_of_int 10 : mword 5) <> 0) by (vm_compute; lia).
    assert (Hma0v : m (Regidx (mword_of_int 10 : mword 5)) = a0v)
      by exact Ha0.
    (* tick nextPC *)
    iMod (reg_update _ nextPC _ (add_vec_int va (if is_rvc then 2 else 4)) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s_pc := set_reg σ nextPC (add_vec_int va (if is_rvc then 2 else 4))).
    iDestruct (big_sepM_lookup_acc _ _ _ _ (rf_to_gmap_lookup m (Regidx (mword_of_int 10 : mword 5))) with "Hfmap") as "[Hspc Hfb1]".
    iDestruct (gpr_pt_value (mword_of_int 10) (m (Regidx (mword_of_int 10 : mword 5))) s_pc with "Hreg Hspc") as %Lva.
    iDestruct ("Hfb1" with "Hspc") as "Hfmap".
    replace (Z.eqb (uint (mword_of_int 10 : mword 5)) 0) with false in Lva
      by (vm_compute; reflexivity).
    rewrite Hma0v in Lva.
    (* the execute at s_pc *)
    assert (Hload : exec (execute ast)
                      (set_reg σ nextPC (add_vec_int (register_lookup PC σ.(sregs))
                                           (if is_rvc then 2 else 4)))
                    = Some (RETIRE_SUCCESS,
                            set_reg s_pc (R_bitvector_64 (gpr_of_Z (uint (mword_of_int 10 : mword 5))))
                              (regval_into_reg vnew))).
    { rewrite Hpceq. fold s_pc. rewrite (Hexec s_pc).
      replace (Z.eqb (uint (mword_of_int 10 : mword 5)) 0) with false
        by (vm_compute; reflexivity).
      rewrite (Hval s_pc Lva). reflexivity. }
    (* a0 := vnew in the ghost gpr file *)
    iDestruct (big_sepM_insert_acc _ _ _ _ (rf_to_gmap_lookup m (Regidx (mword_of_int 10 : mword 5))) with "Hfmap") as "[Hrdc Hfins]".
    rewrite (gpr_pt_nz (mword_of_int 10) _ Hrd10).
    iMod (reg_update _ (R_bitvector_64 (gpr_of_Z (uint (mword_of_int 10 : mword 5)))) _ (regval_into_reg vnew)
            with "Hreg Hrdc") as "[Hreg Hrdc]".
    iDestruct ("Hfins" $! (regval_into_reg vnew) with "[Hrdc]") as "Hfmap".
    { rewrite (gpr_pt_nz (mword_of_int 10) _ Hrd10). iExact "Hrdc". }
    iEval (rewrite -(rf_to_gmap_upd m (Regidx (mword_of_int 10 : mword 5)) (regval_into_reg vnew))) in "Hfmap".
    iModIntro.
    iExists (set_reg s_pc (R_bitvector_64 (gpr_of_Z (uint (mword_of_int 10 : mword 5))))
               (regval_into_reg vnew)).
    iSplitR.
    { iPureIntro. exact Hload. }
    iSplitL "Hreg Hmem".
    { unfold s_pc; rewrite ?sregs_set_reg ?mem_set_reg ?mdev_set_reg. iFrame "Hreg Hmem". }
    iIntros "Hhs' Hpc'".
    assert (Lnpc : register_lookup nextPC
             (set_reg s_pc (R_bitvector_64 (gpr_of_Z (uint (mword_of_int 10 : mword 5))))
                (regval_into_reg vnew)).(sregs)
             = add_vec_int va (if is_rvc then 2 else 4)).
    { unfold s_pc; cbn [sregs]. tmig. rewrite register_lookup_set. reflexivity. }
    iEval (rewrite Lnpc) in "Hpc'".
    iApply ("Hcont" with "Hhs' Hpriv Hms Hmie Hmdl Hmenv
                          Hutlb
                          [$Hpc' $Hnpc] [Hfmap]").
    iSplitR.
    { iPureIntro. apply rf_to_gmap_dom. }
    iExact "Hfmap".
  Qed.

  Lemma wp_usret_pt (uroot tfp : mword 44) (um : gmap (mword 27) (mword 64))
      (m : regfile)
      (mstatus0 mie_v mdv0 menvcfg0 senvcfg0 sepc0 : mword 64) :
    let va := uva 0x120 in
    let pa := upa 0x120 in
    (* S-mode config facts *)
    eq_vec (_get_Mstatus_SIE mstatus0) ('b"1") = false ->
    eq_vec (_get_Mstatus_MPRV mstatus0) ('b"1") = false ->
    _get_Mstatus_SXL mstatus0 = 'b"10" ->
    and_vec mie_v (not_vec mdv0) = zeros' 64 ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    menvcfg0 = MENVCFG_S ->
    senvcfg0 = mword_of_int 0 ->
    (* SRET-specific premises: no trap, and SPP decodes to USER *)
    eq_vec (_get_Mstatus_TSR mstatus0) ('b"1") = false ->
    sret_newpriv mstatus0 = User ->
    hw_config -∗
    minstret_inv -∗
    hart_state ↦ᵣ HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ Supervisor -∗
    mstatus ↦ᵣ mstatus0 -∗
    mie ↦ᵣ mie_v -∗
    mideleg ↦ᵣ mdv0 -∗
    menvcfg ↦ᵣ menvcfg0 -∗
    senvcfg ↦ᵣ senvcfg0 -∗
    sepc ↦ᵣ sepc0 -∗
    utlb_inv_pt uroot tfp um -∗
    pc_is va -∗
    gpr_file m -∗
    instr pa false (SRET tt) -∗
    ( hart_state ↦ᵣ HART_ACTIVE tt -∗
      cur_privilege ↦ᵣ User -∗
      mstatus ↦ᵣ sret_ms5 mstatus0 -∗
      mie ↦ᵣ mie_v -∗
      mideleg ↦ᵣ mdv0 -∗
      menvcfg ↦ᵣ menvcfg0 -∗
      senvcfg ↦ᵣ senvcfg0 -∗
      sepc ↦ᵣ sepc0 -∗
      utlb_inv_pt uroot tfp um -∗
      pc_is (ret_pc sepc0) -∗
      gpr_file m -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros va pa HSIE HMPRV HSXL Hmm HPBMTE Hmenvval0 Hsenvval0 HTSR Hsup.
    iIntros "#Hhw #Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hsenv Hsepc Hutlb
             [Hpc Hnpc] Hfile Hinstr Hcont".
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & _ & %HmisaS & %HmisaC &
        %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np & %HmisaA & %Hmisa_val0 & %Hmseccfg_val0 & #Hkmapb)".
    pose proof (mword1_not_lp elp0 Help_np) as Help0.
    iApply (wp_instr_u_pt uroot tfp um va pa false (SRET tt)
              mstatus0 mie_v mdv0 menvcfg0 (DfracOwn 1)
 HSIE HMPRV HSXL Hmm HPBMTE Hmenvval0
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(intros _; vm_compute; reflexivity)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hutlb Hpc Hinstr").
    iIntros (σ Hpceq)
      "Hpriv Hms Hmie Hmdl Hmenv Hutlb Hsi".
    iDestruct "Hsi" as "[Hreg Hmem]".
    iDestruct (reg_valid    with "Hreg Hpriv") as %Lpriv.
    iDestruct (reg_valid    with "Hreg Hms")   as %Lms.
    iDestruct (reg_valid_dq with "Hreg Hmenv") as %Lmenv.
    iDestruct (reg_valid    with "Hreg Hsenv") as %Lsenv.
    iDestruct (reg_valid    with "Hreg Hsepc") as %Lsepc.
    iDestruct (reg_valid_dq with "Hreg Hmisa") as %Lmisa.
    iDestruct (reg_valid_dq with "Hreg Help")  as %Lelp.
    (* tick nextPC := va+4 *)
    iMod (reg_update _ nextPC _ (add_vec_int va 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s_pc := set_reg σ nextPC (add_vec_int va 4)).
    assert (Lpriv_pc : register_lookup cur_privilege s_pc.(sregs) = Supervisor)
      by (unfold s_pc; tmig; exact Lpriv).
    assert (Lms_pc : register_lookup mstatus s_pc.(sregs) = mstatus0)
      by (unfold s_pc; tmig; exact Lms).
    assert (Lmenv_pc : register_lookup menvcfg s_pc.(sregs) = menvcfg0)
      by (unfold s_pc; tmig; exact Lmenv).
    assert (Lsenv_pc : register_lookup senvcfg s_pc.(sregs) = senvcfg0)
      by (unfold s_pc; tmig; exact Lsenv).
    assert (Lsepc_pc : register_lookup sepc s_pc.(sregs) = sepc0)
      by (unfold s_pc; tmig; exact Lsepc).
    assert (Lmisa_pc : register_lookup misa s_pc.(sregs) = misa0)
      by (unfold s_pc; tmig; exact Lmisa).
    (* the SRET execute reduction at s_pc, with newpriv = User, lpe = false *)
    pose proof (exec_execute_SRET_menvU s_pc false menvcfg0
                  Lpriv_pc
                  ltac:(rewrite Lmisa_pc; exact HmisaS)
                  ltac:(rewrite Lms_pc; exact HTSR)
                  ltac:(rewrite Lmisa_pc; exact HmisaC)
                  Lmenv_pc
                  ltac:(intros sz Hm Hs Hmi;
                        assert (Hx : exec (get_xLPE User) sz = Some (false, sz))
                          by (apply exec_get_xLPE_U;
                              [ rewrite Hmi; rewrite Lmisa_pc; exact HmisaS
                              | rewrite Hs; rewrite Lsenv_pc; exact Hsenvval0
                              | rewrite Hm; exact Hmenvval0 ]);
                        rewrite <- Hsup in Hx;
                        unfold sret_newpriv, sret_ms2, sret_ms1 in Hx;
                        rewrite Lms_pc; exact Hx)) as HexecC0.
    pose (sX := set_reg (set_reg (set_reg (set_reg (set_reg
                  (set_reg (set_reg (set_reg s_pc mstatus (sret_ms1 mstatus0)) mstatus (sret_ms2 mstatus0))
                           cur_privilege User) mstatus (sret_ms3 mstatus0)) mstatus (sret_ms4 mstatus0))
                  mstatus (sret_ms5 mstatus0)) elp (landing_pad_bits_backwards NO_LP_EXPECTED))
                  nextPC (ret_pc sepc0)).
    assert (HexecC : exec (execute (SRET tt)) s_pc = Some (RETIRE_SUCCESS, sX)).
    { rewrite HexecC0. unfold sX.
      rewrite !Lms_pc Lsepc_pc.
      unfold sret_newpriv, sret_ms2, sret_ms1 in Hsup.
      unfold sret_ms1, sret_ms2, sret_ms3, sret_ms4, sret_ms5, ret_pc.
      rewrite Hsup. reflexivity. }
    (* mirror the physical set_regs on the ghost cells *)
    iMod (reg_update _ mstatus _ (sret_ms1 mstatus0) with "Hreg Hms") as "[Hreg Hms]".
    iMod (reg_update _ mstatus _ (sret_ms2 mstatus0) with "Hreg Hms") as "[Hreg Hms]".
    iMod (reg_update _ cur_privilege _ User with "Hreg Hpriv") as "[Hreg Hpriv]".
    iMod (reg_update _ mstatus _ (sret_ms3 mstatus0) with "Hreg Hms") as "[Hreg Hms]".
    iMod (reg_update _ mstatus _ (sret_ms4 mstatus0) with "Hreg Hms") as "[Hreg Hms]".
    iMod (reg_update _ mstatus _ (sret_ms5 mstatus0) with "Hreg Hms") as "[Hreg Hms]".
    assert (Lelp_now : register_lookup elp
              (register_set mstatus (sret_ms5 mstatus0) (register_set mstatus (sret_ms4 mstatus0)
                (register_set mstatus (sret_ms3 mstatus0) (register_set cur_privilege User
                  (register_set mstatus (sret_ms2 mstatus0) (register_set mstatus (sret_ms1 mstatus0)
                    (register_set nextPC (add_vec_int va 4) σ.(sregs))))))))
            = landing_pad_bits_backwards NO_LP_EXPECTED).
    { repeat tmig. rewrite Lelp Help0. reflexivity. }
    iDestruct (reg_interp_set_same _ elp (landing_pad_bits_backwards NO_LP_EXPECTED)
                 Lelp_now with "Hreg") as "Hreg".
    iMod (reg_update _ nextPC _ (ret_pc sepc0) with "Hreg Hnpc") as "[Hreg Hnpc]".
    iModIntro.
    iExists sX.
    iSplitR.
    { iPureIntro. rewrite Hpceq. exact HexecC. }
    iSplitL "Hreg Hmem".
    { unfold sX, s_pc; rewrite ?sregs_set_reg ?mem_set_reg ?mdev_set_reg. iFrame "Hreg Hmem". }
    iIntros "Hhs Hpc'".
    assert (Lnpc : register_lookup nextPC sX.(sregs) = ret_pc sepc0)
      by (unfold sX; rewrite ?sregs_set_reg; rewrite register_lookup_set; reflexivity).
    iEval (rewrite Lnpc) in "Hpc'".
    iApply ("Hcont" with "Hhs Hpriv Hms Hmie Hmdl Hmenv Hsenv Hsepc
                          Hutlb [$Hpc' $Hnpc] Hfile").
  Qed.

End WpUaluUsretPt.
