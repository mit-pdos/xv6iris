(* HartMLoad.v -- the width-8 LOAD path, one [swp] fact per model function.

   It is the read-side twin of [HartMStore]'s write chain, and it shares
   with [HartMFetch] everything that is not access-specific: the Bare
   translation walk ([hfrun_translateAddr_M]), the MMIO exclusion
   ([hfrun_within_mmio_ram]), the 8-byte read request projections
   ([mread_req8] / [hread_req_at_read_ram8] / [hread_resume_read_ram8]) and
   the read node itself.  What is new is only

     - the PMA check at a [Load Data] access ([hfrun_check_pma_load8]),
       which takes the READABLE conjunct of the RAM grant where the fetch
       takes the executable one and the store the writable one;
     - the width-8 PMP, which is a PARAMETER of the chain rather than a
       fixed configuration.  An 8-byte window can straddle a TOR/NA4
       boundary, so [HartMPmp]'s one-grain-fit walk does not apply and the
       M-mode data path has to be stated per PMP configuration
       ([swp_pmpCheck_load8_off] at all-OFF, [swp_pmpCheck_load8_tor0] at a
       TOR entry 0 that covers the access).  Threading the check as an
       obligation -- exactly the shape [swp_mem_read_load8] already uses for
       [checked_mem_read] -- keeps ONE chain instead of an `_off`/`_tor0`
       cross-product, and leaves the configuration where it is known: the
       leaf.  It also drops [pmpcfg_n] out of the chain's own frame
       requirement (the obligation carries whatever cells its proof needs);
     - the ADDRESS stretch: [execute_LOAD] computes its effective address
       from a GPR at a SYMBOLIC index, so [get_transformed_data_addr] is
       peeled through [HartMFrame]'s [gpr_file] rules rather than walked.

   Like the store chain, this one is stated at [Machine] with
   [mstatus.MPRV = 0]: a LOAD consults MPRV where a fetch short-circuits it. *)
From Stdlib Require Import ZArith Zquot Lia.
From stdpp Require Import gmap relations bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap ghost_map.
From iris.program_logic Require Import language weakestpre.
Require Import SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes.
Require Import RiscvLang RiscvPtsto RiscvExec HartSwp HartLift HartRegNode
        HartSpan HartSpanChar HartEvents HartMPmp HartMFetch HartMFrame.
Require Import RiscvTryStep RiscvExtras RiscvFetchExec.
Require Import RegFile WpGpr.
Local Open Scope Z_scope.

Local Arguments Z.sub _ _ : simpl nomatch.
Local Arguments Z.add _ _ : simpl nomatch.
Local Arguments Z.mul _ _ : simpl nomatch.
Local Arguments Z.eqb _ _ : simpl nomatch.
Local Arguments Z.compare _ _ : simpl nomatch.
Local Arguments Z.pos_sub _ _ : simpl nomatch.
Local Arguments Pos.compare _ _ : simpl nomatch.
Local Arguments Pos.compare_cont _ _ _ : simpl nomatch.

Local Ltac l_cbn :=
  cbn beta iota zeta delta
    [Defs.bind Defs.bind0 Interface.iMon_bind Defs.liftR Defs.try_catch
     Defs.catch_early_return Defs.returnm returnM returnR
     Defs.returnR Defs.read_reg Defs.early_return Defs.throw
     Defs.assert_exp Defs.assert_exp'
     Defs.and_boolM Defs.or_boolM andb orb negb not
     check_pma_with_pmp_priority pmaCheck mag_pma_check
     is_mag_applicable_access __id
     get_config_rvfi plat_have_clint plat_have_sig].

(* the GLUE reducer for the swp walk: pure combinators only.  It must NOT
   unfold [Defs.bind]/[liftR]/[catch_early_return] -- those are the shape
   [swp_use_cer] matches on. *)
Local Ltac l_glue :=
  cbn beta iota zeta delta
    [Defs.returnm returnM returnR Defs.returnR andb orb negb not
     Instances.generic_eq Instances.generic_neq].

Local Ltac l_read :=
  rewrite hfrun_read;
  match goal with
  | |- context [ bool_decide ?P ] =>
      rewrite (bool_decide_eq_true_2 P ltac:(assumption))
  end.

(* ====================================================================== *)
(* 1. The PMA check at an 8-byte LOAD.                                     *)
(* ====================================================================== *)

Local Lemma fit8_local (x k : Z) :
  x = 8 * k -> x < 2147483648 + 134217728 -> x + 8 <= 2147483648 + 134217728.
Proof. intros -> H. lia. Qed.

Local Lemma pma_access8_local (a : SailStdpp.Values.mword 64) :
  addr_is_ram a -> is_aligned_paddr (Physaddr a) 8 = true ->
  pma_ram_access a 8.
Proof.
  intros [Hlo Hhi] Hal.
  unfold is_aligned_paddr in Hal. apply Z.eqb_eq in Hal.
  apply Zrem_divides in Hal. destruct Hal as [k Hk].
  unfold ram_base, ram_size in Hhi.
  unfold pma_ram_access, ram_base, ram_size.
  exact (conj (pma_width_ok 8 eq_refl eq_refl)
              (conj Hlo (fit8_local (uint a) k Hk Hhi))).
Qed.

Lemma hfrun_check_pma_load8 (D Drw : gset register) (rs : regstate)
    (pa : SailStdpp.Values.mword 64) (pmar0 : list PMA_Region) :
  (pma_regions : register) ∈ D ->
  register_lookup pma_regions rs = pmar0 ->
  pma_allows_ram pmar0 ->
  addr_is_ram pa ->
  is_aligned_paddr (Physaddr pa) 8 = true ->
  hfrun 6 D Drw rs
    (check_pma_with_pmp_priority (Load Data) PBMT_PMA Machine
       (Physaddr pa) 8 false)
  = Some (Values.Ok
            {| Phys_Mem_Access_Info_splittable := CannotSplit;
               Phys_Mem_Access_Info_granule_size_exp := 0 |}, rs).
Proof.
  intros HD Hpma Hpallow Hram Hpa.
  unfold check_pma_with_pmp_priority. l_cbn.
  l_read. rewrite Hpma. l_cbn.
  destruct (Hpallow pa 8 (pma_access8_local pa Hram Hpa))
    as (region & Hmatch & Hgrant).
  destruct region as [rbase rsize rattr rdtree].
  destruct Hgrant as (_ & Hx & _).
  cbn [PMA_Region_attributes] in Hx.
  rewrite Hmatch. l_cbn.
  rewrite Hx. l_cbn.
  rewrite Hpa. l_cbn.
  apply hfrun_ret.
Qed.

(* ====================================================================== *)
(* 2. The page-split test, as a TERM equation.                             *)
(*                                                                        *)
(* [RiscvExtras.exec_split_on_page_boundary_aligned8] is the same fact at   *)
(* the exec layer; the [swp] chain needs it as a rewrite on the model term  *)
(* instead, and the whole difference is the last line ([reflexivity] where   *)
(* the exec twin says [apply exec_returnm]).  With this the load chain has   *)
(* NO page-split premise -- 8-alignment is all a caller ever has to show.    *)
(* ====================================================================== *)
Lemma split_on_page_boundary_aligned8 (a : SailStdpp.Values.mword 64) :
  is_aligned_vaddr (Virtaddr a) 8 = true ->
  split_on_page_boundary a 8 = returnM (8, 0).
Proof.
  intro Halign.
  pose proof (bv_unsigned_in_range _ a) as Hr. unfold bv_modulus in Hr.
  change (2 ^ Z.of_N (MachineWord.MachineWord.Z_idx 64)) with (2 ^ 64) in Hr.
  destruct Hr as [Hr0 Hr1].
  assert (Hal : bv_unsigned a mod 8 = 0).
  { unfold is_aligned_vaddr in Halign. apply Z.eqb_eq in Halign.
    rewrite uint_unsigned in Halign.
    assert (Hrm : Z.rem (bv_unsigned a) 8 = (bv_unsigned a) mod 8)
      by (apply Z.rem_mod_nonneg; [ exact Hr0 | lia ]).
    rewrite Hrm in Halign. exact Halign. }
  assert (Hnw : bv_unsigned a + 7 < 2 ^ 64)
    by (apply z_align8_room; [ exact Hr0 | exact Hr1 | exact Hal ]).
  assert (Hsub : bv_unsigned (sub_vec_int (add_vec_int a 8) 1) = bv_unsigned a + 7).
  { unfold sub_vec_int, add_vec_int.
    rewrite sub_vec64_unsigned. rewrite add_vec64_unsigned.
    rewrite !moi64_unsigned.
    assert (Hw8 : bv_wrap 64 8 = 8)
      by (apply bv_wrap_small; rewrite bv_modulus64; lia).
    assert (Hw1 : bv_wrap 64 1 = 1)
      by (apply bv_wrap_small; rewrite bv_modulus64; lia).
    rewrite Hw8. rewrite Hw1.
    rewrite bv_wrap_sub_idemp_l.
    assert (Hsimp : bv_unsigned a + 8 - 1 = bv_unsigned a + 7) by (clear; lia).
    rewrite Hsimp.
    apply bv_wrap_small. rewrite bv_modulus64.
    assert (H64 : (2:Z) ^ 64 = 18446744073709551616) by (vm_compute; reflexivity).
    rewrite <- H64. split; [ clear - Hr0; lia | exact Hnw ]. }
  unfold split_on_page_boundary.
  assert (Hintra : eq_vec (and_vec a (update_subrange_vec_dec ((ones 64) : bits 64)
                                        (pagesize_bits - 1) 0 (zeros' (12 - 1 - (0 - 1)))))
                          (and_vec (sub_vec_int (add_vec_int a 8) 1)
                                   (update_subrange_vec_dec ((ones 64) : bits 64)
                                      (pagesize_bits - 1) 0 (zeros' (12 - 1 - (0 - 1))))) = true).
  { apply eq_vec_true_iff. apply bv_eq.
    rewrite !and_vec64_unsigned. rewrite page_mask64_val.
    rewrite Hsub.
    assert (Hnn : 0 <= bv_unsigned a + 7) by (clear - Hr0; lia).
    rewrite (z_land_pagemask (bv_unsigned a) Hr0 Hr1).
    rewrite (z_land_pagemask (bv_unsigned a + 7) Hnn Hnw).
    rewrite <- (z_shiftr12_stable (bv_unsigned a) Hr0 Hal). reflexivity. }
  rewrite Hintra. reflexivity.
Qed.

(* the Bare translation at a LOAD: HartMFetch's generic walk with the two
   access-dependent premises discharged, exactly as the store chain does it. *)
Lemma hfrun_translateAddr_M_load (D Drw : gset register) (rs : regstate)
    (pa : SailStdpp.Values.mword 64) :
  (mstatus : register) ∈ D ->
  (cur_privilege : register) ∈ D ->
  register_lookup cur_privilege rs = Machine ->
  eq_vec (_get_Mstatus_MPRV (register_lookup mstatus rs))
    (MachineWord.MachineWord.N_to_word 1 1%N) = false ->
  hfrun 8 D Drw rs (translateAddr (Virtaddr pa) (Load Data))
  = Some (Values.Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), rs).
Proof.
  intros HD1 HD2 Hpriv Hmprv.
  apply (hfrun_translateAddr_M D Drw rs pa _ HD1 HD2 Hpriv); [|reflexivity].
  unfold effectivePrivilege.
  change (Instances.generic_neq (Load Data) (InstructionFetch tt))
    with true.
  l_glue. rewrite Hmprv. by l_glue.
Qed.

(* at width 64 both extensions are the identity, so the [is_unsigned] flag
   of a [ld]/[ldu] never branches. *)
Local Lemma extend_value_id8 (b : bool) (v : SailStdpp.Values.mword 64) :
  extend_value b v = v.
Proof.
  unfold extend_value. destruct b; [apply zero_extend'_id|].
  cbv [sign_extend' Operators_mwords.sign_extend Operators_mwords.exts_vec
       SailStdpp.Values.to_word SailStdpp.Values.get_word
       MachineWord.MachineWord.sign_extend].
  apply bv_eq_signed. rewrite bv_sign_extend_signed; [ reflexivity | lia ].
Qed.

(* the whole-word write into the zero word, at [vmem_read_addr]'s OWN
   spelling of the indices ([RiscvExtras.usvd_zeros_full_64] is the same fact
   at [checked_mem_read]'s spelling). *)
Local Lemma usvd_zeros_full_64' (v : SailStdpp.Values.mword 64) :
  update_subrange_vec_dec (zeros' (8 * 8)) (8 * 8 - 1) 0 v = v.
Proof. usvd_zeros_full_tac. Qed.

(* [transform_effective_address] at a LOAD in M-mode: three pinned reads
   (mstatus for MPRV, cur_privilege, mseccfg for the pointer-masking mode) and
   nothing else -- so the walker takes it whole.  With PMM disabled the
   transform is the identity. *)
Lemma hfrun_transform_effective_address_load (D Drw : gset register)
    (rs : regstate) (a : SailStdpp.Values.mword 64) :
  (mstatus : register) ∈ D ->
  (cur_privilege : register) ∈ D ->
  (mseccfg : register) ∈ D ->
  register_lookup cur_privilege rs = Machine ->
  eq_vec (_get_Mstatus_MPRV (register_lookup mstatus rs))
    (MachineWord.MachineWord.N_to_word 1 1%N) = false ->
  pmm_mode_backwards (_get_Seccfg_PMM (register_lookup mseccfg rs))
    = PMM_Disabled ->
  hfrun 12 D Drw rs (transform_effective_address (Virtaddr a) (Load Data))
  = Some (Virtaddr a, rs).
Proof.
  intros HDmst HDpriv HDsec Hpriv Hmprv Hpmm.
  unfold transform_effective_address.
  l_cbn.
  l_read. l_cbn.
  l_read. rewrite Hpriv. l_cbn.
  unfold effectivePrivilege.
  change (Instances.generic_neq (Load Data) (InstructionFetch tt)) with true.
  l_cbn. rewrite Hmprv. l_cbn.
  unfold get_pmlen, is_pmm_applicable.
  l_cbn.
  change (Instances.generic_neq (Load Data) (InstructionFetch tt)) with true.
  change (Instances.generic_neq (Load Data) (Load PageTableEntry)) with true.
  change (Instances.generic_neq (Load Data) (Store PageTableEntry)) with true.
  change (Instances.generic_eq Machine Machine) with true.
  l_cbn.
  unfold get_pmm. l_cbn.
  l_read. rewrite Hpmm. l_cbn.
  unfold translationMode.
  change (Instances.generic_eq Machine Machine) with true.
  l_cbn.
  change (Instances.generic_eq Bare Bare) with true.
  l_cbn.
  unfold pm_transform_PA.
  change (xlen - 0 - 1) with 63.
  rewrite subrange_full_64 zero_extend'_id.
  apply hfrun_ret.
Qed.

(* ====================================================================== *)
(* 3. The chain, bottom up.                                                *)
(* ====================================================================== *)

Section load.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Lemma swp_checked_mem_read_load8 (Drw Dro : gset register)
      (Df : register -> dfrac) (rs : regstate)
      (pa : SailStdpp.Values.mword 64)
      (pmar0 : list PMA_Region)
      (bytes : bv 64) (R : iProp Σ) :
    Drw ## Dro ->
    (pma_regions : register) ∈ Drw ∪ Dro ->
    (htif_tohost_base : register) ∈ Drw ∪ Dro ->
    register_lookup htif_tohost_base rs = None ->
    register_lookup pma_regions rs = pmar0 ->
    pma_allows_ram pmar0 ->
    addr_is_ram pa ->
    is_aligned_paddr (Physaddr pa) 8 = true ->
    gen_cert -∗
    hreg_frame rs Drw -∗
    hreg_frame_ro Df rs Dro -∗
    (hreg_frame rs Drw -∗ hreg_frame_ro Df rs Dro -∗
       swp (pmpCheck (Physaddr pa) 8 (Load Data) Machine)
         (fun r => ⌜r = None⌝ ∗
                   hreg_frame rs Drw ∗ hreg_frame_ro Df rs Dro)) -∗
    (∀ σ, mstate_interp σ ={⊤,∅}=∗
        ⌜read_bytes σ.(mem) pa 8 = Some bytes⌝ ∗
        ▷ (|={∅,⊤}=> mstate_interp σ ∗ R)) -∗
    swp (checked_mem_read (Load Data) PBMT_PMA Machine
           (Physaddr pa) 8 false false false false)
      (fun r => ⌜r = Values.Ok (bytes, tt)⌝ ∗
                hreg_frame rs Drw ∗ hreg_frame_ro Df rs Dro ∗ R).
  Proof.
    intros Hdisj HD HDhtif Hhtif Hpma Hpallow Hram Hpa.
    iIntros "#Hcert Hrw Hro Hpmp Hmem".
    rewrite /swp. iIntros (C) "%HC Hcont".
    unfold checked_mem_read.
    iApply (swp_use_cer
              (check_pma_with_pmp_priority (Load Data) PBMT_PMA
                 Machine (Physaddr pa) 8 false) _ _ C HC
              with "[Hrw Hro] [-]").
    { iApply (swp_hfrun 6 Drw Dro Df rs rs _ _ Hdisj
                (hfrun_check_pma_load8 (Drw ∪ Dro) Drw rs pa pmar0
                   HD Hpma Hpallow Hram Hpa) with "Hcert Hrw Hro"). }
    iIntros (v) "(-> & Hrw & Hro)". cbn beta iota.
    rewrite mbind_ret. cbn beta iota zeta.
    cbn [Phys_Mem_Access_Info_granule_size_exp Phys_Mem_Access_Info_splittable].
    cbn beta iota zeta delta [split_misaligned misaligned_order
      sys_misaligned_order_decreasing read_kind_of_flags].
    change (Instances.generic_eq CannotSplit CannotSplit) with true.
    cbn beta iota.
    rewrite /returnM mliftR_ret mbind_ret. cbn beta iota zeta.
    rewrite mliftR_ret mbind_ret. cbn beta iota zeta.
    cbn beta iota zeta delta [Defs.untilMT Defs.untilMT' Defs.Zwf_guarded
      Z_ge_dec Z_ge_lt_dec Zcompare_rec Z.compare].
    cbn beta iota zeta delta [Defs.assert_exp' bits_of_physaddr].
    rewrite mliftR_ret mbind_ret. cbn beta iota.
    change (0 * 8) with 0. rewrite avi0.
    iApply (swp_use_cer3
              (pmpCheck (Physaddr pa) 8 (Load Data) Machine)
              _ _ _ _ C HC with "[Hrw Hro Hpmp] [-]").
    { iApply ("Hpmp" with "Hrw Hro"). }
    iIntros (v) "(-> & Hrw & Hro)". cbn beta iota.
    rewrite mbind0_ret.
    iApply (swp_use_cer3 (within_mmio_readable (Physaddr pa) 8)
              _ _ _ _ C HC with "[Hrw Hro] [-]").
    { iApply (swp_hfrun 12 Drw Dro Df rs rs _ _ Hdisj
                (hfrun_within_mmio_ram (Drw ∪ Dro) Drw rs pa 8
                   ltac:(lia) HDhtif Hhtif Hram)
                with "Hcert Hrw Hro"). }
    iIntros (v) "(-> & Hrw & Hro)". cbn beta iota.
    iApply (swp_use_cer4 (read_ram Read_plain (Physaddr pa) 8 false)
              _ _ _ _ _ C HC with "[Hrw Hro Hmem] [-]").
    { iApply (swp_hart_ram_read 8 (mread_req8 pa) _
                (fun r => (⌜r = (bytes, default_meta)⌝ ∗
                           hreg_frame rs Drw ∗ hreg_frame_ro Df rs Dro ∗ R)%I)
                (hread_req_at_read_ram8 pa)
                (addr_is_ram_not_dev pa Hram) ltac:(reflexivity)
                with "Hcert [Hrw Hro Hmem]").
      iIntros (σ) "Hσ". iMod ("Hmem" $! σ with "Hσ") as "[%Hrb Hclose]".
      iModIntro. iExists bytes. iSplitR; [done|]. iNext.
      iMod "Hclose" as "[Hσ HR]". iModIntro. iFrame "Hσ".
      rewrite hread_resume_read_ram8. iApply swp_ret. by iFrame. }
    iIntros (v) "(-> & Hrw & Hro & HR)". cbn beta iota zeta.
    rewrite mbind_ret. cbn beta.
    change (0 =? 1 - 1) with true. cbn beta iota zeta.
    rewrite !autocast_id usvd_zeros_full_64 mcer_ret.
    iApply ("Hcont" $! (Values.Ok (bytes, tt))). by iFrame.
  Qed.

  (* [mem_read] at a LOAD: the same two config reads as the fetch's, but the
     [effectivePrivilege] here takes the MPRV branch, so the privilege the
     inner check runs at is [Machine] only because MPRV is clear. *)
  Lemma swp_mem_read_load8 (Drw Dro : gset register) (Df : register -> dfrac)
      (rs : regstate) (pa : physaddr) (w : SailStdpp.Values.mword 64)
      (R : iProp Σ) :
    Drw ## Dro ->
    (mstatus : register) ∈ Drw ∪ Dro ->
    (cur_privilege : register) ∈ Drw ∪ Dro ->
    register_lookup cur_privilege rs = Machine ->
    eq_vec (_get_Mstatus_MPRV (register_lookup mstatus rs))
      (MachineWord.MachineWord.N_to_word 1 1%N) = false ->
    gen_cert -∗
    hreg_frame rs Drw -∗
    hreg_frame_ro Df rs Dro -∗
    (hreg_frame rs Drw -∗ hreg_frame_ro Df rs Dro -∗
       swp (checked_mem_read (Load Data) PBMT_PMA Machine pa 8
              false false false false)
         (fun r => ⌜r = Values.Ok (w, tt)⌝ ∗
                   hreg_frame rs Drw ∗ hreg_frame_ro Df rs Dro ∗ R)) -∗
    swp (mem_read (Load Data) PBMT_PMA pa 8 false false false)
      (fun r => ⌜r = Values.Ok w⌝ ∗
                hreg_frame rs Drw ∗ hreg_frame_ro Df rs Dro ∗ R).
  Proof.
    intros Hdisj HDmst HDpriv Hpriv Hmprv.
    iIntros "#Hcert Hrw Hro Hcmr".
    unfold mem_read.
    iApply (swp_bind_use (Defs.read_reg mstatus) _ _ _ with "[Hrw Hro] [-]").
    { iApply (swp_read_reg_pinned Drw Dro Df rs _ Hdisj HDmst
                with "Hcert Hrw Hro"). }
    iIntros (v) "(-> & Hrw & Hro)".
    iApply (swp_bind_use (Defs.read_reg cur_privilege) _ _ _
              with "[Hrw Hro] [-]").
    { iApply (swp_read_reg_pinned Drw Dro Df rs _ Hdisj HDpriv
                with "Hcert Hrw Hro"). }
    iIntros (v) "(-> & Hrw & Hro)". rewrite Hpriv.
    unfold effectivePrivilege.
    change (Instances.generic_neq (Load Data) (InstructionFetch tt))
      with true.
    l_glue. rewrite Hmprv. l_glue.
    rewrite mbind_ret.
    unfold mem_read_priv, mem_read_priv_meta.
    cbn beta iota.
    iApply (swp_bind_use _ _
              (fun r => (⌜r = Values.Ok (w, tt)⌝ ∗
                         hreg_frame rs Drw ∗ hreg_frame_ro Df rs Dro ∗ R)%I) _
              with "[Hrw Hro Hcmr] [-]").
    { iApply (swp_bind_use _ _
                (fun r => (⌜r = Values.Ok (w, tt)⌝ ∗
                           hreg_frame rs Drw ∗ hreg_frame_ro Df rs Dro ∗ R)%I) _
                with "[Hrw Hro Hcmr] [-]").
      - iApply ("Hcmr" with "Hrw Hro").
      - iIntros (v) "(-> & Hrw & Hro & HR)". iApply swp_ret. by iFrame. }
    iIntros (v) "(-> & Hrw & Hro & HR)". iApply swp_ret.
    cbn [MemoryOpResult_drop_meta]. by iFrame.
  Qed.

  (* [translate_and_read_value]: the Bare translation, then the read.  A plain
     [M] spine, so it composes with [swp_bind_use]. *)
  Lemma swp_translate_and_read_value8 (Drw Dro : gset register)
      (Df : register -> dfrac) (rs : regstate)
      (pa : SailStdpp.Values.mword 64)
      (pmar0 : list PMA_Region)
      (bytes : bv 64) (R : iProp Σ) :
    Drw ## Dro ->
    (mstatus : register) ∈ Drw ∪ Dro ->
    (cur_privilege : register) ∈ Drw ∪ Dro ->
    (pma_regions : register) ∈ Drw ∪ Dro ->
    (htif_tohost_base : register) ∈ Drw ∪ Dro ->
    register_lookup cur_privilege rs = Machine ->
    register_lookup pma_regions rs = pmar0 ->
    register_lookup htif_tohost_base rs = None ->
    eq_vec (_get_Mstatus_MPRV (register_lookup mstatus rs))
      (MachineWord.MachineWord.N_to_word 1 1%N) = false ->
    pma_allows_ram pmar0 ->
    addr_is_ram pa ->
    is_aligned_paddr (Physaddr pa) 8 = true ->
    gen_cert -∗
    hreg_frame rs Drw -∗
    hreg_frame_ro Df rs Dro -∗
    (hreg_frame rs Drw -∗ hreg_frame_ro Df rs Dro -∗
       swp (pmpCheck (Physaddr pa) 8 (Load Data) Machine)
         (fun r => ⌜r = None⌝ ∗
                   hreg_frame rs Drw ∗ hreg_frame_ro Df rs Dro)) -∗
    (∀ σ, mstate_interp σ ={⊤,∅}=∗
        ⌜read_bytes σ.(mem) pa 8 = Some bytes⌝ ∗
        ▷ (|={∅,⊤}=> mstate_interp σ ∗ R)) -∗
    swp (translate_and_read_value (Virtaddr pa) 8 (Load Data) false false false)
      (fun r => ⌜r = Values.Ok (Physaddr pa, bytes)⌝ ∗
                hreg_frame rs Drw ∗ hreg_frame_ro Df rs Dro ∗ R).
  Proof.
    intros Hdisj HDmst HDpriv HDpma HDhtif Hpriv Hpma Hhtif
      Hmprv Hpallow Hram Hpa.
    iIntros "#Hcert Hrw Hro Hpmp Hmem".
    unfold translate_and_read_value.
    iApply (swp_bind_use (translateAddr (Virtaddr pa) (Load Data)) _ _ _
              with "[Hrw Hro] [-]").
    { iApply (swp_hfrun 8 Drw Dro Df rs rs _ _ Hdisj
                (hfrun_translateAddr_M_load (Drw ∪ Dro) Drw rs pa
                   HDmst HDpriv Hpriv Hmprv) with "Hcert Hrw Hro"). }
    iIntros (v) "(-> & Hrw & Hro)". cbn beta iota.
    iApply (swp_bind_use _ _
              (fun r => (⌜r = Values.Ok bytes⌝ ∗
                         hreg_frame rs Drw ∗ hreg_frame_ro Df rs Dro ∗ R)%I) _
              with "[Hrw Hro Hpmp Hmem] [-]").
    { iApply (swp_mem_read_load8 Drw Dro Df rs (Physaddr pa) bytes R Hdisj
                HDmst HDpriv Hpriv Hmprv with "Hcert Hrw Hro [Hpmp Hmem]").
      iIntros "Hrw Hro".
      iApply (swp_checked_mem_read_load8 Drw Dro Df rs pa pmar0 bytes R
                Hdisj HDpma HDhtif Hhtif Hpma Hpallow Hram
                Hpa with "Hcert Hrw Hro Hpmp Hmem"). }
    iIntros (v) "(-> & Hrw & Hro & HR)". cbn beta iota.
    iApply swp_ret. by iFrame.
  Qed.

  (* [vmem_read_addr]: the alignment gate, the page-split test, the
     translation-mode short-circuit, and one [translate_and_read_value].
     Unlike the store chain this one has NO page-split premise -- 8-alignment
     already decides it ([split_on_page_boundary_aligned8]). *)
  Lemma swp_vmem_read_addr8 (Drw Dro : gset register)
      (Df : register -> dfrac) (rs : regstate)
      (pa : SailStdpp.Values.mword 64)
      (pmar0 : list PMA_Region)
      (bytes : bv 64) (R : iProp Σ) :
    Drw ## Dro ->
    (mstatus : register) ∈ Drw ∪ Dro ->
    (cur_privilege : register) ∈ Drw ∪ Dro ->
    (pma_regions : register) ∈ Drw ∪ Dro ->
    (htif_tohost_base : register) ∈ Drw ∪ Dro ->
    register_lookup cur_privilege rs = Machine ->
    register_lookup pma_regions rs = pmar0 ->
    register_lookup htif_tohost_base rs = None ->
    eq_vec (_get_Mstatus_MPRV (register_lookup mstatus rs))
      (MachineWord.MachineWord.N_to_word 1 1%N) = false ->
    pma_allows_ram pmar0 ->
    addr_is_ram pa ->
    is_aligned_vaddr (Virtaddr pa) 8 = true ->
    is_aligned_paddr (Physaddr pa) 8 = true ->
    gen_cert -∗
    hreg_frame rs Drw -∗
    hreg_frame_ro Df rs Dro -∗
    (hreg_frame rs Drw -∗ hreg_frame_ro Df rs Dro -∗
       swp (pmpCheck (Physaddr pa) 8 (Load Data) Machine)
         (fun r => ⌜r = None⌝ ∗
                   hreg_frame rs Drw ∗ hreg_frame_ro Df rs Dro)) -∗
    (∀ σ, mstate_interp σ ={⊤,∅}=∗
        ⌜read_bytes σ.(mem) pa 8 = Some bytes⌝ ∗
        ▷ (|={∅,⊤}=> mstate_interp σ ∗ R)) -∗
    swp (vmem_read_addr (Virtaddr pa) 8 (Load Data) false false false)
      (fun r => ⌜r = Values.Ok bytes⌝ ∗
                hreg_frame rs Drw ∗ hreg_frame_ro Df rs Dro ∗ R).
  Proof.
    intros Hdisj HDmst HDpriv HDpma HDhtif Hpriv Hpma Hhtif
      Hmprv Hpallow Hram Hva Hpa.
    iIntros "#Hcert Hrw Hro Hpmp Hmem".
    rewrite /swp. iIntros (C) "%HC Hcont".
    unfold vmem_read_addr.
    rewrite Hva. l_glue.
    rewrite mbind0_ret.
    rewrite (split_on_page_boundary_aligned8 pa Hva).
    rewrite /returnM mliftR_ret mbind_ret. l_glue.
    iApply (swp_use_cer (Defs.read_reg mstatus) _ _ C HC
              with "[Hrw Hro] [-]").
    { iApply (swp_read_reg_pinned Drw Dro Df rs _ Hdisj HDmst
                with "Hcert Hrw Hro"). }
    iIntros (v0) "(-> & Hrw & Hro)".
    iApply (swp_use_cer (Defs.read_reg cur_privilege) _ _ C HC
              with "[Hrw Hro] [-]").
    { iApply (swp_read_reg_pinned Drw Dro Df rs _ Hdisj HDpriv
                with "Hcert Hrw Hro"). }
    iIntros (v0) "(-> & Hrw & Hro)". rewrite Hpriv.
    unfold effectivePrivilege.
    change (Instances.generic_neq (Load Data) (InstructionFetch tt))
      with true.
    l_glue. rewrite Hmprv. l_glue.
    rewrite mliftR_ret mbind_ret. l_glue.
    unfold translationMode.
    change (Instances.generic_eq Machine Machine) with true.
    l_glue.
    unfold Defs.and_boolM.
    rewrite /returnM mliftR_ret mbind_ret. l_glue.
    change (Instances.generic_neq Bare Bare) with false. l_glue.
    rewrite mbind_ret. l_glue.
    change (sys_misaligned_order_decreasing && false) with false. l_glue.
    rewrite mbind_ret. l_glue.
    iApply (swp_use_cer
              (translate_and_read_value (Virtaddr pa) 8 (Load Data)
                 false false false) _ _ C HC with "[Hrw Hro Hpmp Hmem] [-]").
    { iApply (swp_translate_and_read_value8 Drw Dro Df rs pa pmar0 bytes R
                Hdisj HDmst HDpriv HDpma HDhtif Hpriv Hpma Hhtif
                Hmprv Hpallow Hram Hpa with "Hcert Hrw Hro Hpmp Hmem"). }
    iIntros (v0) "(-> & Hrw & Hro & HR)". cbn beta iota. l_glue.
    rewrite mbind0_ret. l_glue.
    rewrite mbind_ret. l_glue.
    change (not sys_misaligned_order_decreasing && false) with false. l_glue.
    rewrite mbind_ret. l_glue.
    rewrite autocast_id usvd_zeros_full_64'.
    rewrite mcer_ret.
    iApply ("Hcont" $! (Values.Ok bytes)). by iFrame.
  Qed.

  (* the effective-address stretch.  [rX_bits] at a SYMBOLIC index is the one
     node no walker takes, so it is peeled at [gpr_file]; everything after it
     is the pinned-register walk above. *)
  Lemma swp_get_transformed_data_addr_load8 (Drw Dro : gset register)
      (Df : register -> dfrac) (rs : regstate) (i : SailStdpp.Values.mword 5)
      (m : regfile) (offset : SailStdpp.Values.mword 64) :
    Drw ## Dro ->
    (mstatus : register) ∈ Drw ∪ Dro ->
    (cur_privilege : register) ∈ Drw ∪ Dro ->
    (mseccfg : register) ∈ Drw ∪ Dro ->
    register_lookup cur_privilege rs = Machine ->
    eq_vec (_get_Mstatus_MPRV (register_lookup mstatus rs))
      (MachineWord.MachineWord.N_to_word 1 1%N) = false ->
    pmm_mode_backwards (_get_Seccfg_PMM (register_lookup mseccfg rs))
      = PMM_Disabled ->
    gen_cert -∗
    gpr_file m -∗
    hreg_frame rs Drw -∗
    hreg_frame_ro Df rs Dro -∗
    swp (get_transformed_data_addr (Regidx i) offset (Load Data) 8)
      (fun r => ⌜r = Ext_DataAddr_OK
                       (Virtaddr (add_vec (m !!! Regidx i) offset))⌝ ∗
                gpr_file m ∗
                hreg_frame rs Drw ∗ hreg_frame_ro Df rs Dro).
  Proof.
    intros Hdisj HDmst HDpriv HDsec Hpriv Hmprv Hpmm.
    iIntros "#Hcert Hf Hrw Hro".
    unfold get_transformed_data_addr, ext_data_get_addr.
    iApply (swp_bind_use _ _
              (fun r => (⌜r = Ext_DataAddr_OK
                               (Virtaddr (add_vec (m !!! Regidx i) offset))⌝ ∗
                         gpr_file m)%I) _ with "[Hf] [-]").
    { iApply (swp_bind_use (rX_bits (Regidx i)) _ _ _ with "[Hf] [-]").
      { iApply (swp_rX_file i m with "Hcert Hf"). }
      iIntros (w) "(-> & Hf)". iApply swp_ret. by iFrame. }
    iIntros (v0) "(-> & Hf)". cbn beta iota.
    iApply (swp_bind_use
              (transform_effective_address
                 (Virtaddr (add_vec (m !!! Regidx i) offset)) (Load Data))
              _ _ _ with "[Hrw Hro] [-]").
    { iApply (swp_hfrun 12 Drw Dro Df rs rs _ _ Hdisj
                (hfrun_transform_effective_address_load (Drw ∪ Dro) Drw rs _
                   HDmst HDpriv HDsec Hpriv Hmprv Hpmm)
                with "Hcert Hrw Hro"). }
    iIntros (v0) "(-> & Hrw & Hro)". iApply swp_ret. by iFrame.
  Qed.

  Lemma swp_vmem_read8 (Drw Dro : gset register) (Df : register -> dfrac)
      (rs : regstate) (i : SailStdpp.Values.mword 5) (m : regfile)
      (offset : SailStdpp.Values.mword 64)
      (pmar0 : list PMA_Region)
      (bytes : bv 64) (R : iProp Σ) :
    Drw ## Dro ->
    (mstatus : register) ∈ Drw ∪ Dro ->
    (cur_privilege : register) ∈ Drw ∪ Dro ->
    (mseccfg : register) ∈ Drw ∪ Dro ->
    (pma_regions : register) ∈ Drw ∪ Dro ->
    (htif_tohost_base : register) ∈ Drw ∪ Dro ->
    register_lookup cur_privilege rs = Machine ->
    register_lookup pma_regions rs = pmar0 ->
    register_lookup htif_tohost_base rs = None ->
    eq_vec (_get_Mstatus_MPRV (register_lookup mstatus rs))
      (MachineWord.MachineWord.N_to_word 1 1%N) = false ->
    pmm_mode_backwards (_get_Seccfg_PMM (register_lookup mseccfg rs))
      = PMM_Disabled ->
    pma_allows_ram pmar0 ->
    addr_is_ram (add_vec (m !!! Regidx i) offset) ->
    is_aligned_paddr (Physaddr (add_vec (m !!! Regidx i) offset)) 8 = true ->
    gen_cert -∗
    gpr_file m -∗
    hreg_frame rs Drw -∗
    hreg_frame_ro Df rs Dro -∗
    (hreg_frame rs Drw -∗ hreg_frame_ro Df rs Dro -∗
       swp (pmpCheck (Physaddr (add_vec (m !!! Regidx i) offset)) 8
              (Load Data) Machine)
         (fun r => ⌜r = None⌝ ∗
                   hreg_frame rs Drw ∗ hreg_frame_ro Df rs Dro)) -∗
    (∀ σ, mstate_interp σ ={⊤,∅}=∗
        ⌜read_bytes σ.(mem) (add_vec (m !!! Regidx i) offset) 8 = Some bytes⌝ ∗
        ▷ (|={∅,⊤}=> mstate_interp σ ∗ R)) -∗
    swp (vmem_read (Regidx i) offset 8 (Load Data) false false false)
      (fun r => ⌜r = Values.Ok bytes⌝ ∗ gpr_file m ∗
                hreg_frame rs Drw ∗ hreg_frame_ro Df rs Dro ∗ R).
  Proof.
    intros Hdisj HDmst HDpriv HDsec HDpma HDhtif Hpriv Hpma Hhtif
      Hmprv Hpmm Hpallow Hram Hpa.
    iIntros "#Hcert Hf Hrw Hro Hpmp Hmem".
    rewrite /swp. iIntros (C) "%HC Hcont".
    unfold vmem_read.
    iApply (swp_use_cer
              (get_transformed_data_addr (Regidx i) offset (Load Data) 8)
              _ _ C HC with "[Hf Hrw Hro] [-]").
    { iApply (swp_get_transformed_data_addr_load8 Drw Dro Df rs i m offset
                Hdisj HDmst HDpriv HDsec Hpriv Hmprv Hpmm
                with "Hcert Hf Hrw Hro"). }
    iIntros (v0) "(-> & Hf & Hrw & Hro)". cbn beta iota. l_glue.
    rewrite mbind_ret. l_glue.
    iApply (swp_use_cer0
              (vmem_read_addr (Virtaddr (add_vec (m !!! Regidx i) offset)) 8
                 (Load Data) false false false) _ C HC
              with "[Hrw Hro Hpmp Hmem] [-]").
    { iApply (swp_vmem_read_addr8 Drw Dro Df rs _ pmar0 bytes R Hdisj
                HDmst HDpriv HDpma HDhtif Hpriv Hpma Hhtif Hmprv
                Hpallow Hram Hpa Hpa with "Hcert Hrw Hro Hpmp Hmem"). }
    iIntros (v0) "(-> & Hrw & Hro & HR)".
    iApply ("Hcont" $! (Values.Ok bytes)). by iFrame.
  Qed.

  (* [execute_LOAD] at width 8: the address stretch, the read, and the
     destination write.  At width 8 both extensions are the identity, so the
     [is_unsigned] flag is carried but never branches. *)
  Lemma swp_execute_LOAD8 (Drw Dro : gset register) (Df : register -> dfrac)
      (rs : regstate) (imm : SailStdpp.Values.mword 12)
      (rs1 rd : SailStdpp.Values.mword 5) (is_unsigned : bool)
      (m : regfile) (bytes : bv 64)
      (pmar0 : list PMA_Region)
      (R : iProp Σ) :
    let ea := add_vec (m !!! Regidx rs1) (sign_extend' 64 imm) in
    Drw ## Dro ->
    (mstatus : register) ∈ Drw ∪ Dro ->
    (cur_privilege : register) ∈ Drw ∪ Dro ->
    (mseccfg : register) ∈ Drw ∪ Dro ->
    (pma_regions : register) ∈ Drw ∪ Dro ->
    (htif_tohost_base : register) ∈ Drw ∪ Dro ->
    register_lookup cur_privilege rs = Machine ->
    register_lookup pma_regions rs = pmar0 ->
    register_lookup htif_tohost_base rs = None ->
    eq_vec (_get_Mstatus_MPRV (register_lookup mstatus rs))
      (MachineWord.MachineWord.N_to_word 1 1%N) = false ->
    pmm_mode_backwards (_get_Seccfg_PMM (register_lookup mseccfg rs))
      = PMM_Disabled ->
    pma_allows_ram pmar0 ->
    addr_is_ram ea ->
    is_aligned_paddr (Physaddr ea) 8 = true ->
    uint rd <> 0 ->
    gen_cert -∗
    gpr_file m -∗
    hreg_frame rs Drw -∗
    hreg_frame_ro Df rs Dro -∗
    (hreg_frame rs Drw -∗ hreg_frame_ro Df rs Dro -∗
       swp (pmpCheck (Physaddr ea) 8 (Load Data) Machine)
         (fun r => ⌜r = None⌝ ∗
                   hreg_frame rs Drw ∗ hreg_frame_ro Df rs Dro)) -∗
    (∀ σ, mstate_interp σ ={⊤,∅}=∗
        ⌜read_bytes σ.(mem) ea 8 = Some bytes⌝ ∗
        ▷ (|={∅,⊤}=> mstate_interp σ ∗ R)) -∗
    swp (execute_LOAD imm (Regidx rs1) (Regidx rd) is_unsigned 8)
      (fun e => ⌜e = RETIRE_SUCCESS⌝ ∗
                gpr_file (<[Regidx rd := regval_into_reg bytes]> m) ∗
                hreg_frame rs Drw ∗ hreg_frame_ro Df rs Dro ∗ R).
  Proof.
    intros ea Hdisj HDmst HDpriv HDsec HDpma HDhtif Hpriv Hpma
      Hhtif Hmprv Hpmm Hpallow Hram Hpa Hrd.
    iIntros "#Hcert Hf Hrw Hro Hpmp Hmem".
    unfold execute_LOAD.
    cbn beta iota zeta delta [Defs.assert_exp'].
    rewrite /returnM mbind_ret. l_glue.
    iApply (swp_bind_use _ _
              (fun r => (⌜r = Values.Ok bytes⌝ ∗ gpr_file m ∗
                         hreg_frame rs Drw ∗ hreg_frame_ro Df rs Dro ∗ R)%I) _
              with "[Hf Hrw Hro Hpmp Hmem] [-]").
    { iApply (swp_vmem_read8 Drw Dro Df rs rs1 m (sign_extend' 64 imm) pmar0
                bytes R Hdisj HDmst HDpriv HDsec HDpma HDhtif Hpriv
                Hpma Hhtif Hmprv Hpmm Hpallow Hram Hpa
                with "Hcert Hf Hrw Hro Hpmp Hmem"). }
    iIntros (v0) "(-> & Hf & Hrw & Hro & HR)". cbn beta iota.
    rewrite extend_value_id8.
    iApply (swp_bind0_use (wX_bits (Regidx rd) bytes) _ _ _
              with "[Hf] [-]").
    { iApply (swp_wX_file rd m bytes Hrd with "Hcert Hf"). }
    iIntros (u) "Hf". iApply swp_ret. by iFrame.
  Qed.

End load.
