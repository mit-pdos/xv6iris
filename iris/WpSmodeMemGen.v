(* WpSmodeMemGen.v -- WIDTH-GENERIC S-mode-walk-pt data access reductions.

   The S-mode load/store execution stack was duplicated per access width
   (exec_{checked_mem_read,mem_read,vmem_read_addr,vmem_read,execute_LOAD}_N,
   for N in {1,4,8}, spread across WpSmodeGpr / WpSmodePtLeaves / WpSmodePtMem).
   This file unifies that stack over a symbolic width, at exactly the layer the
   USER-mode stack unifies (UserMemAccess / UserMemPt): the byte-level
   [read_ram Read_plain] fact stays per-width (supplied as [Hread_plain], the
   S-mode analogue of user-mode's [Context (Hread_plain ...)]), and everything
   above it -- the PMP/PMA/mmio checks, the checked/mem_read reduction, the
   vmem_read_addr misalign loop, and the execute_LOAD retire -- is proved once
   over the abstract width.  The per-width names the existing callers use are
   re-derived as instances at the bottom of the file. *)
From Stdlib Require Import ZArith.
From stdpp Require Import gmap bitvector.definitions.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvExec RiscvExtras RiscvTryStep RiscvFetchExec.
Require Import WpLoad.
Require Import WpGpr.
Require Import WpMmodeLeafBase.
Require Import MemAccessGen.
Require Import WpSmodeGpr.
Local Open Scope Z_scope.
Import Defs.

(* [autocast] between two CONVERTIBLE but not syntactically equal widths --
   the shape a symbolic width leaves behind, where [autocast_id] (which needs
   the two indices to unify syntactically) does not fire. *)
Ltac kill_autocast :=
  match goal with
  | |- context[@autocast _ ?m ?nn ?I ?x] =>
      replace (@autocast mword m nn I x) with x
        by (apply bv_eq; symmetry; apply (autocast_unsigned m nn x); lia)
  end.

Lemma zeros'_unsigned (n : Z) : bv_unsigned (zeros' n) = 0.
Proof. unfold zeros'; destruct n; reflexivity. Qed.

Lemma usvd_zeros_full_gen (n : Z) (w : mword n) :
  0 < n ->
  update_subrange_vec_dec (zeros' n) (n - 1) 0 (autocast (T := mword) w) = w.
Proof.
  intro Hn.
  assert (EN : MachineWord.MachineWord.Z_idx (n - 1 - (0 - 1))
               = MachineWord.MachineWord.Z_idx n) by (f_equal; lia).
  pose proof (bv_unsigned_in_range (MachineWord.MachineWord.Z_idx n) w) as Hr.
  apply bv_eq.
  unfold update_subrange_vec_dec.
  rewrite (autocast_unsigned _ n _ (MachineWord.MachineWord.idx_Z_idx n ltac:(lia))).
  unfold to_word_idx, Values.to_word.
  unfold get_word, MachineWord.MachineWord.update_slice, MachineWord.MachineWord.slice.
  rewrite cast_idx_unsigned.
  rewrite !bv_concat_unsigned'.
  rewrite !bv_extract_unsigned.
  rewrite !zeros'_unsigned.
  rewrite !Z.shiftr_0_l.
  rewrite !bv_wrap_0.
  rewrite Z.shiftl_0_l.
  rewrite Z.lor_0_r. rewrite Z.lor_0_l.
  change (MachineWord.MachineWord.Z_idx 0) with 0%N.
  change (Z.of_N 0) with 0. rewrite Z.shiftl_0_r.
  rewrite (autocast_unsigned n (n - 1 - (0 - 1)) w ltac:(lia)).
  rewrite EN. rewrite N.add_0_l.
  rewrite bv_wrap_idemp. apply bv_wrap_small. exact Hr.
Qed.

Section SmodeMemGenLoad.
Context `{GEN : GenId} `{CID : CpuId}.
Variable width : Z.
Hypothesis Hw0 : 0 < width.
Hypothesis Hw8 : width <= 8.
(* the vmem level now splits on a PAGE boundary, which needs the width to be
   one of the four the ISA allows there *)
Hypothesis Hvw : vmem_width width.
Hypothesis Hread_plain : forall (addr : mword 64) (w : mword (8*width)) s,
  dev_addr addr = false ->
  (forall j : nat, (N.of_nat j < Z.to_N width)%N ->
     s.(mem) !! (pa_add addr j) = Some (nth_byte w j)) ->
  exec (read_ram rv64d_types.Read_plain (Physaddr addr) width false) s
    = Some ((w, default_meta), s).

Lemma exec_checked_mem_read_ram_load_w_S (pbmt : page_based_mem_type) (addr : mword 64)
    (region : PMA_Region) (w : mword (8*width)) s :
  pmpAddrMatchType_encdec_backwards
    (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) = TOR ->
  zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0) = false ->
  pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
    (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0)) 4)
    (uint addr) (uint (to_bits 64 width)) = PMP_Match ->
  eq_vec (_get_Pmpcfg_ent_R (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) ('b"1") = true ->
  matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr addr) width = Some region ->
  is_aligned_paddr (Physaddr addr) width = true ->
  (override_PMA (PMA_Region_attributes region) pbmt).(PMA_readable) = true ->
  exec (within_clint (Physaddr addr) width) s = Some (false, s) ->
  exec (within_sig (Physaddr addr) width) s = Some (false, s) ->
  exec (within_htif_readable (Physaddr addr) width) s = Some (false, s) ->
  dev_addr addr = false ->
  (forall j : nat, (N.of_nat j < Z.to_N width)%N ->
     s.(mem) !! (pa_add addr j) = Some (nth_byte w j)) ->
  exec (checked_mem_read (Load Data) pbmt Supervisor (Physaddr addr) width false false false false)
       s = Some (Ok (w, default_meta), s).
Proof.
  intros HA Hord Hrange HR Hmatch Halign Hread Hc Hsig Hh Hdev Hbytes.
  assert (Hcp : exec (check_pma_with_pmp_priority (Load Data) pbmt Supervisor
                        (Physaddr addr) width false) s = Some (Ok pma_ok_aligned, s)).
  { unfold check_pma_with_pmp_priority.
    rewrite (exec_bind_Some _ _ _ _ _
               (exec_pmaCheck_ram_load_g width addr pbmt region s Hmatch Halign Hread)).
    cbn match. apply exec_returnM. }
  assert (Hmmio : exec (within_mmio_readable (Physaddr addr) width) s = Some (false, s)).
  { unfold within_mmio_readable. cbn [get_config_rvfi].
    rewrite (exec_or_boolM_Some _ _ _ _ _ Hc). cbn match.
    rewrite (exec_or_boolM_Some _ _ _ _ _ Hsig). cbn match.
    rewrite (exec_and_boolM_Some _ _ _ _ _ Hh). cbn match. reflexivity. }
  unfold checked_mem_read. rewrite exec_catch_early_return.
  rewrite (execR_liftR_seq _ _ _ _ _ Hcp). cbn beta. cbn match.
  rewrite execR_bind. rewrite execR_returnR. cbn match beta.
  rewrite pma_ok_aligned_splittable. rewrite pma_ok_aligned_granule.
  rewrite (execR_liftR_seq _ _ _ _ _ (exec_split_misaligned_unsplit addr width 0 s)). cbn beta.
  rewrite misaligned_order_1. cbn zeta.
  assert (Hrkf : exec (read_kind_of_flags false false false) s
                 = Some (rv64d_types.Read_plain, s))
    by (unfold read_kind_of_flags; apply exec_returnM).
  rewrite (execR_liftR_seq _ _ _ _ _ Hrkf). cbn beta.
  match goal with |- context[Defs.bind (Defs.untilMT ?vs ?m ?c ?b) _] =>
    assert (Hu : execR (Defs.untilMT vs m c b) s = Some (inr (w, true, 0), s)) end.
  { eapply execR_untilMT_1; [ reflexivity | | apply execR_returnR_fwd ].
    rewrite (execR_liftR_seq _ _ _ _ _ (exec_assert_exp'_true _ s)). cbn beta.
    change (bits_of_physaddr (Physaddr addr)) with addr.
    assert (Havi : add_vec_int addr (0 * width) = addr)
      by (assert (H0 : (0 * width)%Z = 0) by lia; rewrite H0; apply avi0).
    rewrite Havi.
    rewrite (execR_liftR_seq _ _ _ _ _
               (exec_pmpCheck_supervisor_grant_load_data addr width s HA Hord Hrange HR)).
    cbn beta. cbn match.
    match goal with |- context[Defs.bind (Defs.bind0 ?a ?b) _] =>
      assert (Hseq : execR (Defs.bind0 a b) s = Some (inr false, s)) end.
    { rewrite execR_bind0. rewrite execR_returnR. cbn match.
      rewrite execR_liftR. rewrite Hmmio. reflexivity. }
    rewrite (execR_bind_Some _ _ _ _ _ Hseq). cbn beta. cbn match.
    match goal with
      |- context[Defs.bind (Defs.bind (Defs.liftR (read_ram ?rk ?pa ?wd ?mt)) ?k1) _] =>
      assert (Hrd : execR (Defs.bind (Defs.liftR (read_ram rk pa wd mt)) k1) s
                    = Some (inr w, s)) end.
    { rewrite (execR_liftR_seq _ _ _ _ _ (Hread_plain addr w s Hdev Hbytes)).
      cbn beta match. apply execR_returnR_fwd. }
    rewrite (execR_bind_Some _ _ _ _ _ Hrd). cbn beta zeta.
    change (update_subrange_vec_dec (zeros' (8 * 1 * width))
              (8 * (0 + 1) * width - 1) (8 * 0 * width) (autocast w))
      with (update_subrange_vec_dec (zeros' (8 * width)) (8 * width - 1) 0
              (autocast (T := mword) w)).
    rewrite (usvd_zeros_full_gen (8 * width) w ltac:(lia)).
    apply execR_returnR_fwd. }
  rewrite (execR_bind_Some _ _ _ _ _ Hu). cbn beta zeta.
  rewrite execR_returnR. kill_autocast. reflexivity.
Qed.

Lemma exec_mem_read_load_w_S (pbmt : page_based_mem_type) (addr : mword 64)
    (region : PMA_Region) (w : mword (8*width)) (m : mword 64) s :
  pmpAddrMatchType_encdec_backwards
    (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) = TOR ->
  zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0) = false ->
  pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
    (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0)) 4)
    (uint addr) (uint (to_bits 64 width)) = PMP_Match ->
  eq_vec (_get_Pmpcfg_ent_R (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) ('b"1") = true ->
  matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr addr) width = Some region ->
  is_aligned_paddr (Physaddr addr) width = true ->
  (override_PMA (PMA_Region_attributes region) pbmt).(PMA_readable) = true ->
  exec (within_clint (Physaddr addr) width) s = Some (false, s) ->
  exec (within_sig (Physaddr addr) width) s = Some (false, s) ->
  exec (within_htif_readable (Physaddr addr) width) s = Some (false, s) ->
  dev_addr addr = false ->
  (forall j : nat, (N.of_nat j < Z.to_N width)%N ->
     s.(mem) !! (pa_add addr j) = Some (nth_byte w j)) ->
  register_lookup mstatus s.(sregs) = m ->
  eq_vec (_get_Mstatus_MPRV m) ('b"1" : mword 1) = false ->
  register_lookup cur_privilege s.(sregs) = Supervisor ->
  exec (mem_read (Load Data) pbmt (Physaddr addr) width false false false)
       s = Some (Ok w, s).
Proof.
  intros HA Hord Hrange HR Hmatch Halign Hread Hc Hsig Hh Hdev Hbytes Hms Hmprv Hpriv.
  unfold mem_read.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mstatus s)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg cur_privilege s)).
  rewrite Hpriv.
  rewrite Hms.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_effectivePrivilege_load_S m s Hmprv)).
  unfold mem_read_priv.
  assert (Hcmr : exec (checked_mem_read (Load Data) pbmt Supervisor (Physaddr addr) width false false false false) s = Some (Ok (w, default_meta), s)).
  { apply exec_checked_mem_read_ram_load_w_S with (region := region); assumption. }
  assert (Hmrpm : exec (mem_read_priv_meta (Load Data) pbmt Supervisor (Physaddr addr) width false false false false) s = Some (Ok (w, default_meta), s)).
  { unfold mem_read_priv_meta. cbn [orb andb].
    rewrite (exec_bind_Some _ _ _ _ _ Hcmr).
    cbn match. unfold mem_read_callback. apply exec_returnM. }
  rewrite (exec_bind_Some _ _ _ _ _ Hmrpm).
  cbn [MemoryOpResult_drop_meta]. apply exec_returnM.
Qed.

(* ---- vmem_read_addr reduction (value-pinned, generic width) ---- *)
Section RWwSwalkPt.
Variable a : mword 64.
Variable v : mword (8*width).
Variable region : PMA_Region.
Variable s s' : mstate.
Variable pa : mword 64.
Variable md : SATPMode.
Hypothesis Halign : is_aligned_vaddr (Virtaddr a) width = true.
Hypothesis Hcp' : register_lookup cur_privilege s'.(sregs) = Supervisor.
Hypothesis Hmprv' : eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s'.(sregs))) ('b"1") = false.
(* the vmem level resolves the effective privilege and ITS translation mode
   before the access, so the pre-state's privilege facts are needed too *)
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
    (uint pa) (uint (to_bits 64 width)) = PMP_Match.
Hypothesis HR : eq_vec (_get_Pmpcfg_ent_R (vec_access_dec (register_lookup pmpcfg_n s'.(sregs)) 0)) ('b"1") = true.
Hypothesis Hmatch : matching_pma_region (register_lookup pma_regions s'.(sregs)) (Physaddr pa) width = Some region.
Hypothesis Hpalign : is_aligned_paddr (Physaddr pa) width = true.
Hypothesis Hread : (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_readable) = true.
Hypothesis Hc : exec (within_clint (Physaddr pa) width) s' = Some (false, s').
Hypothesis Hsig : exec (within_sig (Physaddr pa) width) s' = Some (false, s').
Hypothesis Hh : exec (within_htif_readable (Physaddr pa) width) s' = Some (false, s').
Hypothesis Hdev : dev_addr pa = false.
Hypothesis Hbytes : forall j : nat, (N.of_nat j < Z.to_N width)%N -> s'.(mem) !! (pa_add pa j) = Some (nth_byte v j).

Lemma exec_vmem_read_addr_w_S_walk_pt :
  exec (vmem_read_addr (Virtaddr a) width (Load Data) false false false) s
    = Some (Ok v, s').
Proof.
  assert (Heff : exec (effectivePrivilege (Load Data) (register_lookup mstatus s.(sregs))
                         (register_lookup cur_privilege s.(sregs))) s = Some (Supervisor, s)).
  { rewrite Hcps. apply exec_effectivePrivilege_load_S. exact Hmprvs. }
  apply (exec_vmem_read_addr_aligned_load width a pa v Supervisor md s s' Hvw Halign Heff Htm).
  apply (exec_translate_and_read_value_g width a pa PBMT_PMA v s s' Htr).
  apply (exec_mem_read_load_w_S PBMT_PMA pa region v (register_lookup mstatus s'.(sregs)) s'
           HA Hord Hrange HR Hmatch Hpalign Hread Hc Hsig Hh Hdev Hbytes eq_refl Hmprv' Hcp').
Qed.
End RWwSwalkPt.

(* ---- vmem_read (gpr) reduction, generic width ---- *)
Section RWgwSwalkPt.
Variable rs1 : mword 5.
Variable offset : mword 64.
Variable v : mword (8*width).
Variable region : PMA_Region.
Variable s s' : mstate.
Let ea := add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                   else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs)) offset.
Let a8 := sign_extend' 64 (subrange_vec_dec ea (xlen - 0 - 1) 0).
Variable pa : mword 64.
Variable md : SATPMode.
Hypothesis Htea : exec (transform_effective_address (Virtaddr ea) (Load Data)) s
                  = Some (Virtaddr ea, s).
Hypothesis Halign : is_aligned_vaddr (Virtaddr a8) width = true.
Hypothesis Htr : exec (translateAddr (Virtaddr a8) (Load Data)) s
                 = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), s').
Hypothesis Hcp' : register_lookup cur_privilege s'.(sregs) = Supervisor.
Hypothesis Hmprv' : eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s'.(sregs))) ('b"1") = false.
Hypothesis Hcps : register_lookup cur_privilege s.(sregs) = Supervisor.
Hypothesis Hmprvs : eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s.(sregs))) ('b"1") = false.
Hypothesis Htm : exec (translationMode Supervisor) s = Some (md, s).
Hypothesis HA : pmpAddrMatchType_encdec_backwards
    (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s'.(sregs)) 0)) = TOR.
Hypothesis Hord : zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s'.(sregs)) 0) = false.
Hypothesis Hrange : pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
    (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s'.(sregs)) 0)) 4)
    (uint pa) (uint (to_bits 64 width)) = PMP_Match.
Hypothesis HR : eq_vec (_get_Pmpcfg_ent_R (vec_access_dec (register_lookup pmpcfg_n s'.(sregs)) 0)) ('b"1") = true.
Hypothesis Hmatch : matching_pma_region (register_lookup pma_regions s'.(sregs)) (Physaddr pa) width = Some region.
Hypothesis Hpalign : is_aligned_paddr (Physaddr pa) width = true.
Hypothesis Hread : (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_readable) = true.
Hypothesis Hc : exec (within_clint (Physaddr pa) width) s' = Some (false, s').
Hypothesis Hsig : exec (within_sig (Physaddr pa) width) s' = Some (false, s').
Hypothesis Hh : exec (within_htif_readable (Physaddr pa) width) s' = Some (false, s').
Hypothesis Hdev : dev_addr pa = false.
Hypothesis Hbytes : forall j : nat, (N.of_nat j < Z.to_N width)%N -> s'.(mem) !! (pa_add pa j) = Some (nth_byte v j).

Lemma exec_vmem_read_w_gpr_S_walk_pt :
  exec (vmem_read (Regidx rs1) offset width (Load Data) false false false) s = Some (Ok v, s').
Proof.
  unfold vmem_read. rewrite exec_catch_early_return.
  assert (Ha8ea : a8 = ea) by (unfold a8; rewrite subrange_id; apply sign_extend'_id).
  assert (Hgta : exec (get_transformed_data_addr (Regidx rs1) offset (Load Data) width) s
                 = Some (Ext_DataAddr_OK (Virtaddr a8), s)).
  { unfold get_transformed_data_addr.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_ext_data_get_addr_gpr rs1 offset (Load Data) width s)).
    cbn match.
    rewrite (exec_bind_Some _ _ _ _ _ Htea).
    rewrite Ha8ea. apply exec_returnM. }
  rewrite (execR_liftR_seq _ _ _ _ _ Hgta).
  cbn match.
  rewrite (execR_bind_Some _ _ _ _ _ (execR_returnR_fwd (Virtaddr a8) s)).
  rewrite execR_liftR.
  rewrite (exec_vmem_read_addr_w_S_walk_pt a8 v region s s' pa md Halign Hcp' Hmprv'
             Hcps Hmprvs Htm Htr HA Hord Hrange HR Hmatch Hpalign Hread Hc Hsig Hh Hdev Hbytes).
  reflexivity.
Qed.
End RWgwSwalkPt.

(* ---- execute LOAD retire, generic width ---- *)
Section ExecLoadGwSwalkPt.
Variable is_unsigned : bool.
Variable rs1 rd : mword 5.
Variable imm : mword 12.
Variable v : mword (8*width).
Variable region : PMA_Region.
Variable s s' : mstate.
Let offset := sign_extend' 64 imm.
Let ea := add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                   else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs)) offset.
Let a8 := sign_extend' 64 (subrange_vec_dec ea (xlen - 0 - 1) 0).
Variable pa : mword 64.
Variable md : SATPMode.
Hypothesis Hrd : uint rd <> 0.
Hypothesis Htea : exec (transform_effective_address (Virtaddr ea) (Load Data)) s
                  = Some (Virtaddr ea, s).
Hypothesis Halign : is_aligned_vaddr (Virtaddr a8) width = true.
Hypothesis Htr : exec (translateAddr (Virtaddr a8) (Load Data)) s
                 = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), s').
Hypothesis Hcp' : register_lookup cur_privilege s'.(sregs) = Supervisor.
Hypothesis Hmprv' : eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s'.(sregs))) ('b"1") = false.
Hypothesis Hcps : register_lookup cur_privilege s.(sregs) = Supervisor.
Hypothesis Hmprvs : eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s.(sregs))) ('b"1") = false.
Hypothesis Htm : exec (translationMode Supervisor) s = Some (md, s).
Hypothesis HA : pmpAddrMatchType_encdec_backwards
    (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s'.(sregs)) 0)) = TOR.
Hypothesis Hord : zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s'.(sregs)) 0) = false.
Hypothesis Hrange : pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
    (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s'.(sregs)) 0)) 4)
    (uint pa) (uint (to_bits 64 width)) = PMP_Match.
Hypothesis HR : eq_vec (_get_Pmpcfg_ent_R (vec_access_dec (register_lookup pmpcfg_n s'.(sregs)) 0)) ('b"1") = true.
Hypothesis Hmatch : matching_pma_region (register_lookup pma_regions s'.(sregs)) (Physaddr pa) width = Some region.
Hypothesis Hpalign : is_aligned_paddr (Physaddr pa) width = true.
Hypothesis Hread : (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_readable) = true.
Hypothesis Hc : exec (within_clint (Physaddr pa) width) s' = Some (false, s').
Hypothesis Hsig : exec (within_sig (Physaddr pa) width) s' = Some (false, s').
Hypothesis Hh : exec (within_htif_readable (Physaddr pa) width) s' = Some (false, s').
Hypothesis Hdev : dev_addr pa = false.
Hypothesis Hbytes : forall j : nat, (N.of_nat j < Z.to_N width)%N -> s'.(mem) !! (pa_add pa j) = Some (nth_byte v j).

Lemma exec_execute_LOAD_w_gpr_S_walk_pt :
  exec (execute (LOAD (imm, Regidx rs1, Regidx rd, is_unsigned, width))) s
    = Some (RETIRE_SUCCESS,
            set_reg s' (R_bitvector_64 (gpr_of_Z (uint rd))) (regval_into_reg (extend_value is_unsigned v))).
Proof.
  change (execute (LOAD (imm, Regidx rs1, Regidx rd, is_unsigned, width)))
    with (execute_LOAD imm (Regidx rs1) (Regidx rd) is_unsigned width).
  unfold execute_LOAD.
  replace (width <=? xlen_bytes) with true
    by (change xlen_bytes with 8; symmetry; apply Z.leb_le; exact Hw8).
  assert (Hass : exec (assert_exp' true "extensions/I/base_insts.sail:289.28-289.29" : M (true = true)) s = Some (@eq_refl bool true, s)) by reflexivity.
  rewrite (exec_bind_Some _ _ _ _ _ Hass).
  rewrite (exec_bind_Some _ _ _ _ _
    (exec_vmem_read_w_gpr_S_walk_pt rs1 offset v region s s' pa md Htea Halign Htr Hcp' Hmprv'
       Hcps Hmprvs Htm HA Hord Hrange HR Hmatch Hpalign Hread Hc Hsig Hh Hdev Hbytes)).
  cbn match.
  assert (Hw : exec (wX_bits (Regidx rd) (extend_value is_unsigned v)) s'
               = Some (tt, set_reg s' (R_bitvector_64 (gpr_of_Z (uint rd)))
                              (regval_into_reg (extend_value is_unsigned v)))).
  { rewrite (exec_wX_bits_gpr rd (extend_value is_unsigned v) s').
    rewrite (proj2 (Z.eqb_neq (uint rd) 0) Hrd). reflexivity. }
  rewrite (exec_bind0_Some _ _ _ _ _ Hw).
  apply exec_returnM.
Qed.
End ExecLoadGwSwalkPt.

End SmodeMemGenLoad.

(* ===================================================================== *)
(* §2  The width-generic S-mode-walk-pt STORE stack.  Same layering: the  *)
(* byte-level write_ram fact stays per-width (Hwrite_plain), everything    *)
(* above is proved once over the abstract width.                          *)
(* ===================================================================== *)
Section SmodeMemGenStore.
Context `{GEN : GenId} `{CID : CpuId}.
Variable width : Z.
Hypothesis Hw0 : 0 < width.
Hypothesis Hw8 : width <= 8.
Hypothesis Hvw : vmem_width width.
Hypothesis Hwrite_plain : forall (addr : mword 64) (data : mword (8*width)) s,
  dev_addr addr = false ->
  exec (write_ram rv64d_types.Write_plain (Physaddr addr) width data tt) s
    = Some (true, MState s.(sregs) (write_bytes s.(mem) addr (Z.to_N width) data) s.(mdev)).

Lemma exec_checked_mem_write_ram_store_w_S (pbmt : page_based_mem_type) (addr : mword 64)
    (region : PMA_Region) (data : mword (8*width)) s :
  pmpAddrMatchType_encdec_backwards
    (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) = TOR ->
  zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0) = false ->
  pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
    (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0)) 4)
    (uint addr) (uint (to_bits 64 width)) = PMP_Match ->
  eq_vec (_get_Pmpcfg_ent_W (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) ('b"1") = true ->
  matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr addr) width = Some region ->
  is_aligned_paddr (Physaddr addr) width = true ->
  (override_PMA (PMA_Region_attributes region) pbmt).(PMA_writable) = true ->
  exec (within_clint (Physaddr addr) width) s = Some (false, s) ->
  exec (within_sig (Physaddr addr) width) s = Some (false, s) ->
  exec (within_htif_writable (Physaddr addr) width) s = Some (false, s) ->
  dev_addr addr = false ->
  exec (checked_mem_write (Physaddr addr) width data (Store Data) pbmt Supervisor tt false false false) s
    = Some (Ok true, MState s.(sregs) (write_bytes s.(mem) addr (Z.to_N width) data) s.(mdev)).
Proof.
  intros HA Hord Hrange HW Hmatch Halign Hwrite Hc Hsig Hh Hdev.
  assert (Hcp : exec (check_pma_with_pmp_priority (Store Data) pbmt Supervisor
                        (Physaddr addr) width false) s = Some (Ok pma_ok_aligned, s)).
  { unfold check_pma_with_pmp_priority.
    rewrite (exec_bind_Some _ _ _ _ _
               (exec_pmaCheck_ram_store_g width addr pbmt region s Hmatch Halign Hwrite)).
    cbn match. apply exec_returnM. }
  assert (Hmmio : exec (within_mmio_writable (Physaddr addr) width) s = Some (false, s)).
  { unfold within_mmio_writable. cbn [get_config_rvfi].
    rewrite (exec_or_boolM_Some _ _ _ _ _ Hc). cbn match.
    rewrite (exec_or_boolM_Some _ _ _ _ _ Hsig). cbn match.
    rewrite (exec_and_boolM_Some _ _ _ _ _ Hh). cbn match. reflexivity. }
  set (sw := MState s.(sregs) (write_bytes s.(mem) addr (Z.to_N width) data) s.(mdev)).
  unfold checked_mem_write. rewrite exec_catch_early_return.
  rewrite (execR_liftR_seq _ _ _ _ _ Hcp). cbn beta. cbn match.
  rewrite execR_bind. rewrite execR_returnR. cbn match beta.
  rewrite pma_ok_aligned_splittable. rewrite pma_ok_aligned_granule.
  rewrite (execR_liftR_seq _ _ _ _ _ (exec_split_misaligned_unsplit addr width 0 s)). cbn beta.
  rewrite misaligned_order_1. cbn zeta.
  assert (Hwkf : exec (write_kind_of_flags false false false) s
                 = Some (rv64d_types.Write_plain, s))
    by (unfold write_kind_of_flags; cbn match; apply exec_returnM).
  rewrite (execR_liftR_seq _ _ _ _ _ Hwkf). cbn beta.
  match goal with |- context[Defs.bind (Defs.untilMT ?vs ?m0 ?c ?b) _] =>
    assert (Hu : execR (Defs.untilMT vs m0 c b) s = Some (inr (true, 0, true), sw)) end.
  { eapply execR_untilMT_1; [ reflexivity | | apply execR_returnR_fwd ].
    rewrite (execR_liftR_seq _ _ _ _ _ (exec_assert_exp'_true _ s)). cbn beta.
    change (bits_of_physaddr (Physaddr addr)) with addr.
    assert (Havi : add_vec_int addr (0 * width) = addr)
      by (assert (H0 : (0 * width)%Z = 0) by lia; rewrite H0; apply avi0).
    rewrite Havi.
    rewrite (execR_liftR_seq _ _ _ _ _
               (exec_pmpCheck_supervisor_grant_store addr width s HA Hord Hrange HW)).
    cbn beta. cbn match.
    rewrite execR_bind0. rewrite execR_returnR. cbn match zeta.
    rewrite (execR_liftR_seq _ _ _ _ _ Hmmio). cbn beta. cbn match.
    change (autocast (T := mword)
              (subrange_vec_dec data (8 * (0 + 1) * width - 1) (8 * 0 * width))
            : mword (8 * width))
      with (autocast (T := mword) (subrange_vec_dec data (8 * width - 1) 0)
            : mword (8 * width)).
    rewrite (subrange_full_gen_cast (8 * width) data ltac:(lia)).
    match goal with
      |- context[Defs.bind (Defs.bind (Defs.liftR (write_ram ?wk ?pa ?wd ?dt ?mt)) ?k1) _] =>
      assert (Hwr : execR (Defs.bind (Defs.liftR (write_ram wk pa wd dt mt)) k1) s
                    = Some (inr true, sw)) end.
    { rewrite (execR_liftR_seq _ _ _ _ _ (Hwrite_plain addr data s Hdev)).
      cbn beta. cbn [andb]. apply execR_returnR_fwd. }
    rewrite (execR_bind_Some _ _ _ _ _ Hwr). cbn beta zeta.
    apply execR_returnR_fwd. }
  rewrite (execR_bind_Some _ _ _ _ _ Hu). cbn beta zeta.
  rewrite execR_returnR. reflexivity.
Qed.

Lemma exec_mem_write_value_w_S (pbmt : page_based_mem_type) (addr : mword 64)
    (region : PMA_Region) (data : mword (8*width)) (m : mword 64) s :
  pmpAddrMatchType_encdec_backwards
    (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) = TOR ->
  zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0) = false ->
  pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
    (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0)) 4)
    (uint addr) (uint (to_bits 64 width)) = PMP_Match ->
  eq_vec (_get_Pmpcfg_ent_W (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) ('b"1") = true ->
  matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr addr) width = Some region ->
  is_aligned_paddr (Physaddr addr) width = true ->
  (override_PMA (PMA_Region_attributes region) pbmt).(PMA_writable) = true ->
  exec (within_clint (Physaddr addr) width) s = Some (false, s) ->
  exec (within_sig (Physaddr addr) width) s = Some (false, s) ->
  exec (within_htif_writable (Physaddr addr) width) s = Some (false, s) ->
  dev_addr addr = false ->
  register_lookup mstatus s.(sregs) = m ->
  eq_vec (_get_Mstatus_MPRV m) ('b"1" : mword 1) = false ->
  register_lookup cur_privilege s.(sregs) = Supervisor ->
  exec (mem_write_value (Physaddr addr) width data (Store Data) pbmt false false false) s
    = Some (Ok true, MState s.(sregs) (write_bytes s.(mem) addr (Z.to_N width) data) s.(mdev)).
Proof.
  intros HA Hord Hrange HW Hmatch Halign Hwrite Hc Hsig Hh Hdev Hms Hmprv Hpriv.
  unfold mem_write_value, mem_write_value_meta.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mstatus s)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg cur_privilege s)).
  rewrite Hpriv. rewrite Hms.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_effectivePrivilege_store_S m s Hmprv)).
  unfold mem_write_value_priv_meta. cbn [orb andb].
  rewrite (exec_bind_Some _ _ _ _ _ (exec_checked_mem_write_ram_store_w_S pbmt addr region data s HA Hord Hrange HW Hmatch Halign Hwrite Hc Hsig Hh Hdev)).
  cbn match. unfold mem_write_callback. apply exec_returnm.
Qed.

(* ---- vmem_write_addr reduction (generic width, value = model subrange) ---- *)
Section SWwSwalkPt.
Variable a : mword 64.
Variable dat : mword (8*width).
Variable region : PMA_Region.
Variable s s' : mstate.
Variable pa : mword 64.
Variable md : SATPMode.
Hypothesis Halign : is_aligned_vaddr (Virtaddr a) width = true.
Hypothesis Hcp : register_lookup cur_privilege s'.(sregs) = Supervisor.
Hypothesis Hmprv : eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s'.(sregs))) ('b"1") = false.
Hypothesis Hcps : register_lookup cur_privilege s.(sregs) = Supervisor.
Hypothesis Hmprvs : eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s.(sregs))) ('b"1") = false.
Hypothesis Htm : exec (translationMode Supervisor) s = Some (md, s).
Hypothesis Htr : exec (translateAddr (Virtaddr a) (Store Data)) s
                 = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), s').
Hypothesis HA : pmpAddrMatchType_encdec_backwards
    (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s'.(sregs)) 0)) = TOR.
Hypothesis Hord : zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s'.(sregs)) 0) = false.
Hypothesis Hrange : pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
    (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s'.(sregs)) 0)) 4)
    (uint pa) (uint (to_bits 64 width)) = PMP_Match.
Hypothesis HW : eq_vec (_get_Pmpcfg_ent_W (vec_access_dec (register_lookup pmpcfg_n s'.(sregs)) 0)) ('b"1") = true.
Hypothesis Hmatch : matching_pma_region (register_lookup pma_regions s'.(sregs)) (Physaddr pa) width = Some region.
Hypothesis Hpalign : is_aligned_paddr (Physaddr pa) width = true.
Hypothesis Hwrite : (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_writable) = true.
Hypothesis Hc : exec (within_clint (Physaddr pa) width) s' = Some (false, s').
Hypothesis Hsig : exec (within_sig (Physaddr pa) width) s' = Some (false, s').
Hypothesis Hh : exec (within_htif_writable (Physaddr pa) width) s' = Some (false, s').
Hypothesis Hdev : dev_addr pa = false.

Lemma exec_vmem_write_addr_w_S_walk_pt :
  exec (vmem_write_addr (Virtaddr a) width dat (Store Data) false false false) s
    = Some (Ok true, MState s'.(sregs) (write_bytes s'.(mem) pa (Z.to_N width) dat) s'.(mdev)).
Proof.
  assert (Heff : exec (effectivePrivilege (Store Data) (register_lookup mstatus s.(sregs))
                         (register_lookup cur_privilege s.(sregs))) s = Some (Supervisor, s)).
  { rewrite Hcps. apply exec_effectivePrivilege_store_S. exact Hmprvs. }
  assert (Hea : exec (mem_write_ea (Physaddr pa) width (Store Data) PBMT_PMA false false false) s'
                = Some (Ok tt, s')).
  { apply (exec_mem_write_ea_g width pa (Store Data) PBMT_PMA Supervisor s').
    - rewrite Hcp. apply exec_effectivePrivilege_store_S. exact Hmprv.
    - unfold check_pma_with_pmp_priority.
      rewrite (exec_bind_Some _ _ _ _ _
                 (exec_pmaCheck_ram_store_g width pa PBMT_PMA region s' Hmatch Hpalign Hwrite)).
      cbn match. apply exec_returnM.
    - exact (exec_pmpCheck_supervisor_grant_store pa width s' HA Hord Hrange HW). }
  assert (Hwv : exec (mem_write_value (Physaddr pa) width
                        (autocast (T := mword) (subrange_vec_dec dat (8*width-1) 0))
                        (Store Data) PBMT_PMA false false false) s'
                = Some (Ok true, MState s'.(sregs) (write_bytes s'.(mem) pa (Z.to_N width) dat) s'.(mdev))).
  { rewrite (subrange_full_gen_cast (8 * width) dat ltac:(lia)).
    exact (exec_mem_write_value_w_S PBMT_PMA pa region dat (register_lookup mstatus s'.(sregs)) s'
             HA Hord Hrange HW Hmatch Hpalign Hwrite Hc Hsig Hh Hdev eq_refl Hmprv Hcp). }
  exact (exec_vmem_write_addr_aligned_store width a pa dat Supervisor md s s'
           Hvw Halign Heff Htm Htr Hea Hwv).
Qed.
End SWwSwalkPt.

(* ---- vmem_write (gpr) reduction, generic width ---- *)
Section VWgwSwalkPt.
Variable rs1 : mword 5.
Variable offset : mword 64.
Variable dat : mword (8*width).
Variable region : PMA_Region.
Variable s s' : mstate.
Let ea := add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                   else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs)) offset.
Let a8 := sign_extend' 64 (subrange_vec_dec ea (xlen - 0 - 1) 0).
Variable pa : mword 64.
Variable md : SATPMode.
Hypothesis Htea : exec (transform_effective_address (Virtaddr ea) (Store Data)) s
                  = Some (Virtaddr ea, s).
Hypothesis Halign : is_aligned_vaddr (Virtaddr a8) width = true.
Hypothesis Htr : exec (translateAddr (Virtaddr a8) (Store Data)) s
                 = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), s').
Hypothesis Hcp' : register_lookup cur_privilege s'.(sregs) = Supervisor.
Hypothesis Hmprv' : eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s'.(sregs))) ('b"1") = false.
Hypothesis Hcps : register_lookup cur_privilege s.(sregs) = Supervisor.
Hypothesis Hmprvs : eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s.(sregs))) ('b"1") = false.
Hypothesis Htm : exec (translationMode Supervisor) s = Some (md, s).
Hypothesis HA : pmpAddrMatchType_encdec_backwards
    (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s'.(sregs)) 0)) = TOR.
Hypothesis Hord : zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s'.(sregs)) 0) = false.
Hypothesis Hrange : pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
    (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s'.(sregs)) 0)) 4)
    (uint pa) (uint (to_bits 64 width)) = PMP_Match.
Hypothesis HW : eq_vec (_get_Pmpcfg_ent_W (vec_access_dec (register_lookup pmpcfg_n s'.(sregs)) 0)) ('b"1") = true.
Hypothesis Hmatch : matching_pma_region (register_lookup pma_regions s'.(sregs)) (Physaddr pa) width = Some region.
Hypothesis Hpalign : is_aligned_paddr (Physaddr pa) width = true.
Hypothesis Hwrite : (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_writable) = true.
Hypothesis Hc : exec (within_clint (Physaddr pa) width) s' = Some (false, s').
Hypothesis Hsig : exec (within_sig (Physaddr pa) width) s' = Some (false, s').
Hypothesis Hh : exec (within_htif_writable (Physaddr pa) width) s' = Some (false, s').
Hypothesis Hdev : dev_addr pa = false.

Lemma exec_vmem_write_w_gpr_S_walk_pt :
  exec (vmem_write (Regidx rs1) offset width dat (Store Data) false false false) s
    = Some (Ok true, MState s'.(sregs) (write_bytes s'.(mem) pa (Z.to_N width) dat) s'.(mdev)).
Proof.
  unfold vmem_write. rewrite exec_catch_early_return.
  assert (Ha8ea : a8 = ea) by (unfold a8; rewrite subrange_id; apply sign_extend'_id).
  assert (Hgta : exec (get_transformed_data_addr (Regidx rs1) offset (Store Data) width) s
                 = Some (Ext_DataAddr_OK (Virtaddr a8), s)).
  { unfold get_transformed_data_addr.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_ext_data_get_addr_gpr rs1 offset (Store Data) width s)).
    cbn match.
    rewrite (exec_bind_Some _ _ _ _ _ Htea).
    rewrite Ha8ea. apply exec_returnM. }
  rewrite (execR_liftR_seq _ _ _ _ _ Hgta).
  cbn match.
  rewrite (execR_bind_Some _ _ _ _ _ (execR_returnR_fwd (Virtaddr a8) s)).
  rewrite execR_liftR.
  rewrite (exec_vmem_write_addr_w_S_walk_pt a8 dat region s s' pa md Halign Hcp' Hmprv'
             Hcps Hmprvs Htm Htr HA Hord Hrange HW Hmatch Hpalign Hwrite Hc Hsig Hh Hdev).
  reflexivity.
Qed.
End VWgwSwalkPt.

(* ---- execute STORE retire, generic width ---- *)
Section ExecStoreGwSwalkPt.
Variable rs2 rs1 : mword 5.
Variable imm : mword 12.
Variable region : PMA_Region.
Variable s s' : mstate.
Let offset := sign_extend' 64 imm.
Let vrs2 : mword (8*width) := autocast (T := mword)
  (subrange_vec_dec (if Z.eqb (uint rs2) 0 then zero_reg
                     else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs2))) s.(sregs))
     (width*8-1) 0).
Let ea := add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                   else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs)) offset.
Let a8 := sign_extend' 64 (subrange_vec_dec ea (xlen - 0 - 1) 0).
Variable pa : mword 64.
Variable md : SATPMode.
Hypothesis Htea : exec (transform_effective_address (Virtaddr ea) (Store Data)) s
                  = Some (Virtaddr ea, s).
Hypothesis Halign : is_aligned_vaddr (Virtaddr a8) width = true.
Hypothesis Htr : exec (translateAddr (Virtaddr a8) (Store Data)) s
                 = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), s').
Hypothesis Hcp' : register_lookup cur_privilege s'.(sregs) = Supervisor.
Hypothesis Hmprv' : eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s'.(sregs))) ('b"1") = false.
Hypothesis Hcps : register_lookup cur_privilege s.(sregs) = Supervisor.
Hypothesis Hmprvs : eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s.(sregs))) ('b"1") = false.
Hypothesis Htm : exec (translationMode Supervisor) s = Some (md, s).
Hypothesis HA : pmpAddrMatchType_encdec_backwards
    (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s'.(sregs)) 0)) = TOR.
Hypothesis Hord : zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s'.(sregs)) 0) = false.
Hypothesis Hrange : pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
    (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s'.(sregs)) 0)) 4)
    (uint pa) (uint (to_bits 64 width)) = PMP_Match.
Hypothesis HW : eq_vec (_get_Pmpcfg_ent_W (vec_access_dec (register_lookup pmpcfg_n s'.(sregs)) 0)) ('b"1") = true.
Hypothesis Hmatch : matching_pma_region (register_lookup pma_regions s'.(sregs)) (Physaddr pa) width = Some region.
Hypothesis Hpalign : is_aligned_paddr (Physaddr pa) width = true.
Hypothesis Hwrite : (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_writable) = true.
Hypothesis Hc : exec (within_clint (Physaddr pa) width) s' = Some (false, s').
Hypothesis Hsig : exec (within_sig (Physaddr pa) width) s' = Some (false, s').
Hypothesis Hh : exec (within_htif_writable (Physaddr pa) width) s' = Some (false, s').
Hypothesis Hdev : dev_addr pa = false.

Lemma exec_execute_STORE_w_gpr_S_walk_pt :
  exec (execute (STORE (imm, Regidx rs2, Regidx rs1, width))) s
    = Some (RETIRE_SUCCESS, MState s'.(sregs) (write_bytes s'.(mem) pa (Z.to_N width) vrs2) s'.(mdev)).
Proof.
  change (execute (STORE (imm, Regidx rs2, Regidx rs1, width)))
    with (execute_STORE imm (Regidx rs2) (Regidx rs1) width).
  unfold execute_STORE.
  replace (width <=? xlen_bytes) with true
    by (change xlen_bytes with 8; symmetry; apply Z.leb_le; exact Hw8).
  assert (Hass : exec (assert_exp' true "extensions/I/base_insts.sail:320.28-320.29" : M (true = true)) s
                 = Some (@eq_refl bool true, s)) by reflexivity.
  rewrite (exec_bind_Some _ _ _ _ _ Hass).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_rX_bits_gpr rs2 s)).
  cbn match.
  rewrite (exec_bind_Some _ _ _ _ _
    (exec_vmem_write_w_gpr_S_walk_pt rs1 offset vrs2 region s s' pa md Htea Halign Htr Hcp' Hmprv'
       Hcps Hmprvs Htm HA Hord Hrange HW Hmatch Hpalign Hwrite Hc Hsig Hh Hdev)).
  cbn match. rewrite (exec_returnM _ _). reflexivity.
Qed.
End ExecStoreGwSwalkPt.

End SmodeMemGenStore.
