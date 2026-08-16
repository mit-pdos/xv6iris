(* HartMStore.v -- the STORE path, one [swp] fact per model function.

   It mirrors HartMFetch's read path exactly, which is the point: the same
   four moves, the same tools, and the pieces the two share ([translateAddr],
   the PMP walk) are USED, not re-proven.  What is new here is only the
   write event itself.

   The one structural difference from the read side: [effectivePrivilege]
   at a STORE takes the MPRV branch (a fetch short-circuits it), so the
   store chain needs the [mstatus.MPRV = 0] premise the fetch chain did
   not. *)
From Stdlib Require Import ZArith Zquot Lia.
From stdpp Require Import gmap relations bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap ghost_map.
From iris.program_logic Require Import language weakestpre.
Require Import SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes.
Require Import RiscvLang RiscvPtsto RiscvExec HartSwp HartLift HartRegNode
        HartSpan HartSpanChar HartEvents HartMPmp HartMFetch HartMDecode.
Require Import RiscvTryStep RiscvExtras RiscvFetchExec.
Local Open Scope Z_scope.

Local Arguments Z.sub _ _ : simpl nomatch.
Local Arguments Z.add _ _ : simpl nomatch.
Local Arguments Z.mul _ _ : simpl nomatch.
Local Arguments Z.eqb _ _ : simpl nomatch.
Local Arguments Z.compare _ _ : simpl nomatch.
Local Arguments Z.pos_sub _ _ : simpl nomatch.
Local Arguments Pos.compare _ _ : simpl nomatch.
Local Arguments Pos.compare_cont _ _ _ : simpl nomatch.

Local Ltac s_cbn :=
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
Local Ltac s_glue :=
  cbn beta iota zeta delta
    [Defs.returnm returnM returnR Defs.returnR andb orb negb not
     Instances.generic_eq Instances.generic_neq].

Local Ltac s_read :=
  rewrite hfrun_read;
  match goal with
  | |- context [ bool_decide ?P ] =>
      rewrite (bool_decide_eq_true_2 P ltac:(assumption))
  end.

(* ====================================================================== *)
(* 1. The PMA check at a STORE: the same walk as the fetch's, taking the   *)
(*    WRITABLE conjunct of the RAM grant instead of the executable one.    *)
(* ====================================================================== *)

Local Lemma fit4_local (x k : Z) :
  x = 4 * k -> x < 2147483648 + 134217728 -> x + 4 <= 2147483648 + 134217728.
Proof. intros -> H. lia. Qed.

Local Lemma pma_access_local (a : SailStdpp.Values.mword 64) :
  addr_is_ram a -> is_aligned_paddr (Physaddr a) 4 = true ->
  pma_ram_access a 4.
Proof.
  intros [Hlo Hhi] Hal.
  unfold is_aligned_paddr in Hal. apply Z.eqb_eq in Hal.
  apply Zrem_divides in Hal. destruct Hal as [k Hk].
  unfold ram_base, ram_size in Hhi.
  unfold pma_ram_access, ram_base, ram_size.
  exact (conj (pma_width_ok 4 eq_refl eq_refl)
              (conj Hlo (fit4_local (uint a) k Hk Hhi))).
Qed.

Lemma hfrun_check_pma_store4 (D Drw : gset register) (rs : regstate)
    (pa : SailStdpp.Values.mword 64) (pmar0 : list PMA_Region) :
  (pma_regions : register) ∈ D ->
  register_lookup pma_regions rs = pmar0 ->
  pma_allows_ram pmar0 ->
  addr_is_ram pa ->
  is_aligned_paddr (Physaddr pa) 4 = true ->
  hfrun 6 D Drw rs
    (check_pma_with_pmp_priority (Store Data) PBMT_PMA Machine
       (Physaddr pa) 4 false)
  = Some (Values.Ok
            {| Phys_Mem_Access_Info_splittable := CannotSplit;
               Phys_Mem_Access_Info_granule_size_exp := 0 |}, rs).
Proof.
  intros HD Hpma Hpallow Hram Hpa.
  unfold check_pma_with_pmp_priority. s_cbn.
  s_read. rewrite Hpma. s_cbn.
  destruct (Hpallow pa 4 (pma_access_local pa Hram Hpa))
    as (region & Hmatch & Hgrant).
  destruct region as [rbase rsize rattr rdtree].
  destruct Hgrant as (_ & _ & Hx & _).
  cbn [PMA_Region_attributes] in Hx.
  rewrite Hmatch. s_cbn.
  rewrite Hx. s_cbn.
  rewrite Hpa. s_cbn.
  apply hfrun_ret.
Qed.

(* ====================================================================== *)
(* 2. [mem_write_ea]: the announce pass.  Same shape as                    *)
(*    [checked_mem_read] -- the PMA check, the split, an [untilMT] that    *)
(*    runs once, and the PMP check inside it -- but its loop body ends in  *)
(*    [write_ram_ea], which is pure, so there is no event here at all.     *)
(* ====================================================================== *)

Section store.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Lemma swp_mem_write_ea (Drw Dro : gset register) (Df : register -> dfrac)
      (rs : regstate) (pa : SailStdpp.Values.mword 64)
      (pmar0 : list PMA_Region) (pcfg : type_of_register pmpcfg_n) :
    Drw ## Dro ->
    (mstatus : register) ∈ Drw ∪ Dro ->
    (cur_privilege : register) ∈ Drw ∪ Dro ->
    (pma_regions : register) ∈ Drw ∪ Dro ->
    (pmpcfg_n : register) ∈ Drw ∪ Dro ->
    register_lookup cur_privilege rs = Machine ->
    register_lookup pma_regions rs = pmar0 ->
    register_lookup pmpcfg_n rs = pcfg ->
    eq_vec (_get_Mstatus_MPRV (register_lookup mstatus rs))
      (MachineWord.MachineWord.N_to_word 1 1%N) = false ->
    (forall i, pmpLocked (SailStdpp.Values.vec_access_dec pcfg i) = false) ->
    pma_allows_ram pmar0 ->
    addr_is_ram pa ->
    is_aligned_paddr (Physaddr pa) 4 = true ->
    gen_cert -∗
    hreg_frame rs Drw -∗
    hreg_frame_ro Df rs Dro -∗
    swp (mem_write_ea (Physaddr pa) 4 (Store Data) PBMT_PMA false false false)
      (fun r => ⌜r = Values.Ok tt⌝ ∗
                hreg_frame rs Drw ∗ hreg_frame_ro Df rs Dro).
  Proof.
    intros Hdisj HDmst HDpriv HDpma HDcfg Hpriv Hpma Hpcfg Hmprv Hunlock
      Hpallow Hram Hpa.
    iIntros "#Hcert Hrw Hro".
    rewrite /swp. iIntros (C) "%HC Hcont".
    unfold mem_write_ea.
    iApply (swp_use_cer (Defs.read_reg mstatus) _ _ C HC
              with "[Hrw Hro] [-]").
    { iApply (swp_read_reg_pinned Drw Dro Df rs _ Hdisj HDmst
                with "Hcert Hrw Hro"). }
    iIntros (v) "(-> & Hrw & Hro)".
    iApply (swp_use_cer (Defs.read_reg cur_privilege) _ _ C HC
              with "[Hrw Hro] [-]").
    { iApply (swp_read_reg_pinned Drw Dro Df rs _ Hdisj HDpriv
                with "Hcert Hrw Hro"). }
    iIntros (v) "(-> & Hrw & Hro)". rewrite Hpriv.
    unfold effectivePrivilege.
    change (Instances.generic_neq (Store Data) (InstructionFetch tt))
      with true.
    s_glue. rewrite Hmprv. s_glue.
    rewrite /returnM mliftR_ret mbind_ret. s_glue.
    iApply (swp_use_cer
              (check_pma_with_pmp_priority (Store Data) PBMT_PMA Machine
                 (Physaddr pa) 4 false) _ _ C HC with "[Hrw Hro] [-]").
    { iApply (swp_hfrun 6 Drw Dro Df rs rs _ _ Hdisj
                (hfrun_check_pma_store4 (Drw ∪ Dro) Drw rs pa pmar0
                   HDpma Hpma Hpallow Hram Hpa) with "Hcert Hrw Hro"). }
    iIntros (v) "(-> & Hrw & Hro)". s_glue.
    rewrite mbind_ret. s_glue.
    cbn [Phys_Mem_Access_Info_granule_size_exp Phys_Mem_Access_Info_splittable].
    cbn beta iota zeta delta [split_misaligned misaligned_order
      sys_misaligned_order_decreasing write_kind_of_flags].
    change (Instances.generic_eq CannotSplit CannotSplit) with true.
    s_glue.
    rewrite /returnM mliftR_ret mbind_ret. s_glue.
    rewrite mliftR_ret mbind_ret. s_glue.
    cbn beta iota zeta delta [Defs.untilMT Defs.untilMT' Defs.Zwf_guarded
      Z_ge_dec Z_ge_lt_dec Zcompare_rec Z.compare].
    cbn beta iota zeta delta [Defs.assert_exp' bits_of_physaddr].
    rewrite mliftR_ret mbind_ret. s_glue.
    change (0 * 4) with 0. rewrite avi0.
    iApply (swp_use_cer3 (pmpCheck (Physaddr pa) 4 (Store Data) Machine)
              _ _ _ _ C HC with "[Hrw Hro] [-]").
    { iApply (swp_pmpCheck_store4 Drw Dro Df rs pcfg pa Hdisj HDcfg
                Hunlock Hpa Hpcfg with "Hcert Hrw Hro"). }
    iIntros (v) "(-> & Hrw & Hro)". s_glue.
    rewrite mbind0_ret. s_glue.
    change (0 =? 1 - 1) with true. s_glue.
    rewrite mbind_ret. s_glue.
    rewrite mcer_ret.
    iApply ("Hcont" $! (Values.Ok tt)). by iFrame.
  Qed.

End store.
