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

(* WIDTH-GENERIC, as [HartMFetch]'s read twins already are: the page walk's
   A/D write-back is an 8-byte store, so the store side carries the width for
   the same reason the fetch side does. *)
Local Lemma clint_gt_local (x n : Z) : 0 <= n -> 2147483648 <= x -> 34340864 < x + n.
Proof. lia. Qed.

Local Lemma clint_false_local (a : SailStdpp.Values.mword 64) (n : Z) :
  0 <= n ->
  addr_is_ram a ->
  andb (Z.leb (uint plat_clint_base) (uint a))
       (Z.leb (Z.add (uint a) (__id n))
              (Z.add (uint plat_clint_base) (uint plat_clint_size)))
  = false.
Proof.
  intros Hn [Hlo _]. unfold ram_base in Hlo.
  assert (Hsum : Z.add (uint plat_clint_base) (uint plat_clint_size)
                 = 34340864) by (vm_compute; reflexivity).
  rewrite Hsum. unfold __id.
  apply andb_false_intro2. apply Z.leb_gt.
  exact (clint_gt_local (uint a) n Hn Hlo).
Qed.

Lemma hfrun_within_mmio_w_ram (D Drw : gset register) (rs : regstate)
    (pa : SailStdpp.Values.mword 64) (n : Z) :
  0 <= n ->
  (htif_tohost_base : register) ∈ D ->
  register_lookup htif_tohost_base rs = None ->
  addr_is_ram pa ->
  hfrun 12 D Drw rs (within_mmio_writable (Physaddr pa) n) = Some (false, rs).
Proof.
  intros Hn HD Hhtif Hram.
  unfold within_mmio_writable, within_clint, within_sig,
    within_htif_readable, within_htif_writable.
  s_cbn.
  rewrite (clint_false_local pa n Hn Hram). s_cbn.
  s_read. rewrite Hhtif. s_cbn.
  apply hfrun_ret.
Qed.

(* the store request, as the model builds it (the [cast_N] on the value is
   [sail_mem_write]'s own; carrying it here rather than fighting it keeps
   this a [reflexivity]) *)
Definition mwrite_req (pa : SailStdpp.Values.mword 64)
    (v : SailStdpp.Values.mword 32) : Interface.WriteReq.t 4 :=
  {| Interface.WriteReq.pa := pa;
     Interface.WriteReq.access_kind :=
       SailStdpp.ConcurrencyInterfaceTypes.AK_explicit
         {| SailStdpp.ConcurrencyInterfaceTypes.Explicit_access_kind_variety
              := SailStdpp.ConcurrencyInterfaceTypes.AV_plain;
            SailStdpp.ConcurrencyInterfaceTypes.Explicit_access_kind_strength
              := SailStdpp.ConcurrencyInterfaceTypes.AS_normal |};
     Interface.WriteReq.value :=
       TypeCasts.cast_N v (Defs.sail_mem_write_subproof 4);
     Interface.WriteReq.va := None;
     Interface.WriteReq.translation := tt;
     Interface.WriteReq.tag := None |}.

Lemma hwrite_req_at_write_ram (pa : SailStdpp.Values.mword 64)
    (v : SailStdpp.Values.mword 32) :
  hwrite_req_at 4 (write_ram Write_plain (Physaddr pa) 4 v tt)
  = Some (mwrite_req pa v).
Proof.
  unfold write_ram, Defs.sail_mem_write.
  cbn beta iota zeta delta
    [Defs.bind Defs.bind0 Interface.iMon_bind Defs.returnm returnM
     Z.to_N bits_of_physaddr
     SailStdpp.ConcurrencyInterfaceTypes.Mem_write_request_pa
     SailStdpp.ConcurrencyInterfaceTypes.Mem_write_request_access_kind
     SailStdpp.ConcurrencyInterfaceTypes.Mem_write_request_va
     SailStdpp.ConcurrencyInterfaceTypes.Mem_write_request_translation
     SailStdpp.ConcurrencyInterfaceTypes.Mem_write_request_tag
     SailStdpp.ConcurrencyInterfaceTypes.Mem_write_request_size
     SailStdpp.ConcurrencyInterfaceTypes.Mem_write_request_value].
  cbn [hwrite_req_at].
  destruct (decide (4%N = 4%N)) as [Heq|Hne]; [|congruence].
  assert (Heq = eq_refl) as -> by apply proof_irrel.
  reflexivity.
Qed.

Lemma hwrite_resume_write_ram (pa : SailStdpp.Values.mword 64)
    (v : SailStdpp.Values.mword 32) :
  hwrite_resume (write_ram Write_plain (Physaddr pa) 4 v tt)
  = Interface.Ret true.
Proof.
  unfold write_ram, Defs.sail_mem_write.
  cbn beta iota zeta delta
    [Defs.bind Defs.bind0 Interface.iMon_bind Defs.returnm returnM
     Z.to_N bits_of_physaddr
     SailStdpp.ConcurrencyInterfaceTypes.Mem_write_request_pa
     SailStdpp.ConcurrencyInterfaceTypes.Mem_write_request_access_kind
     SailStdpp.ConcurrencyInterfaceTypes.Mem_write_request_va
     SailStdpp.ConcurrencyInterfaceTypes.Mem_write_request_translation
     SailStdpp.ConcurrencyInterfaceTypes.Mem_write_request_tag
     SailStdpp.ConcurrencyInterfaceTypes.Mem_write_request_size
     SailStdpp.ConcurrencyInterfaceTypes.Mem_write_request_value].
  cbn [hwrite_resume]. reflexivity.
Qed.


(* THE 8-BYTE WRITE TWINS, for the page walk's A/D write-back.  A third
   concrete instance rather than a width parameter, for the reason
   [HartMFetch]'s 2-byte read twins already record: [WriteReq.t n] and
   [bv (8 * n)] are TYPE indices and a parameterised version does not reduce
   at a call site. *)
Definition mwrite_req8 (pa : SailStdpp.Values.mword 64)
    (v : SailStdpp.Values.mword 64) : Interface.WriteReq.t 8 :=
  {| Interface.WriteReq.pa := pa;
     Interface.WriteReq.access_kind :=
       SailStdpp.ConcurrencyInterfaceTypes.AK_explicit
         {| SailStdpp.ConcurrencyInterfaceTypes.Explicit_access_kind_variety
              := SailStdpp.ConcurrencyInterfaceTypes.AV_plain;
            SailStdpp.ConcurrencyInterfaceTypes.Explicit_access_kind_strength
              := SailStdpp.ConcurrencyInterfaceTypes.AS_normal |};
     Interface.WriteReq.value :=
       TypeCasts.cast_N v (Defs.sail_mem_write_subproof 8);
     Interface.WriteReq.va := None;
     Interface.WriteReq.translation := tt;
     Interface.WriteReq.tag := None |}.

Lemma hwrite_req_at_write_ram8 (pa : SailStdpp.Values.mword 64)
    (v : SailStdpp.Values.mword 64) :
  hwrite_req_at 8 (write_ram Write_plain (Physaddr pa) 8 v tt)
  = Some (mwrite_req8 pa v).
Proof.
  unfold write_ram, Defs.sail_mem_write.
  cbn beta iota zeta delta
    [Defs.bind Defs.bind0 Interface.iMon_bind Defs.returnm returnM
     Z.to_N bits_of_physaddr
     SailStdpp.ConcurrencyInterfaceTypes.Mem_write_request_pa
     SailStdpp.ConcurrencyInterfaceTypes.Mem_write_request_access_kind
     SailStdpp.ConcurrencyInterfaceTypes.Mem_write_request_va
     SailStdpp.ConcurrencyInterfaceTypes.Mem_write_request_translation
     SailStdpp.ConcurrencyInterfaceTypes.Mem_write_request_tag
     SailStdpp.ConcurrencyInterfaceTypes.Mem_write_request_size
     SailStdpp.ConcurrencyInterfaceTypes.Mem_write_request_value].
  cbn [hwrite_req_at].
  destruct (decide (8%N = 8%N)) as [Heq|Hne]; [|congruence].
  assert (Heq = eq_refl) as -> by apply proof_irrel.
  reflexivity.
Qed.

Lemma hwrite_resume_write_ram8 (pa : SailStdpp.Values.mword 64)
    (v : SailStdpp.Values.mword 64) :
  hwrite_resume (write_ram Write_plain (Physaddr pa) 8 v tt)
  = Interface.Ret true.
Proof.
  unfold write_ram, Defs.sail_mem_write.
  cbn beta iota zeta delta
    [Defs.bind Defs.bind0 Interface.iMon_bind Defs.returnm returnM
     Z.to_N bits_of_physaddr
     SailStdpp.ConcurrencyInterfaceTypes.Mem_write_request_pa
     SailStdpp.ConcurrencyInterfaceTypes.Mem_write_request_access_kind
     SailStdpp.ConcurrencyInterfaceTypes.Mem_write_request_va
     SailStdpp.ConcurrencyInterfaceTypes.Mem_write_request_translation
     SailStdpp.ConcurrencyInterfaceTypes.Mem_write_request_tag
     SailStdpp.ConcurrencyInterfaceTypes.Mem_write_request_size
     SailStdpp.ConcurrencyInterfaceTypes.Mem_write_request_value].
  cbn [hwrite_resume]. reflexivity.
Qed.

(* the Bare translation at a STORE: HartMFetch's generic walk, with the two
   access-dependent premises discharged.  [effectivePrivilege] is the one
   that needs work -- a store consults MPRV where a fetch short-circuits. *)
Lemma hfrun_translateAddr_M_store (D Drw : gset register) (rs : regstate)
    (pa : SailStdpp.Values.mword 64) :
  (mstatus : register) ∈ D ->
  (cur_privilege : register) ∈ D ->
  register_lookup cur_privilege rs = Machine ->
  eq_vec (_get_Mstatus_MPRV (register_lookup mstatus rs))
    (MachineWord.MachineWord.N_to_word 1 1%N) = false ->
  hfrun 8 D Drw rs (translateAddr (Virtaddr pa) (Store Data))
  = Some (Values.Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), rs).
Proof.
  intros HD1 HD2 Hpriv Hmprv.
  apply (hfrun_translateAddr_M D Drw rs pa _ HD1 HD2 Hpriv); [|reflexivity].
  unfold effectivePrivilege.
  change (Instances.generic_neq (Store Data) (InstructionFetch tt))
    with true.
  s_glue. rewrite Hmprv. by s_glue.
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

  Lemma swp_checked_mem_write (Drw Dro : gset register)
      (Df : register -> dfrac) (rs : regstate)
      (pa : SailStdpp.Values.mword 64) (v : SailStdpp.Values.mword 32)
      (pmar0 : list PMA_Region) (pcfg : type_of_register pmpcfg_n)
      (R : iProp Σ) :
    Drw ## Dro ->
    (pma_regions : register) ∈ Drw ∪ Dro ->
    (pmpcfg_n : register) ∈ Drw ∪ Dro ->
    (htif_tohost_base : register) ∈ Drw ∪ Dro ->
    register_lookup pma_regions rs = pmar0 ->
    register_lookup pmpcfg_n rs = pcfg ->
    register_lookup htif_tohost_base rs = None ->
    (forall i, pmpLocked (SailStdpp.Values.vec_access_dec pcfg i) = false) ->
    pma_allows_ram pmar0 ->
    addr_is_ram pa ->
    is_aligned_paddr (Physaddr pa) 4 = true ->
    gen_cert -∗
    hreg_frame rs Drw -∗
    hreg_frame_ro Df rs Dro -∗
    (∀ σ, mstate_interp σ ={⊤,∅}=∗
        ▷ (|={∅,⊤}=> mstate_interp
             (MState σ.(sregs)
                (write_bytes σ.(mem) pa 4
                   (Interface.WriteReq.value (mwrite_req pa v)))
                σ.(mdev)) ∗ R)) -∗
    swp (checked_mem_write (Physaddr pa) 4 v (Store Data) PBMT_PMA Machine
           tt false false false)
      (fun r => ⌜r = Values.Ok true⌝ ∗
                hreg_frame rs Drw ∗ hreg_frame_ro Df rs Dro ∗ R).
  Proof.
    intros Hdisj HDpma HDcfg HDhtif Hpma Hpcfg Hhtif Hunlock Hpallow Hram Hpa.
    iIntros "#Hcert Hrw Hro Hmem".
    rewrite /swp. iIntros (C) "%HC Hcont".
    unfold checked_mem_write.
    iApply (swp_use_cer
              (check_pma_with_pmp_priority (Store Data) PBMT_PMA Machine
                 (Physaddr pa) 4 false) _ _ C HC with "[Hrw Hro] [-]").
    { iApply (swp_hfrun 6 Drw Dro Df rs rs _ _ Hdisj
                (hfrun_check_pma_store4 (Drw ∪ Dro) Drw rs pa pmar0
                   HDpma Hpma Hpallow Hram Hpa) with "Hcert Hrw Hro"). }
    iIntros (v0) "(-> & Hrw & Hro)". s_glue.
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
    iIntros (v0) "(-> & Hrw & Hro)". s_glue.
    rewrite mbind0_ret.
    iApply (swp_use_cer3 (within_mmio_writable (Physaddr pa) 4)
              _ _ _ _ C HC with "[Hrw Hro] [-]").
    { iApply (swp_hfrun 12 Drw Dro Df rs rs _ _ Hdisj
                (hfrun_within_mmio_w_ram (Drw ∪ Dro) Drw rs pa 4
                   ltac:(lia) HDhtif Hhtif Hram) with "Hcert Hrw Hro"). }
    iIntros (v0) "(-> & Hrw & Hro)". s_glue.
    change (8 * (0 + 1) * 4 - 1) with 31. change (8 * 0 * 4) with 0.
    rewrite subrange_full_32 autocast_id.
    iApply (swp_use_cer4 (write_ram Write_plain (Physaddr pa) 4 v tt)
              _ _ _ _ _ C HC with "[Hrw Hro Hmem] [-]").
    { iApply (swp_hart_ram_write 4 (mwrite_req pa v) _
                (fun r => (⌜r = true⌝ ∗
                           hreg_frame rs Drw ∗ hreg_frame_ro Df rs Dro ∗
                           R)%I)
                (hwrite_req_at_write_ram pa v)
                (addr_is_ram_not_dev pa Hram) with "Hcert [Hrw Hro Hmem]").
      iIntros (σ) "Hσ". iMod ("Hmem" $! σ with "Hσ") as "Hclose".
      iModIntro. iNext. iMod "Hclose" as "[Hσ HR]". iModIntro.
      iFrame "Hσ".
      rewrite hwrite_resume_write_ram. iApply swp_ret. by iFrame. }
    iIntros (v0) "(-> & Hrw & Hro & HR)". s_glue.
    change (0 =? 1 - 1) with true. s_glue.
    rewrite mbind_ret. s_glue.
    rewrite mcer_ret.
    iApply ("Hcont" $! (Values.Ok true)). by iFrame.
  Qed.

  (* [mem_write_value] -> [mem_write_value_meta] (a plain-M spine) ->
     [mem_write_value_priv_meta] (one bind over the checked write and a
     pure callback). *)
  Lemma swp_mem_write_value (Drw Dro : gset register)
      (Df : register -> dfrac) (rs : regstate)
      (pa : SailStdpp.Values.mword 64) (v : SailStdpp.Values.mword 32)
      (pmar0 : list PMA_Region) (pcfg : type_of_register pmpcfg_n)
      (R : iProp Σ) :
    Drw ## Dro ->
    (mstatus : register) ∈ Drw ∪ Dro ->
    (cur_privilege : register) ∈ Drw ∪ Dro ->
    (pma_regions : register) ∈ Drw ∪ Dro ->
    (pmpcfg_n : register) ∈ Drw ∪ Dro ->
    (htif_tohost_base : register) ∈ Drw ∪ Dro ->
    register_lookup cur_privilege rs = Machine ->
    register_lookup pma_regions rs = pmar0 ->
    register_lookup pmpcfg_n rs = pcfg ->
    register_lookup htif_tohost_base rs = None ->
    eq_vec (_get_Mstatus_MPRV (register_lookup mstatus rs))
      (MachineWord.MachineWord.N_to_word 1 1%N) = false ->
    (forall i, pmpLocked (SailStdpp.Values.vec_access_dec pcfg i) = false) ->
    pma_allows_ram pmar0 ->
    addr_is_ram pa ->
    is_aligned_paddr (Physaddr pa) 4 = true ->
    gen_cert -∗
    hreg_frame rs Drw -∗
    hreg_frame_ro Df rs Dro -∗
    (∀ σ, mstate_interp σ ={⊤,∅}=∗
        ▷ (|={∅,⊤}=> mstate_interp
             (MState σ.(sregs)
                (write_bytes σ.(mem) pa 4
                   (Interface.WriteReq.value (mwrite_req pa v)))
                σ.(mdev)) ∗ R)) -∗
    swp (mem_write_value (Physaddr pa) 4 v (Store Data) PBMT_PMA
           false false false)
      (fun r => ⌜r = Values.Ok true⌝ ∗
                hreg_frame rs Drw ∗ hreg_frame_ro Df rs Dro ∗ R).
  Proof.
    intros Hdisj HDmst HDpriv HDpma HDcfg HDhtif Hpriv Hpma Hpcfg Hhtif
      Hmprv Hunlock Hpallow Hram Hpa.
    iIntros "#Hcert Hrw Hro Hmem".
    unfold mem_write_value, mem_write_value_meta.
    iApply (swp_bind_use (Defs.read_reg mstatus) _ _ _
              with "[Hrw Hro] [-]").
    { iApply (swp_read_reg_pinned Drw Dro Df rs _ Hdisj HDmst
                with "Hcert Hrw Hro"). }
    iIntros (v0) "(-> & Hrw & Hro)".
    iApply (swp_bind_use (Defs.read_reg cur_privilege) _ _ _
              with "[Hrw Hro] [-]").
    { iApply (swp_read_reg_pinned Drw Dro Df rs _ Hdisj HDpriv
                with "Hcert Hrw Hro"). }
    iIntros (v0) "(-> & Hrw & Hro)". rewrite Hpriv.
    unfold effectivePrivilege.
    change (Instances.generic_neq (Store Data) (InstructionFetch tt))
      with true.
    s_glue. rewrite Hmprv. s_glue.
    rewrite mbind_ret. s_glue.
    unfold mem_write_value_priv_meta.
    iApply (swp_bind_use _ _
              (fun r => (⌜r = Values.Ok true⌝ ∗
                         hreg_frame rs Drw ∗ hreg_frame_ro Df rs Dro ∗ R)%I) _
              with "[Hrw Hro Hmem] [-]").
    { iApply (swp_checked_mem_write Drw Dro Df rs pa v pmar0 pcfg R Hdisj
                HDpma HDcfg HDhtif Hpma Hpcfg Hhtif Hunlock Hpallow Hram Hpa
                with "Hcert Hrw Hro Hmem"). }
    iIntros (v0) "(-> & Hrw & Hro & HR)". s_glue.
    iApply swp_ret. by iFrame.
  Qed.

  Lemma swp_vmem_write_addr (Drw Dro : gset register)
      (Df : register -> dfrac) (rs : regstate)
      (pa : SailStdpp.Values.mword 64) (v : SailStdpp.Values.mword 32)
      (pmar0 : list PMA_Region) (pcfg : type_of_register pmpcfg_n)
      (R : iProp Σ) :
    Drw ## Dro ->
    (mstatus : register) ∈ Drw ∪ Dro ->
    (cur_privilege : register) ∈ Drw ∪ Dro ->
    (pma_regions : register) ∈ Drw ∪ Dro ->
    (pmpcfg_n : register) ∈ Drw ∪ Dro ->
    (htif_tohost_base : register) ∈ Drw ∪ Dro ->
    register_lookup cur_privilege rs = Machine ->
    register_lookup pma_regions rs = pmar0 ->
    register_lookup pmpcfg_n rs = pcfg ->
    register_lookup htif_tohost_base rs = None ->
    eq_vec (_get_Mstatus_MPRV (register_lookup mstatus rs))
      (MachineWord.MachineWord.N_to_word 1 1%N) = false ->
    (forall i, pmpLocked (SailStdpp.Values.vec_access_dec pcfg i) = false) ->
    pma_allows_ram pmar0 ->
    addr_is_ram pa ->
    is_aligned_vaddr (Virtaddr pa) 4 = true ->
    is_aligned_paddr (Physaddr pa) 4 = true ->
    (* the access does not cross a page.  Stated as the model's OWN test so
       a concrete address discharges it by computation; a general bv proof
       (4-aligned => the low 12 bits cannot carry) would replace it. *)
    split_on_page_boundary (bits_of_virtaddr (Virtaddr pa)) 4
      = returnM (4, 0) ->
    gen_cert -∗
    hreg_frame rs Drw -∗
    hreg_frame_ro Df rs Dro -∗
    (∀ σ, mstate_interp σ ={⊤,∅}=∗
        ▷ (|={∅,⊤}=> mstate_interp
             (MState σ.(sregs)
                (write_bytes σ.(mem) pa 4
                   (Interface.WriteReq.value (mwrite_req pa v)))
                σ.(mdev)) ∗ R)) -∗
    swp (vmem_write_addr (Virtaddr pa) 4 v (Store Data) false false false)
      (fun r => ⌜r = Values.Ok true⌝ ∗
                hreg_frame rs Drw ∗ hreg_frame_ro Df rs Dro ∗ R).
  Proof.
    intros Hdisj HDmst HDpriv HDpma HDcfg HDhtif Hpriv Hpma Hpcfg Hhtif
      Hmprv Hunlock Hpallow Hram Hva Hpa Hsplit.
    iIntros "#Hcert Hrw Hro Hmem".
    rewrite /swp. iIntros (C) "%HC Hcont".
    unfold vmem_write_addr.
    rewrite Hva. s_glue.
    rewrite mbind0_ret.
    rewrite Hsplit /returnM mliftR_ret mbind_ret. s_glue.
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
    change (Instances.generic_neq (Store Data) (InstructionFetch tt))
      with true.
    s_glue. rewrite Hmprv. s_glue.
    rewrite mliftR_ret mbind_ret. s_glue.
    unfold translationMode.
    change (Instances.generic_eq Machine Machine) with true.
    s_glue.
    unfold Defs.and_boolM.
    rewrite /returnM mliftR_ret mbind_ret. s_glue.
    change (Instances.generic_neq Bare Bare) with false. s_glue.
    rewrite mbind_ret. s_glue.
    change (sys_misaligned_order_decreasing && false) with false. s_glue.
    rewrite mbind_ret. s_glue.
    iApply (swp_use_cer (translateAddr (Virtaddr pa) (Store Data)) _ _ C HC
              with "[Hrw Hro] [-]").
    { iApply (swp_hfrun 8 Drw Dro Df rs rs _ _ Hdisj
                (hfrun_translateAddr_M_store (Drw ∪ Dro) Drw rs pa
                   HDmst HDpriv Hpriv Hmprv) with "Hcert Hrw Hro"). }
    iIntros (v0) "(-> & Hrw & Hro)". s_glue.
    change (eqb false (is_store_conditional (Store Data))) with true.
    cbn beta iota zeta delta [Defs.assert_exp].
    rewrite /returnM mliftR_ret mbind0_ret. s_glue.
    iApply (swp_use_cer2
              (mem_write_ea (Physaddr pa) 4 (Store Data) PBMT_PMA
                 false false false) _ _ _ C HC with "[Hrw Hro] [-]").
    { iApply (swp_mem_write_ea Drw Dro Df rs pa pmar0 pcfg Hdisj HDmst
                HDpriv HDpma HDcfg Hpriv Hpma Hpcfg Hmprv Hunlock Hpallow
                Hram Hpa with "Hcert Hrw Hro"). }
    iIntros (v0) "(-> & Hrw & Hro)". s_glue.
    change (8 * 4 - 1) with 31. rewrite subrange_full_32 autocast_id.
    iApply (swp_use_cer2
              (mem_write_value (Physaddr pa) 4 v (Store Data) PBMT_PMA
                 false false false) _ _ _ C HC with "[Hrw Hro Hmem] [-]").
    { iApply (swp_mem_write_value Drw Dro Df rs pa v pmar0 pcfg R Hdisj
                HDmst HDpriv HDpma HDcfg HDhtif Hpriv Hpma Hpcfg Hhtif Hmprv
                Hunlock Hpallow Hram Hpa with "Hcert Hrw Hro Hmem"). }
    iIntros (v0) "(-> & Hrw & Hro & HR)". s_glue.
    rewrite mbind_ret. s_glue.
    change (not sys_misaligned_order_decreasing && false) with false. s_glue.
    rewrite mbind_ret. s_glue.
    rewrite mcer_ret.
    iApply ("Hcont" $! (Values.Ok true)). by iFrame.
  Qed.

  (* [vmem_write] and [execute_STORE]: the two outer wrappers.  Each takes
     its GPR-dependent computation as an [hfrun] equation -- the base
     address and the stored data are the leaf's business, and stating them
     this way keeps every register value out of this file while leaving the
     walk complete. *)
  (* ------------------------------------------------------------------ *)
  (* [vmem_write], with the ADDRESS COMPUTATION as an obligation.          *)
  (*                                                                      *)
  (* [get_transformed_data_addr base offset ..] is [rX_bits base >>= ..],   *)
  (* and [rX_bits] at a SYMBOLIC index is the one node no walker can take   *)
  (* -- so the [hfrun] premise below only ever discharges at a CONCRETE     *)
  (* register (which is what the pilot has, and why the corollary keeps     *)
  (* that form).  A generic store leaf quantifies its operands, so it hands *)
  (* in a [swp] for that stretch instead and peels the read itself with     *)
  (* [HartMFrame.swp_rX_file].                                             *)
  (*                                                                      *)
  (* [Q] is an abstract rider so the leaf can carry [gpr_file] through the  *)
  (* obligation and get it back; the lemma never looks inside it.          *)
  (* ------------------------------------------------------------------ *)
  Lemma swp_vmem_write_gen (Drw Dro : gset register) (Df : register -> dfrac)
      (rs : regstate) (base : regidx) (offset : SailStdpp.Values.mword 64)
      (pa : SailStdpp.Values.mword 64) (v : SailStdpp.Values.mword 32)
      (pmar0 : list PMA_Region) (pcfg : type_of_register pmpcfg_n)
      (R Q : iProp Σ) :
    Drw ## Dro ->
    (mstatus : register) ∈ Drw ∪ Dro ->
    (cur_privilege : register) ∈ Drw ∪ Dro ->
    (pma_regions : register) ∈ Drw ∪ Dro ->
    (pmpcfg_n : register) ∈ Drw ∪ Dro ->
    (htif_tohost_base : register) ∈ Drw ∪ Dro ->
    register_lookup cur_privilege rs = Machine ->
    register_lookup pma_regions rs = pmar0 ->
    register_lookup pmpcfg_n rs = pcfg ->
    register_lookup htif_tohost_base rs = None ->
    eq_vec (_get_Mstatus_MPRV (register_lookup mstatus rs))
      (MachineWord.MachineWord.N_to_word 1 1%N) = false ->
    (forall i, pmpLocked (SailStdpp.Values.vec_access_dec pcfg i) = false) ->
    pma_allows_ram pmar0 ->
    addr_is_ram pa ->
    is_aligned_vaddr (Virtaddr pa) 4 = true ->
    is_aligned_paddr (Physaddr pa) 4 = true ->
    split_on_page_boundary (bits_of_virtaddr (Virtaddr pa)) 4
      = returnM (4, 0) ->
    gen_cert -∗
    hreg_frame rs Drw -∗
    hreg_frame_ro Df rs Dro -∗
    Q -∗
    (Q -∗ hreg_frame rs Drw -∗ hreg_frame_ro Df rs Dro -∗
       swp (get_transformed_data_addr base offset (Store Data) 4)
         (fun r => ⌜r = Ext_DataAddr_OK (Virtaddr pa)⌝ ∗ Q ∗
                   hreg_frame rs Drw ∗ hreg_frame_ro Df rs Dro)) -∗
    (∀ σ, mstate_interp σ ={⊤,∅}=∗
        ▷ (|={∅,⊤}=> mstate_interp
             (MState σ.(sregs)
                (write_bytes σ.(mem) pa 4
                   (Interface.WriteReq.value (mwrite_req pa v)))
                σ.(mdev)) ∗ R)) -∗
    swp (vmem_write base offset 4 v (Store Data) false false false)
      (fun r => ⌜r = Values.Ok true⌝ ∗ Q ∗
                hreg_frame rs Drw ∗ hreg_frame_ro Df rs Dro ∗ R).
  Proof.
    intros Hdisj HDmst HDpriv HDpma HDcfg HDhtif Hpriv Hpma Hpcfg Hhtif
      Hmprv Hunlock Hpallow Hram Hva Hpa Hsplit.
    iIntros "#Hcert Hrw Hro HQ Hgta Hmem".
    rewrite /swp. iIntros (C) "%HC Hcont".
    unfold vmem_write.
    iApply (swp_use_cer
              (get_transformed_data_addr base offset (Store Data) 4)
              _ _ C HC with "[HQ Hgta Hrw Hro] [-]").
    { iApply ("Hgta" with "HQ Hrw Hro"). }
    iIntros (v0) "(-> & HQ & Hrw & Hro)". s_glue.
    rewrite mbind_ret. s_glue.
    iApply (swp_use_cer0
              (vmem_write_addr (Virtaddr pa) 4 v (Store Data) false false
                 false) _ C HC with "[Hrw Hro Hmem] [-]").
    { iApply (swp_vmem_write_addr Drw Dro Df rs pa v pmar0 pcfg R Hdisj
                HDmst HDpriv HDpma HDcfg HDhtif Hpriv Hpma Hpcfg Hhtif Hmprv
                Hunlock Hpallow Hram Hva Hpa Hsplit
                with "Hcert Hrw Hro Hmem"). }
    iIntros (v0) "(-> & Hrw & Hro & HR)".
    iApply ("Hcont" $! (Values.Ok true)). by iFrame.
  Qed.

  (* the ORIGINAL form, for callers at concrete register indices (the pilot):
     the address stretch is a computed walk, so [swp_hfrun] discharges the
     obligation and [Q] is [emp]. *)
  Lemma swp_vmem_write (Drw Dro : gset register) (Df : register -> dfrac)
      (rs : regstate) (base : regidx) (offset : SailStdpp.Values.mword 64)
      (pa : SailStdpp.Values.mword 64) (v : SailStdpp.Values.mword 32)
      (pmar0 : list PMA_Region) (pcfg : type_of_register pmpcfg_n)
      (R : iProp Σ) :
    Drw ## Dro ->
    (mstatus : register) ∈ Drw ∪ Dro ->
    (cur_privilege : register) ∈ Drw ∪ Dro ->
    (pma_regions : register) ∈ Drw ∪ Dro ->
    (pmpcfg_n : register) ∈ Drw ∪ Dro ->
    (htif_tohost_base : register) ∈ Drw ∪ Dro ->
    register_lookup cur_privilege rs = Machine ->
    register_lookup pma_regions rs = pmar0 ->
    register_lookup pmpcfg_n rs = pcfg ->
    register_lookup htif_tohost_base rs = None ->
    eq_vec (_get_Mstatus_MPRV (register_lookup mstatus rs))
      (MachineWord.MachineWord.N_to_word 1 1%N) = false ->
    (forall i, pmpLocked (SailStdpp.Values.vec_access_dec pcfg i) = false) ->
    pma_allows_ram pmar0 ->
    addr_is_ram pa ->
    is_aligned_vaddr (Virtaddr pa) 4 = true ->
    is_aligned_paddr (Physaddr pa) 4 = true ->
    split_on_page_boundary (bits_of_virtaddr (Virtaddr pa)) 4
      = returnM (4, 0) ->
    hfrun 8 (Drw ∪ Dro) Drw rs
      (get_transformed_data_addr base offset (Store Data) 4)
      = Some (Ext_DataAddr_OK (Virtaddr pa), rs) ->
    gen_cert -∗
    hreg_frame rs Drw -∗
    hreg_frame_ro Df rs Dro -∗
    (∀ σ, mstate_interp σ ={⊤,∅}=∗
        ▷ (|={∅,⊤}=> mstate_interp
             (MState σ.(sregs)
                (write_bytes σ.(mem) pa 4
                   (Interface.WriteReq.value (mwrite_req pa v)))
                σ.(mdev)) ∗ R)) -∗
    swp (vmem_write base offset 4 v (Store Data) false false false)
      (fun r => ⌜r = Values.Ok true⌝ ∗
                hreg_frame rs Drw ∗ hreg_frame_ro Df rs Dro ∗ R).
  Proof.
    intros Hdisj HDmst HDpriv HDpma HDcfg HDhtif Hpriv Hpma Hpcfg Hhtif
      Hmprv Hunlock Hpallow Hram Hva Hpa Hsplit Hgta.
    iIntros "#Hcert Hrw Hro Hmem".
    iAssert (emp -∗ hreg_frame rs Drw -∗ hreg_frame_ro Df rs Dro -∗
             swp (get_transformed_data_addr base offset (Store Data) 4)
               (fun r => ⌜r = Ext_DataAddr_OK (Virtaddr pa)⌝ ∗ emp ∗
                         hreg_frame rs Drw ∗ hreg_frame_ro Df rs Dro))%I
      as "Hgtaobl".
    { iIntros "_ Hrw Hro".
      iApply (swp_mono with "[] [-]");
        [| iApply (swp_hfrun 8 Drw Dro Df rs rs _ _ Hdisj Hgta
                     with "Hcert Hrw Hro") ].
      iIntros (r) "(-> & Hrw & Hro)". by iFrame. }
    iApply (swp_mono with "[] [-]");
      [| iApply (swp_vmem_write_gen Drw Dro Df rs base offset pa v pmar0 pcfg
                   R emp%I Hdisj HDmst HDpriv HDpma HDcfg HDhtif Hpriv Hpma
                   Hpcfg Hhtif Hmprv Hunlock Hpallow Hram Hva Hpa Hsplit
                   with "Hcert Hrw Hro [//] Hgtaobl Hmem") ].
    iIntros (r) "(-> & _ & Hrw & Hro & HR)". by iFrame.
  Qed.

  Lemma swp_execute_STORE (Drw Dro : gset register) (Df : register -> dfrac)
      (rs : regstate) (imm : SailStdpp.Values.mword 12)
      (rs2 rs1 : regidx) (d : SailStdpp.Values.mword 64)
      (pa : SailStdpp.Values.mword 64)
      (pmar0 : list PMA_Region) (pcfg : type_of_register pmpcfg_n)
      (R : iProp Σ) :
    Drw ## Dro ->
    (mstatus : register) ∈ Drw ∪ Dro ->
    (cur_privilege : register) ∈ Drw ∪ Dro ->
    (pma_regions : register) ∈ Drw ∪ Dro ->
    (pmpcfg_n : register) ∈ Drw ∪ Dro ->
    (htif_tohost_base : register) ∈ Drw ∪ Dro ->
    register_lookup cur_privilege rs = Machine ->
    register_lookup pma_regions rs = pmar0 ->
    register_lookup pmpcfg_n rs = pcfg ->
    register_lookup htif_tohost_base rs = None ->
    eq_vec (_get_Mstatus_MPRV (register_lookup mstatus rs))
      (MachineWord.MachineWord.N_to_word 1 1%N) = false ->
    (forall i, pmpLocked (SailStdpp.Values.vec_access_dec pcfg i) = false) ->
    pma_allows_ram pmar0 ->
    addr_is_ram pa ->
    is_aligned_vaddr (Virtaddr pa) 4 = true ->
    is_aligned_paddr (Physaddr pa) 4 = true ->
    split_on_page_boundary (bits_of_virtaddr (Virtaddr pa)) 4
      = returnM (4, 0) ->
    hfrun 4 (Drw ∪ Dro) Drw rs (rX_bits rs2) = Some (d, rs) ->
    hfrun 8 (Drw ∪ Dro) Drw rs
      (get_transformed_data_addr rs1 (sign_extend' 64 imm) (Store Data) 4)
      = Some (Ext_DataAddr_OK (Virtaddr pa), rs) ->
    gen_cert -∗
    hreg_frame rs Drw -∗
    hreg_frame_ro Df rs Dro -∗
    (∀ σ, mstate_interp σ ={⊤,∅}=∗
        ▷ (|={∅,⊤}=> mstate_interp
             (MState σ.(sregs)
                (write_bytes σ.(mem) pa 4
                   (Interface.WriteReq.value
                      (mwrite_req pa
                         (TypeCasts.autocast (subrange_vec_dec d 31 0)))))
                σ.(mdev)) ∗ R)) -∗
    swp (execute_STORE imm rs2 rs1 4)
      (fun e => ⌜e = RETIRE_SUCCESS⌝ ∗
                hreg_frame rs Drw ∗ hreg_frame_ro Df rs Dro ∗ R).
  Proof.
    intros Hdisj HDmst HDpriv HDpma HDcfg HDhtif Hpriv Hpma Hpcfg Hhtif
      Hmprv Hunlock Hpallow Hram Hva Hpa Hsplit Hrx Hgta.
    iIntros "#Hcert Hrw Hro Hmem".
    unfold execute_STORE.
    cbn beta iota zeta delta [Defs.assert_exp'].
    rewrite /returnM mbind_ret. s_glue.
    iApply (swp_bind_use (rX_bits rs2) _ _ _ with "[Hrw Hro] [-]").
    { iApply (swp_hfrun 4 Drw Dro Df rs rs _ _ Hdisj Hrx
                with "Hcert Hrw Hro"). }
    iIntros (v0) "(-> & Hrw & Hro)". s_glue.
    change (4 * 8 - 1) with 31.
    iApply (swp_bind_use _ _
              (fun r => (⌜r = Values.Ok true⌝ ∗
                         hreg_frame rs Drw ∗ hreg_frame_ro Df rs Dro ∗ R)%I) _
              with "[Hrw Hro Hmem] [-]").
    { iApply (swp_vmem_write Drw Dro Df rs rs1 (sign_extend' 64 imm) pa _
                pmar0 pcfg R Hdisj HDmst HDpriv HDpma HDcfg HDhtif Hpriv
                Hpma Hpcfg Hhtif Hmprv Hunlock Hpallow Hram Hva Hpa Hsplit
                Hgta with "Hcert Hrw Hro Hmem"). }
    iIntros (v0) "(-> & Hrw & Hro & HR)". s_glue.
    iApply swp_ret. by iFrame.
  Qed.

End store.
