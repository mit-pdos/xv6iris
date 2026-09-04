(* UmodeFetchX.v -- THE VERIFIED TIER'S FETCH SHELLS, WITH A PAYER THREADED
   (claude-notes/projects/icache.md, "The verified tier: text OUTSIDE the
   walker").

   The fixed-word U-mode fetch shells of SmodeCorePt PART D/E
   ([swp_checked_mem_read_ifetch{4,2}_U], [spt_fetch_bytes_U{,2}_P],
   [spt_fetch_U_{,rvc2_,base2_}P]) hand the READ node a callback that
   returns nothing but the register frames: their payer is kernel text,
   persistent, so nothing has to come back.  A verified process pays its
   fetch with its OWN stamped text bytes ([HartMemRunX.bytes_own_p]), which
   are exclusive and must return to the tier after the read.  This file is
   the same shells with a resource [R] threaded through the read node: the
   node's interp wand receives [R], proves the obligation from it, and
   hands it back; the shell's read callback receives the walk's residue
   [Rf rsf] and returns it.  Every proof is the original's, line for line,
   with [R] carried along -- the S-mode originals stay untouched (their
   cone is most of the tree).

   Layout: §1 the read node with [R]; §2 the M-privilege read shell with
   [R]; §3 [fetch_bytes] at User with the residue through the read; §4 the
   three [fetch] geometries.                                               *)
From Stdlib Require Import ZArith Bool Lia.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
From iris.base_logic.lib Require Import gen_heap ghost_map ghost_var.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvModelBytes TsoMemPa.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvFetchExec.
Require Import SmodeCore.
Require Import HartSwp HartLift HartSpan HartSpanChar.
Require Import HartEvents HartMFetch PtTreeAdue.
Require Import SmodeCorePt RiscvExtras.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import TsoCtx.
Local Open Scope Z_scope.
Import Defs.
(* [HartMFetch]'s local spelling of the zero bit, for the shells' premises *)
Local Notation zerobit :=
  (MachineWord.MachineWord.N_to_word (MachineWord.MachineWord.Z_idx 1)
     (BinaryString.Raw.to_N "0" 0%N)).

Section UmodeFetchX.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}.

  (* =================================================================== *)
  (* §1 THE READ NODE, WITH A PAYER THREADED.                            *)
  (* [SmodeCorePt.swp_checked_mem_read_ifetch4_U] with [R].              *)
  (* =================================================================== *)
  Lemma swp_checked_mem_read_ifetch4_UR (Drw Dro : gset register)
      (Df : register -> dfrac) (rs : regstate)
      (pa : SailStdpp.Values.mword 64)
      (pmar0 : list PMA_Region) (pcfg : type_of_register pmpcfg_n)
      (paddr : type_of_register pmpaddr_n) (bytes : bv 32) (R : iProp Σ) :
    Drw ## Dro ->
    (pma_regions : register) ∈ Drw ∪ Dro ->
    (pmpcfg_n : register) ∈ Drw ∪ Dro ->
    (pmpaddr_n : register) ∈ Drw ∪ Dro ->
    (htif_tohost_base : register) ∈ Drw ∪ Dro ->
    register_lookup htif_tohost_base rs = None ->
    register_lookup pma_regions rs = pmar0 ->
    register_lookup pmpcfg_n rs = pcfg ->
    register_lookup pmpaddr_n rs = paddr ->
    pmpAddrMatchType_encdec_backwards
      (_get_Pmpcfg_ent_A (vec_access_dec pcfg 0)) = TOR ->
    zopz0zKzJ_u (zeros' 64) (vec_access_dec paddr 0) = false ->
    eq_vec (_get_Pmpcfg_ent_X (vec_access_dec pcfg 0)) ('b"1") = true ->
    (ram_base + ram_size <= uint (vec_access_dec paddr 0) * 4)%Z ->
    pma_allows_ram pmar0 ->
    addr_is_ram pa ->
    addr_is_ram (pa_add pa 3) ->
    is_aligned_paddr (Physaddr pa) 4 = true ->
    gen_cert -∗
    hreg_frame rs Drw -∗
    hreg_frame_ro Df rs Dro -∗
    R -∗
    (∀ σ img log tv itv V,
        ⌜V (hart_agent cpu_id) = tv⌝ -∗
        ⌜(itv <= length log)%nat⌝ -∗
        mstate_interp σ -∗
        hart_iview_auth cpu_id itv -∗
        tso_interp_of riscv_eraGS img σ.(mem) log V -∗
        R ={⊤,∅}=∗
        ⌜fobl_ifetch img log itv pa 4 bytes⌝ ∗
        ▷ (|={∅,⊤}=> mstate_interp σ ∗ hart_iview_auth cpu_id itv ∗
             tso_interp_of riscv_eraGS img σ.(mem) log V ∗ R)) -∗
    swp (checked_mem_read (InstructionFetch tt) PBMT_PMA User
           (Physaddr pa) 4 false false false false)
      (fun r => ⌜r = Values.Ok (bytes, tt)⌝ ∗
                hreg_frame rs Drw ∗ hreg_frame_ro Df rs Dro ∗ R).
  Proof.
    intros Hdisj HD HDcfg HDaddr HDhtif Hhtif Hpma Hpcfg Hpaddr
      HA Hord HX Hcov Hpallow Hram Hram3 Hpa.
    pose proof (ram_fetch_pmp pa (vec_access_dec paddr 0) 4 3
                  ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity)
                  ltac:(reflexivity) Hram Hram3 Hcov) as Hrange.
    iIntros "#Hcert Hrw Hro HR Hmem".
    rewrite /swp. iIntros (C) "%HC Hcont".
    unfold checked_mem_read.
    iApply (swp_use_cer
              (check_pma_with_pmp_priority (InstructionFetch tt) PBMT_PMA
                 User (Physaddr pa) 4 false) _ _ C HC
              with "[Hrw Hro] [-]").
    { iApply (swp_hfrun 6 Drw Dro Df rs rs _ _ Hdisj
                (hfrun_check_pma_ifetch_U (Drw ∪ Dro) Drw rs pa pmar0 4
                   HD Hpma Hpallow (pma_access_ram pa 4 3 Hram Hram3
                      (pma_width_ok 4 eq_refl eq_refl) eq_refl eq_refl) Hpa)
                with "Hcert Hrw Hro"). }
    iIntros (v) "(-> & Hrw & Hro)". cbn beta iota.
    rewrite mbind_ret. cbn beta iota zeta.
    cbn [Phys_Mem_Access_Info_granule_size_exp Phys_Mem_Access_Info_splittable].
    cbn beta iota zeta delta [split_misaligned misaligned_order
      sys_misaligned_order_decreasing read_kind_of_flags].
    change (Instances.generic_eq CannotSplit CannotSplit) with true.
    cbn beta iota.
    rewrite /returnM mliftR_ret mbind_ret. cbn beta iota zeta.
    rewrite mbind_returnR. cbn beta iota zeta.
    cbn beta iota zeta delta [Defs.untilMT Defs.untilMT' Defs.Zwf_guarded
      Z_ge_dec Z_ge_lt_dec Zcompare_rec Z.compare].
    cbn beta iota zeta delta [Defs.assert_exp' bits_of_physaddr].
    rewrite mliftR_ret mbind_ret. cbn beta iota.
    change (0 * 4) with 0. rewrite avi0.
    iApply (swp_use_cer3
              (pmpCheck (Physaddr pa) 4 (InstructionFetch tt) User)
              _ _ _ _ C HC with "[Hrw Hro] [-]").
    { iApply (swp_pmpCheck_U (InstructionFetch tt) Drw Dro Df rs pcfg paddr
                pa 4 Hdisj HDcfg HDaddr Hpcfg Hpaddr HA Hord Hrange
                ltac:(unfold pmpCheckRWX; cbn match; rewrite HX; reflexivity)
                with "Hcert Hrw Hro"). }
    iIntros (v) "(-> & Hrw & Hro)". cbn beta iota.
    rewrite mbind0_ret.
    iApply (swp_use_cer3 (within_mmio_readable (Physaddr pa) 4)
              _ _ _ _ C HC with "[Hrw Hro] [-]").
    { iApply (swp_hfrun 12 Drw Dro Df rs rs _ _ Hdisj
                (hfrun_within_mmio_ram (Drw ∪ Dro) Drw rs pa 4
                   ltac:(lia) HDhtif Hhtif Hram)
                with "Hcert Hrw Hro"). }
    iIntros (v) "(-> & Hrw & Hro)". cbn beta iota.
    iApply (swp_use_cer4 (read_ram Read_ifetch (Physaddr pa) 4 false)
              _ _ _ _ _ C HC with "[Hrw Hro HR Hmem] [-]").
    { iApply (swp_hart_ram_read_ifetch 4 (mread_req_ifetch pa) _
                (fun r => (⌜r = (bytes, default_meta)⌝ ∗
                           hreg_frame rs Drw ∗ hreg_frame_ro Df rs Dro ∗ R)%I)
                (hread_req_at_read_ram_ifetch pa)
                (addr_is_ram_not_dev pa Hram) ltac:(reflexivity)
                with "Hcert [Hrw Hro HR Hmem]").
      iIntros (σ img log tv itv V) "%Htv %Hitv Hσ Hiv Htso".
      iMod ("Hmem" $! σ img log tv itv V with "[//] [//] Hσ Hiv Htso HR")
        as "[%Hrd Hclose]".
      iModIntro. iExists bytes. iSplitR; [done|]. iNext.
      iMod "Hclose" as "(Hσ & Hiv & Htso & HR)". iModIntro. iFrame "Hσ Hiv Htso".
      rewrite hread_resume_read_ram_ifetch. iApply swp_ret. by iFrame. }
    iIntros (v) "(-> & Hrw & Hro & HR)". cbn beta iota zeta.
    rewrite mbind_ret. cbn beta.
    change (0 =? 1 - 1) with true. cbn beta iota zeta.
    rewrite !autocast_id usvd_zeros_full_32 mcer_ret.
    iApply ("Hcont" $! (Values.Ok (bytes, tt))). by iFrame.
  Qed.

  (* [SmodeCorePt.swp_checked_mem_read_ifetch2_U] with [R] *)
  Lemma swp_checked_mem_read_ifetch2_UR (Drw Dro : gset register)
      (Df : register -> dfrac) (rs : regstate)
      (pa : SailStdpp.Values.mword 64)
      (pmar0 : list PMA_Region) (pcfg : type_of_register pmpcfg_n)
      (paddr : type_of_register pmpaddr_n) (bytes : bv 16) (R : iProp Σ) :
    Drw ## Dro ->
    (pma_regions : register) ∈ Drw ∪ Dro ->
    (pmpcfg_n : register) ∈ Drw ∪ Dro ->
    (pmpaddr_n : register) ∈ Drw ∪ Dro ->
    (htif_tohost_base : register) ∈ Drw ∪ Dro ->
    register_lookup htif_tohost_base rs = None ->
    register_lookup pma_regions rs = pmar0 ->
    register_lookup pmpcfg_n rs = pcfg ->
    register_lookup pmpaddr_n rs = paddr ->
    pmpAddrMatchType_encdec_backwards
      (_get_Pmpcfg_ent_A (vec_access_dec pcfg 0)) = TOR ->
    zopz0zKzJ_u (zeros' 64) (vec_access_dec paddr 0) = false ->
    eq_vec (_get_Pmpcfg_ent_X (vec_access_dec pcfg 0)) ('b"1") = true ->
    (ram_base + ram_size <= uint (vec_access_dec paddr 0) * 4)%Z ->
    pma_allows_ram pmar0 ->
    addr_is_ram pa ->
    addr_is_ram (pa_add pa 1) ->
    is_aligned_paddr (Physaddr pa) 2 = true ->
    gen_cert -∗
    hreg_frame rs Drw -∗
    hreg_frame_ro Df rs Dro -∗
    R -∗
    (∀ σ img log tv itv V,
        ⌜V (hart_agent cpu_id) = tv⌝ -∗
        ⌜(itv <= length log)%nat⌝ -∗
        mstate_interp σ -∗
        hart_iview_auth cpu_id itv -∗
        tso_interp_of riscv_eraGS img σ.(mem) log V -∗
        R ={⊤,∅}=∗
        ⌜fobl_ifetch img log itv pa 2 bytes⌝ ∗
        ▷ (|={∅,⊤}=> mstate_interp σ ∗ hart_iview_auth cpu_id itv ∗
             tso_interp_of riscv_eraGS img σ.(mem) log V ∗ R)) -∗
    swp (checked_mem_read (InstructionFetch tt) PBMT_PMA User
           (Physaddr pa) 2 false false false false)
      (fun r => ⌜r = Values.Ok (bytes, tt)⌝ ∗
                hreg_frame rs Drw ∗ hreg_frame_ro Df rs Dro ∗ R).
  Proof.
    intros Hdisj HD HDcfg HDaddr HDhtif Hhtif Hpma Hpcfg Hpaddr
      HA Hord HX Hcov Hpallow Hram Hram1 Hpa.
    pose proof (ram_fetch_pmp pa (vec_access_dec paddr 0) 2 1
                  ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity)
                  ltac:(reflexivity) Hram Hram1 Hcov) as Hrange.
    iIntros "#Hcert Hrw Hro HR Hmem".
    rewrite /swp. iIntros (C) "%HC Hcont".
    unfold checked_mem_read.
    iApply (swp_use_cer
              (check_pma_with_pmp_priority (InstructionFetch tt) PBMT_PMA
                 User (Physaddr pa) 2 false) _ _ C HC
              with "[Hrw Hro] [-]").
    { iApply (swp_hfrun 6 Drw Dro Df rs rs _ _ Hdisj
                (hfrun_check_pma_ifetch_U (Drw ∪ Dro) Drw rs pa pmar0 2
                   HD Hpma Hpallow (pma_access_ram pa 2 1 Hram Hram1
                      (pma_width_ok 2 eq_refl eq_refl) eq_refl eq_refl) Hpa)
                with "Hcert Hrw Hro"). }
    iIntros (v) "(-> & Hrw & Hro)". cbn beta iota.
    rewrite mbind_ret. cbn beta iota zeta.
    cbn [Phys_Mem_Access_Info_granule_size_exp Phys_Mem_Access_Info_splittable].
    cbn beta iota zeta delta [split_misaligned misaligned_order
      sys_misaligned_order_decreasing read_kind_of_flags].
    change (Instances.generic_eq CannotSplit CannotSplit) with true.
    cbn beta iota.
    rewrite /returnM mliftR_ret mbind_ret. cbn beta iota zeta.
    rewrite mbind_returnR. cbn beta iota zeta.
    cbn beta iota zeta delta [Defs.untilMT Defs.untilMT' Defs.Zwf_guarded
      Z_ge_dec Z_ge_lt_dec Zcompare_rec Z.compare].
    cbn beta iota zeta delta [Defs.assert_exp' bits_of_physaddr].
    rewrite mliftR_ret mbind_ret. cbn beta iota.
    change (0 * 2) with 0. rewrite avi0.
    iApply (swp_use_cer3
              (pmpCheck (Physaddr pa) 2 (InstructionFetch tt) User)
              _ _ _ _ C HC with "[Hrw Hro] [-]").
    { iApply (swp_pmpCheck_U (InstructionFetch tt) Drw Dro Df rs pcfg paddr
                pa 2 Hdisj HDcfg HDaddr Hpcfg Hpaddr HA Hord Hrange
                ltac:(unfold pmpCheckRWX; cbn match; rewrite HX; reflexivity)
                with "Hcert Hrw Hro"). }
    iIntros (v) "(-> & Hrw & Hro)". cbn beta iota.
    rewrite mbind0_ret.
    iApply (swp_use_cer3 (within_mmio_readable (Physaddr pa) 2)
              _ _ _ _ C HC with "[Hrw Hro] [-]").
    { iApply (swp_hfrun 12 Drw Dro Df rs rs _ _ Hdisj
                (hfrun_within_mmio_ram (Drw ∪ Dro) Drw rs pa 2
                   ltac:(lia) HDhtif Hhtif Hram)
                with "Hcert Hrw Hro"). }
    iIntros (v) "(-> & Hrw & Hro)". cbn beta iota.
    iApply (swp_use_cer4 (read_ram Read_ifetch (Physaddr pa) 2 false)
              _ _ _ _ _ C HC with "[Hrw Hro HR Hmem] [-]").
    { iApply (swp_hart_ram_read_ifetch 2 (mread_req2_ifetch pa) _
                (fun r => (⌜r = (bytes, default_meta)⌝ ∗
                           hreg_frame rs Drw ∗ hreg_frame_ro Df rs Dro ∗ R)%I)
                (hread_req_at_read_ram2_ifetch pa)
                (addr_is_ram_not_dev pa Hram) ltac:(reflexivity)
                with "Hcert [Hrw Hro HR Hmem]").
      iIntros (σ img log tv itv V) "%Htv %Hitv Hσ Hiv Htso".
      iMod ("Hmem" $! σ img log tv itv V with "[//] [//] Hσ Hiv Htso HR")
        as "[%Hrd Hclose]".
      iModIntro. iExists bytes. iSplitR; [done|]. iNext.
      iMod "Hclose" as "(Hσ & Hiv & Htso & HR)". iModIntro. iFrame "Hσ Hiv Htso".
      rewrite hread_resume_read_ram2_ifetch. iApply swp_ret. by iFrame. }
    iIntros (v) "(-> & Hrw & Hro & HR)". cbn beta iota zeta.
    rewrite mbind_ret. cbn beta.
    change (0 =? 1 - 1) with true. cbn beta iota zeta.
    rewrite !autocast_id usvd_zeros_full_16 mcer_ret.
    iApply ("Hcont" $! (Values.Ok (bytes, tt))). by iFrame.
  Qed.

  (* =================================================================== *)
  (* §2 THE M-PRIVILEGE READ SHELL, WITH [R].                            *)
  (* [HartMFetch.swp_mem_read_M] / [_M2] with [R].                       *)
  (* =================================================================== *)
  Lemma swp_mem_read_MR (Drw Dro : gset register) (Df : register -> dfrac)
      (rs : regstate) (pa : physaddr) (w : SailStdpp.Values.mword 32)
      (pv : Privilege) (R : iProp Σ) :
    Drw ## Dro ->
    (mstatus : register) ∈ Drw ∪ Dro ->
    (cur_privilege : register) ∈ Drw ∪ Dro ->
    register_lookup cur_privilege rs = pv ->
    gen_cert -∗
    hreg_frame rs Drw -∗
    hreg_frame_ro Df rs Dro -∗
    (hreg_frame rs Drw -∗ hreg_frame_ro Df rs Dro -∗
       swp (checked_mem_read (InstructionFetch tt) PBMT_PMA pv pa 4
              false false false false)
         (fun r => ⌜r = Values.Ok (w, tt)⌝ ∗
                   hreg_frame rs Drw ∗ hreg_frame_ro Df rs Dro ∗ R)) -∗
    swp (mem_read (InstructionFetch tt) PBMT_PMA pa 4 false false false)
      (fun r => ⌜r = Values.Ok w⌝ ∗
                hreg_frame rs Drw ∗ hreg_frame_ro Df rs Dro ∗ R).
  Proof.
    intros Hdisj HDmst HDpriv Hpriv.
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
    change (Instances.generic_neq (InstructionFetch tt) (InstructionFetch tt))
      with false.
    cbn beta iota zeta delta [Defs.returnm returnM].
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

  Lemma swp_mem_read_M2R (Drw Dro : gset register) (Df : register -> dfrac)
      (rs : regstate) (pa : physaddr) (w : SailStdpp.Values.mword 16)
      (pv : Privilege) (R : iProp Σ) :
    Drw ## Dro ->
    (mstatus : register) ∈ Drw ∪ Dro ->
    (cur_privilege : register) ∈ Drw ∪ Dro ->
    register_lookup cur_privilege rs = pv ->
    gen_cert -∗
    hreg_frame rs Drw -∗
    hreg_frame_ro Df rs Dro -∗
    (hreg_frame rs Drw -∗ hreg_frame_ro Df rs Dro -∗
       swp (checked_mem_read (InstructionFetch tt) PBMT_PMA pv pa 2
              false false false false)
         (fun r => ⌜r = Values.Ok (w, tt)⌝ ∗
                   hreg_frame rs Drw ∗ hreg_frame_ro Df rs Dro ∗ R)) -∗
    swp (mem_read (InstructionFetch tt) PBMT_PMA pa 2 false false false)
      (fun r => ⌜r = Values.Ok w⌝ ∗
                hreg_frame rs Drw ∗ hreg_frame_ro Df rs Dro ∗ R).
  Proof.
    intros Hdisj HDmst HDpriv Hpriv.
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
    change (Instances.generic_neq (InstructionFetch tt) (InstructionFetch tt))
      with false.
    cbn beta iota zeta delta [Defs.returnm returnM].
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

  (* =================================================================== *)
  (* §3 [fetch_bytes] AT USER, THE WALK'S RESIDUE THROUGH THE READ.       *)
  (* [SmodeCorePt.spt_fetch_bytes_U_P] / [_U2_P]: the read callback       *)
  (* RECEIVES [Rf rsf] and gives it back.                                 *)
  (* =================================================================== *)
  Lemma uv_fetch_bytes4_P (Drw Dro : gset register) (Df : register -> dfrac)
      (rs : regstate) (Qf : regstate -> Prop) (Rf : regstate -> iProp Σ)
      (pc pa : mword 64) (w : mword 32) :
    Drw ## Dro ->
    (mstatus : register) ∈ Drw ∪ Dro ->
    (cur_privilege : register) ∈ Drw ∪ Dro ->
    (forall rsf, Qf rsf -> register_lookup cur_privilege rsf = User) ->
    gen_cert -∗
    hreg_frame rs Drw -∗
    hreg_frame_ro Df rs Dro -∗
    (hreg_frame rs Drw -∗ hreg_frame_ro Df rs Dro -∗
       swp (translateAddr (Virtaddr pc) (InstructionFetch tt))
         (fun r => ⌜r = Values.Ok (Physaddr pa, PBMT_PMA, init_ext_ptw)⌝ ∗
                   ∃ rsf : regstate, ⌜Qf rsf⌝ ∗ Rf rsf ∗
                   hreg_frame rsf Drw ∗ hreg_frame_ro Df rsf Dro)) -∗
    (∀ rsf : regstate, ⌜Qf rsf⌝ -∗ Rf rsf -∗
     hreg_frame rsf Drw -∗ hreg_frame_ro Df rsf Dro -∗
       swp (checked_mem_read (InstructionFetch tt) PBMT_PMA User
              (Physaddr pa) 4 false false false false)
         (fun r => ⌜r = Values.Ok (w, tt)⌝ ∗
                   hreg_frame rsf Drw ∗ hreg_frame_ro Df rsf Dro ∗ Rf rsf)) -∗
    swp (fetch_bytes pc pc 4)
      (fun r => ⌜r = @FetchBytes_Success 4 w⌝ ∗
                ∃ rsf : regstate, ⌜Qf rsf⌝ ∗ Rf rsf ∗
                hreg_frame rsf Drw ∗ hreg_frame_ro Df rsf Dro).
  Proof.
    intros Hdisj HDmst HDpriv Hpriv.
    iIntros "#Hcert Hrw Hro Htr Hcmr".
    rewrite /swp. iIntros (C) "%HC Hcont".
    unfold fetch_bytes.
    cbn beta iota zeta delta [ext_fetch_check_pc].
    rewrite mbind0_ret.
    iApply (swp_use_cer (translateAddr (Virtaddr pc) (InstructionFetch tt))
              _ _ C HC with "[Hrw Hro Htr] [-]").
    { iApply ("Htr" with "Hrw Hro"). }
    iIntros (v) "(-> & Hf)". cbn beta iota.
    iDestruct "Hf" as (rsf) "(%HQ & HRf & Hrw & Hro)".
    iApply (swp_use_cer
              (mem_read (InstructionFetch tt) PBMT_PMA (Physaddr pa) 4
                 false false false) _ _ C HC with "[Hrw Hro HRf Hcmr] [-]").
    { iApply (swp_mem_read_MR Drw Dro Df rsf (Physaddr pa) w User (Rf rsf)
                Hdisj HDmst HDpriv (Hpriv rsf HQ) with "Hcert Hrw Hro [HRf Hcmr]").
      iIntros "Hrw Hro". iApply ("Hcmr" $! rsf with "[%] HRf Hrw Hro"). exact HQ. }
    iIntros (v) "(-> & Hrw & Hro & HRf)". cbn beta iota.
    rewrite autocast_id mcer_ret.
    iApply ("Hcont" $! (@FetchBytes_Success 4 w)).
    iSplitR; [done|]. iExists rsf. by iFrame.
  Qed.

  Lemma uv_fetch_bytes2_P (Drw Dro : gset register) (Df : register -> dfrac)
      (rs : regstate) (Qf : regstate -> Prop) (Rf : regstate -> iProp Σ)
      (fs gs pa : mword 64) (h : mword 16) :
    Drw ## Dro ->
    (mstatus : register) ∈ Drw ∪ Dro ->
    (cur_privilege : register) ∈ Drw ∪ Dro ->
    (forall rsf, Qf rsf -> register_lookup cur_privilege rsf = User) ->
    gen_cert -∗
    hreg_frame rs Drw -∗
    hreg_frame_ro Df rs Dro -∗
    (hreg_frame rs Drw -∗ hreg_frame_ro Df rs Dro -∗
       swp (translateAddr (Virtaddr gs) (InstructionFetch tt))
         (fun r => ⌜r = Values.Ok (Physaddr pa, PBMT_PMA, init_ext_ptw)⌝ ∗
                   ∃ rsf : regstate, ⌜Qf rsf⌝ ∗ Rf rsf ∗
                   hreg_frame rsf Drw ∗ hreg_frame_ro Df rsf Dro)) -∗
    (∀ rsf : regstate, ⌜Qf rsf⌝ -∗ Rf rsf -∗
     hreg_frame rsf Drw -∗ hreg_frame_ro Df rsf Dro -∗
       swp (checked_mem_read (InstructionFetch tt) PBMT_PMA User
              (Physaddr pa) 2 false false false false)
         (fun r => ⌜r = Values.Ok (h, tt)⌝ ∗
                   hreg_frame rsf Drw ∗ hreg_frame_ro Df rsf Dro ∗ Rf rsf)) -∗
    swp (fetch_bytes fs gs 2)
      (fun r => ⌜r = @FetchBytes_Success 2 h⌝ ∗
                ∃ rsf : regstate, ⌜Qf rsf⌝ ∗ Rf rsf ∗
                hreg_frame rsf Drw ∗ hreg_frame_ro Df rsf Dro).
  Proof.
    intros Hdisj HDmst HDpriv Hpriv.
    iIntros "#Hcert Hrw Hro Htr Hcmr".
    rewrite /swp. iIntros (C) "%HC Hcont".
    unfold fetch_bytes.
    cbn beta iota zeta delta [ext_fetch_check_pc].
    rewrite mbind0_ret.
    iApply (swp_use_cer (translateAddr (Virtaddr gs) (InstructionFetch tt))
              _ _ C HC with "[Hrw Hro Htr] [-]").
    { iApply ("Htr" with "Hrw Hro"). }
    iIntros (v) "(-> & Hf)". cbn beta iota.
    iDestruct "Hf" as (rsf) "(%HQ & HRf & Hrw & Hro)".
    iApply (swp_use_cer
              (mem_read (InstructionFetch tt) PBMT_PMA (Physaddr pa) 2
                 false false false) _ _ C HC with "[Hrw Hro HRf Hcmr] [-]").
    { iApply (swp_mem_read_M2R Drw Dro Df rsf (Physaddr pa) h User (Rf rsf)
                Hdisj HDmst HDpriv (Hpriv rsf HQ) with "Hcert Hrw Hro [HRf Hcmr]").
      iIntros "Hrw Hro". iApply ("Hcmr" $! rsf with "[%] HRf Hrw Hro"). exact HQ. }
    iIntros (v) "(-> & Hrw & Hro & HRf)". cbn beta iota.
    rewrite autocast_id mcer_ret.
    iApply ("Hcont" $! (@FetchBytes_Success 2 h)).
    iSplitR; [done|]. iExists rsf. by iFrame.
  Qed.

  (* =================================================================== *)
  (* §4 THE THREE GEOMETRIES.  [spt_fetch_U_P] / [_rvc2_P] / [_base2_P]   *)
  (* over SmodeCorePt's privilege-free shells and §3.                     *)
  (* =================================================================== *)
  Lemma uv_fetch4_P (Drw Dro : gset register) (Df : register -> dfrac)
      (rs : regstate) (Qf : regstate -> Prop) (Rf : regstate -> iProp Σ)
      (pc pa : mword 64) (w : mword 32) :
    Drw ## Dro ->
    (R_bitvector_64 PC : register) ∈ Drw ∪ Dro ->
    (mstatus : register) ∈ Drw ∪ Dro ->
    (cur_privilege : register) ∈ Drw ∪ Dro ->
    register_lookup (R_bitvector_64 PC) rs = pc ->
    (forall rsf, Qf rsf -> register_lookup cur_privilege rsf = User) ->
    neq_vec (access_vec_dec pc 0) zerobit = false ->
    neq_vec (access_vec_dec pc 1) zerobit = false ->
    is_aligned_vaddr (Virtaddr pc) 4 = true ->
    gen_cert -∗
    hreg_frame rs Drw -∗
    hreg_frame_ro Df rs Dro -∗
    (hreg_frame rs Drw -∗ hreg_frame_ro Df rs Dro -∗
       swp (translateAddr (Virtaddr pc) (InstructionFetch tt))
         (fun r => ⌜r = Values.Ok (Physaddr pa, PBMT_PMA, init_ext_ptw)⌝ ∗
                   ∃ rsf : regstate, ⌜Qf rsf⌝ ∗ Rf rsf ∗
                   hreg_frame rsf Drw ∗ hreg_frame_ro Df rsf Dro)) -∗
    (∀ rsf : regstate, ⌜Qf rsf⌝ -∗ Rf rsf -∗
     hreg_frame rsf Drw -∗ hreg_frame_ro Df rsf Dro -∗
       swp (checked_mem_read (InstructionFetch tt) PBMT_PMA User
              (Physaddr pa) 4 false false false false)
         (fun r => ⌜r = Values.Ok (w, tt)⌝ ∗
                   hreg_frame rsf Drw ∗ hreg_frame_ro Df rsf Dro ∗ Rf rsf)) -∗
    swp (fetch tt)
      (fun r => ⌜r = (if isRVC (subrange_vec_dec w 15 0)
                      then F_RVC (subrange_vec_dec w 15 0)
                      else F_Base w)⌝ ∗
                ∃ rsf : regstate, ⌜Qf rsf⌝ ∗ Rf rsf ∗
                hreg_frame rsf Drw ∗ hreg_frame_ro Df rsf Dro).
  Proof.
    intros Hdisj HDpc HDmst HDpriv Hpc Hpriv Hb0 Hb1 Hal.
    iIntros "#Hcert Hrw Hro Htr Hcmr".
    iApply (spt_fetch_P Drw Dro Df rs pc w _ Hdisj HDpc Hpc Hb0 Hb1 Hal
              with "Hcert Hrw Hro [Htr Hcmr]").
    iIntros "Hrw Hro".
    iApply (uv_fetch_bytes4_P Drw Dro Df rs Qf Rf pc pa w Hdisj HDmst
              HDpriv Hpriv with "Hcert Hrw Hro Htr Hcmr").
  Qed.

  Lemma uv_fetch_rvc2_P (Drw Dro : gset register) (Df : register -> dfrac)
      (rs : regstate) (Qf : regstate -> Prop) (Rf : regstate -> iProp Σ)
      (pc pa : mword 64) (h : mword 16) :
    Drw ## Dro ->
    (R_bitvector_64 PC : register) ∈ Drw ∪ Dro ->
    (misa : register) ∈ Drw ∪ Dro ->
    (mstatus : register) ∈ Drw ∪ Dro ->
    (cur_privilege : register) ∈ Drw ∪ Dro ->
    register_lookup (R_bitvector_64 PC) rs = pc ->
    (forall rsf, Qf rsf -> register_lookup cur_privilege rsf = User) ->
    eq_vec (_get_Misa_C (register_lookup misa rs))
      (MachineWord.MachineWord.N_to_word 1 1%N) = true ->
    neq_vec (access_vec_dec pc 0) zerobit = false ->
    neq_vec (access_vec_dec pc 1) zerobit = true ->
    is_aligned_vaddr (Virtaddr pc) 4 = false ->
    isRVC h = true ->
    gen_cert -∗
    hreg_frame rs Drw -∗
    hreg_frame_ro Df rs Dro -∗
    (hreg_frame rs Drw -∗ hreg_frame_ro Df rs Dro -∗
       swp (translateAddr (Virtaddr pc) (InstructionFetch tt))
         (fun r => ⌜r = Values.Ok (Physaddr pa, PBMT_PMA, init_ext_ptw)⌝ ∗
                   ∃ rsf : regstate, ⌜Qf rsf⌝ ∗ Rf rsf ∗
                   hreg_frame rsf Drw ∗ hreg_frame_ro Df rsf Dro)) -∗
    (∀ rsf : regstate, ⌜Qf rsf⌝ -∗ Rf rsf -∗
     hreg_frame rsf Drw -∗ hreg_frame_ro Df rsf Dro -∗
       swp (checked_mem_read (InstructionFetch tt) PBMT_PMA User
              (Physaddr pa) 2 false false false false)
         (fun r => ⌜r = Values.Ok (h, tt)⌝ ∗
                   hreg_frame rsf Drw ∗ hreg_frame_ro Df rsf Dro ∗ Rf rsf)) -∗
    swp (fetch tt)
      (fun r => ⌜r = F_RVC h⌝ ∗
                ∃ rsf : regstate, ⌜Qf rsf⌝ ∗ Rf rsf ∗
                hreg_frame rsf Drw ∗ hreg_frame_ro Df rsf Dro).
  Proof.
    intros Hdisj HDpc HDmisa HDmst HDpriv Hpc Hpriv HmisaC Hb0 Hb1 Hal4 Hrvc.
    iIntros "#Hcert Hrw Hro Htr Hcmr".
    iApply (spt_fetch_rvc2_P Drw Dro Df rs pc h _ Hdisj HDpc HDmisa Hpc Hb0
              Hb1 Hal4 HmisaC Hrvc with "Hcert Hrw Hro [Htr Hcmr]").
    iIntros "Hrw Hro".
    iApply (uv_fetch_bytes2_P Drw Dro Df rs Qf Rf pc pc pa h Hdisj HDmst
              HDpriv Hpriv with "Hcert Hrw Hro Htr Hcmr").
  Qed.

  Lemma uv_fetch_base2_P (Drw Dro : gset register) (Df : register -> dfrac)
      (rs : regstate) (Qf1 Qf2 : regstate -> Prop)
      (Rf1 Rf2 : regstate -> iProp Σ) (pc pa1 pa2 : mword 64)
      (ilo ihi : mword 16) :
    Drw ## Dro ->
    (R_bitvector_64 PC : register) ∈ Drw ∪ Dro ->
    (misa : register) ∈ Drw ∪ Dro ->
    (mstatus : register) ∈ Drw ∪ Dro ->
    (cur_privilege : register) ∈ Drw ∪ Dro ->
    register_lookup (R_bitvector_64 PC) rs = pc ->
    (forall rs1, Qf1 rs1 -> register_lookup (R_bitvector_64 PC) rs1 = pc) ->
    (forall rs1, Qf1 rs1 -> register_lookup cur_privilege rs1 = User) ->
    (forall rs2, Qf2 rs2 -> register_lookup cur_privilege rs2 = User) ->
    eq_vec (_get_Misa_C (register_lookup misa rs))
      (MachineWord.MachineWord.N_to_word 1 1%N) = true ->
    neq_vec (access_vec_dec pc 0) zerobit = false ->
    neq_vec (access_vec_dec pc 1) zerobit = true ->
    is_aligned_vaddr (Virtaddr pc) 4 = false ->
    isRVC ilo = false ->
    gen_cert -∗
    hreg_frame rs Drw -∗
    hreg_frame_ro Df rs Dro -∗
    (hreg_frame rs Drw -∗ hreg_frame_ro Df rs Dro -∗
       swp (translateAddr (Virtaddr pc) (InstructionFetch tt))
         (fun r => ⌜r = Values.Ok (Physaddr pa1, PBMT_PMA, init_ext_ptw)⌝ ∗
                   ∃ rs1 : regstate, ⌜Qf1 rs1⌝ ∗ Rf1 rs1 ∗
                   hreg_frame rs1 Drw ∗ hreg_frame_ro Df rs1 Dro)) -∗
    (∀ rs1 : regstate, ⌜Qf1 rs1⌝ -∗ Rf1 rs1 -∗
     hreg_frame rs1 Drw -∗ hreg_frame_ro Df rs1 Dro -∗
       swp (checked_mem_read (InstructionFetch tt) PBMT_PMA User
              (Physaddr pa1) 2 false false false false)
         (fun r => ⌜r = Values.Ok (ilo, tt)⌝ ∗
                   hreg_frame rs1 Drw ∗ hreg_frame_ro Df rs1 Dro ∗ Rf1 rs1)) -∗
    (∀ rs1 : regstate, ⌜Qf1 rs1⌝ -∗ Rf1 rs1 -∗
     hreg_frame rs1 Drw -∗ hreg_frame_ro Df rs1 Dro -∗
       swp (translateAddr (Virtaddr (add_vec_int pc 2)) (InstructionFetch tt))
         (fun r => ⌜r = Values.Ok (Physaddr pa2, PBMT_PMA, init_ext_ptw)⌝ ∗
                   ∃ rs2 : regstate, ⌜Qf2 rs2⌝ ∗ Rf2 rs2 ∗
                   hreg_frame rs2 Drw ∗ hreg_frame_ro Df rs2 Dro)) -∗
    (∀ rs2 : regstate, ⌜Qf2 rs2⌝ -∗ Rf2 rs2 -∗
     hreg_frame rs2 Drw -∗ hreg_frame_ro Df rs2 Dro -∗
       swp (checked_mem_read (InstructionFetch tt) PBMT_PMA User
              (Physaddr pa2) 2 false false false false)
         (fun r => ⌜r = Values.Ok (ihi, tt)⌝ ∗
                   hreg_frame rs2 Drw ∗ hreg_frame_ro Df rs2 Dro ∗ Rf2 rs2)) -∗
    swp (fetch tt)
      (fun r => ⌜r = F_Base (concat_vec ihi ilo)⌝ ∗
                ∃ rs2 : regstate, ⌜Qf2 rs2⌝ ∗ Rf2 rs2 ∗
                hreg_frame rs2 Drw ∗ hreg_frame_ro Df rs2 Dro).
  Proof.
    intros Hdisj HDpc HDmisa HDmst HDpriv Hpc Hpc1 Hpriv1 Hpriv2 HmisaC
      Hb0 Hb1 Hal4 Hnrvc.
    iIntros "#Hcert Hrw Hro Htr1 Hcmr1 Htr2 Hcmr2".
    iApply (spt_fetch_base2_P Drw Dro Df rs Qf1 Rf1 pc ilo ihi _ Hdisj HDpc
              HDmisa Hpc Hb0 Hb1 Hal4 HmisaC Hnrvc Hpc1
              with "Hcert Hrw Hro [Htr1 Hcmr1] [Htr2 Hcmr2]").
    - iIntros "Hrw Hro".
      iApply (uv_fetch_bytes2_P Drw Dro Df rs Qf1 Rf1 pc pc pa1 ilo Hdisj
                HDmst HDpriv Hpriv1 with "Hcert Hrw Hro Htr1 Hcmr1").
    - iIntros (rs1) "%HQ1 HRf1 Hrw Hro".
      iApply (uv_fetch_bytes2_P Drw Dro Df rs1 Qf2 Rf2 pc (add_vec_int pc 2)
                pa2 ihi Hdisj HDmst HDpriv Hpriv2
                with "Hcert Hrw Hro [Htr2 HRf1] Hcmr2").
      iApply ("Htr2" $! rs1 with "[%] HRf1"). exact HQ1.
  Qed.

End UmodeFetchX.
