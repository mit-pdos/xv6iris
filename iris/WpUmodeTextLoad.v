(* WpUmodeTextLoad.v -- THE LOAD OUT OF THE TEXT HALF (icache).

   The verified tier keeps the process's TEXT bytes outside the walker's map:
   they are stamped ([TsoCtx.ctx_phys_xpointsto], minted by userret's
   fence.i), the fetch reads them at the memory node, and the walker
   ([HartMemRunX.swp_hmrun_of_exec_p]) only ever sees the unstamped data half
   (claude-notes/projects/icache.md, "text outside the walker").  A user
   program does load from its text page -- every string literal lives there
   -- and that load is the ONE data access the walker cannot run.  This file
   drives it at the node instead, exactly as the fetch is driven:

     execute (LOAD ... 1)  =  effective address  ;  vmem_read_addr
     vmem_read_addr        =  cfg reads ; translationMode ; translate_and_read
     translate_and_read    =  translateAddr (THE WALK, over the data half)
                              ; mem_read (THE NODE, paid by the stamped byte)

   Every register-only stretch and the page-table walk go through
   [WpUmodeFetch.uv_swp_walk] with the tier's exec facts; the byte read is
   [HartEvents.swp_hart_ram_read_plain] paid by [TsoCtx.ctx_phys_xload_ok]
   ([uv_load_pay]).  The chain is [HartSMem]'s S-mode load chain at User and
   width 1, with the landing file threaded as a PREDICATE ([uv_ld_post])
   instead of the S-mode "rs or tlb-set rs" disjunction.  Only [lbu] is
   served: the engine's text loads are byte loads ([UkRunMem.wp_uk_lbu_text]). *)

From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language weakestpre.
From iris.base_logic.lib Require Import gen_heap ghost_map.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvModelBytes TsoMemPa RiscvLang RiscvPtsto RiscvExec RiscvTryStep RiscvFetchExec.
Require Import RiscvExtras.
Require Import RegFile WpGpr.
Require Import CommonWalk.
Require Import PtreeType PtAdBits PtTree KptTree.
Require Import SRegime UptTree UptWalkPt.
Require Import UserMem UserFetch UserPtTree UserTranslate.
Require Import HartSwp HartLift HartSpan HartSpanChar HartGoodb HartMemRun HartMemAsm HartMCycle
        HartEvents HartMFetch HartMFrame.
Require Import SmodePte PtTreeAdue HartSMem.
Require Import WpMmodeLeafBase.
Require Import PtBytes UserBytes UserFrame UserClassifyAsm.
Require Import UserFetchCert UserFaultCert.
Require Import UserExec UserStep UserTrap UserExecFacts.
Require Import UserMemPt UserMemAccess UserMemArms UserMemClassify UserMemCert UserMemArmsBase.
Require UserTotalU.
Require Import UserActiveClass.
Require Import UmodeMem UmodeCap UmodeFetch.
Require Import HartMemRunX UmodeText UmodeFetchX UmodeArith.
Require Import WpUmodeFetch WpUmodeStep WpUmodeStore WpUmodeLoad.
Require Import KptGoodb.
Require Import TsoCtx.
Local Open Scope Z_scope.
Import Defs.

Local Arguments Z.sub _ _ : simpl nomatch.
Local Arguments Z.add _ _ : simpl nomatch.
Local Arguments Z.mul _ _ : simpl nomatch.
Local Arguments Z.eqb _ _ : simpl nomatch.
Local Arguments Z.compare _ _ : simpl nomatch.
Local Arguments Z.pos_sub _ _ : simpl nomatch.
Local Arguments Pos.compare _ _ : simpl nomatch.
Local Arguments Pos.compare_cont _ _ _ : simpl nomatch.

(* HartSMem's three reducers, verbatim (they are Local there) *)
Local Ltac sm_cbn :=
  cbn beta iota zeta delta
    [Defs.bind Defs.bind0 Interface.iMon_bind Defs.liftR Defs.try_catch
     Defs.catch_early_return Defs.returnm returnM returnR
     Defs.returnR Riscv.rv64d_types.returnR
     Defs.read_reg Defs.early_return Defs.throw
     Defs.assert_exp Defs.assert_exp'
     Defs.and_boolM Defs.or_boolM andb orb negb not
     check_pma_with_pmp_priority pmaCheck mag_pma_check
     is_mag_applicable_access __id
     get_config_rvfi plat_have_clint plat_have_sig].

Local Ltac sm_glue :=
  cbn beta iota zeta delta
    [Defs.returnm returnM returnR Defs.returnR Riscv.rv64d_types.returnR
     andb orb negb not
     Instances.generic_eq Instances.generic_neq].

Local Ltac sm_read :=
  rewrite hfrun_read;
  match goal with
  | |- context [ bool_decide ?P ] =>
      rewrite (bool_decide_eq_true_2 P ltac:(assumption))
  end.

(* ===================================================================== *)
(* 1. PURE.                                                               *)
(* ===================================================================== *)

Lemma is_aligned_paddr_1 (pa : mword 64) : is_aligned_paddr (Physaddr pa) 1 = true.
Proof. unfold is_aligned_paddr. rewrite Z.rem_1_r. reflexivity. Qed.

(* [HartSMem.hfrun_check_pma_load_S] at User and width 1: the PMA walk never
   looks at the privilege on the RAM path *)
Lemma hfrun_check_pma_load_U (D Drw : gset register) (rs : regstate)
    (pa : mword 64) (pmar0 : list PMA_Region) :
  (pma_regions : register) ∈ D ->
  register_lookup pma_regions rs = pmar0 ->
  pma_allows_ram pmar0 ->
  addr_is_ram pa ->
  hfrun 6 D Drw rs
    (check_pma_with_pmp_priority (Load Data) PBMT_PMA User (Physaddr pa) 1 false)
  = Some (Values.Ok
            {| Phys_Mem_Access_Info_splittable := CannotSplit;
               Phys_Mem_Access_Info_granule_size_exp := 0 |}, rs).
Proof.
  intros HD Hpma Hpallow Hram.
  unfold check_pma_with_pmp_priority. sm_cbn.
  sm_read. rewrite Hpma. sm_cbn.
  destruct (Hpallow pa 1 (pma_ram_access_w pa 1 ltac:(lia) ltac:(lia)
                            (Z.divide_1_l 4096) Hram (is_aligned_paddr_1 pa)))
    as (region & Hmatch & Hgrant).
  destruct region as [rbase rsize rattr rdtree].
  destruct Hgrant as (_ & Hx & _).
  cbn [PMA_Region_attributes] in Hx.
  rewrite Hmatch. sm_cbn.
  rewrite Hx. sm_cbn.
  rewrite (is_aligned_paddr_1 pa). sm_cbn.
  apply hfrun_ret.
Qed.

(* the PMP range test at a RAM byte: entry 0 is TOR from 0 to past RAM *)
Lemma ram_load1_pmp (pa paddr0 : mword 64) :
  addr_is_ram pa ->
  (ram_base + ram_size <= uint paddr0 * 4)%Z ->
  pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
    (Z.mul (uint paddr0) 4) (uint pa) (uint (to_bits 64 1)) = PMP_Match.
Proof.
  intros (Hlo & Hhi) Hcov.
  assert (Hz : uint (zeros' 64 : mword 64) = 0) by (vm_compute; reflexivity).
  assert (H1 : uint (to_bits 64 1 : mword 64) = 1) by (vm_compute; reflexivity).
  rewrite Hz H1 Z.mul_0_l.
  apply pmpRangeMatch_full; unfold ram_base, ram_size in *; lia.
Qed.

Section UmodeTextLoad.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}.

  (* =================================================================== *)
  (* 2. THE STAMPED BYTE AS A PLAIN-LOAD PAYER.                            *)
  (* [HartMemRunX.bytes_own_p_ifetch_of]'s data twin: a stamped byte still  *)
  (* answers a plain read at every view at or after the hart's own          *)
  (* ([TsoCtx.ctx_phys_xload_ok]).                                          *)
  (* =================================================================== *)
  Lemma bytes_own_p_load_of (img mem : PtBytes.pamap)
      (log : list pwmsg) (V : agent -> nat) (rs : regstate) (d : dev_state)
      (F : Arch.pa -> option nat) (mm : PtBytes.pamap) (IK : nat)
      (pa : Arch.pa) (n : N) (w : bv (8 * n)) :
    (forall j : nat, (N.of_nat j < n)%N ->
       mm !! pa_add pa j = Some (nth_byte w j) /\ F (pa_add pa j) = Some IK) ->
    gen_heap_interp (hG := riscv_memGS) mem -∗
    tso_interp_of riscv_eraGS img mem log V -∗
    TsoCtx.own_context XI -∗
    bytes_own_p F mm -∗
    ⌜forall tv' : nat, (V (hart_agent cpu_id) <= tv')%nat ->
       tso_read_bytes img log (hart_agent cpu_id) tv' pa n w⌝.
  Proof.
    intros Hwin. iIntros "Hgh Htso Hrun Hown".
    iDestruct (tso_interp_of_pin with "Htso") as %Hpin.
    rewrite (tso_interp_of_at_gs riscv_eraGS img mem log V rs d Hpin).
    iAssert (⌜forall j : nat, (N.of_nat j < n)%N ->
               forall tv' : nat, (V (hart_agent cpu_id) <= tv')%nat ->
                 tso_read img log (hart_agent cpu_id) tv' (pa_add pa j)
                   = Some (nth_byte w j)⌝)%I
      with "[Hgh Htso Hrun Hown]" as %HH.
    { rewrite bi.pure_forall. iIntros (j). rewrite bi.pure_impl. iIntros (Hj).
      rewrite bi.pure_forall. iIntros (tv'). rewrite bi.pure_impl. iIntros (Htv).
      destruct (Hwin j Hj) as [Hmm HF].
      rewrite /bytes_own_p.
      iDestruct (big_sepM_lookup _ _ _ _ Hmm with "Hown") as "Ha".
      rewrite /xbyte HF.
      iDestruct (TsoCtx.ctx_phys_xload_ok (gs_of img mem log V rs d) XI IK
                   (pa_add pa j) (DfracOwn 1) (nth_byte w j)
                   with "Hgh Htso Hrun Ha") as %Hrd.
      iPureIntro. cbn [gimg glog gtv gs_of] in Hrd. exact (Hrd tv' Htv). }
    iPureIntro. intros tv' Htv j Hj. exact (HH j Hj tv' Htv).
  Qed.

  (* the tier's text byte, as the interp wand the read node wants *)
  Lemma uv_load_pay (pt : uptd) (M : gmap Z (bv 8)) (t : ptree) (IK : nat)
      (w_leaf va : mword 64) (b : bv 8) :
    uva_inj pt M ->
    uv_tree_ok pt (upa_map pt M) t ->
    ud_um pt !! svpn_of va = Some w_leaf ->
    uM_bytes M (uint va) 1 b ->
    uva_text pt (uint va) ->
    ⊢ (∀ σ img log tv V,
         ⌜V (hart_agent cpu_id) = tv⌝ -∗
         mstate_interp σ -∗
         tso_interp_of riscv_eraGS img σ.(mem) log V -∗
         (TsoCtx.own_context XI ∗
          bytes_own_p (uv_F pt M IK) (uv_mm t (upa_map pt M)) ∗
          resv_any cpu_id) ={⊤,∅}=∗
         ⌜forall tv' : nat, (tv <= tv')%nat -> (tv' <= length log)%nat ->
            tso_read_bytes img log (hart_agent cpu_id) tv'
              (u_walk_pa w_leaf va) 1 b⌝ ∗
         ▷ (|={∅,⊤}=> mstate_interp σ ∗
              tso_interp_of riscv_eraGS img σ.(mem) log V ∗
              (TsoCtx.own_context XI ∗
               bytes_own_p (uv_F pt M IK) (uv_mm t (upa_map pt M)) ∗
               resv_any cpu_id))).
  Proof.
    intros Hinj Htok Hl Hb Htx.
    assert (Hnc : forall j : nat, (j < 1)%nat ->
              bv_unsigned va mod 4096 + Z.of_nat j < 4096).
    { intros j Hj. assert (Hj0 : j = 0%nat) by lia. subst j.
      pose proof (Z.mod_pos_bound (bv_unsigned va) 4096 ltac:(lia)). lia. }
    assert (Hwin : forall j : nat, (N.of_nat j < 1)%N ->
              uv_mm t (upa_map pt M) !! pa_add (u_walk_pa w_leaf va) j
                = Some (nth_byte b j) /\
              uv_F pt M IK (pa_add (u_walk_pa w_leaf va) j) = Some IK).
    { intros j Hj. split.
      - exact (uv_win_bytes pt M t w_leaf va 1 _ b Hinj (proj1 (proj2 Htok))
                 Hl Hnc Hb j ltac:(lia)).
      - exact (uv_win_text pt M IK w_leaf va 1 _ b Hinj Hl Hnc Hb Htx j
                 ltac:(lia)). }
    iIntros (σ img log tv V) "%Htv Hσ Htso (Hrun & Hown & Hany)".
    rewrite /mstate_interp. iDestruct "Hσ" as "(Hri & Hmem & Hdev)".
    iDestruct (bytes_own_p_load_of img σ.(mem) log V σ.(sregs) σ.(mdev)
                 (uv_F pt M IK) (uv_mm t (upa_map pt M)) IK
                 (u_walk_pa w_leaf va) 1 b Hwin
                 with "Hmem Htso Hrun Hown") as %Hok.
    iApply fupd_mask_intro; [apply empty_subseteq|]. iIntros "Hmask".
    iSplitR.
    { iPureIntro. intros tv' Hlo _. apply Hok. rewrite Htv. exact Hlo. }
    iNext. iMod "Hmask" as "_". iModIntro.
    iFrame "Hri Hmem Hdev Htso Hrun Hown Hany".
  Qed.

  (* =================================================================== *)
  (* 3. THE NODE.  [HartSMem.swp_checked_mem_read_S] at User, width 1,     *)
  (* RAM, with the obligation in the interp-wand form and a resource [R]   *)
  (* threaded through the node (the [_UR] shape of UmodeFetchX).           *)
  (* =================================================================== *)
  Lemma swp_checked_mem_read_load1_UR (Drw Dro : gset register)
      (Df : register -> dfrac) (rs : regstate)
      (pa : mword 64)
      (pmar0 : list PMA_Region) (pcfg : type_of_register pmpcfg_n)
      (paddr : type_of_register pmpaddr_n) (b : bv 8) (R : iProp Σ) :
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
    eq_vec (_get_Pmpcfg_ent_R (vec_access_dec pcfg 0)) ('b"1") = true ->
    (ram_base + ram_size <= uint (vec_access_dec paddr 0) * 4)%Z ->
    pma_allows_ram pmar0 ->
    addr_is_ram pa ->
    gen_cert -∗
    hreg_frame rs Drw -∗
    hreg_frame_ro Df rs Dro -∗
    (∀ σ img log tv V,
        ⌜V (hart_agent cpu_id) = tv⌝ -∗
        mstate_interp σ -∗
        tso_interp_of riscv_eraGS img σ.(mem) log V -∗
        R ={⊤,∅}=∗
        ⌜forall tv' : nat, (tv <= tv')%nat -> (tv' <= length log)%nat ->
           tso_read_bytes img log (hart_agent cpu_id) tv' pa 1 b⌝ ∗
        ▷ (|={∅,⊤}=> mstate_interp σ ∗
             tso_interp_of riscv_eraGS img σ.(mem) log V ∗ R)) -∗
    R -∗
    swp (checked_mem_read (Load Data) PBMT_PMA User
           (Physaddr pa) 1 false false false false)
      (fun r => ⌜r = Values.Ok (b, tt)⌝ ∗
                hreg_frame rs Drw ∗ hreg_frame_ro Df rs Dro ∗ R).
  Proof.
    intros Hdisj HDpma HDcfg HDaddr HDhtif Hhtif Hpma Hpcfg Hpaddr
      HA Hord HR Hcov Hpallow Hram.
    pose proof (ram_load1_pmp pa (vec_access_dec paddr 0) Hram Hcov) as Hrange.
    iIntros "#Hcert Hrw Hro Hmem HR".
    rewrite /swp. iIntros (C) "%HC Hcont".
    unfold checked_mem_read.
    iApply (swp_use_cer
              (check_pma_with_pmp_priority (Load Data) PBMT_PMA
                 User (Physaddr pa) 1 false) _ _ C HC
              with "[Hrw Hro] [-]").
    { iApply (swp_hfrun 6 Drw Dro Df rs rs _ _ Hdisj
                (hfrun_check_pma_load_U (Drw ∪ Dro) Drw rs pa pmar0
                   HDpma Hpma Hpallow Hram)
                with "Hcert Hrw Hro"). }
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
    replace (0 * 1)%Z with 0%Z by lia. rewrite avi0.
    iApply (swp_use_cer3
              (pmpCheck (Physaddr pa) 1 (Load Data) User)
              _ _ _ _ C HC with "[Hrw Hro] [-]").
    { iApply (swp_pmpCheck_U (Load Data) Drw Dro Df rs pcfg paddr
                pa 1 Hdisj HDcfg HDaddr Hpcfg Hpaddr HA Hord Hrange
                ltac:(unfold pmpCheckRWX; cbn match; rewrite HR; reflexivity)
                with "Hcert Hrw Hro"). }
    iIntros (v) "(-> & Hrw & Hro)". cbn beta iota.
    rewrite mbind0_ret.
    iApply (swp_use_cer3 (within_mmio_readable (Physaddr pa) 1)
              _ _ _ _ C HC with "[Hrw Hro] [-]").
    { iApply (swp_hfrun 12 Drw Dro Df rs rs _ _ Hdisj
                (hfrun_within_mmio_ram (Drw ∪ Dro) Drw rs pa 1
                   ltac:(lia) HDhtif Hhtif Hram)
                with "Hcert Hrw Hro"). }
    iIntros (v) "(-> & Hrw & Hro)". cbn beta iota.
    iApply (swp_use_cer4 (read_ram Riscv.rv64d_types.Read_plain (Physaddr pa) 1 false)
              (fun r => (⌜r = (b, default_meta)⌝ ∗
                         hreg_frame rs Drw ∗ hreg_frame_ro Df rs Dro ∗ R)%I)
              _ _ _ _ C HC with "[Hrw Hro Hmem HR] [-]").
    { iApply (swp_hart_ram_read_plain 1 (mread_req1 pa) _ _
                (hread_req_at_read_ram1 pa) (addr_is_ram_not_dev pa Hram)
                ltac:(reflexivity) ltac:(reflexivity)
                with "Hcert [Hrw Hro Hmem HR]").
      iIntros (σ img log tv V) "%Htv Hσ Htso".
      iMod ("Hmem" $! σ img log tv V with "[//] Hσ Htso HR") as "[%Hrd Hclose]".
      iModIntro. iExists b. iSplitR; [iPureIntro; exact Hrd|]. iNext.
      iMod "Hclose" as "(Hσ & Htso & HR)". iModIntro. iFrame "Hσ Htso".
      iIntros (tvn Hlo Hhi) "_".
      rewrite (hread_resume_read_ram1 pa b). iApply swp_ret. by iFrame. }
    iIntros (v) "(-> & Hrw & Hro & HR)". cbn beta iota zeta.
    rewrite mbind_ret. cbn beta.
    change (0 =? 1 - 1) with true. cbn beta iota zeta.
    rewrite !autocast_id usvd_zeros_full_8 mcer_ret.
    iApply ("Hcont" $! (Values.Ok (b, tt))). by iFrame.
  Qed.

  (* [HartSMem.swp_mem_read_S] at User: the effective privilege is handed
     in as a term equation, which at User is MPRV = 0 *)
  Lemma swp_mem_read_load1_UR (Drw Dro : gset register) (Df : register -> dfrac)
      (rs : regstate) (pa : physaddr) (b : bv 8) (R : iProp Σ) :
    Drw ## Dro ->
    (mstatus : register) ∈ Drw ∪ Dro ->
    (cur_privilege : register) ∈ Drw ∪ Dro ->
    register_lookup cur_privilege rs = User ->
    effectivePrivilege (Load Data) (register_lookup mstatus rs) User
      = returnM User ->
    gen_cert -∗
    hreg_frame rs Drw -∗
    hreg_frame_ro Df rs Dro -∗
    (hreg_frame rs Drw -∗ hreg_frame_ro Df rs Dro -∗
       swp (checked_mem_read (Load Data) PBMT_PMA User pa 1
              false false false false)
         (fun r => ⌜r = Values.Ok (b, tt)⌝ ∗
                   hreg_frame rs Drw ∗ hreg_frame_ro Df rs Dro ∗ R)) -∗
    swp (mem_read (Load Data) PBMT_PMA pa 1 false false false)
      (fun r => ⌜r = Values.Ok b⌝ ∗
                hreg_frame rs Drw ∗ hreg_frame_ro Df rs Dro ∗ R).
  Proof.
    intros Hdisj HDmst HDpriv Hpriv Hep.
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
    rewrite Hep. rewrite mbind_ret.
    unfold mem_read_priv, mem_read_priv_meta.
    cbn beta iota.
    iApply (swp_bind_use _ _
              (fun r => (⌜r = Values.Ok (b, tt)⌝ ∗
                         hreg_frame rs Drw ∗ hreg_frame_ro Df rs Dro ∗ R)%I) _
              with "[Hrw Hro Hcmr] [-]").
    { iApply (swp_bind_use _ _
                (fun r => (⌜r = Values.Ok (b, tt)⌝ ∗
                           hreg_frame rs Drw ∗ hreg_frame_ro Df rs Dro ∗ R)%I) _
                with "[Hrw Hro Hcmr] [-]").
      - iApply ("Hcmr" with "Hrw Hro").
      - iIntros (v) "(-> & Hrw & Hro & HR)". iApply swp_ret. by iFrame. }
    iIntros (v) "(-> & Hrw & Hro & HR)". iApply swp_ret.
    cbn [MemoryOpResult_drop_meta]. by iFrame.
  Qed.

  (* =================================================================== *)
  (* 4. THE CHAIN, over the tier's currency.                               *)
  (* =================================================================== *)

  (* the landing post every link hands on: [WpUmodeFetch.uv_fetch_post]
     at an arbitrary result type *)
  Definition uv_ld_post {X : Type} (dq : dfrac) (pt : uptd) (M : gmap Z (bv 8))
      (rsA : regstate) (t : ptree) (x : X) : X -> iProp Σ :=
    fun r =>
      (⌜r = x⌝ ∗
       ∃ (rs2 rsf : regstate) (t' : ptree),
         ⌜u_tlb_only rsA rsf⌝ ∗
         ⌜reg_agree_on (u_Drw ∪ u_Dro) rs2 rsf⌝ ∗
         ⌜tlb_ok_pt (mword_of_int 0) t' (register_lookup tlb rsf)⌝ ∗
         ⌜uv_tree_ok pt (upa_map pt M) t'⌝ ∗
         ⌜pt_same_shape 2 t t'⌝ ∗
         hreg_frame rs2 u_Drw ∗ hreg_frame_ro (u_Df dq) rs2 u_Dro ∗
         TsoCtx.own_context XI ∗ uv_bytes pt M t' ∗ resv_any cpu_id)%I.

  (* ---- (a) the walk: [translateAddr] at [Load Data] over the data half *)
  Lemma uv_swp_translate_ld (pt : uptd) (M : gmap Z (bv 8)) (t : ptree)
      (dq : dfrac) (rs rsA : regstate) (w_leaf va : mword 64) :
    uva_inj pt M ->
    ud_um pt !! svpn_of va = Some w_leaf ->
    uleaf_ok (Load Data) w_leaf ->
    uva_canon va ->
    u_data_cfg rsA ->
    u_exec_pins pt t rsA ->
    uv_tree_ok pt (upa_map pt M) t ->
    reg_agree_on (u_Drw ∪ u_Dro) rs rsA ->
    gen_cert -∗ resv_any cpu_id -∗
    hreg_frame rs u_Drw -∗ hreg_frame_ro (u_Df dq) rs u_Dro -∗
    TsoCtx.own_context XI -∗ uv_bytes pt M t -∗
    swp (translateAddr (Virtaddr va) (Load Data))
      (uv_ld_post dq pt M rsA t
         (Values.Ok (Physaddr (u_walk_pa w_leaf va), PBMT_PMA, init_ext_ptw))).
  Proof.
    intros Hinj Hl Hlok Hcanon Hcfg Hpins Htok Hag.
    pose proof (uv_tree_ok_data pt M t Hinj Htok) as Htokd.
    destruct (uv_walk_data (Load Data) pt t (upa_map pt (uM_data pt M)) rsA
                w_leaf va (or_intror (or_introl eq_refl)) Hl Hlok Hcanon Hcfg
                Hpins Htokd)
      as (rsf & t' & Htr & Htrg & Tr & Htlbok' & Htokd' & Hshape).
    pose proof (uv_tree_ok_of_data pt M t t' Htok Htokd' Hshape) as Htok'.
    iIntros "#Hcert Hany Hrw Hro Hrun Hown".
    iApply (uv_swp_walk pt M M t t' dq rs rsA rsf _ _ _ Hinj Hinj eq_refl
              Htok Htok' (eq_sym (uv_mmd_dom pt M t t' Hshape)) Hag Htr Htrg
              with "Hcert Hany Hrw Hro Hrun Hown").
    iIntros (rs2) "%Hag2 Hrw Hro Hrun Hown Hany".
    rewrite /uv_ld_post. iSplitR; [done|].
    iExists rs2, rsf, t'. iFrame "Hrw Hro Hrun Hown Hany".
    iPureIntro. split_and!;
      [exact Tr | exact Hag2 | exact Htlbok' | exact Htok' | exact Hshape].
  Qed.

  (* ---- (b) the node: [mem_read] of the text byte, off a file that agrees
     with the entry file everywhere but the TLB *)
  Lemma uv_swp_mem_read_ld1 (pt : uptd) (M : gmap Z (bv 8)) (t : ptree)
      (dq : dfrac) (rs rsA : regstate) (w_leaf va : mword 64) (b : bv 8) :
    uva_inj pt M ->
    uv_tree_ok pt (upa_map pt M) t ->
    ud_um pt !! svpn_of va = Some w_leaf ->
    uM_bytes M (uint va) 1 b ->
    uva_text pt (uint va) ->
    u_hw_pins rsA ->
    u_pt_pins pt rsA ->
    register_lookup cur_privilege rsA = User ->
    eq_vec (_get_Mstatus_MPRV (register_lookup mstatus rsA)) ('b"1") = false ->
    (forall q : register, q ∈ u_Drw ∪ u_Dro ->
       register_beq q (tlb : register) = false ->
       register_lookup q rs = register_lookup q rsA) ->
    gen_cert -∗
    hreg_frame rs u_Drw -∗ hreg_frame_ro (u_Df dq) rs u_Dro -∗
    (TsoCtx.own_context XI ∗ uv_bytes pt M t ∗ resv_any cpu_id) -∗
    swp (mem_read (Load Data) PBMT_PMA (Physaddr (u_walk_pa w_leaf va)) 1
           false false false)
      (fun r => ⌜r = Values.Ok b⌝ ∗
                hreg_frame rs u_Drw ∗ hreg_frame_ro (u_Df dq) rs u_Dro ∗
                (TsoCtx.own_context XI ∗ uv_bytes pt M t ∗ resv_any cpu_id)).
  Proof.
    intros Hinj Htok Hl Hb Htx Hhw Hpt Lcp Hmprv Hmv.
    destruct Hhw as (_ & _ & _ & Hhtif & Hall & _).
    destruct Hpt as (_ & HA & Hord & _ & _ & HRp & Hcov).
    assert (Hnc : forall j : nat, (j < 1)%nat ->
              bv_unsigned va mod 4096 + Z.of_nat j < 4096).
    { intros j Hj. assert (Hj0 : j = 0%nat) by lia. subst j.
      pose proof (Z.mod_pos_bound (bv_unsigned va) 4096 ltac:(lia)). lia. }
    pose proof (proj1 (proj2 (proj2 Htok))) as Hram.
    assert (Hram0 : addr_is_ram (u_walk_pa w_leaf va)).
    { rewrite <- (pa_add_0 (u_walk_pa w_leaf va)). apply Hram. apply elem_of_dom.
      exact (uv_win_some pt M t w_leaf va 1 _ b Hinj (proj1 (proj2 Htok)) Hl
               Hnc Hb 0%nat ltac:(lia)). }
    assert (Lcp' : register_lookup cur_privilege rs = User)
      by (rewrite (Hmv _ u_in_priv ltac:(vm_compute; reflexivity)); exact Lcp).
    assert (Hmst : register_lookup mstatus rs = register_lookup mstatus rsA)
      by (apply (Hmv _ u_in_mst); vm_compute; reflexivity).
    assert (Hep : effectivePrivilege (Load Data) (register_lookup mstatus rs) User
                  = returnM User)
      by (apply effectivePrivilege_mprv0; rewrite Hmst; exact Hmprv).
    iIntros "#Hcert Hrw Hro (Hrun & Hown & Hany)".
    iDestruct "Hown" as (IK) "[#Hlb Hown]".
    iApply (swp_mono with "[] [Hrw Hro Hrun Hown Hany]").
    2:{ iApply (swp_mem_read_load1_UR u_Drw u_Dro (u_Df dq) rs
                  (Physaddr (u_walk_pa w_leaf va)) b
                  (TsoCtx.own_context XI ∗
                   bytes_own_p (uv_F pt M IK) (uv_mm t (upa_map pt M)) ∗
                   resv_any cpu_id)%I
                  u_disj u_in_mst u_in_priv Lcp' Hep
                  with "Hcert Hrw Hro [Hrun Hown Hany]").
        iIntros "Hrw Hro".
        iApply (swp_checked_mem_read_load1_UR u_Drw u_Dro (u_Df dq) rs
                  (u_walk_pa w_leaf va)
                  (register_lookup pma_regions rsA)
                  (register_lookup pmpcfg_n rsA)
                  (register_lookup pmpaddr_n rsA) b
                  (TsoCtx.own_context XI ∗
                   bytes_own_p (uv_F pt M IK) (uv_mm t (upa_map pt M)) ∗
                   resv_any cpu_id)%I
                  u_disj u_in_pma u_in_pcfg u_in_paddr u_in_htif
                  (eq_trans (Hmv _ u_in_htif ltac:(vm_compute; reflexivity)) Hhtif)
                  (Hmv _ u_in_pma ltac:(vm_compute; reflexivity))
                  (Hmv _ u_in_pcfg ltac:(vm_compute; reflexivity))
                  (Hmv _ u_in_paddr ltac:(vm_compute; reflexivity))
                  HA Hord HRp Hcov (pma_all_ram Hall) Hram0
                  with "Hcert Hrw Hro [] [$Hrun $Hown $Hany]").
        iApply (uv_load_pay pt M t IK w_leaf va b Hinj Htok Hl Hb Htx). }
    iIntros (r) "(-> & Hrw & Hro & (Hrun & Hown & Hany))".
    iSplitR; [done|]. iFrame "Hrw Hro Hrun Hany". iExists IK. iFrame "Hlb Hown".
  Qed.

  (* ---- (c) [translate_and_read_value]: the walk, then the node *)
  Lemma uv_swp_translate_and_read_ld1 (pt : uptd) (M : gmap Z (bv 8))
      (t : ptree) (dq : dfrac) (rs rsA : regstate) (w_leaf va : mword 64)
      (b : bv 8) :
    uva_inj pt M ->
    ud_um pt !! svpn_of va = Some w_leaf ->
    uleaf_ok (Load Data) w_leaf ->
    uva_canon va ->
    uM_bytes M (uint va) 1 b ->
    uva_text pt (uint va) ->
    u_data_cfg rsA ->
    u_exec_pins pt t rsA ->
    uv_tree_ok pt (upa_map pt M) t ->
    reg_agree_on (u_Drw ∪ u_Dro) rs rsA ->
    gen_cert -∗ resv_any cpu_id -∗
    hreg_frame rs u_Drw -∗ hreg_frame_ro (u_Df dq) rs u_Dro -∗
    TsoCtx.own_context XI -∗ uv_bytes pt M t -∗
    swp (translate_and_read_value (Virtaddr va) 1 (Load Data) false false false)
      (uv_ld_post dq pt M rsA t (Values.Ok (Physaddr (u_walk_pa w_leaf va), b))).
  Proof.
    intros Hinj Hl Hlok Hcanon Hb Htx Hcfg Hpins Htok Hag.
    pose proof Hcfg as (Lcp & Hms & _).
    pose proof Hpins as (Hhw & _ & Hpt & _).
    iIntros "#Hcert Hany Hrw Hro Hrun Hown".
    unfold translate_and_read_value.
    iApply (swp_bind_use (translateAddr (Virtaddr va) (Load Data)) _ _ _
              with "[Hany Hrw Hro Hrun Hown] [-]").
    { iApply (uv_swp_translate_ld pt M t dq rs rsA w_leaf va Hinj Hl Hlok Hcanon
                Hcfg Hpins Htok Hag with "Hcert Hany Hrw Hro Hrun Hown"). }
    iIntros (v) "(-> & Hland)". cbn beta iota.
    iDestruct "Hland" as (rs2 rsf t')
      "(%Tr & %Hag2 & %Htlbok' & %Htok' & %Hshape & Hrw & Hro & Hrun & Hown & Hany)".
    pose proof (u_bridge_mv rsA rsf rs2 Tr Hag2) as Hmv2.
    iApply (swp_bind_use _ _
              (fun r => (⌜r = Values.Ok b⌝ ∗
                         hreg_frame rs2 u_Drw ∗ hreg_frame_ro (u_Df dq) rs2 u_Dro ∗
                         (TsoCtx.own_context XI ∗ uv_bytes pt M t' ∗
                          resv_any cpu_id))%I) _
              with "[Hrw Hro Hrun Hown Hany] []").
    { iApply (uv_swp_mem_read_ld1 pt M t' dq rs2 rsA w_leaf va b Hinj Htok' Hl
                Hb Htx Hhw Hpt Lcp (proj1 (proj2 Hms)) Hmv2
                with "Hcert Hrw Hro [$Hrun $Hown $Hany]"). }
    iIntros (v) "(-> & Hrw & Hro & (Hrun & Hown & Hany))". cbn beta iota.
    iApply swp_ret. rewrite /uv_ld_post. iSplitR; [done|].
    iExists rs2, rsf, t'. iFrame "Hrw Hro Hrun Hown Hany".
    iPureIntro. split_and!;
      [exact Tr | exact Hag2 | exact Htlbok' | exact Htok' | exact Hshape].
  Qed.

  (* ---- (d) [vmem_read_addr]: the two config reads, the translation mode
     (a walk of its own), then (c).  [HartSMem.swp_vmem_read_addr_S_gen]. *)
  Lemma uv_swp_vmem_read_addr_ld1 (pt : uptd) (M : gmap Z (bv 8))
      (t : ptree) (dq : dfrac) (rs rsA : regstate) (w_leaf va : mword 64)
      (b : bv 8) :
    uva_inj pt M ->
    ud_um pt !! svpn_of va = Some w_leaf ->
    uleaf_ok (Load Data) w_leaf ->
    uva_canon va ->
    uM_bytes M (uint va) 1 b ->
    uva_text pt (uint va) ->
    u_data_cfg rsA ->
    u_exec_pins pt t rsA ->
    uv_tree_ok pt (upa_map pt M) t ->
    reg_agree_on (u_Drw ∪ u_Dro) rs rsA ->
    gen_cert -∗ resv_any cpu_id -∗
    hreg_frame rs u_Drw -∗ hreg_frame_ro (u_Df dq) rs u_Dro -∗
    TsoCtx.own_context XI -∗ uv_bytes pt M t -∗
    swp (vmem_read_addr (Virtaddr va) 1 (Load Data) false false false)
      (uv_ld_post dq pt M rsA t (Values.Ok b)).
  Proof.
    intros Hinj Hl Hlok Hcanon Hb Htx Hcfg Hpins Htok Hag.
    pose proof Hcfg as (Lcp & Hms & _).
    assert (Lcp' : register_lookup cur_privilege rs = User)
      by (rewrite (Hag _ u_in_priv); exact Lcp).
    assert (Hmst : register_lookup mstatus rs = register_lookup mstatus rsA)
      by (apply Hag; exact u_in_mst).
    assert (Hep : effectivePrivilege (Load Data) (register_lookup mstatus rs) User
                  = returnM User)
      by (apply effectivePrivilege_mprv0; rewrite Hmst; exact (proj1 (proj2 Hms))).
    pose proof (u_translationMode_pure pt t rsA (uv_mmd pt M t) Hcfg Hpins) as Htm.
    pose proof (u_goodmb_translationMode_pure pt t rsA (uv_mmd pt M t)
                  (uv_mmd pt M t) Hcfg Hpins) as Htmg.
    iIntros "#Hcert Hany Hrw Hro Hrun Hown".
    rewrite /swp. iIntros (C) "%HC Hcont".
    unfold vmem_read_addr.
    rewrite (is_aligned_vaddr_1 va). sm_glue.
    rewrite mbind0_ret.
    rewrite (split_on_page_boundary_aligned_w va 1 (proj1 uload_width_1)
               (is_aligned_vaddr_1 va)).
    rewrite /returnM mliftR_ret mbind_ret. sm_glue.
    iApply (swp_use_cer (Defs.read_reg mstatus) _ _ C HC
              with "[Hrw Hro] [-]").
    { iApply (swp_read_reg_pinned u_Drw u_Dro (u_Df dq) rs _ u_disj u_in_mst
                with "Hcert Hrw Hro"). }
    iIntros (v0) "(-> & Hrw & Hro)".
    iApply (swp_use_cer (Defs.read_reg cur_privilege) _ _ C HC
              with "[Hrw Hro] [-]").
    { iApply (swp_read_reg_pinned u_Drw u_Dro (u_Df dq) rs _ u_disj u_in_priv
                with "Hcert Hrw Hro"). }
    iIntros (v0) "(-> & Hrw & Hro)". rewrite Lcp'.
    rewrite Hep.
    rewrite mliftR_ret mbind_ret. sm_glue.
    unfold Defs.and_boolM.
    iApply (swp_use_cer3 (translationMode User) _ _ _ _ C HC
              with "[Hany Hrw Hro Hrun Hown] [-]").
    { iApply (uv_swp_walk pt M M t t dq rs rsA rsA _ _
                (fun v => (⌜v = Sv39⌝ ∗
                           ∃ rs2 : regstate,
                             ⌜reg_agree_on (u_Drw ∪ u_Dro) rs2 rsA⌝ ∗
                             hreg_frame rs2 u_Drw ∗ hreg_frame_ro (u_Df dq) rs2 u_Dro ∗
                             TsoCtx.own_context XI ∗ uv_bytes pt M t ∗
                             resv_any cpu_id)%I)
                Hinj Hinj eq_refl Htok Htok eq_refl Hag Htm Htmg
                with "Hcert Hany Hrw Hro Hrun Hown").
      iIntros (rs2) "%Hag2 Hrw Hro Hrun Hown Hany".
      iSplitR; [done|]. iExists rs2. iFrame. done. }
    iIntros (v0) "(-> & Hland)".
    iDestruct "Hland" as (rs2) "(%Hag2 & Hrw & Hro & Hrun & Hown & Hany)".
    sm_glue.
    rewrite mbindR_ret.
    try (match goal with
         | |- context [ if Instances.generic_neq Sv39 Bare then ?x else ?y ] =>
             replace (if Instances.generic_neq Sv39 Bare then x else y) with x
               by (destruct (Instances.generic_neq Sv39 Bare); reflexivity)
         end).
    sm_glue.
    change (Z.gtb 0 0) with false. sm_glue.
    change (sys_misaligned_order_decreasing && false) with false. sm_glue.
    rewrite mbindR_ret. sm_glue.
    iApply (swp_use_cer
              (translate_and_read_value (Virtaddr va) 1 (Load Data)
                 false false false) _ _ C HC
              with "[Hany Hrw Hro Hrun Hown] [-]").
    { iApply (uv_swp_translate_and_read_ld1 pt M t dq rs2 rsA w_leaf va b
                Hinj Hl Hlok Hcanon Hb Htx Hcfg Hpins Htok Hag2
                with "Hcert Hany Hrw Hro Hrun Hown"). }
    iIntros (v0) "(-> & Hland)". cbn beta iota. sm_glue.
    rewrite mbind0R_ret. sm_glue.
    rewrite mbindR_ret. sm_glue.
    change (not sys_misaligned_order_decreasing && false) with false. sm_glue.
    rewrite mbindR_ret. sm_glue.
    rewrite (usvd_zeros_full_gen (8 * 1) b ltac:(lia)).
    rewrite mcer_ret.
    iApply ("Hcont" $! (Values.Ok b)). iSplitR; [done|]. iExact "Hland".
  Qed.

  (* ---- (e) [vmem_read]: the effective address (a walk over the register
     reads), then (d) *)
  Lemma uv_swp_vmem_read_ld1 (pt : uptd) (M : gmap Z (bv 8))
      (t : ptree) (dq : dfrac) (rs rsA : regstate) (w_leaf va : mword 64)
      (b : bv 8) (rs1 : mword 5) (imm : mword 12) :
    va = add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                  else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) rsA)
           (sign_extend' 64 imm) ->
    uva_inj pt M ->
    ud_um pt !! svpn_of va = Some w_leaf ->
    uleaf_ok (Load Data) w_leaf ->
    uva_canon va ->
    uM_bytes M (uint va) 1 b ->
    uva_text pt (uint va) ->
    u_data_cfg rsA ->
    u_exec_pins pt t rsA ->
    uv_tree_ok pt (upa_map pt M) t ->
    reg_agree_on (u_Drw ∪ u_Dro) rs rsA ->
    gen_cert -∗ resv_any cpu_id -∗
    hreg_frame rs u_Drw -∗ hreg_frame_ro (u_Df dq) rs u_Dro -∗
    TsoCtx.own_context XI -∗ uv_bytes pt M t -∗
    swp (vmem_read (Regidx rs1) (sign_extend' 64 imm) 1 (Load Data)
           false false false)
      (uv_ld_post dq pt M rsA t (Values.Ok b)).
  Proof.
    intros Hva Hinj Hl Hlok Hcanon Hb Htx Hcfg Hpins Htok Hag.
    pose proof Hcfg as (Lcp & Hms & Lmenv).
    pose proof Hpins as (Hhw & _ & _ & _).
    destruct Hhw as (Lmisa & _ & Lsenv & _ & _ & _).
    set (s := u_state rsA (uv_mmd pt M t)).
    assert (Hcp : register_lookup cur_privilege s.(sregs) = User) by exact Lcp.
    assert (Hmprv : eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s.(sregs)))
                      ('b"1") = false)
      by exact (proj1 (proj2 Hms)).
    pose proof (exec_effectivePrivilege_mprv0 (Load Data)
                  (register_lookup mstatus s.(sregs)) User s Hmprv) as Heff.
    pose proof (goodmb_effectivePrivilege_mprv0 Du_r Du_w (Load Data)
                  (register_lookup mstatus s.(sregs)) User s (uv_mmd pt M t) Hmprv)
      as Heffg.
    assert (Hpml : exec (get_pmlen (Load Data) User) s = Some (0, s))
      by exact (exec_get_pmlen_u (Load Data) s
                  ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                  ltac:(vm_compute; reflexivity) (proj1 (proj2 (proj2 Hms)))
                  Lmisa Lmenv Lsenv).
    assert (Hpmlg : goodmb Du_r Du_w (get_pmlen (Load Data) User) s (uv_mmd pt M t)
                    = true)
      by (apply goodmb_of_goodb;
          exact (goodb_get_pmlen_u Du_r (Load Data) s
                   ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                   ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                   ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                   ltac:(vm_compute; reflexivity) (proj1 (proj2 (proj2 Hms)))
                   Lmisa Lmenv Lsenv)).
    pose proof (u_translationMode_pure pt t rsA (uv_mmd pt M t) Hcfg Hpins) as Htm.
    pose proof (u_goodmb_translationMode_pure pt t rsA (uv_mmd pt M t)
                  (uv_mmd pt M t) Hcfg Hpins) as Htmg.
    set (base := if Z.eqb (uint rs1) 0 then zero_reg
                 else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) rsA).
    assert (Hedga : exec (ext_data_get_addr (Regidx rs1) (sign_extend' 64 imm)
                            (Load Data) 1) s
                    = Some (Ext_DataAddr_OK
                              (Virtaddr (add_vec base (sign_extend' 64 imm))), s)).
    { unfold ext_data_get_addr.
      rewrite (exec_bind_Some _ _ _ _ _ (exec_rX_bits_gpr rs1 s)).
      apply exec_returnM. }
    assert (Hgtda : exec (get_transformed_data_addr (Regidx rs1) (sign_extend' 64 imm)
                            (Load Data) 1) s
                    = Some (Ext_DataAddr_OK
                              (Virtaddr (add_vec base (sign_extend' 64 imm))), s)).
    { unfold get_transformed_data_addr.
      rewrite (exec_bind_Some _ _ _ _ _ Hedga). cbn match.
      rewrite (exec_bind_Some _ _ _ _ _
                 (exec_transform_effective_address_u (Load Data) Sv39 _ s
                    Hcp Heff Hpml Htm)).
      apply exec_returnM. }
    assert (Hgtdag : goodmb Du_r Du_w
                       (get_transformed_data_addr (Regidx rs1) (sign_extend' 64 imm)
                          (Load Data) 1) s (uv_mmd pt M t) = true).
    { unfold get_transformed_data_addr.
      assert (Hgedga : goodmb Du_r Du_w
                         (ext_data_get_addr (Regidx rs1) (sign_extend' 64 imm)
                            (Load Data) 1) s (uv_mmd pt M t) = true).
      { unfold ext_data_get_addr.
        erewrite gm_bind;
          [ | apply goodmb_rX_bits_gpr, Du_gpr_of_Z_r
            | apply (exec_rX_bits_gpr rs1 s) ].
        apply goodmb_returnm. }
      erewrite (gm_bind _ _ _ _ _ _ _ _ Hgedga Hedga). cbn match.
      erewrite (gm_bind _ _ _ _ _ _ _ _
                  (goodmb_transform_effective_address_u Du_r Du_w (Load Data) Sv39
                     _ s (uv_mmd pt M t)
                     ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                     Hcp Heff Heffg Hpml Hpmlg Htm Htmg)
                  (exec_transform_effective_address_u (Load Data) Sv39 _ s
                     Hcp Heff Hpml Htm)).
      apply goodmb_returnm. }
    iIntros "#Hcert Hany Hrw Hro Hrun Hown".
    rewrite /swp. iIntros (C) "%HC Hcont".
    unfold vmem_read.
    iApply (swp_use_cer
              (get_transformed_data_addr (Regidx rs1) (sign_extend' 64 imm)
                 (Load Data) 1) _ _ C HC
              with "[Hany Hrw Hro Hrun Hown] [-]").
    { iApply (uv_swp_walk pt M M t t dq rs rsA rsA _ _
                (fun v => (⌜v = Ext_DataAddr_OK (Virtaddr va)⌝ ∗
                           ∃ rs2 : regstate,
                             ⌜reg_agree_on (u_Drw ∪ u_Dro) rs2 rsA⌝ ∗
                             hreg_frame rs2 u_Drw ∗ hreg_frame_ro (u_Df dq) rs2 u_Dro ∗
                             TsoCtx.own_context XI ∗ uv_bytes pt M t ∗
                             resv_any cpu_id)%I)
                Hinj Hinj eq_refl Htok Htok eq_refl Hag Hgtda Hgtdag
                with "Hcert Hany Hrw Hro Hrun Hown").
      iIntros (rs2) "%Hag2 Hrw Hro Hrun Hown Hany".
      iSplitR; [iPureIntro; rewrite Hva; reflexivity|].
      iExists rs2. iFrame. done. }
    iIntros (v0) "(-> & Hland)".
    iDestruct "Hland" as (rs2) "(%Hag2 & Hrw & Hro & Hrun & Hown & Hany)".
    cbn beta iota. sm_glue.
    rewrite mbindR_ret. sm_glue.
    iApply (swp_use_cer0
              (vmem_read_addr (Virtaddr va) 1 (Load Data) false false false)
              _ C HC with "[Hany Hrw Hro Hrun Hown] [-]").
    { iApply (uv_swp_vmem_read_addr_ld1 pt M t dq rs2 rsA w_leaf va b
                Hinj Hl Hlok Hcanon Hb Htx Hcfg Hpins Htok Hag2
                with "Hcert Hany Hrw Hro Hrun Hown"). }
    iIntros (v0) "(-> & Hland)".
    iApply ("Hcont" $! (Values.Ok b)). iSplitR; [done|]. iExact "Hland".
  Qed.

  (* ---- (f) THE INSTRUCTION.  [lbu rd, imm(rs1)] at User: (e), then the
     register write (a walk), then the retire. *)
  Definition uv_lbu_post (dq : dfrac) (pt : uptd) (M : gmap Z (bv 8))
      (rsA : regstate) (t : ptree) (rd : mword 5) (wval : mword 64)
      : ExecutionResult -> iProp Σ :=
    fun r =>
      (⌜r = RETIRE_SUCCESS⌝ ∗
       ∃ (rs3 rsf : regstate) (t' : ptree),
         ⌜u_tlb_only rsA rsf⌝ ∗
         ⌜reg_agree_on (u_Drw ∪ u_Dro) rs3 (uv_post_rs rsf None (Some (rd, wval)))⌝ ∗
         ⌜tlb_ok_pt (mword_of_int 0) t' (register_lookup tlb rsf)⌝ ∗
         ⌜uv_tree_ok pt (upa_map pt M) t'⌝ ∗
         ⌜pt_same_shape 2 t t'⌝ ∗
         hreg_frame rs3 u_Drw ∗ hreg_frame_ro (u_Df dq) rs3 u_Dro ∗
         TsoCtx.own_context XI ∗ uv_bytes pt M t' ∗ resv_any cpu_id)%I.

  Lemma uv_swp_lbu_text (pt : uptd) (M : gmap Z (bv 8)) (t : ptree)
      (dq : dfrac) (rsA : regstate) (w_leaf va : mword 64) (b : mword 8)
      (imm : mword 12) (rs1 rd : mword 5) :
    uint rd <> 0 ->
    va = add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                  else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) rsA)
           (sign_extend' 64 imm) ->
    uva_inj pt M ->
    ud_um pt !! svpn_of va = Some w_leaf ->
    uleaf_ok (Load Data) w_leaf ->
    uva_canon va ->
    uM_bytes M (uint va) 1 b ->
    uva_text pt (uint va) ->
    u_data_cfg rsA ->
    u_exec_pins pt t rsA ->
    uv_tree_ok pt (upa_map pt M) t ->
    gen_cert -∗ resv_any cpu_id -∗
    hreg_frame rsA u_Drw -∗ hreg_frame_ro (u_Df dq) rsA u_Dro -∗
    TsoCtx.own_context XI -∗ uv_bytes pt M t -∗
    swp (execute (LOAD (imm, Regidx rs1, Regidx rd, true, 1)))
      (uv_lbu_post dq pt M rsA t rd (extend_value true b)).
  Proof.
    intros Hrd Hva Hinj Hl Hlok Hcanon Hb Htx Hcfg Hpins Htok.
    iIntros "#Hcert Hany Hrw Hro Hrun Hown".
    change (execute (LOAD (imm, Regidx rs1, Regidx rd, true, 1)))
      with (execute_LOAD imm (Regidx rs1) (Regidx rd) true 1).
    unfold execute_LOAD.
    change (Z.leb 1 xlen_bytes) with true.
    cbn beta iota zeta delta [Defs.assert_exp'].
    rewrite /returnM mbind_ret. sm_glue.
    iApply (swp_bind_use _ _ (uv_ld_post dq pt M rsA t (Values.Ok b)) _
              with "[Hany Hrw Hro Hrun Hown] [-]").
    { iApply (uv_swp_vmem_read_ld1 pt M t dq rsA rsA w_leaf va b rs1 imm Hva
                Hinj Hl Hlok Hcanon Hb Htx Hcfg Hpins Htok
                ltac:(intros r _; reflexivity)
                with "Hcert Hany Hrw Hro Hrun Hown"). }
    iIntros (v0) "(-> & Hland)". cbn beta iota.
    iDestruct "Hland" as (rs2 rsf t')
      "(%Tr & %Hag2 & %Htlbok' & %Htok' & %Hshape & Hrw & Hro & Hrun & Hown & Hany)".
    set (wval := extend_value true b).
    assert (Hex : exec (wX_bits (Regidx rd) wval) (u_state rsf (uv_mmd pt M t'))
                  = Some (tt, u_state (uv_post_rs rsf None (Some (rd, wval)))
                                (uv_mmd pt M t'))).
    { rewrite (exec_wX_bits_gpr rd wval (u_state rsf (uv_mmd pt M t'))).
      destruct (Z.eqb (uint rd) 0) eqn:E;
        [ exfalso; apply Hrd; apply Z.eqb_eq; exact E | ].
      reflexivity. }
    assert (Hexg : goodmb Du_r Du_w (wX_bits (Regidx rd) wval)
                     (u_state rsf (uv_mmd pt M t')) (uv_mmd pt M t') = true)
      by exact (goodmb_wX_bits_gpr Du_r Du_w rd wval (u_state rsf (uv_mmd pt M t'))
                  (uv_mmd pt M t') (fun H => Du_gpr_of_Z rd H)).
    iApply (swp_bind0_use (wX_bits (Regidx rd) wval) _
              (fun _ => (∃ rs3 : regstate,
                          ⌜reg_agree_on (u_Drw ∪ u_Dro) rs3
                             (uv_post_rs rsf None (Some (rd, wval)))⌝ ∗
                          hreg_frame rs3 u_Drw ∗ hreg_frame_ro (u_Df dq) rs3 u_Dro ∗
                          TsoCtx.own_context XI ∗ uv_bytes pt M t' ∗
                          resv_any cpu_id)%I) _
              with "[Hany Hrw Hro Hrun Hown] [-]").
    { iApply (uv_swp_walk pt M M t' t' dq rs2 rsf
                (uv_post_rs rsf None (Some (rd, wval))) _ _ _
                Hinj Hinj eq_refl Htok' Htok' eq_refl Hag2 Hex Hexg
                with "Hcert Hany Hrw Hro Hrun Hown").
      iIntros (rs3) "%Hag3 Hrw Hro Hrun Hown Hany". iExists rs3. iFrame. done. }
    iIntros (u) "Hland".
    iDestruct "Hland" as (rs3) "(%Hag3 & Hrw & Hro & Hrun & Hown & Hany)".
    iApply swp_ret. rewrite /uv_lbu_post. iSplitR; [done|].
    iExists rs3, rsf, t'. iFrame "Hrw Hro Hrun Hown Hany".
    iPureIntro. split_and!;
      [exact Tr | exact Hag3 | exact Htlbok' | exact Htok' | exact Hshape].
  Qed.

End UmodeTextLoad.
