(* UserretPt.v -- the userret trampoline-step leaves over [utlb_inv_pt],
   per node.

   userret runs ON the trampoline page with the USER table installed, so
   every instruction fetch goes through the user table's trampoline leaf
   (the [UptWalkPt.wp_instr_u_pt] engine) and the trapframe loads go
   through its TRAPFRAME leaf ([UptWalkPt.utf_translate]) -- which is
   exactly the shape [HartSMem]'s mode-generic data engines take their
   translation in, so the load leaf below is [WpSmodePtMem.wp_ld_s_r_t]
   with the regime's translation swapped for the user table's and the
   physical word [tfpa ↦ₚ₈] in place of the claim-carrying [↦₈].

   - [wp_uld_pt]  : ld rd, imm(a0)  via the trapframe leaf;
   - [wp_ualu_pt] : any a0-writing ALU instruction (register-only);
   - [wp_usret_pt]: sret to USER. *)
From Stdlib Require Import ZArith Bool Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
From iris.base_logic.lib Require Import gen_heap ghost_map ghost_var invariants.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvModelBytes RiscvLang RiscvPtsto RiscvExec RiscvTryStep RiscvFetchExec RiscvExtras.
Require Import MinstretInv InstrBytes.
Require Import ExecCommon WpGpr WpMmodeLeafBase.
Require Import Pt4kWalk TrampPt.
Require Import UptTree.
Require Import HartLift HartSpan HartSpanChar HartSwp HartSMem.
Require Import WpSmodePtEngine KptGoodb HartGoodb WpDecodeBridge HartRegNode.
Require Import UptWalkPt.
Require Import UserretDefs MstatusBits WpDecode WpGprMret.
Require Import RegFile.
Require Import Riscv.rv64d_types Riscv.rv64d.
From Kernel Require KernelSyms.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Local Open Scope Z_scope.
Import Defs.


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
  Context `{!riscvGS Σ, !xv6G Σ}.
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
    iIntros "#Hhw #Hminv Hhs Hpriv Hms Hmie Hmdl Hmenv Hutlb
             Hpc Hfile Hinstr Hbw Hcont".
    iDestruct (hw_config_cert with "Hhw") as "#Hcert".
    iDestruct (phys_word_pointsto_ram with "Hbw") as %Hram_tf.
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & #Hsenv & %HmisaS & %HmisaC &
        %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np & %HmisaA &
        %Hmisa_val0 & %Hmseccfg_val0 & #Hkmapb)".
    subst misa0.
    (* the data effective address IS the trapframe va, and the word it
       lands on is the leaf's own [tfpa] *)
    assert (Hea : add_vec (m !!! Regidx (mword_of_int 10 : mword 5))
                    (sign_extend' 64 imm) = iva)
      by (rewrite Ha0; exact Heva).
    assert (Hpalign8 : is_aligned_paddr (Physaddr tfpa) 8 = true)
      by exact (tfcat_aligned8 tfp _ Hmod8).
    assert (Hev : extend_value (n := 8 * 8) false v = v)
      by (unfold extend_value; apply sign_extend'_id).
    iApply (wp_instr_u_pt uroot tfp um va pa is_rvc
              (LOAD (imm, Regidx (mword_of_int 10), Regidx rd, false, 8))
              mstatus0 mie_v mdv0 menvcfg0 mie_v menvcfg0
              (fun npc ms1 mdv1 =>
                 (⌜npc = add_vec_int va (if is_rvc then 2 else 4)⌝ ∗
                  ⌜ms1 = mstatus0⌝ ∗ ⌜mdv1 = mdv0⌝ ∗
                  gpr_file (<[Regidx rd := regval_into_reg v]> m) ∗
                  tfpa ↦ₚ₈{ dqm } v)%I)
              (dq := dq) HSIE HMPRV HSXL Hmm HPBMTE Hmenvval0
              Hcanon Hvpn Hident Hcanon2 Hvpn2 Hident2 Hva2 Hpa4va4
              with "Hhw Hminv Hhs Hpriv Hms Hmie Hmdl Hmenv Hutlb Hpc Hinstr
                    [Hfile Hbw] [Hcont]").
    - (* THE LEAF, at the bundle's cells and the walk's landing tlb value *)
      iIntros (satp0 pcfg paddr tv') "%Hsok %Hpok
        Hpriv Hms Hmie Hmdl Hmenv Hsatp Hpcfg Hpaddr Htlbc HRes Hclk HPC HnPC
        Hresv".
      pose proof Hpok as (HA & Hord & HX & HW & HR & Hcov).
      iDestruct (sda_frames_in dq mstatus0 menvcfg0 satp0 pmar0 pcfg paddr tv'
                   with "Htlbc Hms Hpriv Hmenv Hsatp Hpma Hpcfg Hpaddr Hhtif
                         Hmisa") as "[Hrw Hro]".
      iAssert (upt_res_pt uroot tfp um
                 (register_lookup tlb
                    (sda_rs mstatus0 menvcfg0 satp0 pmar0 pcfg paddr tv')))
        with "[HRes]" as "HRes".
      { rewrite sda_rs_tlb. iExact "HRes". }
      assert (Lmxr : eq_vec (_get_Mstatus_MXR (register_lookup mstatus
                (sda_rs mstatus0 menvcfg0 satp0 pmar0 pcfg paddr tv'))) ('b"0") = true)
        by (rewrite sda_rs_mst; exact HMXR).
      assert (Lpmm : pmm_mode_backwards (_get_MEnvcfg_PMM (register_lookup menvcfg
                (sda_rs mstatus0 menvcfg0 satp0 pmar0 pcfg paddr tv'))) = PMM_Disabled)
        by (rewrite sda_rs_menv; exact Hpmm).
      assert (Lsxl : _get_Mstatus_SXL (register_lookup mstatus
                (sda_rs mstatus0 menvcfg0 satp0 pmar0 pcfg paddr tv')) = 'b"10")
        by (rewrite sda_rs_mst; exact HSXL).
      assert (Lmd : satpMode_of_bits RV64 (_get_Satp64_Mode (Mk_Satp64
                (register_lookup satp
                   (sda_rs mstatus0 menvcfg0 satp0 pmar0 pcfg paddr tv'))))
              = Some Sv39)
        by (rewrite sda_rs_satp; exact (upt_swp_mode_ok uroot satp0 Hsok)).
      assert (Lep : effectivePrivilege (Load Data)
                (register_lookup mstatus
                   (sda_rs mstatus0 menvcfg0 satp0 pmar0 pcfg paddr tv'))
                Supervisor = returnM Supervisor)
        by (rewrite sda_rs_mst;
            exact (effectivePrivilege_mprv0 (Load Data) _ Supervisor HMPRV)).
      assert (Lalign : is_aligned_vaddr (Virtaddr
                (add_vec (m !!! Regidx (mword_of_int 10 : mword 5))
                   (sign_extend' 64 imm))) 8 = true)
        by (rewrite Hea; exact Halignd).
      assert (Lvpn : svpn_of (add_vec (m !!! Regidx (mword_of_int 10 : mword 5))
                       (sign_extend' 64 imm)) = tf_vpn)
        by (rewrite Hea; exact Hvpnd).
      assert (Lcanon : neq_vec (bits_of_virtaddr (Virtaddr
                (add_vec (m !!! Regidx (mword_of_int 10 : mword 5))
                   (sign_extend' 64 imm))))
                (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr
                   (add_vec (m !!! Regidx (mword_of_int 10 : mword 5))
                      (sign_extend' 64 imm)))) (Z.sub 39 1) 0)) = false)
        by (rewrite Hea; exact Hcanond).
      assert (Lid : zero_extend' 64 (concat_vec tfp
                (subrange_vec_dec (bits_of_virtaddr (Virtaddr
                   (add_vec (m !!! Regidx (mword_of_int 10 : mword 5))
                      (sign_extend' 64 imm)))) (Z.sub pagesize_bits 1) 0)) = tfpa)
        by (rewrite Hea; reflexivity).
      iDestruct "Hresv" as (rr) "Hfrag".
      change (execute (LOAD (imm, Regidx (mword_of_int 10), Regidx rd, false, 8)))
        with (execute_LOAD imm (Regidx (mword_of_int 10)) (Regidx rd) false 8).
      iApply (swp_mono with "[Hmie Hmdl Hclk HPC HnPC] [-]").
      2:{ iApply (swp_execute_LOAD_ram_S8 sda_Drw sda_Dro (sda_Df dq)
                    (sda_rs mstatus0 menvcfg0 satp0 pmar0 pcfg paddr tv')
                    imm (mword_of_int 10) rd false m tfpa pmar0 pcfg paddr v
                    (tfpa ↦ₚ₈{ dqm } v)%I
                    (fun rs => upt_res_pt uroot tfp um (register_lookup tlb rs))
                    rr Sv39
                    sda_disj sda_in_mst sda_in_priv sda_in_menv sda_in_satp
                    sda_in_pma sda_in_pcfg sda_in_paddr sda_in_htif
                    (sda_rs_priv _ _ _ _ _ _ _) (sda_rs_htif _ _ _ _ _ _ _)
                    (sda_rs_pma _ _ _ _ _ _ _) (sda_rs_pcfg _ _ _ _ _ _ _)
                    (sda_rs_paddr _ _ _ _ _ _ _)
                    Lmxr Lpmm Lsxl
                    (hval_transform_effective_address_S_mode
                       (sda_Drw ∪ sda_Dro) sda_Drw
                       (sda_rs mstatus0 menvcfg0 satp0 pmar0 pcfg paddr tv')
                       (add_vec (m !!! Regidx (mword_of_int 10 : mword 5))
                          (sign_extend' 64 imm))
                       (Load Data) Sv39
                       sda_in_mst sda_in_priv sda_in_menv sda_in_satp
                       (sda_rs_priv _ _ _ _ _ _ _)
                       Lep eq_refl eq_refl eq_refl Lmxr Lpmm Lsxl Lmd)
                    (hval_translationMode_S_mode (sda_Drw ∪ sda_Dro) sda_Drw
                       (sda_rs mstatus0 menvcfg0 satp0 pmar0 pcfg paddr tv')
                       Sv39 sda_in_mst sda_in_satp Lsxl Lmd)
                    Lep HA Hord HR Hcov (pma_all_ram Hpma_all) Hram_tf
                    Lalign Hpalign8 Hrd
                    with "Hcert Hfrag HRes Hfile Hrw Hro [] [Hbw]").
          - (* THE DATA TRANSLATION, the user table's own *)
            iIntros "Hfrag HRes Hrw Hro".
            iApply (utf_translate (Load Data) sda_Drw sda_Dro (sda_Df dq)
                      (sda_rs mstatus0 menvcfg0 satp0 pmar0 pcfg paddr tv')
                      uroot tfp um
                      (add_vec (m !!! Regidx (mword_of_int 10 : mword 5))
                         (sign_extend' 64 imm))
                      tfpa satp0 mstatus0 pcfg paddr pmar0 rr
                      (or_introl eq_refl) sda_disj upt_Dr_in_sda upt_Dw_in_sda
                      (sda_rs_misa _ _ _ _ _ _ _)
                      ltac:(rewrite sda_rs_menv; exact Hmenvval0)
                      (sda_rs_htif _ _ _ _ _ _ _)
                      (sda_rs_priv _ _ _ _ _ _ _)
                      (sda_rs_mst _ _ _ _ _ _ _)
                      HSXL HMPRV
                      (sda_rs_satp _ _ _ _ _ _ _)
                      (sda_rs_pcfg _ _ _ _ _ _ _)
                      (sda_rs_paddr _ _ _ _ _ _ _)
                      (sda_rs_pma _ _ _ _ _ _ _)
                      Hsok Hpok Hpma_all Lvpn Lcanon Lid
                      with "Hcert Hfrag HRes Hrw Hro").
          - (* THE RAM OBLIGATION, off the physical word the leaf owns *)
            iIntros (sigma) "Hsi".
            iDestruct "Hsi" as "[Hreg [Hmem Hdev]]".
            iDestruct "Hbw" as "[%Hbal Hbytes]".
            iAssert (⌜forall j : nat, (N.of_nat j < 8)%N ->
                       sigma.(mem) !! (pa_add tfpa j) = Some (nth_byte v j)⌝)%I
              as %Hbf.
            { iIntros (j Hj). assert (Hj' : (j < 8)%nat) by lia.
              iDestruct (big_sepL_lookup _ _ j j with "Hbytes") as "Hbj".
              { rewrite lookup_seq_lt; [reflexivity | exact Hj']. }
              iDestruct (phys_valid with "Hmem Hbj") as %Hmj.
              iPureIntro. exact Hmj. }
            iMod (fupd_mask_subseteq ∅) as "Hclose"; [set_solver|].
            iModIntro. iSplitR; [iPureIntro; exact Hbf |].
            iNext. iMod "Hclose" as "_". iModIntro.
            iFrame "Hreg Hmem Hdev".
            rewrite /phys_word_pointsto. iFrame "Hbytes".
            iPureIntro. exact Hbal. }
      iIntros (e) "(-> & Hfile & Hland)".
      iDestruct "Hland" as (rsf) "(%Hshape & Hrw & Hro & HRes & Hany & Hword)".
      iAssert (∃ tv2 : type_of_register tlb,
                 hreg_frame (sda_rs mstatus0 menvcfg0 satp0 pmar0 pcfg paddr tv2)
                   sda_Drw ∗
                 hreg_frame_ro (sda_Df dq)
                   (sda_rs mstatus0 menvcfg0 satp0 pmar0 pcfg paddr tv2) sda_Dro ∗
                 upt_res_pt uroot tfp um tv2)%I
        with "[Hrw Hro HRes]" as (tv2) "(Hrw & Hro & HRes)".
      { destruct Hshape as [-> | (tvx & ->)].
        - iExists tv'. iFrame "Hrw Hro".
          iEval (rewrite sda_rs_tlb) in "HRes". iExact "HRes".
        - iExists tvx.
          iDestruct (sda_rw_ext _ _ (sda_set_tlb mstatus0 menvcfg0 satp0 pmar0
                       pcfg paddr tv' tvx) with "Hrw") as "Hrw".
          iDestruct (sda_ro_ext _ _ _ (sda_set_tlb mstatus0 menvcfg0 satp0 pmar0
                       pcfg paddr tv' tvx) with "Hro") as "Hro".
          iFrame "Hrw Hro".
          iEval (rewrite register_lookup_set) in "HRes". iExact "HRes". }
      iDestruct (sda_frames_out dq mstatus0 menvcfg0 satp0 pmar0 pcfg paddr tv2
                   with "[$Hrw $Hro]")
        as "(Htlbc & Hms & Hpriv & Hmenv & Hsatp & _ & Hpcfg & Hpaddr & _ & _)".
      iSplitR; [done|].
      iFrame "Hpriv Hmie Hmenv Hsatp Hpcfg Hpaddr".
      iSplitL "Htlbc HRes". { iExists tv2. iFrame "Htlbc HRes". }
      iFrame "Hclk".
      iSplitR "Hany"; [| iExact "Hany"].
      iExists mstatus0, mdv0, (add_vec_int va (if is_rvc then 2 else 4)).
      iFrame "Hms Hmdl HPC HnPC".
      iSplitR; [done|]. iSplitR; [done|]. iSplitR; [done|].
      rewrite Hev. iFrame "Hfile Hword".
    - iNext. iIntros (npc ms1 mdv1)
        "Hhs Hpriv Hms Hmie Hmdl Hmenv Hutlb Hpc
         (-> & -> & -> & Hfile & Hword)".
      iApply ("Hcont" with "Hhs Hpriv Hms Hmie Hmdl Hmenv Hutlb Hpc Hfile
                            Hword").
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


(* ===================================================================== *)
(* §5  THE SRET-TO-USER FOOTPRINT.                                        *)
(*                                                                       *)
(* [WpSmodePtEngine]'s six-cell sret frame plus [senvcfg]: at [newpriv =  *)
(* User] the landing-pad probe is [get_xLPE User], which reads the        *)
(* SUPERVISOR envcfg through [read_senvcfg] rather than [menvcfg]         *)
(* directly, so senvcfg is in the read set and must be in the frame.      *)
(* [hw_config] pins it (discarded, at 0), so it costs the caller nothing. *)
(* Everything else is the S walk one privilege over.                      *)
(* ===================================================================== *)

Definition usret_Drw : gset register :=
  {[ (mstatus : register); (cur_privilege : register);
     (R_bitvector_64 nextPC : register) ]}.
Definition usret_Dro : gset register :=
  {[ (misa : register); (menvcfg : register); (sepc : register);
     (senvcfg : register) ]}.
Definition usret_Df : register -> dfrac := fun r =>
  if decide (r = (misa : register)) then DfracDiscarded
  else if decide (r = (senvcfg : register)) then DfracDiscarded
  else DfracOwn 1.

Definition usret_rs (ms : mword 64) (p : Privilege)
    (npc menv sep senv : mword 64) : regstate :=
  register_set mstatus ms
  (register_set cur_privilege p
  (register_set (R_bitvector_64 nextPC) npc
  (register_set misa MISA_C
  (register_set menvcfg menv
  (register_set sepc sep
  (register_set senvcfg senv init_regstate)))))).

Local Ltac urtm := rewrite irrelevant_register_set; [ | vm_compute; reflexivity ].

Lemma usret_rs_ms ms p npc menv sep senv :
  register_lookup mstatus (usret_rs ms p npc menv sep senv) = ms.
Proof. rewrite /usret_rs. apply register_lookup_set. Qed.
Lemma usret_rs_priv ms p npc menv sep senv :
  register_lookup cur_privilege (usret_rs ms p npc menv sep senv) = p.
Proof. rewrite /usret_rs. urtm. apply register_lookup_set. Qed.
Lemma usret_rs_npc ms p npc menv sep senv :
  register_lookup (R_bitvector_64 nextPC) (usret_rs ms p npc menv sep senv) = npc.
Proof. rewrite /usret_rs. urtm. urtm. apply register_lookup_set. Qed.
Lemma usret_rs_misa ms p npc menv sep senv :
  register_lookup misa (usret_rs ms p npc menv sep senv) = MISA_C.
Proof. rewrite /usret_rs. urtm. urtm. urtm. apply register_lookup_set. Qed.
Lemma usret_rs_menv ms p npc menv sep senv :
  register_lookup menvcfg (usret_rs ms p npc menv sep senv) = menv.
Proof. rewrite /usret_rs. urtm. urtm. urtm. urtm. apply register_lookup_set. Qed.
Lemma usret_rs_sepc ms p npc menv sep senv :
  register_lookup sepc (usret_rs ms p npc menv sep senv) = sep.
Proof.
  rewrite /usret_rs. urtm. urtm. urtm. urtm. urtm. apply register_lookup_set.
Qed.
Lemma usret_rs_senv ms p npc menv sep senv :
  register_lookup senvcfg (usret_rs ms p npc menv sep senv) = senv.
Proof.
  rewrite /usret_rs. urtm. urtm. urtm. urtm. urtm. urtm.
  apply register_lookup_set.
Qed.

Lemma usret_disj : usret_Drw ## usret_Dro.
Proof. rewrite /usret_Drw /usret_Dro. set_solver. Qed.

Lemma usret_in_ms : (mstatus : register) ∈ usret_Drw ∪ usret_Dro.
Proof. rewrite /usret_Drw. set_solver. Qed.
Lemma usret_in_priv : (cur_privilege : register) ∈ usret_Drw ∪ usret_Dro.
Proof. rewrite /usret_Drw. set_solver. Qed.
Lemma usret_in_npc : (R_bitvector_64 nextPC : register) ∈ usret_Drw ∪ usret_Dro.
Proof. rewrite /usret_Drw. set_solver. Qed.
Lemma usret_in_misa : (misa : register) ∈ usret_Drw ∪ usret_Dro.
Proof. rewrite /usret_Dro. set_solver. Qed.
Lemma usret_in_menv : (menvcfg : register) ∈ usret_Drw ∪ usret_Dro.
Proof. rewrite /usret_Dro. set_solver. Qed.
Lemma usret_in_sepc : (sepc : register) ∈ usret_Drw ∪ usret_Dro.
Proof. rewrite /usret_Dro. set_solver. Qed.
Lemma usret_in_senv : (senvcfg : register) ∈ usret_Drw ∪ usret_Dro.
Proof. rewrite /usret_Dro. set_solver. Qed.
Lemma usret_w_ms : (mstatus : register) ∈ usret_Drw.
Proof. rewrite /usret_Drw. set_solver. Qed.
Lemma usret_w_priv : (cur_privilege : register) ∈ usret_Drw.
Proof. rewrite /usret_Drw. set_solver. Qed.
Lemma usret_w_npc : (R_bitvector_64 nextPC : register) ∈ usret_Drw.
Proof. rewrite /usret_Drw. set_solver. Qed.

Local Ltac urdf :=
  unfold usret_Df;
  repeat first [ rewrite decide_True; [reflexivity|reflexivity]
               | rewrite decide_False; [|discriminate] ];
  reflexivity.
Lemma usret_Df_misa : usret_Df misa = DfracDiscarded.
Proof. urdf. Qed.
Lemma usret_Df_menv : usret_Df menvcfg = DfracOwn 1.
Proof. urdf. Qed.
Lemma usret_Df_sepc : usret_Df sepc = DfracOwn 1.
Proof. urdf. Qed.
Lemma usret_Df_senv : usret_Df senvcfg = DfracDiscarded.
Proof. urdf. Qed.

Local Ltac urag :=
  intros r Hr; rewrite /usret_Drw /usret_Dro in Hr;
  repeat (apply elem_of_union in Hr as [Hr|Hr]);
  apply elem_of_singleton in Hr; subst r;
  first [ rewrite register_lookup_set | urtm ];
  rewrite ?usret_rs_ms ?usret_rs_priv ?usret_rs_npc ?usret_rs_misa
          ?usret_rs_menv ?usret_rs_sepc ?usret_rs_senv;
  reflexivity.

Lemma usret_set_ms (ms ms' : mword 64) p npc menv sep senv :
  reg_agree_on (usret_Drw ∪ usret_Dro)
    (register_set mstatus ms' (usret_rs ms p npc menv sep senv))
    (usret_rs ms' p npc menv sep senv).
Proof. urag. Qed.

Lemma usret_set_priv (ms : mword 64) p p' npc menv sep senv :
  reg_agree_on (usret_Drw ∪ usret_Dro)
    (register_set cur_privilege p' (usret_rs ms p npc menv sep senv))
    (usret_rs ms p' npc menv sep senv).
Proof. urag. Qed.

Lemma usret_set_npc (ms : mword 64) p npc npc' menv sep senv :
  reg_agree_on (usret_Drw ∪ usret_Dro)
    (register_set (R_bitvector_64 nextPC) npc' (usret_rs ms p npc menv sep senv))
    (usret_rs ms p npc' menv sep senv).
Proof. urag. Qed.

(* the landing-pad probe at User: [currentlyEnabled Ext_S] (misa) and then
   [read_senvcfg] (senvcfg, menvcfg, senvcfg).  [WpDecodeBridge.dstateS] is
   the reference state -- misa = MISA_C, menvcfg = MENVCFG_S and every other
   config CSR (senvcfg included) zero -- so both [goodb] and the concrete
   [exec] are [vm_compute]. *)
Definition uD_lpe (r : register) : bool :=
  orb (register_beq r (misa : register))
 (orb (register_beq r (menvcfg : register))
      (register_beq r (senvcfg : register))).

Section UsretSwp.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Lemma hval_get_xLPE_U (D Drw : gset register) (rs : regstate) :
    (misa : register) ∈ D -> (menvcfg : register) ∈ D ->
    (senvcfg : register) ∈ D ->
    register_lookup misa rs = MISA_C ->
    register_lookup menvcfg rs = MENVCFG_S ->
    register_lookup senvcfg rs = mword_of_int 0 ->
    hval D Drw rs (get_xLPE User) false rs.
  Proof.
    intros HDm HDe HDs Hmisa Hmenv Hsenv.
    apply (hval_of_goodb uD_lpe D Drw _ dstateS rs false).
    - intros r Hr. unfold uD_lpe in Hr.
      repeat (apply orb_prop in Hr; destruct Hr as [Hr|Hr]);
        apply register_beq_eq in Hr; subst r; assumption.
    - intros r Hr. unfold uD_lpe in Hr.
      repeat (apply orb_prop in Hr; destruct Hr as [Hr|Hr]);
        apply register_beq_eq in Hr; subst r;
        first [ rewrite Hmisa | rewrite Hmenv | rewrite Hsenv ];
        vm_compute; reflexivity.
    - vm_compute; reflexivity.
    - apply exec_get_xLPE_U;
        [ vm_compute; reflexivity
        | vm_compute; reflexivity
        | vm_compute; reflexivity ].
  Qed.

  Lemma usret_frames (ms : mword 64) (p : Privilege)
      (npc menv sep senv : mword 64) :
    (hreg_frame (usret_rs ms p npc menv sep senv) usret_Drw ∗
     hreg_frame_ro usret_Df (usret_rs ms p npc menv sep senv) usret_Dro
     : iProp Σ)
    ⊣⊢ (reg_pointsto mstatus (DfracOwn 1) ms ∗
        reg_pointsto cur_privilege (DfracOwn 1) p ∗
        reg_pointsto (R_bitvector_64 nextPC) (DfracOwn 1) npc ∗
        reg_pointsto misa DfracDiscarded MISA_C ∗
        reg_pointsto menvcfg (DfracOwn 1) menv ∗
        reg_pointsto sepc (DfracOwn 1) sep ∗
        reg_pointsto senvcfg DfracDiscarded senv).
  Proof.
    rewrite /hreg_frame /hreg_frame_ro /usret_Drw /usret_Dro.
    repeat (rewrite big_sepS_union; last set_solver).
    rewrite !big_sepS_singleton.
    rewrite usret_rs_ms usret_rs_priv usret_rs_npc usret_rs_misa
            usret_rs_menv usret_rs_sepc usret_rs_senv.
    rewrite usret_Df_misa usret_Df_menv usret_Df_sepc usret_Df_senv.
    by rewrite !bi.sep_assoc.
  Qed.

  Lemma usret_frames_in (ms : mword 64) (p : Privilege)
      (npc menv sep senv : mword 64) :
    reg_pointsto mstatus (DfracOwn 1) ms -∗
    reg_pointsto cur_privilege (DfracOwn 1) p -∗
    reg_pointsto (R_bitvector_64 nextPC) (DfracOwn 1) npc -∗
    reg_pointsto misa DfracDiscarded MISA_C -∗
    reg_pointsto menvcfg (DfracOwn 1) menv -∗
    reg_pointsto sepc (DfracOwn 1) sep -∗
    reg_pointsto senvcfg DfracDiscarded senv -∗
    (hreg_frame (usret_rs ms p npc menv sep senv) usret_Drw ∗
     hreg_frame_ro usret_Df (usret_rs ms p npc menv sep senv) usret_Dro
     : iProp Σ).
  Proof.
    iIntros "H1 H2 H3 H4 H5 H6 H7". rewrite usret_frames. iFrame.
  Qed.

  Lemma usret_frames_out (ms : mword 64) (p : Privilege)
      (npc menv sep senv : mword 64) :
    (hreg_frame (usret_rs ms p npc menv sep senv) usret_Drw ∗
     hreg_frame_ro usret_Df (usret_rs ms p npc menv sep senv) usret_Dro
     : iProp Σ) -∗
    (reg_pointsto mstatus (DfracOwn 1) ms ∗
     reg_pointsto cur_privilege (DfracOwn 1) p ∗
     reg_pointsto (R_bitvector_64 nextPC) (DfracOwn 1) npc ∗
     reg_pointsto misa DfracDiscarded MISA_C ∗
     reg_pointsto menvcfg (DfracOwn 1) menv ∗
     reg_pointsto sepc (DfracOwn 1) sep ∗
     reg_pointsto senvcfg DfracDiscarded senv).
  Proof. rewrite usret_frames. iIntros "H". iExact "H". Qed.

  Lemma usret_rw_ext (rs rs' : regstate) :
    reg_agree_on (usret_Drw ∪ usret_Dro) rs rs' ->
    hreg_frame rs usret_Drw -∗ (hreg_frame rs' usret_Drw : iProp Σ).
  Proof.
    intros Hag. rewrite (hreg_frame_ext _ _ usret_Drw
      (reg_agree_mono (usret_Drw ∪ usret_Dro) usret_Drw _ _
         ltac:(set_solver) Hag)).
    iIntros "H". iExact "H".
  Qed.

  Lemma usret_ro_ext (rs rs' : regstate) :
    reg_agree_on (usret_Drw ∪ usret_Dro) rs rs' ->
    hreg_frame_ro usret_Df rs usret_Dro -∗
    (hreg_frame_ro usret_Df rs' usret_Dro : iProp Σ).
  Proof.
    intros Hag. rewrite (hreg_frame_ro_ext usret_Df _ _ usret_Dro
      (reg_agree_mono (usret_Drw ∪ usret_Dro) usret_Dro _ _
         ltac:(set_solver) Hag)).
    iIntros "H". iExact "H".
  Qed.

  (* [WpSmodePtEngine.swp_zicfilp_sRET_S] at [y := User]: the SPELP clear is
     the same two mstatus reads and one write, and the probe is the User one. *)
  Lemma swp_zicfilp_sRET_U (ms : mword 64) (p : Privilege)
      (npc sep : mword 64) :
    gen_cert -∗
    reg_pointsto elp DfracDiscarded (landing_pad_bits_backwards NO_LP_EXPECTED) -∗
    hreg_frame (usret_rs ms p npc MENVCFG_S sep (mword_of_int 0)) usret_Drw -∗
    hreg_frame_ro usret_Df
      (usret_rs ms p npc MENVCFG_S sep (mword_of_int 0)) usret_Dro -∗
    swp (zicfilp_restore_elp_on_xret sRET User)
      (fun _ => hreg_frame
                  (usret_rs (sret_elpclr ms) p npc MENVCFG_S sep
                     (mword_of_int 0)) usret_Drw ∗
                hreg_frame_ro usret_Df
                  (usret_rs (sret_elpclr ms) p npc MENVCFG_S sep
                     (mword_of_int 0)) usret_Dro).
  Proof.
    iIntros "#Hcert #Help Hrw Hro".
    unfold zicfilp_restore_elp_on_xret. cbn match.
    iApply (swp_bind_use _ _
              (fun x => ⌜x = _get_Mstatus_SPELP ms⌝ ∗
                hreg_frame (usret_rs (sret_elpclr ms) p npc MENVCFG_S sep
                              (mword_of_int 0)) usret_Drw ∗
                hreg_frame_ro usret_Df
                  (usret_rs (sret_elpclr ms) p npc MENVCFG_S sep
                     (mword_of_int 0)) usret_Dro)%I
              _ with "[Hrw Hro] [-]").
    { iApply (swp_bind_use _ _ _ _ with "[Hrw Hro] [-]").
      { iApply (swp_read_reg_pinned usret_Drw usret_Dro usret_Df _ mstatus
                  usret_disj usret_in_ms with "Hcert Hrw Hro"). }
      iIntros (w0) "(-> & Hrw & Hro)". rewrite usret_rs_ms. cbn zeta.
      iApply (swp_bind_use _ _ _ _ with "[Hrw Hro] [-]").
      { iApply (swp_read_reg_pinned usret_Drw usret_Dro usret_Df _ mstatus
                  usret_disj usret_in_ms with "Hcert Hrw Hro"). }
      iIntros (w1) "(-> & Hrw & Hro)". rewrite usret_rs_ms.
      iApply (swp_bind0_use _ _ _ _ with "[Hrw Hro] [-]").
      { iApply (swp_write_reg_owned usret_Drw usret_Dro usret_Df _ mstatus
                  (sret_elpclr ms) usret_disj usret_w_ms with "Hcert Hrw Hro"). }
      iIntros (u) "[Hrw Hro]".
      iDestruct (usret_rw_ext _ _ (usret_set_ms ms (sret_elpclr ms) p npc
                   MENVCFG_S sep (mword_of_int 0)) with "Hrw") as "Hrw".
      iDestruct (usret_ro_ext _ _ (usret_set_ms ms (sret_elpclr ms) p npc
                   MENVCFG_S sep (mword_of_int 0)) with "Hro") as "Hro".
      iApply swp_ret. iFrame. done. }
    iIntros (pelp) "(-> & Hrw & Hro)".
    iApply (swp_bind_use (get_xLPE User) _ _ _ with "[Hrw Hro] [-]").
    { iApply (swp_span usret_Drw usret_Dro usret_Df _ _ _ false usret_disj
                (hval_get_xLPE_U (usret_Drw ∪ usret_Dro) usret_Drw
                   (usret_rs (sret_elpclr ms) p npc MENVCFG_S sep
                      (mword_of_int 0))
                   usret_in_misa usret_in_menv usret_in_senv
                   (usret_rs_misa _ _ _ _ _ _)
                   (usret_rs_menv _ _ _ _ _ _)
                   (usret_rs_senv _ _ _ _ _ _))
                with "Hcert Hrw Hro"). }
    iIntros (b) "(-> & Hrw & Hro)". cbn zeta match.
    iApply (swp_write_reg_same elp DfracDiscarded _ _ _
              (s_hregwrite_val_at_write_reg elp _) with "Hcert Help [-]").
    iIntros "_". rewrite s_hregwrite_resume_write_reg.
    iApply swp_ret. iFrame.
  Qed.

  (* ------------------------------------------------------------------ *)
  (* THE WALK, at [newpriv = User].                                       *)
  (* [WpSmodePtEngine.swp_execute_SRET_S] one privilege over: the SPP      *)
  (* decode lands on User, so the cur_privilege write MOVES the cell, and  *)
  (* the landing-pad probe is [get_xLPE User].  Everything else --          *)
  (* [ext_check_xret_priv Supervisor], the five mstatus writes,            *)
  (* [prepare_xret_target Supervisor] -- is unchanged: SRET's TARGET       *)
  (* privilege is what moves, not the instruction's own.                   *)
  (* ------------------------------------------------------------------ *)
  Local Notation UFS ms npc sep :=
    (hreg_frame (usret_rs ms Supervisor npc MENVCFG_S sep (mword_of_int 0))
       usret_Drw ∗
     hreg_frame_ro usret_Df
       (usret_rs ms Supervisor npc MENVCFG_S sep (mword_of_int 0))
       usret_Dro)%I.

  Lemma swp_execute_SRET_U (ms_cur npc sepc0 : mword 64) :
    eq_vec (_get_Mstatus_TSR ms_cur) ('b"1") = false ->
    sret_newpriv ms_cur = User ->
    gen_cert -∗
    reg_pointsto elp DfracDiscarded (landing_pad_bits_backwards NO_LP_EXPECTED) -∗
    hreg_frame (usret_rs ms_cur Supervisor npc MENVCFG_S sepc0
                  (mword_of_int 0)) usret_Drw -∗
    hreg_frame_ro usret_Df
      (usret_rs ms_cur Supervisor npc MENVCFG_S sepc0 (mword_of_int 0))
      usret_Dro -∗
    swp (execute (SRET tt))
      (fun e => ⌜e = RETIRE_SUCCESS⌝ ∗
        hreg_frame (usret_rs (sret_ms5 ms_cur) User (ret_pc sepc0) MENVCFG_S
                      sepc0 (mword_of_int 0)) usret_Drw ∗
        hreg_frame_ro usret_Df
          (usret_rs (sret_ms5 ms_cur) User (ret_pc sepc0) MENVCFG_S sepc0
             (mword_of_int 0)) usret_Dro).
  Proof.
    intros HTSR Hsup.
    assert (Hnpm : generic_neq User Machine = true)
      by (vm_compute; reflexivity).
    iIntros "#Hcert #Help Hrw Hro".
    change (execute (SRET tt)) with (execute_SRET tt).
    unfold execute_SRET.
    (* -- cur_privilege, then the sret_illegal guard -- *)
    iApply (swp_bind_use _ _ _ _ with "[Hrw Hro] [-]").
    { iApply (swp_read_reg_pinned usret_Drw usret_Dro usret_Df _ cur_privilege
                usret_disj usret_in_priv with "Hcert Hrw Hro"). }
    iIntros (p0) "(-> & Hrw & Hro)". rewrite usret_rs_priv. cbn match.
    iApply (swp_bind_use _ _
              (fun l : bool => ⌜l = false⌝ ∗ UFS ms_cur npc sepc0)%I
              _ with "[Hrw Hro] [-]").
    { unfold or_boolM.
      iApply (swp_bind_use _ _
                (fun a : bool => ⌜a = false⌝ ∗ UFS ms_cur npc sepc0)%I
                _ with "[Hrw Hro] [-]").
      { iApply (swp_bind_use _ _ _ _ with "[Hrw Hro] [-]").
        { iApply (swp_span usret_Drw usret_Dro usret_Df _ _ _ true usret_disj
                    (hval_cE_S (usret_Drw ∪ usret_Dro) usret_Drw
                       (usret_rs ms_cur Supervisor npc MENVCFG_S sepc0
                          (mword_of_int 0))
                       usret_in_misa (usret_rs_misa _ _ _ _ _ _))
                    with "Hcert Hrw Hro"). }
        iIntros (w1) "(-> & Hrw & Hro)".
        iApply swp_ret. iSplitR; [done|]. iFrame. }
      iIntros (a) "(-> & Hrw & Hro)". cbn match.
      iApply (swp_bind_use _ _ _ _ with "[Hrw Hro] [-]").
      { iApply (swp_read_reg_pinned usret_Drw usret_Dro usret_Df _ mstatus
                  usret_disj usret_in_ms with "Hcert Hrw Hro"). }
      iIntros (w2) "(-> & Hrw & Hro)". rewrite usret_rs_ms.
      iApply swp_ret. iSplitR; [iPureIntro; exact HTSR|]. iFrame. }
    iIntros (l) "(-> & Hrw & Hro)". cbn match.
    change (ext_check_xret_priv Supervisor) with true.
    cbn [Riscv.rv64d.not negb]. cbn match.
    (* -- prev_priv -- *)
    iApply (swp_bind_use _ _ _ _ with "[Hrw Hro] [-]").
    { iApply (swp_read_reg_pinned usret_Drw usret_Dro usret_Df _ cur_privilege
                usret_disj usret_in_priv with "Hcert Hrw Hro"). }
    iIntros (pp) "(-> & Hrw & Hro)".
    (* -- w7, w8 -- *)
    iApply (swp_bind_use _ _ _ _ with "[Hrw Hro] [-]").
    { iApply (swp_read_reg_pinned usret_Drw usret_Dro usret_Df _ mstatus
                usret_disj usret_in_ms with "Hcert Hrw Hro"). }
    iIntros (w7) "(-> & Hrw & Hro)". rewrite usret_rs_ms.
    iApply (swp_bind_use _ _ _ _ with "[Hrw Hro] [-]").
    { iApply (swp_read_reg_pinned usret_Drw usret_Dro usret_Df _ mstatus
                usret_disj usret_in_ms with "Hcert Hrw Hro"). }
    iIntros (w8) "(-> & Hrw & Hro)". rewrite usret_rs_ms.
    (* -- write sret_ms1, read back -- *)
    iApply (swp_bind_use _ _ _ _ with "[Hrw Hro] [-]").
    { iApply (swp_bind0_use _ _ _ _ with "[Hrw Hro] [-]").
      { iApply (swp_write_reg_owned usret_Drw usret_Dro usret_Df _ mstatus
                  (sret_ms1 ms_cur) usret_disj usret_w_ms
                  with "Hcert Hrw Hro"). }
      iIntros (u) "[Hrw Hro]".
      iDestruct (usret_rw_ext _ _ (usret_set_ms ms_cur (sret_ms1 ms_cur)
                   Supervisor npc MENVCFG_S sepc0 (mword_of_int 0))
                   with "Hrw") as "Hrw".
      iDestruct (usret_ro_ext _ _ (usret_set_ms ms_cur (sret_ms1 ms_cur)
                   Supervisor npc MENVCFG_S sepc0 (mword_of_int 0))
                   with "Hro") as "Hro".
      iApply (swp_read_reg_pinned usret_Drw usret_Dro usret_Df _ mstatus
                usret_disj usret_in_ms with "Hcert Hrw Hro"). }
    iIntros (w9) "(-> & Hrw & Hro)". rewrite usret_rs_ms.
    (* -- write sret_ms2, read back -- *)
    iApply (swp_bind_use _ _ _ _ with "[Hrw Hro] [-]").
    { iApply (swp_bind0_use _ _ _ _ with "[Hrw Hro] [-]").
      { iApply (swp_write_reg_owned usret_Drw usret_Dro usret_Df _ mstatus
                  (sret_ms2 ms_cur) usret_disj usret_w_ms
                  with "Hcert Hrw Hro"). }
      iIntros (u) "[Hrw Hro]".
      iDestruct (usret_rw_ext _ _ (usret_set_ms (sret_ms1 ms_cur)
                   (sret_ms2 ms_cur) Supervisor npc MENVCFG_S sepc0
                   (mword_of_int 0)) with "Hrw") as "Hrw".
      iDestruct (usret_ro_ext _ _ (usret_set_ms (sret_ms1 ms_cur)
                   (sret_ms2 ms_cur) Supervisor npc MENVCFG_S sepc0
                   (mword_of_int 0)) with "Hro") as "Hro".
      iApply (swp_read_reg_pinned usret_Drw usret_Dro usret_Df _ mstatus
                usret_disj usret_in_ms with "Hcert Hrw Hro"). }
    iIntros (w10) "(-> & Hrw & Hro)". rewrite usret_rs_ms.
    (* -- the SPP decode lands on USER: the privilege write MOVES the cell -- *)
    change (if eq_vec (_get_Mstatus_SPP (sret_ms2 ms_cur)) ('b"1")
            then Supervisor else User) with (sret_newpriv ms_cur).
    rewrite Hsup.
    iApply (swp_bind_use _ _ _ _ with "[Hrw Hro] [-]").
    { iApply (swp_bind0_use _ _ _ _ with "[Hrw Hro] [-]").
      { iApply (swp_write_reg_owned usret_Drw usret_Dro usret_Df _ cur_privilege
                  User usret_disj usret_w_priv with "Hcert Hrw Hro"). }
      iIntros (u) "[Hrw Hro]".
      iDestruct (usret_rw_ext _ _ (usret_set_priv (sret_ms2 ms_cur) Supervisor
                   User npc MENVCFG_S sepc0 (mword_of_int 0))
                   with "Hrw") as "Hrw".
      iDestruct (usret_ro_ext _ _ (usret_set_priv (sret_ms2 ms_cur) Supervisor
                   User npc MENVCFG_S sepc0 (mword_of_int 0))
                   with "Hro") as "Hro".
      iApply (swp_read_reg_pinned usret_Drw usret_Dro usret_Df _ mstatus
                usret_disj usret_in_ms with "Hcert Hrw Hro"). }
    iIntros (w12) "(-> & Hrw & Hro)". rewrite usret_rs_ms.
    (* -- write sret_ms3, read cur_privilege, the newpriv guard -- *)
    iApply (swp_bind_use _ _ _ _ with "[Hrw Hro] [-]").
    { iApply (swp_bind0_use _ _ _ _ with "[Hrw Hro] [-]").
      { iApply (swp_write_reg_owned usret_Drw usret_Dro usret_Df _ mstatus
                  (sret_ms3 ms_cur) usret_disj usret_w_ms
                  with "Hcert Hrw Hro"). }
      iIntros (u) "[Hrw Hro]".
      iDestruct (usret_rw_ext _ _ (usret_set_ms (sret_ms2 ms_cur)
                   (sret_ms3 ms_cur) User npc MENVCFG_S sepc0
                   (mword_of_int 0)) with "Hrw") as "Hrw".
      iDestruct (usret_ro_ext _ _ (usret_set_ms (sret_ms2 ms_cur)
                   (sret_ms3 ms_cur) User npc MENVCFG_S sepc0
                   (mword_of_int 0)) with "Hro") as "Hro".
      iApply (swp_read_reg_pinned usret_Drw usret_Dro usret_Df _ cur_privilege
                usret_disj usret_in_priv with "Hcert Hrw Hro"). }
    iIntros (w13) "(-> & Hrw & Hro)". rewrite usret_rs_priv. rewrite Hnpm.
    cbn match.
    (* -- the MPRV clear, then hartSupports Zicfilp -- *)
    iApply (swp_bind_use _ _ _ _ with "[Hrw Hro] [-]").
    { iApply (swp_bind0_use _ _ _ _ with "[Hrw Hro] [-]").
      { iApply (swp_bind_use _ _ _ _ with "[Hrw Hro] [-]").
        { iApply (swp_read_reg_pinned usret_Drw usret_Dro usret_Df _ mstatus
                    usret_disj usret_in_ms with "Hcert Hrw Hro"). }
        iIntros (w14) "(-> & Hrw & Hro)". rewrite usret_rs_ms.
        iApply (swp_write_reg_owned usret_Drw usret_Dro usret_Df _ mstatus
                  (sret_ms4 ms_cur) usret_disj usret_w_ms
                  with "Hcert Hrw Hro"). }
      iIntros (u) "[Hrw Hro]".
      iDestruct (usret_rw_ext _ _ (usret_set_ms (sret_ms3 ms_cur)
                   (sret_ms4 ms_cur) User npc MENVCFG_S sepc0
                   (mword_of_int 0)) with "Hrw") as "Hrw".
      iDestruct (usret_ro_ext _ _ (usret_set_ms (sret_ms3 ms_cur)
                   (sret_ms4 ms_cur) User npc MENVCFG_S sepc0
                   (mword_of_int 0)) with "Hro") as "Hro".
      iApply (swp_span usret_Drw usret_Dro usret_Df _ _ _ true usret_disj
                (s_hval_hS_Zicfilp (usret_Drw ∪ usret_Dro) usret_Drw
                   (usret_rs (sret_ms4 ms_cur) User npc MENVCFG_S sepc0
                      (mword_of_int 0))
                   usret_in_misa (usret_rs_misa _ _ _ _ _ _))
                with "Hcert Hrw Hro"). }
    iIntros (w15) "(-> & Hrw & Hro)". cbn match.
    (* -- the elp reset, then read mstatus -- *)
    iApply (swp_bind_use _ _ _ _ with "[Hrw Hro] [-]").
    { iApply (swp_bind0_use _ _ _ _ with "[Hrw Hro] [-]").
      { iApply (swp_bind_use _ _ _ _ with "[Hrw Hro] [-]").
        { iApply (swp_read_reg_pinned usret_Drw usret_Dro usret_Df _
                    cur_privilege usret_disj usret_in_priv
                    with "Hcert Hrw Hro"). }
        iIntros (w16) "(-> & Hrw & Hro)". rewrite usret_rs_priv.
        iApply (swp_zicfilp_sRET_U (sret_ms4 ms_cur) User npc sepc0
                  with "Hcert Help Hrw Hro"). }
      iIntros (u) "[Hrw Hro]".
      iApply (swp_read_reg_pinned usret_Drw usret_Dro usret_Df _ mstatus
                usret_disj usret_in_ms with "Hcert Hrw Hro"). }
    iIntros (w17) "(-> & Hrw & Hro)". rewrite usret_rs_ms.
    rewrite sret_elpclr_ms5.
    (* -- the callback, the print guard, prepare_xret_target -- *)
    iApply (swp_bind_use _ _ _ _ with "[Hrw Hro] [-]").
    { iApply (swp_bind0_use _ _
                (fun _ : unit =>
                   (hreg_frame (usret_rs (sret_ms5 ms_cur) User npc MENVCFG_S
                                  sepc0 (mword_of_int 0)) usret_Drw ∗
                    hreg_frame_ro usret_Df
                      (usret_rs (sret_ms5 ms_cur) User npc MENVCFG_S sepc0
                         (mword_of_int 0)) usret_Dro)%I)
                _ with "[Hrw Hro] [-]").
      { iApply (swp_bind0_use _ _
                  (fun x : unit => (⌜x = tt⌝ ∗
                     hreg_frame (usret_rs (sret_ms5 ms_cur) User npc MENVCFG_S
                                   sepc0 (mword_of_int 0)) usret_Drw ∗
                     hreg_frame_ro usret_Df
                       (usret_rs (sret_ms5 ms_cur) User npc MENVCFG_S sepc0
                          (mword_of_int 0)) usret_Dro)%I)
                  _ with "[Hrw Hro] [-]").
        { iApply (swp_span usret_Drw usret_Dro usret_Df _ _ _ tt usret_disj
                    (s_hval_long_csr (usret_Drw ∪ usret_Dro) usret_Drw
                       (usret_rs (sret_ms5 ms_cur) User npc MENVCFG_S sepc0
                          (mword_of_int 0))
                       _ usret_in_misa (usret_rs_misa _ _ _ _ _ _))
                    with "Hcert Hrw Hro"). }
        iIntros (u) "(_ & Hrw & Hro)".
        replace (get_config_print_exception tt) with false by reflexivity.
        cbn match. iApply swp_ret. iFrame. }
      iIntros (u) "[Hrw Hro]".
      iApply (swp_hfrun 8 usret_Drw usret_Dro usret_Df _ _ _ _ usret_disj
                (hfrun_prepare_xret_S (usret_Drw ∪ usret_Dro) usret_Drw
                   (usret_rs (sret_ms5 ms_cur) User npc MENVCFG_S sepc0
                      (mword_of_int 0))
                   usret_in_sepc usret_in_misa
                   ltac:(rewrite usret_rs_misa; vm_compute; reflexivity))
                with "Hcert Hrw Hro"). }
    iIntros (w21) "(-> & Hrw & Hro)". rewrite usret_rs_sepc.
    (* -- set_next_pc -- *)
    iApply (swp_bind0_use _ _
              (fun _ : unit =>
                 (hreg_frame (usret_rs (sret_ms5 ms_cur) User (ret_pc sepc0)
                                MENVCFG_S sepc0 (mword_of_int 0)) usret_Drw ∗
                  hreg_frame_ro usret_Df
                    (usret_rs (sret_ms5 ms_cur) User (ret_pc sepc0) MENVCFG_S
                       sepc0 (mword_of_int 0)) usret_Dro)%I)
              _ with "[Hrw Hro] [-]").
    { unfold set_next_pc. cbn match zeta.
      iApply (swp_bind0_use _ _ _
                (fun _ : unit =>
                   (hreg_frame (usret_rs (sret_ms5 ms_cur) User (ret_pc sepc0)
                                  MENVCFG_S sepc0 (mword_of_int 0)) usret_Drw ∗
                    hreg_frame_ro usret_Df
                      (usret_rs (sret_ms5 ms_cur) User (ret_pc sepc0) MENVCFG_S
                         sepc0 (mword_of_int 0)) usret_Dro)%I)
                with "[Hrw Hro] [-]").
      { iApply (swp_write_reg_owned usret_Drw usret_Dro usret_Df _
                  (R_bitvector_64 nextPC) (ret_pc sepc0)
                  usret_disj usret_w_npc with "Hcert Hrw Hro"). }
      iIntros (u) "[Hrw Hro]".
      iDestruct (usret_rw_ext _ _ (usret_set_npc (sret_ms5 ms_cur) User npc
                   (ret_pc sepc0) MENVCFG_S sepc0 (mword_of_int 0))
                   with "Hrw") as "Hrw".
      iDestruct (usret_ro_ext _ _ (usret_set_npc (sret_ms5 ms_cur) User npc
                   (ret_pc sepc0) MENVCFG_S sepc0 (mword_of_int 0))
                   with "Hro") as "Hro".
      iApply swp_ret. iFrame. }
    iIntros (u) "[Hrw Hro]". iApply swp_ret. iSplitR; [done|]. iFrame.
  Qed.

End UsretSwp.

Section WpUaluUsretPt.
  Context `{!riscvGS Σ, !xv6G Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  (* any a0-writing instruction on the trampoline page inside userret:
     register-only, so the leaf is [WpSmodePtLeaves.wp_gpr_write_s_config_regime]'s
     shape over the USER table.

     THE FORCED PREMISE CHANGE (the sweep's standing one): the instruction
     arrived as a whole-[execute] [exec] equation, which is unusable per node
     -- an [exec] fact carries no footprint, and every swp lifter needs one.
     It is now the [swp] OBLIGATION the node shapes conclude
     ([WpMmodeSwpBase.swp_execute_rw] & co. discharge it at a call site). *)
  Lemma wp_ualu_pt (uroot tfp : mword 44) (um : gmap (mword 27) (mword 64))
      (off : Z) (is_rvc : bool) (ast : instruction)
      (m : regfile) (vnew : mword 64)
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
    (* THE INSTRUCTION, as a per-node obligation: a0 := vnew *)
    (gen_cert -∗ gpr_file m -∗
       swp (execute ast)
         (fun e => ⌜e = RETIRE_SUCCESS⌝ ∗
                   gpr_file (<[Regidx (mword_of_int 10)
                               := regval_into_reg vnew]> m))) -∗
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
    intros va pa HSIE HMPRV HSXL Hmm HPBMTE Hmenvval0
      Hcanon Hvpn Hident Hcanon2 Hvpn2 Hident2 Hva2 Hpa4va4.
    iIntros "Hex #Hhw #Hminv Hhs Hpriv Hms Hmie Hmdl Hmenv Hutlb Hpc Hfile
             Hinstr Hcont".
    iDestruct (hw_config_cert with "Hhw") as "#Hcert".
    iApply (wp_instr_u_pt uroot tfp um va pa is_rvc ast
              mstatus0 mie_v mdv0 menvcfg0 mie_v menvcfg0
              (fun npc ms1 mdv1 =>
                 (⌜npc = add_vec_int va (if is_rvc then 2 else 4)⌝ ∗
                  ⌜ms1 = mstatus0⌝ ∗ ⌜mdv1 = mdv0⌝ ∗
                  gpr_file (<[Regidx (mword_of_int 10)
                              := regval_into_reg vnew]> m))%I)
              (dq := dq) HSIE HMPRV HSXL Hmm HPBMTE Hmenvval0
              Hcanon Hvpn Hident Hcanon2 Hvpn2 Hident2 Hva2 Hpa4va4
              with "Hhw Hminv Hhs Hpriv Hms Hmie Hmdl Hmenv Hutlb Hpc Hinstr
                    [Hex Hfile] [Hcont]").
    - iIntros (satp0 pcfg paddr tv') "%Hsok %Hpok
        Hpriv Hms Hmie Hmdl Hmenv Hsatp Hpcfg Hpaddr Htlbc HRes Hclk HPC HnPC
        Hresv".
      iDestruct ("Hex" with "Hcert Hfile") as "Hexx".
      iApply (swp_mono with "[Hpriv Hms Hmie Hmdl Hmenv Hsatp Hpcfg Hpaddr
                              Htlbc HRes Hclk HPC HnPC Hresv] [Hexx]");
        [| iExact "Hexx" ].
      iIntros (e) "(-> & Hfile)".
      iSplitR; [done|].
      iFrame "Hpriv Hmie Hmenv Hsatp Hpcfg Hpaddr".
      iSplitL "Htlbc HRes". { iExists tv'. iFrame "Htlbc HRes". }
      iFrame "Hclk".
      iSplitR "Hresv"; [| iExact "Hresv"].
      iExists mstatus0, mdv0, (add_vec_int va (if is_rvc then 2 else 4)).
      iFrame "Hms Hmdl HPC HnPC".
      iSplitR; [done|]. iSplitR; [done|]. iSplitR; [done|]. iExact "Hfile".
    - iNext. iIntros (npc ms1 mdv1)
        "Hhs Hpriv Hms Hmie Hmdl Hmenv Hutlb Hpc (-> & -> & -> & Hfile)".
      iApply ("Hcont" with "Hhs Hpriv Hms Hmie Hmdl Hmenv Hutlb Hpc Hfile").
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
    senvcfg ↦ᵣ□ senvcfg0 -∗
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
      senvcfg ↦ᵣ□ senvcfg0 -∗
      sepc ↦ᵣ sepc0 -∗
      utlb_inv_pt uroot tfp um -∗
      pc_is (ret_pc sepc0) -∗
      gpr_file m -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros va pa HSIE HMPRV HSXL Hmm HPBMTE Hmenvval0 Hsenvval0 HTSR Hsup.
    subst menvcfg0.
    iIntros "#Hhw #Hminv Hhs Hpriv Hms Hmie Hmdl Hmenv Hsenvc Hsepc Hutlb
             Hpc Hfile Hinstr Hcont".
    iDestruct (hw_config_cert with "Hhw") as "#Hcert".
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & #Hsenv & %HmisaS & %HmisaC &
        %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np & %HmisaA &
        %Hmisa_val0 & %Hmseccfg_val0 & #Hkmapb)".
    subst misa0.
    rewrite (mword1_not_lp elp0 Help_np).
    iApply (wp_instr_u_pt_user uroot tfp um va pa false (SRET tt)
              mstatus0 mie_v mdv0 MENVCFG_S mie_v MENVCFG_S
              (fun npc ms1 mdv1 =>
                 (⌜npc = ret_pc sepc0⌝ ∗ ⌜ms1 = sret_ms5 mstatus0⌝ ∗
                  ⌜mdv1 = mdv0⌝ ∗ gpr_file m ∗ sepc ↦ᵣ sepc0)%I)
              (dq := DfracOwn 1) HSIE HMPRV HSXL Hmm HPBMTE eq_refl
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "Hhw Hminv Hhs Hpriv Hms Hmie Hmdl Hmenv Hutlb Hpc Hinstr
                    [Hfile Hsepc] [Hcont Hsenvc]").
    - iIntros (satp0 pcfg paddr tv') "%Hsok %Hpok
        Hpriv Hms Hmie Hmdl Hmenv Hsatp Hpcfg Hpaddr Htlbc HRes Hclk HPC HnPC
        Hresv".
      iDestruct (usret_frames_in mstatus0 Supervisor (add_vec_int va 4)
                   MENVCFG_S sepc0 (mword_of_int 0)
                   with "Hms Hpriv HnPC Hmisa Hmenv Hsepc Hsenv")
        as "[Hrw Hro]".
      iApply (swp_mono with "[Hmie Hmdl Hclk Hsatp Hpcfg Hpaddr Htlbc HRes
                              Hresv HPC Hfile] [Hrw Hro]").
      2:{ iApply (swp_execute_SRET_U mstatus0 (add_vec_int va 4) sepc0
                    HTSR Hsup with "Hcert Help Hrw Hro"). }
      iIntros (e) "(-> & Hrw & Hro)".
      iDestruct (usret_frames_out (sret_ms5 mstatus0) User (ret_pc sepc0)
                   MENVCFG_S sepc0 (mword_of_int 0) with "[$Hrw $Hro]")
        as "(Hms & Hpriv & HnPC & _ & Hmenv & Hsepc & _)".
      iSplitR; [done|].
      iFrame "Hpriv Hmie Hmenv Hsatp Hpcfg Hpaddr".
      iSplitL "Htlbc HRes". { iExists tv'. iFrame "Htlbc HRes". }
      iFrame "Hclk".
      iSplitR "Hresv"; [| iExact "Hresv"].
      iExists (sret_ms5 mstatus0), mdv0, (ret_pc sepc0).
      iFrame "Hms Hmdl HPC HnPC".
      iSplitR; [done|]. iSplitR; [done|]. iSplitR; [done|].
      iFrame "Hfile Hsepc".
    - iNext. iIntros (npc ms1 mdv1)
        "Hhs Hpriv Hms Hmie Hmdl Hmenv Hutlb Hpc
         (-> & -> & -> & Hfile & Hsepc)".
      iApply ("Hcont" with "Hhs Hpriv Hms Hmie Hmdl Hmenv Hsenvc Hsepc Hutlb
                            Hpc Hfile").
  Qed.

End WpUaluUsretPt.
