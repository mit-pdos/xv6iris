(* WpStart3.v -- the final chunk c7 (idx 60..63: csrr mhartid; c.addiw a5;
   c.mv tp,a5; MRET) and the composition wp_start.  Built on WpStart2 +
   WpStartChain.  COMPILE:
   coqc -R . xv6iris -R /shared/xv6rocq/model-xv6iris Riscv -R /shared/xv6rocq/kernel-rocq Kernel WpStart3.v *)
From Stdlib Require Import Eqdep_dec ZArith Lia List.
From stdpp Require Import gmap list list_monad bitvector.definitions bitvector.tactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes.
Require Import SailStdpp.Base SailStdpp.TypeCasts.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvTryStep RiscvFetchExec RiscvExtras WpEntry WpGpr WpRvc KernelBoot WpStartText.
Require Import WpGprCsrr WpGprMretWp.
Require Import WpStartChain WpStart2.
From Kernel Require Import KernelInstrs.
Local Open Scope Z_scope.

Section WpStart3.
  Context `{!riscvGS Σ}.

  Local Ltac vmc := vm_compute; reflexivity.

  (* ===================================================================== *)
  (* CHUNK c7 (THE TAIL): idx 60 csrr a5,mhartid ; idx 61 c.addiw a5 ;       *)
  (* idx 62 c.mv tp,a5 ; idx 63 MRET.  The MRET is the FINAL step → S-mode.  *)
  (* Precondition = c6's postcondition (PC=spc60, existential gpr_file with   *)
  (* x15 present) PLUS mepc (held aside through c6).  mstatus0 here is the    *)
  (* legalized mstatus whose MPP=Supervisor (set by start idx 41).           *)
  (* ===================================================================== *)
  Lemma wp_st_c7
      (mfin : gmap register_bitvector_64 (mword 64))
      (mst0 : mword 64) (mi0 : bool)
      (misa0 mstatus0 mseccfg0 mdv0 mepc0 mhartid0 : mword 64)
      (mc : mword 32) (mcfg : mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (pmar0 : list PMA_Region)
      (newpriv : Privilege) (lpe : bool)
      (elp0 : mword 1)
      E (Φ : mval -> iProp Σ) :
    let b1   := andb (eq_vec (_get_Counterin_IR mc) ('b"0"))
                     (eq_vec (counter_priv_filter_bit mcfg Machine) ('b"0")) in
    is_Some (mfin !! gpr_of_Z 15) ->
    is_Some (mfin !! gpr_of_Z 4) ->
    pma_allows_all pmar0 -> pmp_allows_all pmpcfg0 ->
    eq_vec (_get_Mstatus_MIE mstatus0) ('b"1") = false ->
    eq_vec elp0 (landing_pad_bits_backwards LP_EXPECTED) = false ->
    eq_vec (_get_Misa_C misa0) ('b"1") = true ->
    eq_vec (_get_Misa_S misa0) ('b"1") = true ->
    eq_vec (_get_Misa_U misa0) ('b"1") = true ->
    (* the MRET's MPP reduces to a non-Machine privilege (Supervisor). *)
    privLevel_bits_forwards (_get_Mstatus_MPP (cms2 mstatus0), ('b"0")) = returnM newpriv ->
    generic_neq newpriv Machine = true ->
    (forall sz, exec (get_xLPE newpriv) sz = Some (lpe, sz)) ->
    PC ↦ᵣ spc60 -∗ gpr_file mfin -∗ misa ↦ᵣ misa0 -∗ mhartid ↦ᵣ mhartid0 -∗ nextPC ↦ᵣ spc60 -∗
    (R_bool minstret_increment) ↦ᵣ b1 -∗ minstret ↦ᵣ mst0 -∗
    cur_privilege ↦ᵣ Machine -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
    (R_bitvector_64 mideleg) ↦ᵣ mdv0 -∗ (R_bitvector_64 mstatus) ↦ᵣ mstatus0 -∗
    mepc ↦ᵣ mepc0 -∗
    elp ↦ᵣ elp0 -∗ mseccfg ↦ᵣ mseccfg0 -∗ mcountinhibit ↦ᵣ mc -∗ minstretcfg ↦ᵣ mcfg -∗
    pmpcfg_n ↦ᵣ pmpcfg0 -∗ pma_regions ↦ᵣ pmar0 -∗ htif_tohost_base ↦ᵣ None -∗
    kernel_text -∗
    (* After the MRET, the hart is in Supervisor mode at PC = mepc.  Expose the
       full final machine state. *)
    ▷ ( PC ↦ᵣ ctgt mepc0 -∗ nextPC ↦ᵣ ctgt mepc0 -∗
        (∃ mf2, gpr_file mf2) -∗ misa ↦ᵣ misa0 -∗ mhartid ↦ᵣ mhartid0 -∗
        (R_bool minstret_increment) ↦ᵣ b1 -∗ (∃ mstf : mword 64, minstret ↦ᵣ mstf) -∗
        cur_privilege ↦ᵣ newpriv -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
        (R_bitvector_64 mideleg) ↦ᵣ mdv0 -∗ (R_bitvector_64 mstatus) ↦ᵣ cms5 mstatus0 -∗
        mepc ↦ᵣ mepc0 -∗
        elp ↦ᵣ celpv lpe mstatus0 -∗ mseccfg ↦ᵣ mseccfg0 -∗ mcountinhibit ↦ᵣ mc -∗ minstretcfg ↦ᵣ mcfg -∗
        pmpcfg_n ↦ᵣ pmpcfg0 -∗ pma_regions ↦ᵣ pmar0 -∗ htif_tohost_base ↦ᵣ None -∗
        kernel_text -∗
        WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intros b1 Hf15 Hf4 Hpmaall Hpmpf HmIE Hlp HmisaC HmisaS HmisaU Hnp Hnpm Hlpe.
    destruct Hf4 as [vtp Hf4].
    iIntros "Hpc Hfile Hmisa Hmhartid Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Hmepc
             Help Hsec Hmcinh Hmcfg Hpmpc Hpma Hhtif #H".
    iIntros "Hcont".
    (* ---- idx 60: csrr a5,mhartid (4-aligned at spc60=0xb4); kernel_text duplicable ---- *)
    destruct Hf15 as [va5_60 Hf15].
    iAssert (kinstr_bytes (skinstr 60)) as "#K60". { sg 60. }
    assert (Hk_a : ki_addr (skinstr 60) = (kentry + 0xb4)) by (vm_compute; reflexivity); assert (Hk_e : ki_enc (skinstr 60) = 0xf14027f3) by (vm_compute; reflexivity); assert (Hk_w : ki_width (skinstr 60) = 32%nat) by (vm_compute; reflexivity); iDestruct (kinstr_window32 (skinstr 60) (kentry + 0xb4) 0xf14027f3 Hk_a Hk_e Hk_w with "K60") as "#W60"; clear Hk_a Hk_e Hk_w.
    iApply (wp_csrr_gpr spc60 sw60 (scsr_rd sw60) mfin va5_60 mhartid0 misa0 mdv0 b1
              _ mst0 mstatus0 mc mcfg pmpcfg0 pmar0 b1 elp0 E Φ
              ltac:(vm_compute; discriminate) Hf15 HmisaS Hpmaall Hpmpf
              ltac:(vmc) ltac:(vmc) ltac:(vmc) ltac:(vmc) ltac:(vmc)
              ltac:(intros s0 Hpriv;
                    replace (subrange_vec_dec sw60 31 20) with csr_csrr by (vm_compute; reflexivity);
                    replace (scsr_rs1z sw60) with i_rs1_csrr by (vm_compute; reflexivity);
                    exact (decode_s60 s0 Hpriv))
              eq_refl HmIE Hlp
              with "Hpc Hfile Hmhartid Hmisa Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif W60").
    iNext.
    iIntros "Hpc Hfile Hmhartid Hmisa Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif _".
    replace (add_vec_int spc60 4) with spc61 by (vm_compute; reflexivity).
    set (m60 := <[gpr_of_Z (uint (scsr_rd sw60)) := regval_into_reg mhartid0]> mfin).
    (* ---- idx 61: c.addiw a5 (4-byte window from skinstr 61 ++ 62) ---- *)
    iAssert (kinstr_bytes (skinstr 61)) as "#K61". { sg 61. }
    iAssert (kinstr_bytes (skinstr 62)) as "#K62". { sg 62. }
    assert (Hk_a : ki_addr (skinstr 61) = kentry + 0xb8) by (vm_compute; reflexivity); assert (Hk_e : ki_enc (skinstr 61) = 0x2781) by (vm_compute; reflexivity); iDestruct (kinstr_rvc4 (skinstr 61) (kentry + 0xb8) (0x2781) Hk_a Hk_e with "K61") as (wr_s61) "[%Hsub_s61 #W61]"; clear Hk_a Hk_e.
    assert (Ha561 : m60 !! gpr_of_Z (uint (sreg117 sw61)) = Some (regval_into_reg mhartid0)).
    { unfold m60. replace (uint (sreg117 sw61)) with 15 by (vm_compute; reflexivity).
      replace (uint (scsr_rd sw60)) with 15 by (vm_compute; reflexivity).
      rewrite lookup_insert. reflexivity. }
    iApply (wp_caddiw_gpr_4 spc61 wr_s61 (sreg117 sw61) (scaddiw_imm sw61) m60 (regval_into_reg mhartid0) misa0 mdv0 b1
              _ _ mstatus0 mc mcfg pmpcfg0 pmar0 _ elp0 E Φ
              ltac:(vm_compute; discriminate) Ha561 Hpmaall Hpmpf
              ltac:(vmc) ltac:(vmc) ltac:(vmc) ltac:(vmc) ltac:(rewrite Hsub_s61; vm_compute; reflexivity)
              HmisaC HmisaS (decode4_s61 wr_s61 Hsub_s61) eq_refl HmIE Hlp
              with "Hpc Hfile Hmisa Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif W61").
    iNext.
    iIntros "Hpc Hfile Hmisa Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif _".
    replace (add_vec_int spc61 2) with spc62 by (vm_compute; reflexivity).
    set (m61 := <[gpr_of_Z (uint (sreg117 sw61)) := regval_into_reg (caddiw_wval (scaddiw_imm sw61) (regval_into_reg mhartid0))]> m60).
    assert (Hk_a : ki_addr (skinstr 62) = (kentry + 0xba)) by (vm_compute; reflexivity); assert (Hk_e : ki_enc (skinstr 62) = 0x823e) by (vm_compute; reflexivity); assert (Hk_w : (2 <= ki_width (skinstr 62) / 8)%nat) by (vm_compute; lia); iDestruct (kinstr_window16 (skinstr 62) (kentry + 0xba) 0x823e Hk_a Hk_e Hk_w with "K62") as "#W62"; clear Hk_a Hk_e Hk_w.
    (* ---- idx 62: c.mv tp,a5 (2-aligned at spc62=0xba) ---- *)
    assert (Ha562 : m61 !! gpr_of_Z (uint (sreg62 sw62)) = Some (regval_into_reg (caddiw_wval (scaddiw_imm sw61) (regval_into_reg mhartid0)))).
    { unfold m61. replace (uint (sreg62 sw62)) with 15 by (vm_compute; reflexivity).
      replace (uint (sreg117 sw61)) with 15 by (vm_compute; reflexivity).
      rewrite lookup_insert. reflexivity. }
    assert (Htp62 : m61 !! gpr_of_Z (uint (sreg117 sw62)) = Some vtp).
    { unfold m61, m60. replace (uint (sreg117 sw62)) with 4 by (vm_compute; reflexivity).
      rewrite lookup_insert_ne; [| vm_compute; discriminate].
      rewrite lookup_insert_ne; [| vm_compute; discriminate]. exact Hf4. }
    iApply (wp_cmv_gpr spc62 sw62 (sreg117 sw62) (sreg62 sw62) m61 _ _ misa0 mdv0 b1
              _ _ mstatus0 mc mcfg pmpcfg0 pmar0 _ elp0 E Φ
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) Ha562 Htp62 Hpmaall Hpmpf
              ltac:(vmc) ltac:(vmc) ltac:(vmc) ltac:(vmc) ltac:(vmc)
              HmisaC HmisaS decode_s62 eq_refl HmIE Hlp
              with "Hpc Hfile Hmisa Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif W62").
    iNext.
    iIntros "Hpc Hfile Hmisa Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif _".
    replace (add_vec_int spc62 2) with spc63 by (vm_compute; reflexivity).
    (* ---- idx 63: MRET (4-aligned at spc63=0xbc).  Drops gpr_file (not needed). ---- *)
    iAssert (kinstr_bytes (skinstr 63)) as "#K63". { sg 63. }
    assert (Hk_a : ki_addr (skinstr 63) = (kentry + 0xbc)) by (vm_compute; reflexivity); assert (Hk_e : ki_enc (skinstr 63) = 0x30200073) by (vm_compute; reflexivity); assert (Hk_w : ki_width (skinstr 63) = 32%nat) by (vm_compute; reflexivity); iDestruct (kinstr_window32 (skinstr 63) (kentry + 0xbc) 0x30200073 Hk_a Hk_e Hk_w with "K63") as "#W63"; clear Hk_a Hk_e Hk_w.
    (* K63 is now [∗list seq 0 4] nth_byte (mword_of_int 0x30200073 : mword 32) at
       fetch_pa (mword_of_int (kentry+0xbc)) = fetch_pa spc63 = wp_mret's window
       (w_mret = mword_of_int 0x30200073). *)
    iApply (wp_mret spc63 newpriv lpe b1 _ _ mstatus0 misa0 mepc0 mdv0
              mc mcfg pmpcfg0 pmar0 _ elp0 E Φ
              Hpmaall Hpmpf ltac:(vmc) ltac:(vmc) ltac:(vmc) ltac:(vmc)
              eq_refl HmIE Hlp HmisaS HmisaU HmisaC Hnp Hnpm Hlpe
              with "Hpc Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Hmisa Hmepc Help Hmcinh Hmcfg Hpmpc Hpma Hhtif W63").
    iNext.
    iIntros "Hpc Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Hmisa Hmepc Help Hmcinh Hmcfg Hpmpc Hpma Hhtif _".
    (* kernel_text is duplicable -> the persistent #H is still here. *)
    with_strategy transparent [mbump] (iApply ("Hcont" with "Hpc Hnpc [Hfile] Hmisa Hmhartid Hmi [Hmst] Hpriv Hhs Hmdl Hms Hmepc
              Help Hsec Hmcinh Hmcfg Hpmpc Hpma Hhtif H")).
    { iExists _. iFrame "Hfile". }
    { iExists _. iFrame "Hmst". }
  Qed.

End WpStart3.
