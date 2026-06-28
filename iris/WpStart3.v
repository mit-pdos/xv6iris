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
Require Import RiscvLang RiscvPtsto RiscvExec RiscvTryStep RiscvFetchExec RiscvExtras WpFetch WpDecode WpEntry WpGpr WpRvc WpAuipc WpGprCsrw KernelBoot WpStartText.
Require Import WpGprCsrr WpGprMretWp.
Require Import WpStartChain WpStart2.
Require Import MinstretInv.
From iris.base_logic.lib Require Import invariants.
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
      (mstatus0 mdv0 mepc0 mhartid0 : mword 64)
      (mc : mword 32) (mcfg : mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n)
      (newpriv : Privilege) (lpe : bool)
      (elp0 : mword 1)
      E (Φ : mval -> iProp Σ) :
    let b1   := andb (eq_vec (_get_Counterin_IR mc) ('b"0"))
                     (eq_vec (counter_priv_filter_bit mcfg Machine) ('b"0")) in
    ↑minstretN ⊆ E ->
    is_Some (mfin !! gpr_of_Z 15) ->
    is_Some (mfin !! gpr_of_Z 4) ->
    is_Some (mfin !! gpr_of_Z 2) ->
    pmp_allows_all pmpcfg0 ->
    eq_vec (_get_Mstatus_MIE mstatus0) ('b"1") = false ->
    eq_vec elp0 (landing_pad_bits_backwards LP_EXPECTED) = false ->
    (* the MRET's MPP reduces to a non-Machine privilege (Supervisor). *)
    privLevel_bits_forwards (_get_Mstatus_MPP (cms2 mstatus0), ('b"0")) = returnM newpriv ->
    generic_neq newpriv Machine = true ->
    (forall sz, exec (get_xLPE newpriv) sz = Some (lpe, sz)) ->
    PC ↦ᵣ spc60 -∗ gpr_file mfin -∗ mhartid ↦ᵣ mhartid0 -∗ nextPC ↦ᵣ spc60 -∗
    minstret_inv -∗
    cur_privilege ↦ᵣ Machine -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
    (R_bitvector_64 mideleg) ↦ᵣ mdv0 -∗ (R_bitvector_64 mstatus) ↦ᵣ mstatus0 -∗
    mepc ↦ᵣ mepc0 -∗
    elp ↦ᵣ elp0 -∗
    pmpcfg_n ↦ᵣ pmpcfg0 -∗
    hw_config mc mcfg -∗
    kernel_text -∗
    (* After the MRET, the hart is in Supervisor mode at PC = mepc.  Expose the
       full final machine state. *)
    ▷ ( PC ↦ᵣ ctgt mepc0 -∗ nextPC ↦ᵣ ctgt mepc0 -∗
        (∃ mf2, gpr_file mf2 ∗ ⌜ is_Some (mf2 !! gpr_of_Z 2) ⌝) -∗ mhartid ↦ᵣ mhartid0 -∗
        cur_privilege ↦ᵣ newpriv -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
        (R_bitvector_64 mideleg) ↦ᵣ mdv0 -∗ (R_bitvector_64 mstatus) ↦ᵣ cms5 mstatus0 -∗
        mepc ↦ᵣ mepc0 -∗
        elp ↦ᵣ celpv lpe mstatus0 -∗
        pmpcfg_n ↦ᵣ pmpcfg0 -∗
        kernel_text -∗
        WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
 intros b1 HN Hf15 Hf4 Hf2 Hpmpf HmIE Hlp Hnp Hnpm Hlpe.
    destruct Hf4 as [vtp Hf4].
    iIntros "Hpc Hfile Hmhartid Hnpc #Hinv Hpriv Hhs Hmdl Hms Hmepc
             Help Hpmpc #Hhw #H".
    iPoseProof "Hhw" as "#Hhwb".
    iDestruct "Hhwb" as (misa0 mseccfg0 pmar0) "#(Hmisa & Hsec & Hmcinh & Hmcfg & Hpma & Hhtif & %HmisaS & %HmisaC & %HmisaU & %HmisaM & %Hpmaall & %Hpmm & %Hmlpe)".
    iIntros "Hcont".
    (* ---- idx 60: csrr a5,mhartid (4-aligned at spc60=0xb4); kernel_text duplicable ---- *)
    destruct Hf15 as [va5_60 Hf15].
    iAssert (kinstr_bytes (skinstr 60)) as "#K60". { sg 60. }
    assert (Hk_a : ki_addr (skinstr 60) = (kentry + 0xb4)) by (vm_compute; reflexivity); assert (Hk_e : ki_enc (skinstr 60) = 0xf14027f3) by (vm_compute; reflexivity); assert (Hk_w : ki_width (skinstr 60) = 32%nat) by (vm_compute; reflexivity); iDestruct (kinstr_window32 (skinstr 60) (kentry + 0xb4) 0xf14027f3 Hk_a Hk_e Hk_w with "K60") as "#W60"; clear Hk_a Hk_e Hk_w.
    iApply (wp_csrr_gpr spc60 sw60 (scsr_rd sw60) mfin va5_60 mhartid0 misa0 mdv0 b1
              _ mstatus0 mc mcfg pmpcfg0 pmar0 elp0 E Φ
              HN ltac:(vm_compute; discriminate) Hf15 HmisaS Hpmaall Hpmpf
              ltac:(vmc) ltac:(vmc) ltac:(vmc) ltac:(vmc) ltac:(vmc)
              ltac:(intros s0 Hpriv;
                    replace (subrange_vec_dec sw60 31 20) with csr_csrr by (vm_compute; reflexivity);
                    replace (scsr_rs1z sw60) with i_rs1_csrr by (vm_compute; reflexivity);
                    exact (decode_s60 s0 Hpriv))
              eq_refl HmIE Hlp
              with "Hinv Hpc Hfile Hmhartid Hmisa Hnpc Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif W60").
    iNext.
    iIntros "Hpc Hfile Hmhartid _ Hnpc Hpriv Hhs Hmdl Hms Help _ _ Hpmpc _ _ _".
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
              _ mstatus0 mc mcfg pmpcfg0 pmar0 elp0 E Φ
              HN ltac:(vm_compute; discriminate) Ha561 Hpmaall Hpmpf
              ltac:(vmc) ltac:(vmc) ltac:(vmc) ltac:(vmc) ltac:(rewrite Hsub_s61; vm_compute; reflexivity)
              HmisaC HmisaS (decode4_s61 wr_s61 Hsub_s61) eq_refl HmIE Hlp
              with "Hpc Hfile Hmisa Hnpc Hinv Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif W61").
    iNext.
    iIntros "Hpc Hfile _ Hnpc Hpriv Hhs Hmdl Hms Help _ _ Hpmpc _ _ _".
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
              _ mstatus0 mc mcfg pmpcfg0 pmar0 elp0 E Φ
              HN ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) Ha562 Htp62 Hpmaall Hpmpf
              ltac:(vmc) ltac:(vmc) ltac:(vmc) ltac:(vmc) ltac:(vmc)
              HmisaC HmisaS decode_s62 eq_refl HmIE Hlp
              with "Hpc Hfile Hmisa Hnpc Hinv Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif W62").
    iNext.
    iIntros "Hpc Hfile _ Hnpc Hpriv Hhs Hmdl Hms Help _ _ Hpmpc _ _ _".
    replace (add_vec_int spc62 2) with spc63 by (vm_compute; reflexivity).
    (* ---- idx 63: MRET (4-aligned at spc63=0xbc).  Drops gpr_file (not needed). ---- *)
    iAssert (kinstr_bytes (skinstr 63)) as "#K63". { sg 63. }
    assert (Hk_a : ki_addr (skinstr 63) = (kentry + 0xbc)) by (vm_compute; reflexivity); assert (Hk_e : ki_enc (skinstr 63) = 0x30200073) by (vm_compute; reflexivity); assert (Hk_w : ki_width (skinstr 63) = 32%nat) by (vm_compute; reflexivity); iDestruct (kinstr_window32 (skinstr 63) (kentry + 0xbc) 0x30200073 Hk_a Hk_e Hk_w with "K63") as "#W63"; clear Hk_a Hk_e Hk_w.
    (* K63 is now [∗list seq 0 4] nth_byte (mword_of_int 0x30200073 : mword 32) at
       fetch_pa (mword_of_int (kentry+0xbc)) = fetch_pa spc63 = wp_mret's window
       (w_mret = mword_of_int 0x30200073). *)
    iApply (wp_mret spc63 newpriv lpe b1 _ mstatus0 misa0 mepc0 mdv0
              mc mcfg pmpcfg0 pmar0 elp0 E Φ
              HN Hpmaall Hpmpf ltac:(vmc) ltac:(vmc) ltac:(vmc) ltac:(vmc)
              eq_refl HmIE Hlp HmisaS HmisaU HmisaC Hnp Hnpm Hlpe
              with "Hinv Hpc Hnpc Hpriv Hhs Hmdl Hms Hmisa Hmepc Help Hmcinh Hmcfg Hpmpc Hpma Hhtif W63").
    iNext.
    iIntros "Hpc Hnpc Hpriv Hhs Hmdl Hms _ Hmepc Help _ _ Hpmpc _ _ _".
    (* kernel_text is duplicable -> the persistent #H is still here. *)
    with_strategy transparent [mbump] (iApply ("Hcont" with "Hpc Hnpc [Hfile] Hmhartid Hpriv Hhs Hmdl Hms Hmepc
              Help Hpmpc H")).
    { iExists _. iFrame "Hfile". iPureIntro.
      (* x2 (sp) untouched by idx 60/61/62 (they write x15/x15/x4) -> from input Hf2. *)
      replace (uint (sreg117 sw62)) with 4 by (vm_compute; reflexivity).
      rewrite lookup_insert_ne; [| vm_compute; discriminate].
      unfold m61. replace (uint (sreg117 sw61)) with 15 by (vm_compute; reflexivity).
      rewrite lookup_insert_ne; [| vm_compute; discriminate].
      unfold m60. replace (uint (scsr_rd sw60)) with 15 by (vm_compute; reflexivity).
      rewrite lookup_insert_ne; [| vm_compute; discriminate].
      exact Hf2. }
  Qed.

  (* ===================================================================== *)
  (* wp_start : the whole start() function (idx 30..63), composing the      *)
  (* seven chunk lemmas wp_st_c1..c7 (c6 nests wp_timerinit).  Begins at     *)
  (* spc30 (0x80000058, the _entry jal target) in Machine mode and ends      *)
  (* after the MRET in Supervisor mode at PC = mepc.  Final machine state is  *)
  (* existentially abstracted (the legalised CSR values are not needed by     *)
  (* the caller; only that the hart left Machine mode with kernel_text intact).*)
  (* ===================================================================== *)
  Lemma wp_start
      (sp0 vra vs0 va4 va5 : mword 64)
      (m : gmap register_bitvector_64 (mword 64))
      (mst0 npc0 : mword 64) (mi0 : bool)
      (mstatus0 menvcfg0 mtime0 stimecmp0 mhartid0 mepc0 satp0 medeleg0 mie0 : mword 64)
      (mcounteren0 : mword 32)
      (mc : mword 32) (mcfg : mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (pmpaddr00 : type_of_register pmpaddr_n)
      (elp0 : mword 1) (vold_ra vold_s0 vti_ra vti_s0 : bv 64)
      (newpriv : Privilege) (lpe : bool)
      E (Φ : mval -> iProp Σ) :
    let b1   := andb (eq_vec (_get_Counterin_IR mc) ('b"0"))
                     (eq_vec (counter_priv_filter_bit mcfg Machine) ('b"0")) in
    let sp1  := add_vec sp0 (sign_extend' 64 (sign_extend' 12 imm9)) in
    let imm_ra := zero_extend' 12 (concat_vec uimm10 ('b"000")) in
    let pa_ra  := zero_extend' 64 (add_vec_int (zero_extend' 64 (subrange_vec_dec (add_vec sp1 (sign_extend' 64 imm_ra)) (xlen - 0 - 1) 0)) (0 * 8)) in
    let imm_s0 := zero_extend' 12 (concat_vec uimm11 ('b"000")) in
    let pa_s0  := zero_extend' 64 (add_vec_int (zero_extend' 64 (subrange_vec_dec (add_vec sp1 (sign_extend' 64 imm_s0)) (xlen - 0 - 1) 0)) (0 * 8)) in
    let a8_ra  := zero_extend' 64 (subrange_vec_dec (add_vec sp1 (sign_extend' 64 imm_ra)) (xlen - 0 - 1) 0) in
    let a8_s0  := zero_extend' 64 (subrange_vec_dec (add_vec sp1 (sign_extend' 64 imm_s0)) (xlen - 0 - 1) 0) in
    (* a5 (x15) value threaded through the chunks.  c1 writes csrr mstatus -> a5;
       c2 computes menvcfg-mask in a5; the legalised mstatus after idx 41 csrw is
       [mstatus1].  The two conditions below (MIE stays 0, SXL=10) are facts about
       the kernel's concrete computation, dischargeable once mstatus0 is concrete. *)
    let va5_c2 := regval_into_reg (subrange_vec_dec mstatus0 (Z.sub xlen 1) 0) in
    let va4_35 := WpGprLui.luival (sign_extend' 20 (sclui_imm sw35)) in
    let va4_36 := add_vec va4_35 (sign_extend' 64 (subrange_vec_dec sw36 31 20)) in
    let va5_37 := and_vec va5_c2 va4_36 in
    let va4_38 := WpGprLui.luival (sign_extend' 20 (sclui_imm sw38)) in
    let va4_39 := add_vec va4_38 (sign_extend' 64 (subrange_vec_dec sw39 31 20)) in
    let va5_40 := or_vec va5_37 va4_39 in
    let mstatus1 := mstatus_legalized mstatus0 va5_40 in
    (* a5 values in c3 (mepc target) and c4 (mideleg mask); mdv0 = final mideleg. *)
    let va5_42 := add_vec spc42 (auipc_off (subrange_vec_dec sw42 31 12)) in
    let va5_43 := add_vec va5_42 (sign_extend' 64 (subrange_vec_dec sw43 31 20)) in
    let va5_45 := cli_wval (scli_imm sw45) in
    let va5_47 := WpGprLui.luival (sign_extend' 20 (sclui_imm sw47)) in
    let va5_48 := add_vec va5_47 (sign_extend' 64 (sign_extend' 12 (scli_imm sw48))) in
    let mdv0 := mideleg_legalized (zeros' 64) va5_48 in
    (* a5 values in c5 (sie / pmpcfg setup); pmpcfg1 = final pmpcfg after pmpcfg0 write. *)
    let va5_51 := lower_mie mie0 mdv0 in
    let va5_52 := or_vec va5_51 (sign_extend' 64 (subrange_vec_dec sw52 31 20)) in
    let va5_54 := cli_wval (scli_imm sw54) in
    let va5_55 := csrli_wval (scsrli_sh sw55) va5_54 in
    let va5_57 := cli_wval (scli_imm sw57) in
    let pmpcfg1 := pmpcfg0_finalvec va5_57 pmpcfg0 in
    (* timerinit's own stack frame (sp at c6 entry is sp1; timerinit subtracts 16 again). *)
    let c6sp   := add_vec sp1 (sign_extend' 64 (sign_extend' 12 imm9)) in
    let tpa_ra := zero_extend' 64 (add_vec_int (zero_extend' 64 (subrange_vec_dec (add_vec c6sp (sign_extend' 64 imm_ra)) (xlen - 0 - 1) 0)) (0 * 8)) in
    let tpa_s0 := zero_extend' 64 (add_vec_int (zero_extend' 64 (subrange_vec_dec (add_vec c6sp (sign_extend' 64 imm_s0)) (xlen - 0 - 1) 0)) (0 * 8)) in
    let ta8_ra := zero_extend' 64 (subrange_vec_dec (add_vec c6sp (sign_extend' 64 imm_ra)) (xlen - 0 - 1) 0) in
    let ta8_s0 := zero_extend' 64 (subrange_vec_dec (add_vec c6sp (sign_extend' 64 imm_s0)) (xlen - 0 - 1) 0) in
    ↑minstretN ⊆ E ->
    m !! gpr_of_Z 1 = Some vra -> m !! gpr_of_Z 2 = Some sp0 ->
    m !! gpr_of_Z 8 = Some vs0 -> m !! gpr_of_Z 14 = Some va4 -> m !! gpr_of_Z 15 = Some va5 ->
    is_Some (m !! gpr_of_Z 4) ->
    pmp_allows_all pmpcfg0 ->
    eq_vec (_get_Mstatus_MIE mstatus0) ('b"1") = false ->
    eq_vec elp0 (landing_pad_bits_backwards LP_EXPECTED) = false ->
    eq_vec (_get_Mstatus_MPRV mstatus0) ('b"1") = false ->
    eq_vec (_get_Mstatus_MIE mstatus1) ('b"1") = false ->
    _get_Mstatus_SXL mstatus1 = 'b"10" ->
    is_aligned_vaddr (Virtaddr a8_ra) 8 = true -> is_aligned_paddr (Physaddr pa_ra) 8 = true ->
    is_aligned_vaddr (Virtaddr a8_s0) 8 = true -> is_aligned_paddr (Physaddr pa_s0) 8 = true ->
    (* extra conditions for the timerinit call (c6): MPRV/MLPE after the mstatus
       write, and alignment of timerinit's own stack frame. *)
    eq_vec (_get_Mstatus_MPRV mstatus1) ('b"1") = false ->
    pmp_allows_all pmpcfg1 ->
    is_aligned_vaddr (Virtaddr ta8_ra) 8 = true -> is_aligned_paddr (Physaddr tpa_ra) 8 = true ->
    is_aligned_vaddr (Virtaddr ta8_s0) 8 = true -> is_aligned_paddr (Physaddr tpa_s0) 8 = true ->
    (* the MRET (c7) sends the hart to a non-Machine privilege (Supervisor); the
       MPP field of the (post-write) mstatus reduces to [newpriv]. *)
    privLevel_bits_forwards (_get_Mstatus_MPP (cms2 mstatus1), ('b"0")) = returnM newpriv ->
    generic_neq newpriv Machine = true ->
    (forall sz, exec (get_xLPE newpriv) sz = Some (lpe, sz)) ->
    PC ↦ᵣ spc30 -∗ gpr_file m -∗ nextPC ↦ᵣ npc0 -∗
    minstret_inv -∗
    menvcfg ↦ᵣ menvcfg0 -∗ mcounteren ↦ᵣ mcounteren0 -∗ mtime ↦ᵣ mtime0 -∗ stimecmp ↦ᵣ stimecmp0 -∗
    mepc ↦ᵣ mepc0 -∗ satp ↦ᵣ satp0 -∗ medeleg ↦ᵣ medeleg0 -∗ mie ↦ᵣ mie0 -∗ pmpaddr_n ↦ᵣ pmpaddr00 -∗
    mhartid ↦ᵣ mhartid0 -∗
    ti_ctx mstatus0 (zeros' 64) mc mcfg pmpcfg0 elp0 -∗
    ([∗ list] j ∈ seq 0 8, (pa_add pa_ra j) ↦ₘ nth_byte vold_ra j) -∗
    ([∗ list] j ∈ seq 0 8, (pa_add pa_s0 j) ↦ₘ nth_byte vold_s0 j) -∗
    ([∗ list] j ∈ seq 0 8, (pa_add tpa_ra j) ↦ₘ nth_byte vti_ra j) -∗
    ([∗ list] j ∈ seq 0 8, (pa_add tpa_s0 j) ↦ₘ nth_byte vti_s0 j) -∗
    kernel_text -∗
    (* Post-MRET state, now exposed CONCRETELY (no longer abstract) so the first
       Supervisor-mode instruction can chain onto it.  PC = ctgt (mepc_val va5_43)
       = 0x80000e82 = <main>; cur_privilege = newpriv (Supervisor); satp written to
       [satp_legalized satp0 va5_45] (va5_45 = 0, MODE = Bare); pmpcfg = pmpcfg1.
       Only the gpr_file (a4/a5 clobbered), minstret, and pmpaddr stay existential;
       the gpr_file exposes that x2 (sp) is present. *)
    ▷ ( (∃ (mf : gmap register_bitvector_64 (mword 64)),
          PC ↦ᵣ ctgt (mepc_val va5_43) ∗ nextPC ↦ᵣ ctgt (mepc_val va5_43) ∗
          gpr_file mf ∗ ⌜ is_Some (mf !! gpr_of_Z 2) ⌝ ∗ mhartid ↦ᵣ mhartid0 ∗
          cur_privilege ↦ᵣ newpriv ∗ ⌜ generic_neq newpriv Machine = true ⌝ ∗ hart_state ↦ᵣ HART_ACTIVE tt ∗
          (R_bitvector_64 mideleg) ↦ᵣ mdv0 ∗ (R_bitvector_64 mstatus) ↦ᵣ cms5 mstatus1 ∗ mepc ↦ᵣ mepc_val va5_43 ∗
          satp ↦ᵣ satp_legalized satp0 va5_45 ∗
          elp ↦ᵣ celpv lpe mstatus1 ∗
          pmpcfg_n ↦ᵣ pmpcfg1 ∗ pmpaddr_n ↦ᵣ pmp0_newaddr pmpcfg0 pmpaddr00 va5_55 ∗
          mie ↦ᵣ sie_new_mie mie0 mdv0 va5_52 ∗ kernel_text)
        -∗ WP (Loop : expr riscv_lang) @ E {{ Φ }} ) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
 intros b1 sp1 imm_ra pa_ra imm_s0 pa_s0 a8_ra a8_s0 va5_c2 va4_35 va4_36 va5_37 va4_38 va4_39 va5_40 mstatus1
           va5_42 va5_43 va5_45 va5_47 va5_48 mdv0 va5_51 va5_52 va5_54 va5_55 va5_57 pmpcfg1
           c6sp tpa_ra tpa_s0 ta8_ra ta8_s0.
 intros HN Hm1 Hm2 Hm8 Hm14 Hm15 Hm4 Hpmpf HmIE Hlp HMPRV HmIE1 HSXL1
           Ha8ra Hpara Ha8s0 Hpas0 HMPRV1 Hpmpf1 Hta8ra Htpara Hta8s0 Htpas0 Hnp Hnpm Hlpe.
    iIntros "Hpc Hfile Hnpc #Hinv Hmenv Hmcen Hmtime Hstc Hmepc Hsatp Hmede Hmie Hpmpaddr Hmhartid Hctx Hstkra Hstks0 Htra Htrs0 #H Hcont".
    (* ---- chunk c1 (idx 30..34): spc30 -> spc35 ---- *)
    iApply (wp_st_c1 sp0 vra vs0 va5 m mst0 npc0 mi0 mstatus0 menvcfg0 mtime0 stimecmp0
              mcounteren0 mc mcfg pmpcfg0 elp0 vold_ra vold_s0 E Φ
              HN Hm1 Hm2 Hm8 Hm15 Hpmpf HmIE Hlp HMPRV Ha8ra Hpara Ha8s0 Hpas0
              with "Hpc Hfile Hnpc Hinv Hmenv Hmcen Hmtime Hstc Hctx Hstkra Hstks0 H").
    iNext.
    iIntros "Hpc Hfile Hnpc Hmenv Hmcen Hmtime Hstc Hctx Hstkra Hstks0".
    (* ---- chunk c2 (idx 35..40): spc35 -> spc41.  a5 now holds c1's csrr value. ---- *)
    set (m1 := <[gpr_of_Z (uint srd34) := regval_into_reg (subrange_vec_dec mstatus0 (Z.sub xlen 1) 0)]>
              (<[gpr_of_Z (uint r_s0) := regval_into_reg (add_vec sp1 (sign_extend' 64 (caddi4spn_imm nzimm12)))]>
              (<[gpr_of_Z (uint rd9) := regval_into_reg sp1]> m))).
    assert (Hc2_14 : m1 !! gpr_of_Z 14 = Some va4).
    { unfold m1. replace (uint srd34) with 15 by (vm_compute; reflexivity).
      replace (uint r_s0) with 8 by (vm_compute; reflexivity).
      replace (uint rd9) with 2 by (vm_compute; reflexivity).
      do 3 (rewrite lookup_insert_ne; [| discriminate]). exact Hm14. }
    assert (Hc2_15 : m1 !! gpr_of_Z 15 = Some (regval_into_reg (subrange_vec_dec mstatus0 (Z.sub xlen 1) 0))).
    { unfold m1. replace (uint srd34) with 15 by (vm_compute; reflexivity).
      rewrite lookup_insert. reflexivity. }
    iApply (wp_st_c2 va4 (regval_into_reg (subrange_vec_dec mstatus0 (Z.sub xlen 1) 0)) m1
              mst0 spc35 mi0 mstatus0 menvcfg0 mtime0 stimecmp0 mcounteren0 mc mcfg pmpcfg0 elp0 E Φ
              HN Hc2_14 Hc2_15 Hpmpf HmIE Hlp
              with "Hpc Hfile Hnpc Hinv Hmenv Hmcen Hmtime Hstc Hctx H").
    iNext.
    iIntros "Hpc Hfile Hnpc Hmenv Hmcen Hmtime Hstc Hctx".
    (* ---- chunk c3 (idx 41..46): spc41 -> spc47.  csrw mstatus -> mstatus1; csrw mepc; satp. ---- *)
    set (m2 := <[gpr_of_Z (uint r_a5) := regval_into_reg va5_40]>
              (<[gpr_of_Z (uint (sit_rd sw39)) := regval_into_reg va4_39]>
              (<[gpr_of_Z (uint (sreg117 sw38)) := regval_into_reg va4_38]>
              (<[gpr_of_Z (uint r_a5) := regval_into_reg va5_37]>
              (<[gpr_of_Z (uint (sit_rd sw36)) := regval_into_reg va4_36]>
              (<[gpr_of_Z (uint (sreg117 sw35)) := regval_into_reg va4_35]> m1)))))).
    assert (Hc3_15 : m2 !! gpr_of_Z 15 = Some va5_40).
    { unfold m2. replace (uint r_a5) with 15 by (vm_compute; reflexivity).
      rewrite lookup_insert. reflexivity. }
    iApply (wp_st_c3 va5_40 m2 mst0 _ mi0 mstatus0 menvcfg0 mtime0 stimecmp0 mepc0 satp0
              mcounteren0 mc mcfg pmpcfg0 elp0 E Φ
              HN Hc3_15 Hpmpf HmIE Hlp HmIE1 HSXL1
              with "Hpc Hfile Hnpc Hinv Hmenv Hmcen Hmtime Hstc Hmepc Hsatp Hctx H").
    iNext.
    iIntros "Hpc Hfile Hnpc Hmenv Hmcen Hmtime Hstc Hmepc Hsatp Hctx".
    (* ---- chunk c4 (idx 47..50): spc47 -> spc51.  csrw medeleg/mideleg -> mideleg NONZERO (mdv0). ---- *)
    set (m3 := <[gpr_of_Z (uint (sreg117 sw45)) := regval_into_reg va5_45]>
              (<[gpr_of_Z (uint (sit_rd sw43)) := regval_into_reg va5_43]>
              (<[gpr_of_Z (uint srd42) := regval_into_reg va5_42]> m2))).
    assert (Hc4_15 : m3 !! gpr_of_Z 15 = Some va5_45).
    { unfold m3. replace (uint (sreg117 sw45)) with 15 by (vm_compute; reflexivity).
      rewrite lookup_insert. reflexivity. }
    (* extract persistent hw_config (kept) and rebuild ti_ctx for c4 *)
    iDestruct "Hctx" as "(#Hhw & Hpriv & Hhs & Hmdl & Hms & Help & Hpmpc)".
    iAssert (ti_ctx mstatus1 (zeros' 64) mc mcfg pmpcfg0 elp0)
      with "[Hpriv Hhs Hmdl Hms Help Hpmpc]" as "Hctx".
    { rewrite /ti_ctx. iFrame "Hhw". iFrame. }
    iApply (wp_st_c4 va5_45 m3 mst0 _ mi0 mstatus1 medeleg0 mc mcfg pmpcfg0 elp0 E Φ
              HN Hc4_15 Hpmpf HmIE1 Hlp
              with "Hpc Hfile Hnpc Hinv Hmede Hctx H").
    iNext.
    iIntros "Hpc Hfile Hnpc Hpriv Hhs Hmdl Hms Hmede Help Hpmpc".
    (* ---- chunk c5 (idx 51..58): spc51 -> spc59.  re-assemble ti_ctx with nonzero mdv0. ---- *)
    iAssert (ti_ctx mstatus1 mdv0 mc mcfg pmpcfg0 elp0)
      with "[Hhw Hpriv Hhs Hmdl Hms Help Hpmpc]" as "Hctx".
    { rewrite /ti_ctx. iFrame "Hhw". iFrame. }
    set (m4 := <[gpr_of_Z (uint (sreg117 sw48)) := regval_into_reg va5_48]>
              (<[gpr_of_Z (uint (sreg117 sw47)) := regval_into_reg va5_47]> m3)).
    assert (Hc5_15 : m4 !! gpr_of_Z 15 = Some va5_48).
    { unfold m4. replace (uint (sreg117 sw48)) with 15 by (vm_compute; reflexivity).
      rewrite lookup_insert. reflexivity. }
    iApply (wp_st_c5 va5_48 m4 mst0 _ mi0 mstatus1 mdv0 mie0 mc mcfg pmpcfg0 pmpaddr00 elp0 E Φ
              HN Hc5_15 Hpmpf HmIE1 Hlp
              with "Hpc Hfile Hnpc Hinv Hmie Hpmpaddr Hctx H").
    iNext.
    iIntros "Hpc Hfile Hnpc Hmie Hpmpaddr Hctx".
    (* ---- chunk c6 (idx 59..60): spc59 -> spc60.  jal timerinit (nested); csrr mhartid. ---- *)
    iDestruct "Hctx" as "(_ & Hpriv & Hhs & Hmdl & Hms & Help & Hpmpc)".
    set (m5 := <[gpr_of_Z (uint (sreg117 sw57)) := regval_into_reg va5_57]>
              (<[gpr_of_Z (uint r_a5) := regval_into_reg va5_55]>
              (<[gpr_of_Z (uint (sreg117 sw54)) := regval_into_reg va5_54]>
              (<[gpr_of_Z (uint (sit_rd sw52)) := regval_into_reg va5_52]>
              (<[gpr_of_Z (uint (scsr_rd sw51)) := regval_into_reg va5_51]> m4))))).
    assert (Hc6_1 : m5 !! gpr_of_Z 1 = Some vra).
    { unfold m5, m4, m3, m2, m1. repeat (rewrite lookup_insert_ne; [| vm_compute; discriminate]). exact Hm1. }
    assert (Hc6_2 : m5 !! gpr_of_Z 2 = Some sp1).
    { unfold m5, m4, m3, m2, m1. repeat (rewrite lookup_insert_ne; [| vm_compute; discriminate]).
      replace (uint rd9) with 2 by (vm_compute; reflexivity). rewrite lookup_insert. reflexivity. }
    assert (Hc6_8 : m5 !! gpr_of_Z 8 = Some (regval_into_reg (add_vec sp1 (sign_extend' 64 (caddi4spn_imm nzimm12))))).
    { unfold m5, m4, m3, m2, m1. repeat (rewrite lookup_insert_ne; [| vm_compute; discriminate]).
      replace (uint r_s0) with 8 by (vm_compute; reflexivity). rewrite lookup_insert. reflexivity. }
    assert (Hc6_14 : m5 !! gpr_of_Z 14 = Some va4_39).
    { unfold m5, m4, m3, m2, m1. repeat (rewrite lookup_insert_ne; [| vm_compute; discriminate]).
      rewrite lookup_insert. reflexivity. }
    assert (Hc6_15 : m5 !! gpr_of_Z 15 = Some va5_57).
    { unfold m5, m4, m3, m2, m1.
      replace (uint (sreg117 sw57)) with 15 by (vm_compute; reflexivity). rewrite lookup_insert. reflexivity. }
    assert (Hc6_4 : is_Some (m5 !! gpr_of_Z 4)).
    { unfold m5, m4, m3, m2, m1. repeat (rewrite lookup_insert_ne; [| vm_compute; discriminate]). exact Hm4. }
    iApply (wp_st_c6 sp1 vra (regval_into_reg (add_vec sp1 (sign_extend' 64 (caddi4spn_imm nzimm12)))) va4_39 va5_57 m5
              mst0 _ mi0 mstatus1 menvcfg0 (zeros' 64) mtime0 stimecmp0 mdv0 mhartid0
              mcounteren0 mc mcfg pmpcfg1 elp0 vti_ra vti_s0 E Φ
              HN Hc6_1 Hc6_2 Hc6_8 Hc6_14 Hc6_15 Hc6_4 Hpmpf1 HmIE1 Hlp HMPRV1
              Hta8ra Htpara Hta8s0 Htpas0
              with "Hpc Hfile Hnpc Hinv Hpriv Hhs Hmdl Hms Help Hmenv Hmcen Hmtime Hstc Hmhartid Hpmpc Hhw Htra Htrs0 H").
    iNext.
    iIntros "Hpc Hfile Hmhartid Hnpc Hpriv Hhs Hmdl Hms Help Hpmpc Hktx".
    (* ---- chunk c7 (idx 60..63): spc60 -> MRET.  Supervisor mode at PC = mepc. ---- *)
    iDestruct "Hfile" as (mfin) "[Hfile %Hfp]". destruct Hfp as [Hf15 [Hf4 Hf2]].
    iApply (wp_st_c7 mfin mst0 mi0 mstatus1 mdv0 (mepc_val va5_43) mhartid0 mc mcfg pmpcfg1
              newpriv lpe elp0 E Φ
              HN Hf15 Hf4 Hf2 Hpmpf1 HmIE1 Hlp Hnp Hnpm Hlpe
              with "Hpc Hfile Hmhartid Hnpc Hinv Hpriv Hhs Hmdl Hms Hmepc Help Hpmpc Hhw H").
    iNext.
    iIntros "Hpc Hnpc Hfile Hmhartid Hpriv Hhs Hmdl Hms Hmepc Help Hpmpc Hktx2".
    iDestruct "Hfile" as (mf2) "[Hfile %Hf2sp]".
    iApply "Hcont".
    iExists mf2.
    iFrame. iPureIntro. split; [exact Hf2sp | exact Hnpm].
  Qed.

  (* ===================================================================== *)
  (* wp_kernel : the WHOLE boot path from CPU reset (PC = 0x80000000) through *)
  (* _entry (wp_kernel_entry) and start() (wp_start, which calls timerinit)   *)
  (* up to and including the MRET into Supervisor mode.  This is the end-to-   *)
  (* end chain: CPU initialization -> _entry -> start -> (timerinit) -> mret.  *)
  (* ===================================================================== *)
  Lemma wp_kernel
      (v : bv 64) (sp0b mst0 mstatus0 : mword 64) (mi0 : bool) (elp0 : mword 1)
      (mc : mword 32) (mcfg : mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n)
      (x1_0 x10_0 x11_0 mhartid0 : mword 64)
      (m : gmap register_bitvector_64 (mword 64))
      (menvcfg0 mtime0 stimecmp0 mepc0 satp0 medeleg0 mie0 : mword 64)
      (mcounteren0 : mword 32) (pmpaddr00 : type_of_register pmpaddr_n)
      (vs0b va4b va5b : mword 64)
      (vold_ra vold_s0 vti_ra vti_s0 : bv 64) (newpriv : Privilege) (lpe : bool)
      E (Φ : mval -> iProp Σ) :
    let bb     := andb (eq_vec (_get_Counterin_IR mc) ('b"0"))
                       (eq_vec (counter_priv_filter_bit mcfg Machine) ('b"0")) in
    (* ---- _entry's computed values (reproduce wp_kernel_entry's let-chain) ---- *)
    let sp1e   := regval_into_reg (add_vec kpc0 (auipc_off imm_auipc)) in
    let eal    := add_vec sp1e (sign_extend' 64 imm_ld) in
    let a8l    := zero_extend' 64 (subrange_vec_dec eal (xlen - 0 - 1) 0) in
    let pal    := zero_extend' 64 (add_vec_int a8l (0 * 8)) in
    let bumpe  := fun mm => if bb then add_vec_int mm 1 else mm in
    let mst1   := if bb then add_vec_int mst0 1 else mst0 in
    let x2ld   := regval_into_reg (extend_value false (update_subrange_vec_dec (zeros' (8*1*8)) (8*(0+1)*8-1) (8*0*8) v)) in
    let x10l   := regval_into_reg luival in
    let x11c   := regval_into_reg mhartid0 in
    let x11a   := regval_into_reg (add_vec x11c (sign_extend' 64 (sign_extend' 12 imm_caddi))) in
    let x10m   := regval_into_reg (mult_to_bits_half xlen (mulop_mul.(mul_op_signed_rs1))
                    (mulop_mul.(mul_op_signed_rs2)) x10l x11a (mulop_mul.(mul_op_result_part))) in
    let x2add  := regval_into_reg (add_vec x2ld x10m) in
    let x1j    := regval_into_reg (add_vec_int kpc7 4) in
    let m8     := bumpe (bumpe (bumpe (bumpe (bumpe (bumpe (bumpe mst1)))))) in
    (* ---- start()'s values (wp_start's lets, with sp0 := x2add, va5 := va5b) ---- *)
    let sp1  := add_vec x2add (sign_extend' 64 (sign_extend' 12 imm9)) in
    let imm_ra := zero_extend' 12 (concat_vec uimm10 ('b"000")) in
    let pa_ra  := zero_extend' 64 (add_vec_int (zero_extend' 64 (subrange_vec_dec (add_vec sp1 (sign_extend' 64 imm_ra)) (xlen - 0 - 1) 0)) (0 * 8)) in
    let imm_s0 := zero_extend' 12 (concat_vec uimm11 ('b"000")) in
    let pa_s0  := zero_extend' 64 (add_vec_int (zero_extend' 64 (subrange_vec_dec (add_vec sp1 (sign_extend' 64 imm_s0)) (xlen - 0 - 1) 0)) (0 * 8)) in
    let a8_ra  := zero_extend' 64 (subrange_vec_dec (add_vec sp1 (sign_extend' 64 imm_ra)) (xlen - 0 - 1) 0) in
    let a8_s0  := zero_extend' 64 (subrange_vec_dec (add_vec sp1 (sign_extend' 64 imm_s0)) (xlen - 0 - 1) 0) in
    let va5_c2 := regval_into_reg (subrange_vec_dec mstatus0 (Z.sub xlen 1) 0) in
    let va4_35 := WpGprLui.luival (sign_extend' 20 (sclui_imm sw35)) in
    let va4_36 := add_vec va4_35 (sign_extend' 64 (subrange_vec_dec sw36 31 20)) in
    let va5_37 := and_vec va5_c2 va4_36 in
    let va4_38 := WpGprLui.luival (sign_extend' 20 (sclui_imm sw38)) in
    let va4_39 := add_vec va4_38 (sign_extend' 64 (subrange_vec_dec sw39 31 20)) in
    let va5_40 := or_vec va5_37 va4_39 in
    let mstatus1 := mstatus_legalized mstatus0 va5_40 in
    let va5_42 := add_vec spc42 (auipc_off (subrange_vec_dec sw42 31 12)) in
    let va5_43 := add_vec va5_42 (sign_extend' 64 (subrange_vec_dec sw43 31 20)) in
    let va5_45 := cli_wval (scli_imm sw45) in
    let va5_47 := WpGprLui.luival (sign_extend' 20 (sclui_imm sw47)) in
    let va5_48 := add_vec va5_47 (sign_extend' 64 (sign_extend' 12 (scli_imm sw48))) in
    let mdv0 := mideleg_legalized (zeros' 64) va5_48 in
    let va5_51 := lower_mie mie0 mdv0 in
    let va5_52 := or_vec va5_51 (sign_extend' 64 (subrange_vec_dec sw52 31 20)) in
    let va5_54 := cli_wval (scli_imm sw54) in
    let va5_55 := csrli_wval (scsrli_sh sw55) va5_54 in
    let va5_57 := cli_wval (scli_imm sw57) in
    let pmpcfg1 := pmpcfg0_finalvec va5_57 pmpcfg0 in
    let c6sp   := add_vec sp1 (sign_extend' 64 (sign_extend' 12 imm9)) in
    let tpa_ra := zero_extend' 64 (add_vec_int (zero_extend' 64 (subrange_vec_dec (add_vec c6sp (sign_extend' 64 imm_ra)) (xlen - 0 - 1) 0)) (0 * 8)) in
    let tpa_s0 := zero_extend' 64 (add_vec_int (zero_extend' 64 (subrange_vec_dec (add_vec c6sp (sign_extend' 64 imm_s0)) (xlen - 0 - 1) 0)) (0 * 8)) in
    let ta8_ra := zero_extend' 64 (subrange_vec_dec (add_vec c6sp (sign_extend' 64 imm_ra)) (xlen - 0 - 1) 0) in
    let ta8_s0 := zero_extend' 64 (subrange_vec_dec (add_vec c6sp (sign_extend' 64 imm_s0)) (xlen - 0 - 1) 0) in
    (* ---- _entry's hypotheses ---- *)
    ↑minstretN ⊆ E ->
    m !! x1 = Some x1_0 -> m !! x2 = Some sp0b ->
    m !! x10 = Some x10_0 -> m !! x11 = Some x11_0 ->
    m !! gpr_of_Z 8 = Some vs0b -> m !! gpr_of_Z 14 = Some va4b -> m !! gpr_of_Z 15 = Some va5b ->
    is_Some (m !! gpr_of_Z 4) ->
    pmp_allows_all pmpcfg0 ->
    eq_vec (_get_Mstatus_MIE mstatus0) ('b"1") = false ->
    eq_vec elp0 (landing_pad_bits_backwards LP_EXPECTED) = false ->
    eq_vec (_get_Mstatus_MPRV mstatus0) ('b"1") = false ->
    is_aligned_vaddr (Virtaddr a8l) 8 = true -> is_aligned_paddr (Physaddr pal) 8 = true ->
    (* ---- start()'s extra hypotheses (legalisation / MRET / stack alignment) ---- *)
    eq_vec (_get_Mstatus_MIE mstatus1) ('b"1") = false ->
    _get_Mstatus_SXL mstatus1 = 'b"10" ->
    is_aligned_vaddr (Virtaddr a8_ra) 8 = true -> is_aligned_paddr (Physaddr pa_ra) 8 = true ->
    is_aligned_vaddr (Virtaddr a8_s0) 8 = true -> is_aligned_paddr (Physaddr pa_s0) 8 = true ->
    eq_vec (_get_Mstatus_MPRV mstatus1) ('b"1") = false ->
    pmp_allows_all pmpcfg1 ->
    is_aligned_vaddr (Virtaddr ta8_ra) 8 = true -> is_aligned_paddr (Physaddr tpa_ra) 8 = true ->
    is_aligned_vaddr (Virtaddr ta8_s0) 8 = true -> is_aligned_paddr (Physaddr tpa_s0) 8 = true ->
    privLevel_bits_forwards (_get_Mstatus_MPP (cms2 mstatus1), ('b"0")) = returnM newpriv ->
    generic_neq newpriv Machine = true ->
    (forall sz, exec (get_xLPE newpriv) sz = Some (lpe, sz)) ->
    (* ---- boot resources (wp_kernel_entry) + start()'s held-aside resources ---- *)
    PC ↦ᵣ kpc0 -∗ gpr_file m -∗
    mhartid ↦ᵣ mhartid0 -∗
    nextPC ↦ᵣ kpc0 -∗ minstret_inv -∗
    cur_privilege ↦ᵣ Machine -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
    (R_bitvector_64 mideleg) ↦ᵣ zeros' 64 -∗ (R_bitvector_64 mstatus) ↦ᵣ mstatus0 -∗
    elp ↦ᵣ elp0 -∗ pmpcfg_n ↦ᵣ pmpcfg0 -∗
    hw_config mc mcfg -∗
    ([∗ list] j ∈ seq 0 8, (pa_add pal j) ↦ₘ nth_byte v j) -∗
    menvcfg ↦ᵣ menvcfg0 -∗ mcounteren ↦ᵣ mcounteren0 -∗ mtime ↦ᵣ mtime0 -∗ stimecmp ↦ᵣ stimecmp0 -∗
    mepc ↦ᵣ mepc0 -∗ satp ↦ᵣ satp0 -∗ medeleg ↦ᵣ medeleg0 -∗ mie ↦ᵣ mie0 -∗ pmpaddr_n ↦ᵣ pmpaddr00 -∗
    ([∗ list] j ∈ seq 0 8, (pa_add pa_ra j) ↦ₘ nth_byte vold_ra j) -∗
    ([∗ list] j ∈ seq 0 8, (pa_add pa_s0 j) ↦ₘ nth_byte vold_s0 j) -∗
    ([∗ list] j ∈ seq 0 8, (pa_add tpa_ra j) ↦ₘ nth_byte vti_ra j) -∗
    ([∗ list] j ∈ seq 0 8, (pa_add tpa_s0 j) ↦ₘ nth_byte vti_s0 j) -∗
    kernel_text -∗
    (* Post-MRET state exposed CONCRETELY (matches wp_start's post): PC =
       ctgt (mepc_val va5_43) = 0x80000e82 = <main>; Supervisor mode (newpriv);
       satp written Bare (satp_legalized satp0 va5_45, va5_45 = 0); only gpr_file
       (clobbered a4/a5), minstret and pmpaddr stay existential, with x2 (sp) shown
       present so the first S-mode instruction (c.addi sp,sp,-16) can chain. *)
    ▷ ( (∃ (mf : gmap register_bitvector_64 (mword 64)),
          PC ↦ᵣ ctgt (mepc_val va5_43) ∗ nextPC ↦ᵣ ctgt (mepc_val va5_43) ∗
          gpr_file mf ∗ ⌜ is_Some (mf !! gpr_of_Z 2) ⌝ ∗ mhartid ↦ᵣ mhartid0 ∗
          cur_privilege ↦ᵣ newpriv ∗ ⌜ generic_neq newpriv Machine = true ⌝ ∗ hart_state ↦ᵣ HART_ACTIVE tt ∗
          (R_bitvector_64 mideleg) ↦ᵣ mdv0 ∗ (R_bitvector_64 mstatus) ↦ᵣ cms5 mstatus1 ∗ mepc ↦ᵣ mepc_val va5_43 ∗
          satp ↦ᵣ satp_legalized satp0 va5_45 ∗
          elp ↦ᵣ celpv lpe mstatus1 ∗
          pmpcfg_n ↦ᵣ pmpcfg1 ∗ pmpaddr_n ↦ᵣ pmp0_newaddr pmpcfg0 pmpaddr00 va5_55 ∗
          mie ↦ᵣ sie_new_mie mie0 mdv0 va5_52 ∗ kernel_text)
        -∗ WP (Loop : expr riscv_lang) @ E {{ Φ }} ) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
 intros bb sp1e eal a8l pal bumpe mst1 x2ld x10l x11c x11a x10m x2add x1j m8
           sp1 imm_ra pa_ra imm_s0 pa_s0 a8_ra a8_s0 va5_c2 va4_35 va4_36 va5_37 va4_38 va4_39 va5_40 mstatus1
           va5_42 va5_43 va5_45 va5_47 va5_48 mdv0 va5_51 va5_52 va5_54 va5_55 va5_57 pmpcfg1
           c6sp tpa_ra tpa_s0 ta8_ra ta8_s0.
 intros HN Hm1 Hm2 Hm10 Hm11 Hm8 Hm14 Hm15 Hm4 Hpmpf HmIE Hlp HMPRV Ha8l Hpall
           HmIE1 HSXL1 Hsa8ra Hspara Hsa8s0 Hspas0 HMPRV1 Hpmpf1 Hta8ra Htpara Hta8s0 Htpas0 Hnp Hnpm Hlpe.
    iIntros "Hpc Hfile Hmh Hnpc #Hinv Hpriv Hhs Hmdl Hms Help Hpmpc #Hhw Hbytes
             Hmenv Hmcen Hmtime Hstc Hmepc Hsatp Hmede Hmie Hpmpaddr Hstkra Hstks0 Htra Htrs0 #H Hcont".
    (* ---- _entry: boot -> start entry (PC = kstart = spc30) ---- *)
    iApply (wp_kernel_entry sp0b mstatus0 elp0 v mc mcfg pmpcfg0
              x1_0 x10_0 x11_0 mhartid0 m E Φ
              HN Hm1 Hm2 Hm10 Hm11 Hpmpf HmIE Hlp HMPRV Ha8l Hpall
              with "Hpc Hfile Hmh Hnpc Hinv Hpriv Hhs Hmdl Hms Help Hpmpc Hhw Hbytes H").
    iNext.
    iIntros "Hpc Hfile Hmh Hnpc Hpriv Hhs Hmdl Hms Help Hpmpc Hbytes Hktx".
    (* _entry lands at kstart = 0x80000058 = spc30, the start() entry; convert so
       the points-to syntactically match wp_start's (iApply does not delta-unfold). *)
    assert (Hks : kstart = spc30) by reflexivity.
    iEval (rewrite Hks) in "Hpc". iEval (rewrite Hks) in "Hnpc".
    (* assemble ti_ctx for start() from _entry's (unchanged) output CSRs *)
    iAssert (ti_ctx mstatus0 (zeros' 64) mc mcfg pmpcfg0 elp0)
      with "[Hhw Hpriv Hhs Hmdl Hms Help Hpmpc]" as "Hctx".
    { rewrite /ti_ctx. iFrame "Hhw". iFrame. }
    (* lookups over _entry's output gpr file *)
    set (mE := <[x1:=x1j]> (<[x2:=x2add]> (<[x10:=x10m]> (<[x11:=x11a]> m)))).
    assert (HE1 : mE !! gpr_of_Z 1 = Some x1j).
    { unfold mE. change (gpr_of_Z 1) with x1. rewrite lookup_insert. reflexivity. }
    assert (HE2 : mE !! gpr_of_Z 2 = Some x2add).
    { unfold mE. change (gpr_of_Z 2) with x2. rewrite lookup_insert_ne; [| vm_compute; discriminate].
      rewrite lookup_insert. reflexivity. }
    assert (HE8 : mE !! gpr_of_Z 8 = Some vs0b).
    { unfold mE. repeat (rewrite lookup_insert_ne; [| vm_compute; discriminate]). exact Hm8. }
    assert (HE14 : mE !! gpr_of_Z 14 = Some va4b).
    { unfold mE. repeat (rewrite lookup_insert_ne; [| vm_compute; discriminate]). exact Hm14. }
    assert (HE15 : mE !! gpr_of_Z 15 = Some va5b).
    { unfold mE. repeat (rewrite lookup_insert_ne; [| vm_compute; discriminate]). exact Hm15. }
    assert (HE4 : is_Some (mE !! gpr_of_Z 4)).
    { unfold mE. repeat (rewrite lookup_insert_ne; [| vm_compute; discriminate]). exact Hm4. }
    (* ---- start(): start entry -> MRET (Supervisor mode) ---- *)
    iPoseProof (wp_start x2add x1j vs0b va4b va5b mE m8 kstart bb mstatus0 menvcfg0 mtime0 stimecmp0
              mhartid0 mepc0 satp0 medeleg0 mie0 mcounteren0 mc mcfg pmpcfg0 pmpaddr00 elp0
              vold_ra vold_s0 vti_ra vti_s0 newpriv lpe E Φ
              HN HE1 HE2 HE8 HE14 HE15 HE4 Hpmpf HmIE Hlp HMPRV HmIE1 HSXL1
              Hsa8ra Hspara Hsa8s0 Hspas0 HMPRV1 Hpmpf1 Hta8ra Htpara Hta8s0 Htpas0 Hnp Hnpm Hlpe
              with "Hpc Hfile Hnpc Hinv Hmenv Hmcen Hmtime Hstc Hmepc Hsatp Hmede Hmie Hpmpaddr Hmh Hctx
                    Hstkra Hstks0 Htra Htrs0 H Hcont") as "Hgoal".
    iExact "Hgoal".
  Qed.

End WpStart3.
