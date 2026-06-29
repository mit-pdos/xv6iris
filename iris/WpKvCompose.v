From Stdlib Require Import Eqdep_dec ZArith Lia List.
From stdpp Require Import gmap list list_monad bitvector.definitions bitvector.tactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre lifting.
Require Import MinstretInv.
From iris.base_logic.lib Require Import invariants.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvTryStep RiscvFetchExec RiscvExtras WpFetch WpDecode WpEntry WpGpr WpRvc WpAuipc WpGprCsrw WpAdd WpGprAddi WpLoad WpGprLoad WpGprStore WpSmode WpSmode2 WpKernelvec WpPageWalk WpStoreS WpStoreWalk WpStoreS2 WpKvStore WpKvJal WpKvTrap WpGprMret WpGprSret WpKvLoad WpKvLoadWp WpKvSret.
From Kernel Require Import KernelInstrs.
Local Open Scope Z_scope.
Import Defs.

(* WpKvCompose.v — wp_kv_jal_kerneltrap: the `jal kerneltrap` @va composed with
   the kerneltrap_returns axiom.  The jal sets ra := va+4 and jumps to the
   kerneltrap entry 0x800026a2; the axiom then runs the handler and returns to
   PC = va+4 with sp and the saved-register frame and the CSRs preserved.  This
   is the bridge that makes the kerneltrap axiom usable inside the kernelvec
   chain: prologue -> [this] -> ld restores -> addi -> sret. *)

Section KVCOMPOSE.
  Context `{!riscvGS Σ}.
  Context (root_ppn : mword 44).

  Lemma wp_kv_jal_kerneltrap (va : mword 64) (w : mword 32) (imm : mword 21)
      (m : gmap register_bitvector_64 (mword 64))
      (vsp vd misa0 mdv0 mstatus0 menvcfg0 mseccfg0 satp0 mie_v : mword 64)
      (b1 : bool) (npc0 : mword 64) (mc : mword 32) (mcfg : mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (pmpaddr00 : type_of_register pmpaddr_n)
      (pmar0 : list PMA_Region) (elp0 : mword 1)
      (tlbvec : vec (option TLB_Entry) (2 ^ 6)) (region_f : PMA_Region)
      (vra vgp vt0 vR5 vR6 vR7 vR8 vR9 vR10 vR11 vR12 vR13 vR14 vR15 vR16 vR17 vR18 : bv 64)
      (pa pa3 pa4 pa5 pa6 pa7 pa8 pa9 pa10 pa11 pa12 pa13 pa14 pa15 pa16 pa17 pa18 : mword 64)
      E {dq : dfrac} (Phi : mval -> iProp Σ) :
    ↑minstretN ⊆ E ->
    m !! gpr_of_Z 2 = Some vsp ->
    m !! gpr_of_Z 1 = Some vd ->
    add_vec va (sign_extend' 64 imm) = (mword_of_int 0x800026a2 : mword 64) ->
    _get_Mstatus_SXL mstatus0 = 'b"10" ->
    _get_Satp64_Mode (Mk_Satp64 satp0) = ('b"1000" : mword 4) ->
    zero_extend' 16 (satp_to_asid (autocast (T := mword) satp0 : mword 64)) = (mword_of_int 0 : mword 16) ->
    vec_access_dec tlbvec 5 = Some (pw_tlb_entry root_ppn (mword_of_int 0)) ->
    neq_vec (bits_of_virtaddr (Virtaddr va))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = sp_vpn ->
    zero_extend' 64 (concat_vec (mword_of_int 0x80005 : mword 44)
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub pagesize_bits 1) 0)) = va ->
    neq_vec (access_vec_dec va 0) ('b"0") = false ->
    neq_vec (access_vec_dec va 1) ('b"0") = false ->
    is_aligned_vaddr (Virtaddr va) 4 = true ->
    matching_pma_region pmar0 (Physaddr va) 4 = Some region_f ->
    (override_PMA (PMA_Region_attributes region_f) PBMT_PMA).(PMA_executable) = true ->
    pmpAddrMatchType_encdec_backwards (_get_Pmpcfg_ent_A (vec_access_dec pmpcfg0 0)) = TOR ->
    zopz0zKzJ_u (zeros' 64) (vec_access_dec pmpaddr00 0) = false ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
      (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4)
      (uint va) (uint (to_bits 64 4)) = PMP_Match ->
    eq_vec (_get_Pmpcfg_ent_X (vec_access_dec pmpcfg0 0)) ('b"1") = true ->
    is_aligned_paddr (Physaddr va) 4 = true ->
    eq_vec (_get_Misa_C misa0) ('b"1") = true ->
    eq_vec (_get_Misa_S misa0) ('b"1") = true ->
    isRVC (subrange_vec_dec w 15 0) = false ->
    (forall s0, register_lookup cur_privilege (sregs s0) = Supervisor ->
       exec (ext_decode w) s0 = Some (JAL (imm, Regidx (mword_of_int 1)), s0)) ->
    eq_vec (access_vec_dec (add_vec va (sign_extend' 64 imm)) 0) ('b"0") = true ->
    b1 = andb (eq_vec (_get_Counterin_IR mc) ('b"0"))
              (eq_vec (counter_priv_filter_bit mcfg Supervisor) ('b"0")) ->
    and_vec mie_v (not_vec mdv0) = zeros' 64 ->
    eq_vec (_get_Mstatus_SIE mstatus0) ('b"1") = false ->
    eq_vec elp0 (landing_pad_bits_backwards LP_EXPECTED) = false ->
    minstret_inv -∗
    PC ↦ᵣ va -∗ gpr_file m -∗ misa ↦ᵣ misa0 -∗ nextPC ↦ᵣ npc0 -∗
    cur_privilege ↦ᵣ Supervisor -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
    (R_bitvector_64 mideleg) ↦ᵣ mdv0 -∗ (R_bitvector_64 mstatus) ↦ᵣ mstatus0 -∗ satp ↦ᵣ satp0 -∗
    tlb ↦ᵣ tlbvec -∗ menvcfg ↦ᵣ menvcfg0 -∗ mseccfg ↦ᵣ mseccfg0 -∗ mie ↦ᵣ mie_v -∗
    elp ↦ᵣ elp0 -∗ mcountinhibit ↦ᵣ mc -∗ minstretcfg ↦ᵣ mcfg -∗
    pmpcfg_n ↦ᵣ pmpcfg0 -∗ pmpaddr_n ↦ᵣ pmpaddr00 -∗ pma_regions ↦ᵣ pmar0 -∗ htif_tohost_base ↦ᵣ None -∗
    ([∗ list] j ∈ seq 0 4, (pa_add va j) ↦ₘ{dq} nth_byte w j) -∗
    kv_cell pa vra -∗ kv_cell pa3 vgp -∗ kv_cell pa4 vt0 -∗ kv_cell pa5 vR5 -∗ kv_cell pa6 vR6 -∗
    kv_cell pa7 vR7 -∗ kv_cell pa8 vR8 -∗ kv_cell pa9 vR9 -∗ kv_cell pa10 vR10 -∗ kv_cell pa11 vR11 -∗
    kv_cell pa12 vR12 -∗ kv_cell pa13 vR13 -∗ kv_cell pa14 vR14 -∗ kv_cell pa15 vR15 -∗ kv_cell pa16 vR16 -∗
    kv_cell pa17 vR17 -∗ kv_cell pa18 vR18 -∗
    ▷ ( ∀ (m' : gmap register_bitvector_64 (mword 64)) (npc' : mword 64),
        ⌜ m' !! gpr_of_Z 2 = Some vsp ⌝ -∗
        PC ↦ᵣ regval_into_reg (add_vec_int va 4) -∗ nextPC ↦ᵣ npc' -∗ gpr_file m' -∗ minstret_inv -∗
        kv_csrs misa0 mdv0 mstatus0 menvcfg0 mseccfg0 satp0 mie_v mc mcfg elp0 pmpcfg0 pmpaddr00 pmar0 tlbvec -∗
        kv_cell pa vra -∗ kv_cell pa3 vgp -∗ kv_cell pa4 vt0 -∗ kv_cell pa5 vR5 -∗ kv_cell pa6 vR6 -∗
        kv_cell pa7 vR7 -∗ kv_cell pa8 vR8 -∗ kv_cell pa9 vR9 -∗ kv_cell pa10 vR10 -∗ kv_cell pa11 vR11 -∗
        kv_cell pa12 vR12 -∗ kv_cell pa13 vR13 -∗ kv_cell pa14 vR14 -∗ kv_cell pa15 vR15 -∗ kv_cell pa16 vR16 -∗
        kv_cell pa17 vR17 -∗ kv_cell pa18 vR18 -∗
        ([∗ list] j ∈ seq 0 4, (pa_add va j) ↦ₘ{dq} nth_byte w j) -∗
        WP (Loop : expr riscv_lang) @ E {{ Phi }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Phi }}.
  Proof.
    intros HN Hsp Hra Htgt HSXL Hmode Hasid Hvec5
      Hcanonf Hvpndeff Hidentf Hbit0 Hbit1 Halign4 Hmatchf Hexecf
      HA0 Hord0 Hrange0f HX0 Halignf HmisaC HmisaS HisRVC
      Hdec Hal0 Hb1 Hmie_mdl HSIE Help.
    iIntros "#Hinv Hpc Hfile Hmisa' Hnpc Hpriv Hhs Hmdl Hms Hsatp Htlb Hmenv Hsec Hmie Help' Hmcinh Hmcfg Hpmpc Hpmpaddr Hpma Hhtif Hibytes
                  Hc0 Hc3 Hc4 Hc5 Hc6 Hc7 Hc8 Hc9 Hc10 Hc11 Hc12 Hc13 Hc14 Hc15 Hc16 Hc17 Hc18 Hcont".
    (* ---- the jal: ra := va+4, jump to kerneltrap entry 0x800026a2 ---- *)
    iApply (wp_kv_jal root_ppn va w imm (mword_of_int 1)
              m vd misa0 mdv0 mstatus0 menvcfg0 mseccfg0 satp0 mie_v b1 npc0 mc mcfg
              pmpcfg0 pmpaddr00 pmar0 elp0 tlbvec region_f E Phi
              HN ltac:(vm_compute; discriminate) Hra HSXL Hmode Hasid Hvec5
              Hcanonf Hvpndeff Hidentf Hbit0 Hbit1 Halign4 Hmatchf Hexecf
              HA0 Hord0 Hrange0f HX0 Halignf HmisaC HmisaS HisRVC
              Hdec Hal0 Hb1 Hmie_mdl HSIE Help
              with "Hinv Hpc Hfile Hmisa' Hnpc Hpriv Hhs Hmdl Hms Hsatp Htlb Hmenv Hsec Hmie Help' Hmcinh Hmcfg Hpmpc Hpmpaddr Hpma Hhtif Hibytes").
    iNext.
    iIntros "Hpc Hfile Hmisa' Hnpc Hpriv Hhs Hmdl Hms Hsatp Htlb Hmenv Hsec Hmie Help' Hmcinh Hmcfg Hpmpc Hpmpaddr Hpma Hhtif Hibytes".
    (* PC and nextPC now hold the jump target = 0x800026a2 *)
    iEval (rewrite Htgt) in "Hpc".
    set (m' := <[gpr_of_Z (uint (mword_of_int 1 : mword 5)) := regval_into_reg (add_vec_int va 4)]> m).
    (* ---- the kerneltrap axiom: returns to PC = ra = va+4 ---- *)
    iApply (kerneltrap_returns m' vsp (regval_into_reg (add_vec_int va 4))
              vra vgp vt0 vR5 vR6 vR7 vR8 vR9 vR10 vR11 vR12 vR13 vR14 vR15 vR16 vR17 vR18
              pa pa3 pa4 pa5 pa6 pa7 pa8 pa9 pa10 pa11 pa12 pa13 pa14 pa15 pa16 pa17 pa18
              misa0 mdv0 mstatus0 menvcfg0 mseccfg0 satp0 mie_v mc mcfg elp0 pmpcfg0 pmpaddr00 pmar0 tlbvec
              (add_vec va (sign_extend' 64 imm)) E Phi
              ltac:(subst m'; rewrite lookup_insert_ne; [exact Hsp | vm_compute; discriminate])
              ltac:(subst m'; rewrite lookup_insert; reflexivity)
              with "Hpc Hnpc Hfile Hinv [$Hmisa' $Hpriv $Hhs $Hmdl $Hms $Hsatp $Htlb $Hmenv $Hsec $Hmie $Help' $Hmcinh $Hmcfg $Hpmpc $Hpmpaddr $Hpma $Hhtif]
                    Hc0 Hc3 Hc4 Hc5 Hc6 Hc7 Hc8 Hc9 Hc10 Hc11 Hc12 Hc13 Hc14 Hc15 Hc16 Hc17 Hc18 [Hcont Hibytes]").
    iNext.
    iIntros (m'' npc'') "Hsp'' Hpc Hnpc Hfile #Hinv2 Hcsrs Hc0 Hc3 Hc4 Hc5 Hc6 Hc7 Hc8 Hc9 Hc10 Hc11 Hc12 Hc13 Hc14 Hc15 Hc16 Hc17 Hc18".
    iApply ("Hcont" $! m'' npc'' with "Hsp'' Hpc Hnpc Hfile Hinv2 Hcsrs
              Hc0 Hc3 Hc4 Hc5 Hc6 Hc7 Hc8 Hc9 Hc10 Hc11 Hc12 Hc13 Hc14 Hc15 Hc16 Hc17 Hc18 Hibytes").
  Qed.

  (* ==================================================================== *)
  (* wp_kv_addi_sret: the kernelvec epilogue TAIL — `c.addi16sp sp,256`     *)
  (* @va (2-aligned) then `sret` @va+2 (4-aligned).  The addi restores sp;   *)
  (* the sret returns to PC = aligned sepc in privilege newpriv.  Demonstrates*)
  (* that wp_kv_addi16sp_2 and wp_kv_sret chain (CSRs/sepc threaded).        *)
  (* ==================================================================== *)
  Lemma wp_kv_addi_sret (va : mword 64) (wa : mword 16) (imm6 : mword 6) (ws : mword 32)
      (m : gmap register_bitvector_64 (mword 64))
      (vsp misa0 mdv0 mstatus0 satp0 mie_v sepc0 : mword 64)
      (b1 lpe : bool) (npc0 : mword 64) (mc : mword 32) (mcfg : mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (pmpaddr00 : type_of_register pmpaddr_n)
      (pmar0 : list PMA_Region) (elp0 : mword 1)
      (tlbvec : vec (option TLB_Entry) (2 ^ 6)) (region_a region_s : PMA_Region)
      E {dq : dfrac} (Phi : mval -> iProp Σ) :
    let vs := add_vec_int va 2 in
    ↑minstretN ⊆ E ->
    m !! gpr_of_Z 2 = Some vsp ->
    _get_Mstatus_SXL mstatus0 = 'b"10" ->
    _get_Satp64_Mode (Mk_Satp64 satp0) = ('b"1000" : mword 4) ->
    zero_extend' 16 (satp_to_asid (autocast (T := mword) satp0 : mword 64)) = (mword_of_int 0 : mword 16) ->
    vec_access_dec tlbvec 5 = Some (pw_tlb_entry root_ppn (mword_of_int 0)) ->
    (* addi @va (2-aligned) fetch facts *)
    neq_vec (bits_of_virtaddr (Virtaddr va))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = sp_vpn ->
    zero_extend' 64 (concat_vec (mword_of_int 0x80005 : mword 44)
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub pagesize_bits 1) 0)) = va ->
    neq_vec (access_vec_dec va 0) ('b"0") = false ->
    neq_vec (access_vec_dec va 1) ('b"0") = true ->
    is_aligned_vaddr (Virtaddr va) 4 = false ->
    matching_pma_region pmar0 (Physaddr va) 2 = Some region_a ->
    (override_PMA (PMA_Region_attributes region_a) PBMT_PMA).(PMA_executable) = true ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
      (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4)
      (uint va) (uint (to_bits 64 2)) = PMP_Match ->
    is_aligned_paddr (Physaddr va) 2 = true ->
    isRVC wa = true ->
    (forall s0, eq_vec (_get_Misa_C (register_lookup misa s0.(sregs))) ('b"1") = true ->
       exec (ext_decode_compressed wa) s0 = Some (C_ADDI16SP imm6, s0)) ->
    (* sret @vs (4-aligned) fetch facts *)
    neq_vec (bits_of_virtaddr (Virtaddr vs))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr vs)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr vs)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = sp_vpn ->
    zero_extend' 64 (concat_vec (mword_of_int 0x80005 : mword 44)
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr vs)) (Z.sub pagesize_bits 1) 0)) = vs ->
    neq_vec (access_vec_dec vs 0) ('b"0") = false ->
    neq_vec (access_vec_dec vs 1) ('b"0") = false ->
    is_aligned_vaddr (Virtaddr vs) 4 = true ->
    matching_pma_region pmar0 (Physaddr vs) 4 = Some region_s ->
    (override_PMA (PMA_Region_attributes region_s) PBMT_PMA).(PMA_executable) = true ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
      (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4)
      (uint vs) (uint (to_bits 64 4)) = PMP_Match ->
    is_aligned_paddr (Physaddr vs) 4 = true ->
    isRVC (subrange_vec_dec ws 15 0) = false ->
    eq_vec (_get_Mstatus_TSR mstatus0) ('b"1") = false ->
    (forall sz : mstate, exec (get_xLPE (sret_newpriv mstatus0)) sz = Some (lpe, sz)) ->
    (forall s0, register_lookup cur_privilege (sregs s0) = Supervisor ->
       exec (ext_decode ws) s0 = Some (SRET tt, s0)) ->
    (* shared CSR/PMP facts *)
    pmpAddrMatchType_encdec_backwards (_get_Pmpcfg_ent_A (vec_access_dec pmpcfg0 0)) = TOR ->
    zopz0zKzJ_u (zeros' 64) (vec_access_dec pmpaddr00 0) = false ->
    eq_vec (_get_Pmpcfg_ent_X (vec_access_dec pmpcfg0 0)) ('b"1") = true ->
    eq_vec (_get_Misa_C misa0) ('b"1") = true ->
    eq_vec (_get_Misa_S misa0) ('b"1") = true ->
    b1 = andb (eq_vec (_get_Counterin_IR mc) ('b"0"))
              (eq_vec (counter_priv_filter_bit mcfg Supervisor) ('b"0")) ->
    and_vec mie_v (not_vec mdv0) = zeros' 64 ->
    eq_vec (_get_Mstatus_SIE mstatus0) ('b"1") = false ->
    eq_vec elp0 (landing_pad_bits_backwards LP_EXPECTED) = false ->
    minstret_inv -∗
    PC ↦ᵣ va -∗ gpr_file m -∗ misa ↦ᵣ misa0 -∗ nextPC ↦ᵣ npc0 -∗
    cur_privilege ↦ᵣ Supervisor -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
    (R_bitvector_64 mideleg) ↦ᵣ mdv0 -∗ (R_bitvector_64 mstatus) ↦ᵣ mstatus0 -∗ satp ↦ᵣ satp0 -∗
    tlb ↦ᵣ tlbvec -∗ mie ↦ᵣ mie_v -∗ sepc ↦ᵣ sepc0 -∗
    elp ↦ᵣ elp0 -∗ mcountinhibit ↦ᵣ mc -∗ minstretcfg ↦ᵣ mcfg -∗
    pmpcfg_n ↦ᵣ pmpcfg0 -∗ pmpaddr_n ↦ᵣ pmpaddr00 -∗ pma_regions ↦ᵣ pmar0 -∗ htif_tohost_base ↦ᵣ None -∗
    ([∗ list] j ∈ seq 0 2, (pa_add va j) ↦ₘ{dq} nth_byte wa j) -∗
    ([∗ list] j ∈ seq 0 4, (pa_add vs j) ↦ₘ{dq} nth_byte ws j) -∗
    ▷ ( PC ↦ᵣ sret_tgt sepc0 -∗
        gpr_file (<[gpr_of_Z 2 := regval_into_reg (add_vec vsp (sign_extend' 64 (caddi16sp_imm imm6)))]> m) -∗
        misa ↦ᵣ misa0 -∗ nextPC ↦ᵣ sret_tgt sepc0 -∗
        cur_privilege ↦ᵣ sret_newpriv mstatus0 -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
        (R_bitvector_64 mideleg) ↦ᵣ mdv0 -∗ (R_bitvector_64 mstatus) ↦ᵣ sret_ms5 mstatus0 -∗ satp ↦ᵣ satp0 -∗
        tlb ↦ᵣ tlbvec -∗ mie ↦ᵣ mie_v -∗ sepc ↦ᵣ sepc0 -∗
        elp ↦ᵣ sret_elpv mstatus0 lpe -∗ mcountinhibit ↦ᵣ mc -∗ minstretcfg ↦ᵣ mcfg -∗
        pmpcfg_n ↦ᵣ pmpcfg0 -∗ pmpaddr_n ↦ᵣ pmpaddr00 -∗ pma_regions ↦ᵣ pmar0 -∗ htif_tohost_base ↦ᵣ None -∗
        ([∗ list] j ∈ seq 0 2, (pa_add va j) ↦ₘ{dq} nth_byte wa j) -∗
        ([∗ list] j ∈ seq 0 4, (pa_add vs j) ↦ₘ{dq} nth_byte ws j) -∗
        WP (Loop : expr riscv_lang) @ E {{ Phi }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Phi }}.
  Proof.
    intros vs HN Hsp HSXL Hmode Hasid Hvec5
      Hcanonfa Hvpndeffa Hidentfa Hbit0a Hbit1a Halign4a Hmatchfa Hexecfa Hrange0fa Halignfa HisRVCa Hdeca
      Hcanonfs Hvpndeffs Hidentfs Hbit0s Hbit1s Halign4s Hmatchfs Hexecfs Hrange0fs Halignfs HisRVCs HTSR0 Hlpe Hdecs
      HA0 Hord0 HX0 HmisaC HmisaS Hb1 Hmie_mdl HSIE Help.
    iIntros "#Hinv Hpc Hfile Hmisa' Hnpc Hpriv Hhs Hmdl Hms Hsatp Htlb Hmie Hsepc Help' Hmcinh Hmcfg Hpmpc Hpmpaddr Hpma Hhtif Hiba Hibs Hcont".
    (* ---- instruction 1: c.addi16sp sp, imm ---- *)
    iApply (wp_kv_addi16sp_2 root_ppn va wa imm6 m vsp misa0 mdv0 mstatus0 satp0 mie_v b1 npc0 mc mcfg
              pmpcfg0 pmpaddr00 pmar0 elp0 tlbvec region_a E Phi
              HN Hsp HSXL Hmode Hasid Hvec5 Hcanonfa Hvpndeffa Hidentfa Hbit0a Hbit1a Halign4a Hmatchfa Hexecfa
              HA0 Hord0 Hrange0fa HX0 Halignfa HisRVCa HmisaC HmisaS Hdeca Hb1 Hmie_mdl HSIE Help
              with "Hinv Hpc Hfile Hmisa' Hnpc Hpriv Hhs Hmdl Hms Hsatp Htlb Hmie Help' Hmcinh Hmcfg Hpmpc Hpmpaddr Hpma Hhtif Hiba").
    iNext.
    iIntros "Hpc Hfile Hmisa' Hnpc Hpriv Hhs Hmdl Hms Hsatp Htlb Hmie Help' Hmcinh Hmcfg Hpmpc Hpmpaddr Hpma Hhtif Hiba".
    (* PC now = va+2 = vs *)
    (* ---- instruction 2: sret ---- *)
    iApply (wp_kv_sret root_ppn vs ws
              (<[gpr_of_Z 2 := regval_into_reg (add_vec vsp (sign_extend' 64 (caddi16sp_imm imm6)))]> m)
              misa0 mdv0 mstatus0 satp0 mie_v sepc0 b1 lpe (add_vec_int va 2) mc mcfg
              pmpcfg0 pmpaddr00 pmar0 elp0 tlbvec region_s E Phi
              HN HSXL Hmode Hasid Hvec5 Hcanonfs Hvpndeffs Hidentfs Hbit0s Hbit1s Halign4s Hmatchfs Hexecfs
              HA0 Hord0 Hrange0fs HX0 Halignfs HmisaC HmisaS HisRVCs HTSR0 Hlpe Hdecs Hb1 Hmie_mdl HSIE Help
              with "Hinv Hpc Hfile Hmisa' Hnpc Hpriv Hhs Hmdl Hms Hsatp Htlb Hmie Hsepc Help' Hmcinh Hmcfg Hpmpc Hpmpaddr Hpma Hhtif Hibs").
    iNext.
    iIntros "Hpc Hfile Hmisa' Hnpc Hpriv Hhs Hmdl Hms Hsatp Htlb Hmie Hsepc Help' Hmcinh Hmcfg Hpmpc Hpmpaddr Hpma Hhtif Hibs".
    iApply ("Hcont" with "Hpc Hfile Hmisa' Hnpc Hpriv Hhs Hmdl Hms Hsatp Htlb Hmie Hsepc Help' Hmcinh Hmcfg Hpmpc Hpmpaddr Hpma Hhtif Hiba Hibs").
  Qed.

End KVCOMPOSE.
