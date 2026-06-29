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
        ⌜ dom m' = dom (<[gpr_of_Z 1 := regval_into_reg (add_vec_int va 4)]> m) ⌝ -∗
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
    iIntros (m'' npc'') "Hsp'' Hdom'' Hpc Hnpc Hfile #Hinv2 Hcsrs Hc0 Hc3 Hc4 Hc5 Hc6 Hc7 Hc8 Hc9 Hc10 Hc11 Hc12 Hc13 Hc14 Hc15 Hc16 Hc17 Hc18".
    iApply ("Hcont" $! m'' npc'' with "Hsp'' Hdom'' Hpc Hnpc Hfile Hinv2 Hcsrs
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

  Lemma wp_kernelvec_tail (va : mword 64) (wj : mword 32) (imm : mword 21) (wL0 : mword 32) (wL1 : mword 16) (wL2 : mword 32) (wL3 : mword 16) (wL4 : mword 32) (wL5 : mword 16) (wL6 : mword 32) (wL7 : mword 16) (wL8 : mword 32) (wL9 : mword 16) (wL10 : mword 32) (wL11 : mword 16) (wL12 : mword 32) (wL13 : mword 16) (wL14 : mword 32) (wL15 : mword 16) (wL16 : mword 32)
      (wA : mword 16) (immA : mword 6) (wS : mword 32) (svpn : mword 27)
      (m : gmap register_bitvector_64 (mword 64))
      (vsp vd misa0 mdv0 mstatus0 menvcfg0 mseccfg0 satp0 mie_v sepc0 : mword 64)
      (b1 lpe : bool) (npc0 : mword 64) (mc : mword 32) (mcfg : mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (pmpaddr00 : type_of_register pmpaddr_n)
      (pmar0 : list PMA_Region) (elp0 : mword 1)
      (tlbvec : vec (option TLB_Entry) (2 ^ 6)) (region_j region_A region_S : PMA_Region)
      (region_fL0 region_fL1 region_fL2 region_fL3 region_fL4 region_fL5 region_fL6 region_fL7 region_fL8 region_fL9 region_fL10 region_fL11 region_fL12 region_fL13 region_fL14 region_fL15 region_fL16 : PMA_Region) (region_lL0 region_lL1 region_lL2 region_lL3 region_lL4 region_lL5 region_lL6 region_lL7 region_lL8 region_lL9 region_lL10 region_lL11 region_lL12 region_lL13 region_lL14 region_lL15 region_lL16 : PMA_Region)
      (vLval0 vLval1 vLval2 vLval3 vLval4 vLval5 vLval6 vLval7 vLval8 vLval9 vLval10 vLval11 vLval12 vLval13 vLval14 vLval15 vLval16 : bv 64)
      E (Phi : mval -> iProp Σ) :
    let link := regval_into_reg (add_vec_int va 4) in
    let vL0 := add_vec_int va 4 in
    let vL1 := add_vec_int vL0 2 in
    let vL2 := add_vec_int vL1 2 in
    let vL3 := add_vec_int vL2 2 in
    let vL4 := add_vec_int vL3 2 in
    let vL5 := add_vec_int vL4 2 in
    let vL6 := add_vec_int vL5 2 in
    let vL7 := add_vec_int vL6 2 in
    let vL8 := add_vec_int vL7 2 in
    let vL9 := add_vec_int vL8 2 in
    let vL10 := add_vec_int vL9 2 in
    let vL11 := add_vec_int vL10 2 in
    let vL12 := add_vec_int vL11 2 in
    let vL13 := add_vec_int vL12 2 in
    let vL14 := add_vec_int vL13 2 in
    let vL15 := add_vec_int vL14 2 in
    let vL16 := add_vec_int vL15 2 in
    let vA := add_vec_int vL16 2 in
    let vS := add_vec_int vA 2 in
    let offL0 := sign_extend' 64 (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000"))) in
    let a8L0 := sign_extend' 64 (subrange_vec_dec (add_vec vsp offL0) (xlen - 0 - 1) 0) in
    let paL0 := zero_extend' 64 (add_vec_int a8L0 (0 * 8)) in
    let dL0 := update_subrange_vec_dec (zeros' (8*1*8)) (8*(0+1)*8-1) (8*0*8) vLval0 in
    let offL1 := sign_extend' 64 (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000"))) in
    let a8L1 := sign_extend' 64 (subrange_vec_dec (add_vec vsp offL1) (xlen - 0 - 1) 0) in
    let paL1 := zero_extend' 64 (add_vec_int a8L1 (0 * 8)) in
    let dL1 := update_subrange_vec_dec (zeros' (8*1*8)) (8*(0+1)*8-1) (8*0*8) vLval1 in
    let offL2 := sign_extend' 64 (zero_extend' 12 (concat_vec (mword_of_int 4 : mword 6) ('b"000"))) in
    let a8L2 := sign_extend' 64 (subrange_vec_dec (add_vec vsp offL2) (xlen - 0 - 1) 0) in
    let paL2 := zero_extend' 64 (add_vec_int a8L2 (0 * 8)) in
    let dL2 := update_subrange_vec_dec (zeros' (8*1*8)) (8*(0+1)*8-1) (8*0*8) vLval2 in
    let offL3 := sign_extend' 64 (zero_extend' 12 (concat_vec (mword_of_int 5 : mword 6) ('b"000"))) in
    let a8L3 := sign_extend' 64 (subrange_vec_dec (add_vec vsp offL3) (xlen - 0 - 1) 0) in
    let paL3 := zero_extend' 64 (add_vec_int a8L3 (0 * 8)) in
    let dL3 := update_subrange_vec_dec (zeros' (8*1*8)) (8*(0+1)*8-1) (8*0*8) vLval3 in
    let offL4 := sign_extend' 64 (zero_extend' 12 (concat_vec (mword_of_int 6 : mword 6) ('b"000"))) in
    let a8L4 := sign_extend' 64 (subrange_vec_dec (add_vec vsp offL4) (xlen - 0 - 1) 0) in
    let paL4 := zero_extend' 64 (add_vec_int a8L4 (0 * 8)) in
    let dL4 := update_subrange_vec_dec (zeros' (8*1*8)) (8*(0+1)*8-1) (8*0*8) vLval4 in
    let offL5 := sign_extend' 64 (zero_extend' 12 (concat_vec (mword_of_int 9 : mword 6) ('b"000"))) in
    let a8L5 := sign_extend' 64 (subrange_vec_dec (add_vec vsp offL5) (xlen - 0 - 1) 0) in
    let paL5 := zero_extend' 64 (add_vec_int a8L5 (0 * 8)) in
    let dL5 := update_subrange_vec_dec (zeros' (8*1*8)) (8*(0+1)*8-1) (8*0*8) vLval5 in
    let offL6 := sign_extend' 64 (zero_extend' 12 (concat_vec (mword_of_int 10 : mword 6) ('b"000"))) in
    let a8L6 := sign_extend' 64 (subrange_vec_dec (add_vec vsp offL6) (xlen - 0 - 1) 0) in
    let paL6 := zero_extend' 64 (add_vec_int a8L6 (0 * 8)) in
    let dL6 := update_subrange_vec_dec (zeros' (8*1*8)) (8*(0+1)*8-1) (8*0*8) vLval6 in
    let offL7 := sign_extend' 64 (zero_extend' 12 (concat_vec (mword_of_int 11 : mword 6) ('b"000"))) in
    let a8L7 := sign_extend' 64 (subrange_vec_dec (add_vec vsp offL7) (xlen - 0 - 1) 0) in
    let paL7 := zero_extend' 64 (add_vec_int a8L7 (0 * 8)) in
    let dL7 := update_subrange_vec_dec (zeros' (8*1*8)) (8*(0+1)*8-1) (8*0*8) vLval7 in
    let offL8 := sign_extend' 64 (zero_extend' 12 (concat_vec (mword_of_int 12 : mword 6) ('b"000"))) in
    let a8L8 := sign_extend' 64 (subrange_vec_dec (add_vec vsp offL8) (xlen - 0 - 1) 0) in
    let paL8 := zero_extend' 64 (add_vec_int a8L8 (0 * 8)) in
    let dL8 := update_subrange_vec_dec (zeros' (8*1*8)) (8*(0+1)*8-1) (8*0*8) vLval8 in
    let offL9 := sign_extend' 64 (zero_extend' 12 (concat_vec (mword_of_int 13 : mword 6) ('b"000"))) in
    let a8L9 := sign_extend' 64 (subrange_vec_dec (add_vec vsp offL9) (xlen - 0 - 1) 0) in
    let paL9 := zero_extend' 64 (add_vec_int a8L9 (0 * 8)) in
    let dL9 := update_subrange_vec_dec (zeros' (8*1*8)) (8*(0+1)*8-1) (8*0*8) vLval9 in
    let offL10 := sign_extend' 64 (zero_extend' 12 (concat_vec (mword_of_int 14 : mword 6) ('b"000"))) in
    let a8L10 := sign_extend' 64 (subrange_vec_dec (add_vec vsp offL10) (xlen - 0 - 1) 0) in
    let paL10 := zero_extend' 64 (add_vec_int a8L10 (0 * 8)) in
    let dL10 := update_subrange_vec_dec (zeros' (8*1*8)) (8*(0+1)*8-1) (8*0*8) vLval10 in
    let offL11 := sign_extend' 64 (zero_extend' 12 (concat_vec (mword_of_int 15 : mword 6) ('b"000"))) in
    let a8L11 := sign_extend' 64 (subrange_vec_dec (add_vec vsp offL11) (xlen - 0 - 1) 0) in
    let paL11 := zero_extend' 64 (add_vec_int a8L11 (0 * 8)) in
    let dL11 := update_subrange_vec_dec (zeros' (8*1*8)) (8*(0+1)*8-1) (8*0*8) vLval11 in
    let offL12 := sign_extend' 64 (zero_extend' 12 (concat_vec (mword_of_int 16 : mword 6) ('b"000"))) in
    let a8L12 := sign_extend' 64 (subrange_vec_dec (add_vec vsp offL12) (xlen - 0 - 1) 0) in
    let paL12 := zero_extend' 64 (add_vec_int a8L12 (0 * 8)) in
    let dL12 := update_subrange_vec_dec (zeros' (8*1*8)) (8*(0+1)*8-1) (8*0*8) vLval12 in
    let offL13 := sign_extend' 64 (zero_extend' 12 (concat_vec (mword_of_int 27 : mword 6) ('b"000"))) in
    let a8L13 := sign_extend' 64 (subrange_vec_dec (add_vec vsp offL13) (xlen - 0 - 1) 0) in
    let paL13 := zero_extend' 64 (add_vec_int a8L13 (0 * 8)) in
    let dL13 := update_subrange_vec_dec (zeros' (8*1*8)) (8*(0+1)*8-1) (8*0*8) vLval13 in
    let offL14 := sign_extend' 64 (zero_extend' 12 (concat_vec (mword_of_int 28 : mword 6) ('b"000"))) in
    let a8L14 := sign_extend' 64 (subrange_vec_dec (add_vec vsp offL14) (xlen - 0 - 1) 0) in
    let paL14 := zero_extend' 64 (add_vec_int a8L14 (0 * 8)) in
    let dL14 := update_subrange_vec_dec (zeros' (8*1*8)) (8*(0+1)*8-1) (8*0*8) vLval14 in
    let offL15 := sign_extend' 64 (zero_extend' 12 (concat_vec (mword_of_int 29 : mword 6) ('b"000"))) in
    let a8L15 := sign_extend' 64 (subrange_vec_dec (add_vec vsp offL15) (xlen - 0 - 1) 0) in
    let paL15 := zero_extend' 64 (add_vec_int a8L15 (0 * 8)) in
    let dL15 := update_subrange_vec_dec (zeros' (8*1*8)) (8*(0+1)*8-1) (8*0*8) vLval15 in
    let offL16 := sign_extend' 64 (zero_extend' 12 (concat_vec (mword_of_int 30 : mword 6) ('b"000"))) in
    let a8L16 := sign_extend' 64 (subrange_vec_dec (add_vec vsp offL16) (xlen - 0 - 1) 0) in
    let paL16 := zero_extend' 64 (add_vec_int a8L16 (0 * 8)) in
    let dL16 := update_subrange_vec_dec (zeros' (8*1*8)) (8*(0+1)*8-1) (8*0*8) vLval16 in
    ↑minstretN ⊆ E ->
    m !! gpr_of_Z 2 = Some vsp ->
    m !! gpr_of_Z 1 = Some vd ->
    (exists vo, m !! gpr_of_Z 1 = Some vo) ->
    (exists vo, m !! gpr_of_Z 3 = Some vo) ->
    (exists vo, m !! gpr_of_Z 5 = Some vo) ->
    (exists vo, m !! gpr_of_Z 6 = Some vo) ->
    (exists vo, m !! gpr_of_Z 7 = Some vo) ->
    (exists vo, m !! gpr_of_Z 10 = Some vo) ->
    (exists vo, m !! gpr_of_Z 11 = Some vo) ->
    (exists vo, m !! gpr_of_Z 12 = Some vo) ->
    (exists vo, m !! gpr_of_Z 13 = Some vo) ->
    (exists vo, m !! gpr_of_Z 14 = Some vo) ->
    (exists vo, m !! gpr_of_Z 15 = Some vo) ->
    (exists vo, m !! gpr_of_Z 16 = Some vo) ->
    (exists vo, m !! gpr_of_Z 17 = Some vo) ->
    (exists vo, m !! gpr_of_Z 28 = Some vo) ->
    (exists vo, m !! gpr_of_Z 29 = Some vo) ->
    (exists vo, m !! gpr_of_Z 30 = Some vo) ->
    (exists vo, m !! gpr_of_Z 31 = Some vo) ->
    _get_Mstatus_SXL mstatus0 = 'b"10" ->
    _get_Satp64_Mode (Mk_Satp64 satp0) = ('b"1000" : mword 4) ->
    zero_extend' 16 (satp_to_asid (autocast (T := mword) satp0 : mword 64)) = (mword_of_int 0 : mword 16) ->
    vec_access_dec tlbvec 5 = Some (pw_tlb_entry root_ppn (mword_of_int 0)) ->
    vec_access_dec tlbvec (tlb_hash (__id 39) svpn) = Some (pw_tlb_entry root_ppn (mword_of_int 0)) ->
    and_vec (sign_extend' (57 - 12) svpn) (not_vec (mword_of_int 0x3FFFF : mword 45)) = (mword_of_int 0x80000 : mword 45) ->
    pmm_mode_backwards (_get_MEnvcfg_PMM menvcfg0) = PMM_Disabled ->
    pmpAddrMatchType_encdec_backwards (_get_Pmpcfg_ent_A (vec_access_dec pmpcfg0 0)) = TOR ->
    zopz0zKzJ_u (zeros' 64) (vec_access_dec pmpaddr00 0) = false ->
    eq_vec (_get_Pmpcfg_ent_X (vec_access_dec pmpcfg0 0)) ('b"1") = true ->
    eq_vec (_get_Pmpcfg_ent_R (vec_access_dec pmpcfg0 0)) ('b"1") = true ->
    eq_vec (_get_Misa_C misa0) ('b"1") = true ->
    eq_vec (_get_Misa_S misa0) ('b"1") = true ->
    eq_vec (_get_Mstatus_MPRV mstatus0) ('b"1") = false ->
    eq_vec (_get_Mstatus_MXR mstatus0) ('b"0") = true ->
    b1 = andb (eq_vec (_get_Counterin_IR mc) ('b"0")) (eq_vec (counter_priv_filter_bit mcfg Supervisor) ('b"0")) ->
    and_vec mie_v (not_vec mdv0) = zeros' 64 ->
    eq_vec (_get_Mstatus_SIE mstatus0) ('b"1") = false ->
    eq_vec elp0 (landing_pad_bits_backwards LP_EXPECTED) = false ->
    eq_vec (_get_Mstatus_TSR mstatus0) ('b"1") = false ->
    (forall sz : mstate, exec (get_xLPE (sret_newpriv mstatus0)) sz = Some (lpe, sz)) ->
    neq_vec (bits_of_virtaddr (Virtaddr va)) (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = sp_vpn ->
    zero_extend' 64 (concat_vec (mword_of_int 0x80005 : mword 44) (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub pagesize_bits 1) 0)) = va ->
    neq_vec (access_vec_dec va 0) ('b"0") = false ->
    neq_vec (access_vec_dec va 1) ('b"0") = false ->
    is_aligned_vaddr (Virtaddr va) 4 = true ->
    matching_pma_region pmar0 (Physaddr va) 4 = Some region_j ->
    (override_PMA (PMA_Region_attributes region_j) PBMT_PMA).(PMA_executable) = true ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4) (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4) (uint va) (uint (to_bits 64 4)) = PMP_Match ->
    is_aligned_paddr (Physaddr va) 4 = true ->
    isRVC (subrange_vec_dec wj 15 0) = false ->
    add_vec va (sign_extend' 64 imm) = (mword_of_int 0x800026a2 : mword 64) ->
    (forall s0, register_lookup cur_privilege (sregs s0) = Supervisor -> exec (ext_decode wj) s0 = Some (JAL (imm, Regidx (mword_of_int 1)), s0)) ->
    eq_vec (access_vec_dec (add_vec va (sign_extend' 64 imm)) 0) ('b"0") = true ->
    neq_vec (bits_of_virtaddr (Virtaddr vL0)) (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr vL0)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec (subrange_vec_dec (bits_of_virtaddr (Virtaddr vL0)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = sp_vpn ->
    zero_extend' 64 (concat_vec (mword_of_int 0x80005 : mword 44) (subrange_vec_dec (bits_of_virtaddr (Virtaddr vL0)) (Z.sub pagesize_bits 1) 0)) = vL0 ->
    neq_vec (access_vec_dec vL0 0) ('b"0") = false ->
    neq_vec (access_vec_dec vL0 1) ('b"0") = false ->
    is_aligned_vaddr (Virtaddr vL0) 4 = true ->
    neq_vec (bits_of_virtaddr (Virtaddr a8L0)) (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8L0)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8L0)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = svpn ->
    zero_extend' 64 (concat_vec (tlb_get_ppn 39 (pw_tlb_entry root_ppn (mword_of_int 0)) svpn) (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8L0)) (Z.sub pagesize_bits 1) 0)) = a8L0 ->
    matching_pma_region pmar0 (Physaddr vL0) 4 = Some region_fL0 ->
    (override_PMA (PMA_Region_attributes region_fL0) PBMT_PMA).(PMA_executable) = true ->
    matching_pma_region pmar0 (Physaddr paL0) 8 = Some region_lL0 ->
    (override_PMA (PMA_Region_attributes region_lL0) PBMT_PMA).(PMA_readable) = true ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4) (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4) (uint vL0) (uint (to_bits 64 4)) = PMP_Match ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4) (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4) (uint paL0) (uint (to_bits 64 8)) = PMP_Match ->
    is_aligned_paddr (Physaddr vL0) 4 = true ->
    is_aligned_vaddr (Virtaddr a8L0) 8 = true ->
    is_aligned_paddr (Physaddr paL0) 8 = true ->
    isRVC (subrange_vec_dec wL0 15 0) = true ->
    (forall s0, eq_vec (_get_Misa_C (register_lookup misa s0.(sregs))) ('b"1") = true -> exec (ext_decode_compressed (subrange_vec_dec wL0 15 0)) s0 = Some (C_LDSP (mword_of_int 0, Regidx (mword_of_int 1)), s0)) ->
    neq_vec (bits_of_virtaddr (Virtaddr vL1)) (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr vL1)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec (subrange_vec_dec (bits_of_virtaddr (Virtaddr vL1)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = sp_vpn ->
    zero_extend' 64 (concat_vec (mword_of_int 0x80005 : mword 44) (subrange_vec_dec (bits_of_virtaddr (Virtaddr vL1)) (Z.sub pagesize_bits 1) 0)) = vL1 ->
    neq_vec (access_vec_dec vL1 0) ('b"0") = false ->
    neq_vec (access_vec_dec vL1 1) ('b"0") = true ->
    is_aligned_vaddr (Virtaddr vL1) 4 = false ->
    neq_vec (bits_of_virtaddr (Virtaddr a8L1)) (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8L1)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8L1)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = svpn ->
    zero_extend' 64 (concat_vec (tlb_get_ppn 39 (pw_tlb_entry root_ppn (mword_of_int 0)) svpn) (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8L1)) (Z.sub pagesize_bits 1) 0)) = a8L1 ->
    matching_pma_region pmar0 (Physaddr vL1) 2 = Some region_fL1 ->
    (override_PMA (PMA_Region_attributes region_fL1) PBMT_PMA).(PMA_executable) = true ->
    matching_pma_region pmar0 (Physaddr paL1) 8 = Some region_lL1 ->
    (override_PMA (PMA_Region_attributes region_lL1) PBMT_PMA).(PMA_readable) = true ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4) (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4) (uint vL1) (uint (to_bits 64 2)) = PMP_Match ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4) (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4) (uint paL1) (uint (to_bits 64 8)) = PMP_Match ->
    is_aligned_paddr (Physaddr vL1) 2 = true ->
    is_aligned_vaddr (Virtaddr a8L1) 8 = true ->
    is_aligned_paddr (Physaddr paL1) 8 = true ->
    isRVC wL1 = true ->
    (forall s0, eq_vec (_get_Misa_C (register_lookup misa s0.(sregs))) ('b"1") = true -> exec (ext_decode_compressed wL1) s0 = Some (C_LDSP (mword_of_int 2, Regidx (mword_of_int 3)), s0)) ->
    neq_vec (bits_of_virtaddr (Virtaddr vL2)) (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr vL2)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec (subrange_vec_dec (bits_of_virtaddr (Virtaddr vL2)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = sp_vpn ->
    zero_extend' 64 (concat_vec (mword_of_int 0x80005 : mword 44) (subrange_vec_dec (bits_of_virtaddr (Virtaddr vL2)) (Z.sub pagesize_bits 1) 0)) = vL2 ->
    neq_vec (access_vec_dec vL2 0) ('b"0") = false ->
    neq_vec (access_vec_dec vL2 1) ('b"0") = false ->
    is_aligned_vaddr (Virtaddr vL2) 4 = true ->
    neq_vec (bits_of_virtaddr (Virtaddr a8L2)) (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8L2)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8L2)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = svpn ->
    zero_extend' 64 (concat_vec (tlb_get_ppn 39 (pw_tlb_entry root_ppn (mword_of_int 0)) svpn) (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8L2)) (Z.sub pagesize_bits 1) 0)) = a8L2 ->
    matching_pma_region pmar0 (Physaddr vL2) 4 = Some region_fL2 ->
    (override_PMA (PMA_Region_attributes region_fL2) PBMT_PMA).(PMA_executable) = true ->
    matching_pma_region pmar0 (Physaddr paL2) 8 = Some region_lL2 ->
    (override_PMA (PMA_Region_attributes region_lL2) PBMT_PMA).(PMA_readable) = true ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4) (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4) (uint vL2) (uint (to_bits 64 4)) = PMP_Match ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4) (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4) (uint paL2) (uint (to_bits 64 8)) = PMP_Match ->
    is_aligned_paddr (Physaddr vL2) 4 = true ->
    is_aligned_vaddr (Virtaddr a8L2) 8 = true ->
    is_aligned_paddr (Physaddr paL2) 8 = true ->
    isRVC (subrange_vec_dec wL2 15 0) = true ->
    (forall s0, eq_vec (_get_Misa_C (register_lookup misa s0.(sregs))) ('b"1") = true -> exec (ext_decode_compressed (subrange_vec_dec wL2 15 0)) s0 = Some (C_LDSP (mword_of_int 4, Regidx (mword_of_int 5)), s0)) ->
    neq_vec (bits_of_virtaddr (Virtaddr vL3)) (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr vL3)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec (subrange_vec_dec (bits_of_virtaddr (Virtaddr vL3)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = sp_vpn ->
    zero_extend' 64 (concat_vec (mword_of_int 0x80005 : mword 44) (subrange_vec_dec (bits_of_virtaddr (Virtaddr vL3)) (Z.sub pagesize_bits 1) 0)) = vL3 ->
    neq_vec (access_vec_dec vL3 0) ('b"0") = false ->
    neq_vec (access_vec_dec vL3 1) ('b"0") = true ->
    is_aligned_vaddr (Virtaddr vL3) 4 = false ->
    neq_vec (bits_of_virtaddr (Virtaddr a8L3)) (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8L3)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8L3)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = svpn ->
    zero_extend' 64 (concat_vec (tlb_get_ppn 39 (pw_tlb_entry root_ppn (mword_of_int 0)) svpn) (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8L3)) (Z.sub pagesize_bits 1) 0)) = a8L3 ->
    matching_pma_region pmar0 (Physaddr vL3) 2 = Some region_fL3 ->
    (override_PMA (PMA_Region_attributes region_fL3) PBMT_PMA).(PMA_executable) = true ->
    matching_pma_region pmar0 (Physaddr paL3) 8 = Some region_lL3 ->
    (override_PMA (PMA_Region_attributes region_lL3) PBMT_PMA).(PMA_readable) = true ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4) (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4) (uint vL3) (uint (to_bits 64 2)) = PMP_Match ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4) (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4) (uint paL3) (uint (to_bits 64 8)) = PMP_Match ->
    is_aligned_paddr (Physaddr vL3) 2 = true ->
    is_aligned_vaddr (Virtaddr a8L3) 8 = true ->
    is_aligned_paddr (Physaddr paL3) 8 = true ->
    isRVC wL3 = true ->
    (forall s0, eq_vec (_get_Misa_C (register_lookup misa s0.(sregs))) ('b"1") = true -> exec (ext_decode_compressed wL3) s0 = Some (C_LDSP (mword_of_int 5, Regidx (mword_of_int 6)), s0)) ->
    neq_vec (bits_of_virtaddr (Virtaddr vL4)) (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr vL4)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec (subrange_vec_dec (bits_of_virtaddr (Virtaddr vL4)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = sp_vpn ->
    zero_extend' 64 (concat_vec (mword_of_int 0x80005 : mword 44) (subrange_vec_dec (bits_of_virtaddr (Virtaddr vL4)) (Z.sub pagesize_bits 1) 0)) = vL4 ->
    neq_vec (access_vec_dec vL4 0) ('b"0") = false ->
    neq_vec (access_vec_dec vL4 1) ('b"0") = false ->
    is_aligned_vaddr (Virtaddr vL4) 4 = true ->
    neq_vec (bits_of_virtaddr (Virtaddr a8L4)) (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8L4)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8L4)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = svpn ->
    zero_extend' 64 (concat_vec (tlb_get_ppn 39 (pw_tlb_entry root_ppn (mword_of_int 0)) svpn) (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8L4)) (Z.sub pagesize_bits 1) 0)) = a8L4 ->
    matching_pma_region pmar0 (Physaddr vL4) 4 = Some region_fL4 ->
    (override_PMA (PMA_Region_attributes region_fL4) PBMT_PMA).(PMA_executable) = true ->
    matching_pma_region pmar0 (Physaddr paL4) 8 = Some region_lL4 ->
    (override_PMA (PMA_Region_attributes region_lL4) PBMT_PMA).(PMA_readable) = true ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4) (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4) (uint vL4) (uint (to_bits 64 4)) = PMP_Match ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4) (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4) (uint paL4) (uint (to_bits 64 8)) = PMP_Match ->
    is_aligned_paddr (Physaddr vL4) 4 = true ->
    is_aligned_vaddr (Virtaddr a8L4) 8 = true ->
    is_aligned_paddr (Physaddr paL4) 8 = true ->
    isRVC (subrange_vec_dec wL4 15 0) = true ->
    (forall s0, eq_vec (_get_Misa_C (register_lookup misa s0.(sregs))) ('b"1") = true -> exec (ext_decode_compressed (subrange_vec_dec wL4 15 0)) s0 = Some (C_LDSP (mword_of_int 6, Regidx (mword_of_int 7)), s0)) ->
    neq_vec (bits_of_virtaddr (Virtaddr vL5)) (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr vL5)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec (subrange_vec_dec (bits_of_virtaddr (Virtaddr vL5)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = sp_vpn ->
    zero_extend' 64 (concat_vec (mword_of_int 0x80005 : mword 44) (subrange_vec_dec (bits_of_virtaddr (Virtaddr vL5)) (Z.sub pagesize_bits 1) 0)) = vL5 ->
    neq_vec (access_vec_dec vL5 0) ('b"0") = false ->
    neq_vec (access_vec_dec vL5 1) ('b"0") = true ->
    is_aligned_vaddr (Virtaddr vL5) 4 = false ->
    neq_vec (bits_of_virtaddr (Virtaddr a8L5)) (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8L5)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8L5)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = svpn ->
    zero_extend' 64 (concat_vec (tlb_get_ppn 39 (pw_tlb_entry root_ppn (mword_of_int 0)) svpn) (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8L5)) (Z.sub pagesize_bits 1) 0)) = a8L5 ->
    matching_pma_region pmar0 (Physaddr vL5) 2 = Some region_fL5 ->
    (override_PMA (PMA_Region_attributes region_fL5) PBMT_PMA).(PMA_executable) = true ->
    matching_pma_region pmar0 (Physaddr paL5) 8 = Some region_lL5 ->
    (override_PMA (PMA_Region_attributes region_lL5) PBMT_PMA).(PMA_readable) = true ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4) (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4) (uint vL5) (uint (to_bits 64 2)) = PMP_Match ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4) (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4) (uint paL5) (uint (to_bits 64 8)) = PMP_Match ->
    is_aligned_paddr (Physaddr vL5) 2 = true ->
    is_aligned_vaddr (Virtaddr a8L5) 8 = true ->
    is_aligned_paddr (Physaddr paL5) 8 = true ->
    isRVC wL5 = true ->
    (forall s0, eq_vec (_get_Misa_C (register_lookup misa s0.(sregs))) ('b"1") = true -> exec (ext_decode_compressed wL5) s0 = Some (C_LDSP (mword_of_int 9, Regidx (mword_of_int 10)), s0)) ->
    neq_vec (bits_of_virtaddr (Virtaddr vL6)) (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr vL6)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec (subrange_vec_dec (bits_of_virtaddr (Virtaddr vL6)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = sp_vpn ->
    zero_extend' 64 (concat_vec (mword_of_int 0x80005 : mword 44) (subrange_vec_dec (bits_of_virtaddr (Virtaddr vL6)) (Z.sub pagesize_bits 1) 0)) = vL6 ->
    neq_vec (access_vec_dec vL6 0) ('b"0") = false ->
    neq_vec (access_vec_dec vL6 1) ('b"0") = false ->
    is_aligned_vaddr (Virtaddr vL6) 4 = true ->
    neq_vec (bits_of_virtaddr (Virtaddr a8L6)) (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8L6)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8L6)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = svpn ->
    zero_extend' 64 (concat_vec (tlb_get_ppn 39 (pw_tlb_entry root_ppn (mword_of_int 0)) svpn) (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8L6)) (Z.sub pagesize_bits 1) 0)) = a8L6 ->
    matching_pma_region pmar0 (Physaddr vL6) 4 = Some region_fL6 ->
    (override_PMA (PMA_Region_attributes region_fL6) PBMT_PMA).(PMA_executable) = true ->
    matching_pma_region pmar0 (Physaddr paL6) 8 = Some region_lL6 ->
    (override_PMA (PMA_Region_attributes region_lL6) PBMT_PMA).(PMA_readable) = true ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4) (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4) (uint vL6) (uint (to_bits 64 4)) = PMP_Match ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4) (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4) (uint paL6) (uint (to_bits 64 8)) = PMP_Match ->
    is_aligned_paddr (Physaddr vL6) 4 = true ->
    is_aligned_vaddr (Virtaddr a8L6) 8 = true ->
    is_aligned_paddr (Physaddr paL6) 8 = true ->
    isRVC (subrange_vec_dec wL6 15 0) = true ->
    (forall s0, eq_vec (_get_Misa_C (register_lookup misa s0.(sregs))) ('b"1") = true -> exec (ext_decode_compressed (subrange_vec_dec wL6 15 0)) s0 = Some (C_LDSP (mword_of_int 10, Regidx (mword_of_int 11)), s0)) ->
    neq_vec (bits_of_virtaddr (Virtaddr vL7)) (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr vL7)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec (subrange_vec_dec (bits_of_virtaddr (Virtaddr vL7)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = sp_vpn ->
    zero_extend' 64 (concat_vec (mword_of_int 0x80005 : mword 44) (subrange_vec_dec (bits_of_virtaddr (Virtaddr vL7)) (Z.sub pagesize_bits 1) 0)) = vL7 ->
    neq_vec (access_vec_dec vL7 0) ('b"0") = false ->
    neq_vec (access_vec_dec vL7 1) ('b"0") = true ->
    is_aligned_vaddr (Virtaddr vL7) 4 = false ->
    neq_vec (bits_of_virtaddr (Virtaddr a8L7)) (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8L7)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8L7)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = svpn ->
    zero_extend' 64 (concat_vec (tlb_get_ppn 39 (pw_tlb_entry root_ppn (mword_of_int 0)) svpn) (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8L7)) (Z.sub pagesize_bits 1) 0)) = a8L7 ->
    matching_pma_region pmar0 (Physaddr vL7) 2 = Some region_fL7 ->
    (override_PMA (PMA_Region_attributes region_fL7) PBMT_PMA).(PMA_executable) = true ->
    matching_pma_region pmar0 (Physaddr paL7) 8 = Some region_lL7 ->
    (override_PMA (PMA_Region_attributes region_lL7) PBMT_PMA).(PMA_readable) = true ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4) (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4) (uint vL7) (uint (to_bits 64 2)) = PMP_Match ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4) (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4) (uint paL7) (uint (to_bits 64 8)) = PMP_Match ->
    is_aligned_paddr (Physaddr vL7) 2 = true ->
    is_aligned_vaddr (Virtaddr a8L7) 8 = true ->
    is_aligned_paddr (Physaddr paL7) 8 = true ->
    isRVC wL7 = true ->
    (forall s0, eq_vec (_get_Misa_C (register_lookup misa s0.(sregs))) ('b"1") = true -> exec (ext_decode_compressed wL7) s0 = Some (C_LDSP (mword_of_int 11, Regidx (mword_of_int 12)), s0)) ->
    neq_vec (bits_of_virtaddr (Virtaddr vL8)) (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr vL8)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec (subrange_vec_dec (bits_of_virtaddr (Virtaddr vL8)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = sp_vpn ->
    zero_extend' 64 (concat_vec (mword_of_int 0x80005 : mword 44) (subrange_vec_dec (bits_of_virtaddr (Virtaddr vL8)) (Z.sub pagesize_bits 1) 0)) = vL8 ->
    neq_vec (access_vec_dec vL8 0) ('b"0") = false ->
    neq_vec (access_vec_dec vL8 1) ('b"0") = false ->
    is_aligned_vaddr (Virtaddr vL8) 4 = true ->
    neq_vec (bits_of_virtaddr (Virtaddr a8L8)) (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8L8)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8L8)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = svpn ->
    zero_extend' 64 (concat_vec (tlb_get_ppn 39 (pw_tlb_entry root_ppn (mword_of_int 0)) svpn) (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8L8)) (Z.sub pagesize_bits 1) 0)) = a8L8 ->
    matching_pma_region pmar0 (Physaddr vL8) 4 = Some region_fL8 ->
    (override_PMA (PMA_Region_attributes region_fL8) PBMT_PMA).(PMA_executable) = true ->
    matching_pma_region pmar0 (Physaddr paL8) 8 = Some region_lL8 ->
    (override_PMA (PMA_Region_attributes region_lL8) PBMT_PMA).(PMA_readable) = true ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4) (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4) (uint vL8) (uint (to_bits 64 4)) = PMP_Match ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4) (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4) (uint paL8) (uint (to_bits 64 8)) = PMP_Match ->
    is_aligned_paddr (Physaddr vL8) 4 = true ->
    is_aligned_vaddr (Virtaddr a8L8) 8 = true ->
    is_aligned_paddr (Physaddr paL8) 8 = true ->
    isRVC (subrange_vec_dec wL8 15 0) = true ->
    (forall s0, eq_vec (_get_Misa_C (register_lookup misa s0.(sregs))) ('b"1") = true -> exec (ext_decode_compressed (subrange_vec_dec wL8 15 0)) s0 = Some (C_LDSP (mword_of_int 12, Regidx (mword_of_int 13)), s0)) ->
    neq_vec (bits_of_virtaddr (Virtaddr vL9)) (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr vL9)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec (subrange_vec_dec (bits_of_virtaddr (Virtaddr vL9)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = sp_vpn ->
    zero_extend' 64 (concat_vec (mword_of_int 0x80005 : mword 44) (subrange_vec_dec (bits_of_virtaddr (Virtaddr vL9)) (Z.sub pagesize_bits 1) 0)) = vL9 ->
    neq_vec (access_vec_dec vL9 0) ('b"0") = false ->
    neq_vec (access_vec_dec vL9 1) ('b"0") = true ->
    is_aligned_vaddr (Virtaddr vL9) 4 = false ->
    neq_vec (bits_of_virtaddr (Virtaddr a8L9)) (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8L9)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8L9)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = svpn ->
    zero_extend' 64 (concat_vec (tlb_get_ppn 39 (pw_tlb_entry root_ppn (mword_of_int 0)) svpn) (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8L9)) (Z.sub pagesize_bits 1) 0)) = a8L9 ->
    matching_pma_region pmar0 (Physaddr vL9) 2 = Some region_fL9 ->
    (override_PMA (PMA_Region_attributes region_fL9) PBMT_PMA).(PMA_executable) = true ->
    matching_pma_region pmar0 (Physaddr paL9) 8 = Some region_lL9 ->
    (override_PMA (PMA_Region_attributes region_lL9) PBMT_PMA).(PMA_readable) = true ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4) (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4) (uint vL9) (uint (to_bits 64 2)) = PMP_Match ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4) (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4) (uint paL9) (uint (to_bits 64 8)) = PMP_Match ->
    is_aligned_paddr (Physaddr vL9) 2 = true ->
    is_aligned_vaddr (Virtaddr a8L9) 8 = true ->
    is_aligned_paddr (Physaddr paL9) 8 = true ->
    isRVC wL9 = true ->
    (forall s0, eq_vec (_get_Misa_C (register_lookup misa s0.(sregs))) ('b"1") = true -> exec (ext_decode_compressed wL9) s0 = Some (C_LDSP (mword_of_int 13, Regidx (mword_of_int 14)), s0)) ->
    neq_vec (bits_of_virtaddr (Virtaddr vL10)) (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr vL10)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec (subrange_vec_dec (bits_of_virtaddr (Virtaddr vL10)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = sp_vpn ->
    zero_extend' 64 (concat_vec (mword_of_int 0x80005 : mword 44) (subrange_vec_dec (bits_of_virtaddr (Virtaddr vL10)) (Z.sub pagesize_bits 1) 0)) = vL10 ->
    neq_vec (access_vec_dec vL10 0) ('b"0") = false ->
    neq_vec (access_vec_dec vL10 1) ('b"0") = false ->
    is_aligned_vaddr (Virtaddr vL10) 4 = true ->
    neq_vec (bits_of_virtaddr (Virtaddr a8L10)) (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8L10)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8L10)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = svpn ->
    zero_extend' 64 (concat_vec (tlb_get_ppn 39 (pw_tlb_entry root_ppn (mword_of_int 0)) svpn) (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8L10)) (Z.sub pagesize_bits 1) 0)) = a8L10 ->
    matching_pma_region pmar0 (Physaddr vL10) 4 = Some region_fL10 ->
    (override_PMA (PMA_Region_attributes region_fL10) PBMT_PMA).(PMA_executable) = true ->
    matching_pma_region pmar0 (Physaddr paL10) 8 = Some region_lL10 ->
    (override_PMA (PMA_Region_attributes region_lL10) PBMT_PMA).(PMA_readable) = true ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4) (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4) (uint vL10) (uint (to_bits 64 4)) = PMP_Match ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4) (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4) (uint paL10) (uint (to_bits 64 8)) = PMP_Match ->
    is_aligned_paddr (Physaddr vL10) 4 = true ->
    is_aligned_vaddr (Virtaddr a8L10) 8 = true ->
    is_aligned_paddr (Physaddr paL10) 8 = true ->
    isRVC (subrange_vec_dec wL10 15 0) = true ->
    (forall s0, eq_vec (_get_Misa_C (register_lookup misa s0.(sregs))) ('b"1") = true -> exec (ext_decode_compressed (subrange_vec_dec wL10 15 0)) s0 = Some (C_LDSP (mword_of_int 14, Regidx (mword_of_int 15)), s0)) ->
    neq_vec (bits_of_virtaddr (Virtaddr vL11)) (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr vL11)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec (subrange_vec_dec (bits_of_virtaddr (Virtaddr vL11)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = sp_vpn ->
    zero_extend' 64 (concat_vec (mword_of_int 0x80005 : mword 44) (subrange_vec_dec (bits_of_virtaddr (Virtaddr vL11)) (Z.sub pagesize_bits 1) 0)) = vL11 ->
    neq_vec (access_vec_dec vL11 0) ('b"0") = false ->
    neq_vec (access_vec_dec vL11 1) ('b"0") = true ->
    is_aligned_vaddr (Virtaddr vL11) 4 = false ->
    neq_vec (bits_of_virtaddr (Virtaddr a8L11)) (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8L11)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8L11)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = svpn ->
    zero_extend' 64 (concat_vec (tlb_get_ppn 39 (pw_tlb_entry root_ppn (mword_of_int 0)) svpn) (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8L11)) (Z.sub pagesize_bits 1) 0)) = a8L11 ->
    matching_pma_region pmar0 (Physaddr vL11) 2 = Some region_fL11 ->
    (override_PMA (PMA_Region_attributes region_fL11) PBMT_PMA).(PMA_executable) = true ->
    matching_pma_region pmar0 (Physaddr paL11) 8 = Some region_lL11 ->
    (override_PMA (PMA_Region_attributes region_lL11) PBMT_PMA).(PMA_readable) = true ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4) (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4) (uint vL11) (uint (to_bits 64 2)) = PMP_Match ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4) (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4) (uint paL11) (uint (to_bits 64 8)) = PMP_Match ->
    is_aligned_paddr (Physaddr vL11) 2 = true ->
    is_aligned_vaddr (Virtaddr a8L11) 8 = true ->
    is_aligned_paddr (Physaddr paL11) 8 = true ->
    isRVC wL11 = true ->
    (forall s0, eq_vec (_get_Misa_C (register_lookup misa s0.(sregs))) ('b"1") = true -> exec (ext_decode_compressed wL11) s0 = Some (C_LDSP (mword_of_int 15, Regidx (mword_of_int 16)), s0)) ->
    neq_vec (bits_of_virtaddr (Virtaddr vL12)) (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr vL12)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec (subrange_vec_dec (bits_of_virtaddr (Virtaddr vL12)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = sp_vpn ->
    zero_extend' 64 (concat_vec (mword_of_int 0x80005 : mword 44) (subrange_vec_dec (bits_of_virtaddr (Virtaddr vL12)) (Z.sub pagesize_bits 1) 0)) = vL12 ->
    neq_vec (access_vec_dec vL12 0) ('b"0") = false ->
    neq_vec (access_vec_dec vL12 1) ('b"0") = false ->
    is_aligned_vaddr (Virtaddr vL12) 4 = true ->
    neq_vec (bits_of_virtaddr (Virtaddr a8L12)) (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8L12)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8L12)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = svpn ->
    zero_extend' 64 (concat_vec (tlb_get_ppn 39 (pw_tlb_entry root_ppn (mword_of_int 0)) svpn) (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8L12)) (Z.sub pagesize_bits 1) 0)) = a8L12 ->
    matching_pma_region pmar0 (Physaddr vL12) 4 = Some region_fL12 ->
    (override_PMA (PMA_Region_attributes region_fL12) PBMT_PMA).(PMA_executable) = true ->
    matching_pma_region pmar0 (Physaddr paL12) 8 = Some region_lL12 ->
    (override_PMA (PMA_Region_attributes region_lL12) PBMT_PMA).(PMA_readable) = true ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4) (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4) (uint vL12) (uint (to_bits 64 4)) = PMP_Match ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4) (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4) (uint paL12) (uint (to_bits 64 8)) = PMP_Match ->
    is_aligned_paddr (Physaddr vL12) 4 = true ->
    is_aligned_vaddr (Virtaddr a8L12) 8 = true ->
    is_aligned_paddr (Physaddr paL12) 8 = true ->
    isRVC (subrange_vec_dec wL12 15 0) = true ->
    (forall s0, eq_vec (_get_Misa_C (register_lookup misa s0.(sregs))) ('b"1") = true -> exec (ext_decode_compressed (subrange_vec_dec wL12 15 0)) s0 = Some (C_LDSP (mword_of_int 16, Regidx (mword_of_int 17)), s0)) ->
    neq_vec (bits_of_virtaddr (Virtaddr vL13)) (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr vL13)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec (subrange_vec_dec (bits_of_virtaddr (Virtaddr vL13)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = sp_vpn ->
    zero_extend' 64 (concat_vec (mword_of_int 0x80005 : mword 44) (subrange_vec_dec (bits_of_virtaddr (Virtaddr vL13)) (Z.sub pagesize_bits 1) 0)) = vL13 ->
    neq_vec (access_vec_dec vL13 0) ('b"0") = false ->
    neq_vec (access_vec_dec vL13 1) ('b"0") = true ->
    is_aligned_vaddr (Virtaddr vL13) 4 = false ->
    neq_vec (bits_of_virtaddr (Virtaddr a8L13)) (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8L13)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8L13)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = svpn ->
    zero_extend' 64 (concat_vec (tlb_get_ppn 39 (pw_tlb_entry root_ppn (mword_of_int 0)) svpn) (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8L13)) (Z.sub pagesize_bits 1) 0)) = a8L13 ->
    matching_pma_region pmar0 (Physaddr vL13) 2 = Some region_fL13 ->
    (override_PMA (PMA_Region_attributes region_fL13) PBMT_PMA).(PMA_executable) = true ->
    matching_pma_region pmar0 (Physaddr paL13) 8 = Some region_lL13 ->
    (override_PMA (PMA_Region_attributes region_lL13) PBMT_PMA).(PMA_readable) = true ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4) (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4) (uint vL13) (uint (to_bits 64 2)) = PMP_Match ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4) (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4) (uint paL13) (uint (to_bits 64 8)) = PMP_Match ->
    is_aligned_paddr (Physaddr vL13) 2 = true ->
    is_aligned_vaddr (Virtaddr a8L13) 8 = true ->
    is_aligned_paddr (Physaddr paL13) 8 = true ->
    isRVC wL13 = true ->
    (forall s0, eq_vec (_get_Misa_C (register_lookup misa s0.(sregs))) ('b"1") = true -> exec (ext_decode_compressed wL13) s0 = Some (C_LDSP (mword_of_int 27, Regidx (mword_of_int 28)), s0)) ->
    neq_vec (bits_of_virtaddr (Virtaddr vL14)) (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr vL14)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec (subrange_vec_dec (bits_of_virtaddr (Virtaddr vL14)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = sp_vpn ->
    zero_extend' 64 (concat_vec (mword_of_int 0x80005 : mword 44) (subrange_vec_dec (bits_of_virtaddr (Virtaddr vL14)) (Z.sub pagesize_bits 1) 0)) = vL14 ->
    neq_vec (access_vec_dec vL14 0) ('b"0") = false ->
    neq_vec (access_vec_dec vL14 1) ('b"0") = false ->
    is_aligned_vaddr (Virtaddr vL14) 4 = true ->
    neq_vec (bits_of_virtaddr (Virtaddr a8L14)) (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8L14)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8L14)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = svpn ->
    zero_extend' 64 (concat_vec (tlb_get_ppn 39 (pw_tlb_entry root_ppn (mword_of_int 0)) svpn) (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8L14)) (Z.sub pagesize_bits 1) 0)) = a8L14 ->
    matching_pma_region pmar0 (Physaddr vL14) 4 = Some region_fL14 ->
    (override_PMA (PMA_Region_attributes region_fL14) PBMT_PMA).(PMA_executable) = true ->
    matching_pma_region pmar0 (Physaddr paL14) 8 = Some region_lL14 ->
    (override_PMA (PMA_Region_attributes region_lL14) PBMT_PMA).(PMA_readable) = true ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4) (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4) (uint vL14) (uint (to_bits 64 4)) = PMP_Match ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4) (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4) (uint paL14) (uint (to_bits 64 8)) = PMP_Match ->
    is_aligned_paddr (Physaddr vL14) 4 = true ->
    is_aligned_vaddr (Virtaddr a8L14) 8 = true ->
    is_aligned_paddr (Physaddr paL14) 8 = true ->
    isRVC (subrange_vec_dec wL14 15 0) = true ->
    (forall s0, eq_vec (_get_Misa_C (register_lookup misa s0.(sregs))) ('b"1") = true -> exec (ext_decode_compressed (subrange_vec_dec wL14 15 0)) s0 = Some (C_LDSP (mword_of_int 28, Regidx (mword_of_int 29)), s0)) ->
    neq_vec (bits_of_virtaddr (Virtaddr vL15)) (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr vL15)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec (subrange_vec_dec (bits_of_virtaddr (Virtaddr vL15)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = sp_vpn ->
    zero_extend' 64 (concat_vec (mword_of_int 0x80005 : mword 44) (subrange_vec_dec (bits_of_virtaddr (Virtaddr vL15)) (Z.sub pagesize_bits 1) 0)) = vL15 ->
    neq_vec (access_vec_dec vL15 0) ('b"0") = false ->
    neq_vec (access_vec_dec vL15 1) ('b"0") = true ->
    is_aligned_vaddr (Virtaddr vL15) 4 = false ->
    neq_vec (bits_of_virtaddr (Virtaddr a8L15)) (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8L15)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8L15)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = svpn ->
    zero_extend' 64 (concat_vec (tlb_get_ppn 39 (pw_tlb_entry root_ppn (mword_of_int 0)) svpn) (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8L15)) (Z.sub pagesize_bits 1) 0)) = a8L15 ->
    matching_pma_region pmar0 (Physaddr vL15) 2 = Some region_fL15 ->
    (override_PMA (PMA_Region_attributes region_fL15) PBMT_PMA).(PMA_executable) = true ->
    matching_pma_region pmar0 (Physaddr paL15) 8 = Some region_lL15 ->
    (override_PMA (PMA_Region_attributes region_lL15) PBMT_PMA).(PMA_readable) = true ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4) (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4) (uint vL15) (uint (to_bits 64 2)) = PMP_Match ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4) (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4) (uint paL15) (uint (to_bits 64 8)) = PMP_Match ->
    is_aligned_paddr (Physaddr vL15) 2 = true ->
    is_aligned_vaddr (Virtaddr a8L15) 8 = true ->
    is_aligned_paddr (Physaddr paL15) 8 = true ->
    isRVC wL15 = true ->
    (forall s0, eq_vec (_get_Misa_C (register_lookup misa s0.(sregs))) ('b"1") = true -> exec (ext_decode_compressed wL15) s0 = Some (C_LDSP (mword_of_int 29, Regidx (mword_of_int 30)), s0)) ->
    neq_vec (bits_of_virtaddr (Virtaddr vL16)) (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr vL16)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec (subrange_vec_dec (bits_of_virtaddr (Virtaddr vL16)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = sp_vpn ->
    zero_extend' 64 (concat_vec (mword_of_int 0x80005 : mword 44) (subrange_vec_dec (bits_of_virtaddr (Virtaddr vL16)) (Z.sub pagesize_bits 1) 0)) = vL16 ->
    neq_vec (access_vec_dec vL16 0) ('b"0") = false ->
    neq_vec (access_vec_dec vL16 1) ('b"0") = false ->
    is_aligned_vaddr (Virtaddr vL16) 4 = true ->
    neq_vec (bits_of_virtaddr (Virtaddr a8L16)) (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8L16)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8L16)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = svpn ->
    zero_extend' 64 (concat_vec (tlb_get_ppn 39 (pw_tlb_entry root_ppn (mword_of_int 0)) svpn) (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8L16)) (Z.sub pagesize_bits 1) 0)) = a8L16 ->
    matching_pma_region pmar0 (Physaddr vL16) 4 = Some region_fL16 ->
    (override_PMA (PMA_Region_attributes region_fL16) PBMT_PMA).(PMA_executable) = true ->
    matching_pma_region pmar0 (Physaddr paL16) 8 = Some region_lL16 ->
    (override_PMA (PMA_Region_attributes region_lL16) PBMT_PMA).(PMA_readable) = true ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4) (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4) (uint vL16) (uint (to_bits 64 4)) = PMP_Match ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4) (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4) (uint paL16) (uint (to_bits 64 8)) = PMP_Match ->
    is_aligned_paddr (Physaddr vL16) 4 = true ->
    is_aligned_vaddr (Virtaddr a8L16) 8 = true ->
    is_aligned_paddr (Physaddr paL16) 8 = true ->
    isRVC (subrange_vec_dec wL16 15 0) = true ->
    (forall s0, eq_vec (_get_Misa_C (register_lookup misa s0.(sregs))) ('b"1") = true -> exec (ext_decode_compressed (subrange_vec_dec wL16 15 0)) s0 = Some (C_LDSP (mword_of_int 30, Regidx (mword_of_int 31)), s0)) ->
    neq_vec (bits_of_virtaddr (Virtaddr vA)) (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr vA)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec (subrange_vec_dec (bits_of_virtaddr (Virtaddr vA)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = sp_vpn ->
    zero_extend' 64 (concat_vec (mword_of_int 0x80005 : mword 44) (subrange_vec_dec (bits_of_virtaddr (Virtaddr vA)) (Z.sub pagesize_bits 1) 0)) = vA ->
    neq_vec (access_vec_dec vA 0) ('b"0") = false ->
    neq_vec (access_vec_dec vA 1) ('b"0") = true ->
    is_aligned_vaddr (Virtaddr vA) 4 = false ->
    matching_pma_region pmar0 (Physaddr vA) 2 = Some region_A ->
    (override_PMA (PMA_Region_attributes region_A) PBMT_PMA).(PMA_executable) = true ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4) (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4) (uint vA) (uint (to_bits 64 2)) = PMP_Match ->
    is_aligned_paddr (Physaddr vA) 2 = true ->
    isRVC wA = true ->
    (forall s0, eq_vec (_get_Misa_C (register_lookup misa s0.(sregs))) ('b"1") = true -> exec (ext_decode_compressed wA) s0 = Some (C_ADDI16SP immA, s0)) ->
    neq_vec (bits_of_virtaddr (Virtaddr vS)) (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr vS)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec (subrange_vec_dec (bits_of_virtaddr (Virtaddr vS)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = sp_vpn ->
    zero_extend' 64 (concat_vec (mword_of_int 0x80005 : mword 44) (subrange_vec_dec (bits_of_virtaddr (Virtaddr vS)) (Z.sub pagesize_bits 1) 0)) = vS ->
    neq_vec (access_vec_dec vS 0) ('b"0") = false ->
    neq_vec (access_vec_dec vS 1) ('b"0") = false ->
    is_aligned_vaddr (Virtaddr vS) 4 = true ->
    matching_pma_region pmar0 (Physaddr vS) 4 = Some region_S ->
    (override_PMA (PMA_Region_attributes region_S) PBMT_PMA).(PMA_executable) = true ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4) (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4) (uint vS) (uint (to_bits 64 4)) = PMP_Match ->
    is_aligned_paddr (Physaddr vS) 4 = true ->
    isRVC (subrange_vec_dec wS 15 0) = false ->
    (forall s0, register_lookup cur_privilege (sregs s0) = Supervisor -> exec (ext_decode wS) s0 = Some (SRET tt, s0)) ->
    minstret_inv -∗
    PC ↦ᵣ va -∗ gpr_file m -∗ misa ↦ᵣ misa0 -∗ nextPC ↦ᵣ npc0 -∗
    cur_privilege ↦ᵣ Supervisor -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
    (R_bitvector_64 mideleg) ↦ᵣ mdv0 -∗ (R_bitvector_64 mstatus) ↦ᵣ mstatus0 -∗ satp ↦ᵣ satp0 -∗
    tlb ↦ᵣ tlbvec -∗ menvcfg ↦ᵣ menvcfg0 -∗ mseccfg ↦ᵣ mseccfg0 -∗ mie ↦ᵣ mie_v -∗
    elp ↦ᵣ elp0 -∗ mcountinhibit ↦ᵣ mc -∗ minstretcfg ↦ᵣ mcfg -∗
    pmpcfg_n ↦ᵣ pmpcfg0 -∗ pmpaddr_n ↦ᵣ pmpaddr00 -∗ pma_regions ↦ᵣ pmar0 -∗ htif_tohost_base ↦ᵣ None -∗
    sepc ↦ᵣ sepc0 -∗
    ([∗ list] j ∈ seq 0 4, (pa_add va j) ↦ₘ nth_byte wj j) -∗
    kv_cell paL0 vLval0 -∗
    kv_cell paL1 vLval1 -∗
    kv_cell paL2 vLval2 -∗
    kv_cell paL3 vLval3 -∗
    kv_cell paL4 vLval4 -∗
    kv_cell paL5 vLval5 -∗
    kv_cell paL6 vLval6 -∗
    kv_cell paL7 vLval7 -∗
    kv_cell paL8 vLval8 -∗
    kv_cell paL9 vLval9 -∗
    kv_cell paL10 vLval10 -∗
    kv_cell paL11 vLval11 -∗
    kv_cell paL12 vLval12 -∗
    kv_cell paL13 vLval13 -∗
    kv_cell paL14 vLval14 -∗
    kv_cell paL15 vLval15 -∗
    kv_cell paL16 vLval16 -∗
    ([∗ list] j ∈ seq 0 4, (pa_add vL0 j) ↦ₘ nth_byte wL0 j) -∗
    ([∗ list] j ∈ seq 0 2, (pa_add vL1 j) ↦ₘ nth_byte wL1 j) -∗
    ([∗ list] j ∈ seq 0 4, (pa_add vL2 j) ↦ₘ nth_byte wL2 j) -∗
    ([∗ list] j ∈ seq 0 2, (pa_add vL3 j) ↦ₘ nth_byte wL3 j) -∗
    ([∗ list] j ∈ seq 0 4, (pa_add vL4 j) ↦ₘ nth_byte wL4 j) -∗
    ([∗ list] j ∈ seq 0 2, (pa_add vL5 j) ↦ₘ nth_byte wL5 j) -∗
    ([∗ list] j ∈ seq 0 4, (pa_add vL6 j) ↦ₘ nth_byte wL6 j) -∗
    ([∗ list] j ∈ seq 0 2, (pa_add vL7 j) ↦ₘ nth_byte wL7 j) -∗
    ([∗ list] j ∈ seq 0 4, (pa_add vL8 j) ↦ₘ nth_byte wL8 j) -∗
    ([∗ list] j ∈ seq 0 2, (pa_add vL9 j) ↦ₘ nth_byte wL9 j) -∗
    ([∗ list] j ∈ seq 0 4, (pa_add vL10 j) ↦ₘ nth_byte wL10 j) -∗
    ([∗ list] j ∈ seq 0 2, (pa_add vL11 j) ↦ₘ nth_byte wL11 j) -∗
    ([∗ list] j ∈ seq 0 4, (pa_add vL12 j) ↦ₘ nth_byte wL12 j) -∗
    ([∗ list] j ∈ seq 0 2, (pa_add vL13 j) ↦ₘ nth_byte wL13 j) -∗
    ([∗ list] j ∈ seq 0 4, (pa_add vL14 j) ↦ₘ nth_byte wL14 j) -∗
    ([∗ list] j ∈ seq 0 2, (pa_add vL15 j) ↦ₘ nth_byte wL15 j) -∗
    ([∗ list] j ∈ seq 0 4, (pa_add vL16 j) ↦ₘ nth_byte wL16 j) -∗
    ([∗ list] j ∈ seq 0 2, (pa_add vA j) ↦ₘ nth_byte wA j) -∗
    ([∗ list] j ∈ seq 0 4, (pa_add vS j) ↦ₘ nth_byte wS j) -∗
    ▷ ( ∀ (m' : gmap register_bitvector_64 (mword 64)) (npc' : mword 64),
        ⌜ m' !! gpr_of_Z 2 = Some vsp ⌝ -∗ ⌜ dom m' = dom (<[gpr_of_Z 1 := link]> m) ⌝ -∗
        PC ↦ᵣ sret_tgt sepc0 -∗
        gpr_file (<[gpr_of_Z 2 := regval_into_reg (add_vec vsp (sign_extend' 64 (caddi16sp_imm immA)))]> (<[gpr_of_Z 31 := regval_into_reg (extend_value false (update_subrange_vec_dec (zeros' (8*1*8)) (8*(0+1)*8-1) (8*0*8) vLval16))]> (<[gpr_of_Z 30 := regval_into_reg (extend_value false (update_subrange_vec_dec (zeros' (8*1*8)) (8*(0+1)*8-1) (8*0*8) vLval15))]> (<[gpr_of_Z 29 := regval_into_reg (extend_value false (update_subrange_vec_dec (zeros' (8*1*8)) (8*(0+1)*8-1) (8*0*8) vLval14))]> (<[gpr_of_Z 28 := regval_into_reg (extend_value false (update_subrange_vec_dec (zeros' (8*1*8)) (8*(0+1)*8-1) (8*0*8) vLval13))]> (<[gpr_of_Z 17 := regval_into_reg (extend_value false (update_subrange_vec_dec (zeros' (8*1*8)) (8*(0+1)*8-1) (8*0*8) vLval12))]> (<[gpr_of_Z 16 := regval_into_reg (extend_value false (update_subrange_vec_dec (zeros' (8*1*8)) (8*(0+1)*8-1) (8*0*8) vLval11))]> (<[gpr_of_Z 15 := regval_into_reg (extend_value false (update_subrange_vec_dec (zeros' (8*1*8)) (8*(0+1)*8-1) (8*0*8) vLval10))]> (<[gpr_of_Z 14 := regval_into_reg (extend_value false (update_subrange_vec_dec (zeros' (8*1*8)) (8*(0+1)*8-1) (8*0*8) vLval9))]> (<[gpr_of_Z 13 := regval_into_reg (extend_value false (update_subrange_vec_dec (zeros' (8*1*8)) (8*(0+1)*8-1) (8*0*8) vLval8))]> (<[gpr_of_Z 12 := regval_into_reg (extend_value false (update_subrange_vec_dec (zeros' (8*1*8)) (8*(0+1)*8-1) (8*0*8) vLval7))]> (<[gpr_of_Z 11 := regval_into_reg (extend_value false (update_subrange_vec_dec (zeros' (8*1*8)) (8*(0+1)*8-1) (8*0*8) vLval6))]> (<[gpr_of_Z 10 := regval_into_reg (extend_value false (update_subrange_vec_dec (zeros' (8*1*8)) (8*(0+1)*8-1) (8*0*8) vLval5))]> (<[gpr_of_Z 7 := regval_into_reg (extend_value false (update_subrange_vec_dec (zeros' (8*1*8)) (8*(0+1)*8-1) (8*0*8) vLval4))]> (<[gpr_of_Z 6 := regval_into_reg (extend_value false (update_subrange_vec_dec (zeros' (8*1*8)) (8*(0+1)*8-1) (8*0*8) vLval3))]> (<[gpr_of_Z 5 := regval_into_reg (extend_value false (update_subrange_vec_dec (zeros' (8*1*8)) (8*(0+1)*8-1) (8*0*8) vLval2))]> (<[gpr_of_Z 3 := regval_into_reg (extend_value false (update_subrange_vec_dec (zeros' (8*1*8)) (8*(0+1)*8-1) (8*0*8) vLval1))]> (<[gpr_of_Z 1 := regval_into_reg (extend_value false (update_subrange_vec_dec (zeros' (8*1*8)) (8*(0+1)*8-1) (8*0*8) vLval0))]> m')))))))))))))))))) -∗
        misa ↦ᵣ misa0 -∗ nextPC ↦ᵣ sret_tgt sepc0 -∗
        cur_privilege ↦ᵣ sret_newpriv mstatus0 -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
        (R_bitvector_64 mideleg) ↦ᵣ mdv0 -∗ (R_bitvector_64 mstatus) ↦ᵣ sret_ms5 mstatus0 -∗ satp ↦ᵣ satp0 -∗
        tlb ↦ᵣ tlbvec -∗ mie ↦ᵣ mie_v -∗ sepc ↦ᵣ sepc0 -∗
        elp ↦ᵣ sret_elpv mstatus0 lpe -∗ mcountinhibit ↦ᵣ mc -∗ minstretcfg ↦ᵣ mcfg -∗
        pmpcfg_n ↦ᵣ pmpcfg0 -∗ pmpaddr_n ↦ᵣ pmpaddr00 -∗ pma_regions ↦ᵣ pmar0 -∗ htif_tohost_base ↦ᵣ None -∗
        ([∗ list] j ∈ seq 0 4, (pa_add va j) ↦ₘ nth_byte wj j) -∗
        ([∗ list] j ∈ seq 0 8, (pa_add paL0 j) ↦ₘ nth_byte vLval0 j) -∗
        ([∗ list] j ∈ seq 0 8, (pa_add paL1 j) ↦ₘ nth_byte vLval1 j) -∗
        ([∗ list] j ∈ seq 0 8, (pa_add paL2 j) ↦ₘ nth_byte vLval2 j) -∗
        ([∗ list] j ∈ seq 0 8, (pa_add paL3 j) ↦ₘ nth_byte vLval3 j) -∗
        ([∗ list] j ∈ seq 0 8, (pa_add paL4 j) ↦ₘ nth_byte vLval4 j) -∗
        ([∗ list] j ∈ seq 0 8, (pa_add paL5 j) ↦ₘ nth_byte vLval5 j) -∗
        ([∗ list] j ∈ seq 0 8, (pa_add paL6 j) ↦ₘ nth_byte vLval6 j) -∗
        ([∗ list] j ∈ seq 0 8, (pa_add paL7 j) ↦ₘ nth_byte vLval7 j) -∗
        ([∗ list] j ∈ seq 0 8, (pa_add paL8 j) ↦ₘ nth_byte vLval8 j) -∗
        ([∗ list] j ∈ seq 0 8, (pa_add paL9 j) ↦ₘ nth_byte vLval9 j) -∗
        ([∗ list] j ∈ seq 0 8, (pa_add paL10 j) ↦ₘ nth_byte vLval10 j) -∗
        ([∗ list] j ∈ seq 0 8, (pa_add paL11 j) ↦ₘ nth_byte vLval11 j) -∗
        ([∗ list] j ∈ seq 0 8, (pa_add paL12 j) ↦ₘ nth_byte vLval12 j) -∗
        ([∗ list] j ∈ seq 0 8, (pa_add paL13 j) ↦ₘ nth_byte vLval13 j) -∗
        ([∗ list] j ∈ seq 0 8, (pa_add paL14 j) ↦ₘ nth_byte vLval14 j) -∗
        ([∗ list] j ∈ seq 0 8, (pa_add paL15 j) ↦ₘ nth_byte vLval15 j) -∗
        ([∗ list] j ∈ seq 0 8, (pa_add paL16 j) ↦ₘ nth_byte vLval16 j) -∗
        ([∗ list] j ∈ seq 0 4, (pa_add vL0 j) ↦ₘ nth_byte wL0 j) -∗
        ([∗ list] j ∈ seq 0 2, (pa_add vL1 j) ↦ₘ nth_byte wL1 j) -∗
        ([∗ list] j ∈ seq 0 4, (pa_add vL2 j) ↦ₘ nth_byte wL2 j) -∗
        ([∗ list] j ∈ seq 0 2, (pa_add vL3 j) ↦ₘ nth_byte wL3 j) -∗
        ([∗ list] j ∈ seq 0 4, (pa_add vL4 j) ↦ₘ nth_byte wL4 j) -∗
        ([∗ list] j ∈ seq 0 2, (pa_add vL5 j) ↦ₘ nth_byte wL5 j) -∗
        ([∗ list] j ∈ seq 0 4, (pa_add vL6 j) ↦ₘ nth_byte wL6 j) -∗
        ([∗ list] j ∈ seq 0 2, (pa_add vL7 j) ↦ₘ nth_byte wL7 j) -∗
        ([∗ list] j ∈ seq 0 4, (pa_add vL8 j) ↦ₘ nth_byte wL8 j) -∗
        ([∗ list] j ∈ seq 0 2, (pa_add vL9 j) ↦ₘ nth_byte wL9 j) -∗
        ([∗ list] j ∈ seq 0 4, (pa_add vL10 j) ↦ₘ nth_byte wL10 j) -∗
        ([∗ list] j ∈ seq 0 2, (pa_add vL11 j) ↦ₘ nth_byte wL11 j) -∗
        ([∗ list] j ∈ seq 0 4, (pa_add vL12 j) ↦ₘ nth_byte wL12 j) -∗
        ([∗ list] j ∈ seq 0 2, (pa_add vL13 j) ↦ₘ nth_byte wL13 j) -∗
        ([∗ list] j ∈ seq 0 4, (pa_add vL14 j) ↦ₘ nth_byte wL14 j) -∗
        ([∗ list] j ∈ seq 0 2, (pa_add vL15 j) ↦ₘ nth_byte wL15 j) -∗
        ([∗ list] j ∈ seq 0 4, (pa_add vL16 j) ↦ₘ nth_byte wL16 j) -∗
        ([∗ list] j ∈ seq 0 2, (pa_add vA j) ↦ₘ nth_byte wA j) -∗
        ([∗ list] j ∈ seq 0 4, (pa_add vS j) ↦ₘ nth_byte wS j) -∗
        WP (Loop : expr riscv_lang) @ E {{ Phi }} ) -∗
    WP (Loop : expr riscv_lang) @ E {{ Phi }}.
  Proof.
    intros link vL0 vL1 vL2 vL3 vL4 vL5 vL6 vL7 vL8 vL9 vL10 vL11 vL12 vL13 vL14 vL15 vL16 vA vS offL0 a8L0 paL0 dL0 offL1 a8L1 paL1 dL1 offL2 a8L2 paL2 dL2 offL3 a8L3 paL3 dL3 offL4 a8L4 paL4 dL4 offL5 a8L5 paL5 dL5 offL6 a8L6 paL6 dL6 offL7 a8L7 paL7 dL7 offL8 a8L8 paL8 dL8 offL9 a8L9 paL9 dL9 offL10 a8L10 paL10 dL10 offL11 a8L11 paL11 dL11 offL12 a8L12 paL12 dL12 offL13 a8L13 paL13 dL13 offL14 a8L14 paL14 dL14 offL15 a8L15 paL15 dL15 offL16 a8L16 paL16 dL16 HN Hsp Hra Hor0 Hor1 Hor2 Hor3 Hor4 Hor5 Hor6 Hor7 Hor8 Hor9 Hor10 Hor11 Hor12 Hor13 Hor14 Hor15 Hor16 HSXL Hmode Hasid Hvec5 Hvecld Hmask Hpmm HA0 Hord0 HX0 HR0 HmisaC HmisaS HMPRV HMXR Hb1 Hmie_mdl HSIE Help HTSR0 Hlpe jcanon jvpndef jident jbit0 jbit1 jalign4 jmatchf jexecf jrangef jalignf jisRVC Htgt jdec jal0 Lcanon0 Lvpndef0 Lident0 Lbit00 Lbit10 Lalign40 La8canon0 La8vpndef0 La8ident0 Lmatchf0 Lexecf0 Lmatchl0 Lread0 Lrangef0 Lrangel0 Lalignf0 Lalign80 Lpalign80 LisRVC0 Ldec0 Lcanon1 Lvpndef1 Lident1 Lbit01 Lbit11 Lalign41 La8canon1 La8vpndef1 La8ident1 Lmatchf1 Lexecf1 Lmatchl1 Lread1 Lrangef1 Lrangel1 Lalignf1 Lalign81 Lpalign81 LisRVC1 Ldec1 Lcanon2 Lvpndef2 Lident2 Lbit02 Lbit12 Lalign42 La8canon2 La8vpndef2 La8ident2 Lmatchf2 Lexecf2 Lmatchl2 Lread2 Lrangef2 Lrangel2 Lalignf2 Lalign82 Lpalign82 LisRVC2 Ldec2 Lcanon3 Lvpndef3 Lident3 Lbit03 Lbit13 Lalign43 La8canon3 La8vpndef3 La8ident3 Lmatchf3 Lexecf3 Lmatchl3 Lread3 Lrangef3 Lrangel3 Lalignf3 Lalign83 Lpalign83 LisRVC3 Ldec3 Lcanon4 Lvpndef4 Lident4 Lbit04 Lbit14 Lalign44 La8canon4 La8vpndef4 La8ident4 Lmatchf4 Lexecf4 Lmatchl4 Lread4 Lrangef4 Lrangel4 Lalignf4 Lalign84 Lpalign84 LisRVC4 Ldec4 Lcanon5 Lvpndef5 Lident5 Lbit05 Lbit15 Lalign45 La8canon5 La8vpndef5 La8ident5 Lmatchf5 Lexecf5 Lmatchl5 Lread5 Lrangef5 Lrangel5 Lalignf5 Lalign85 Lpalign85 LisRVC5 Ldec5 Lcanon6 Lvpndef6 Lident6 Lbit06 Lbit16 Lalign46 La8canon6 La8vpndef6 La8ident6 Lmatchf6 Lexecf6 Lmatchl6 Lread6 Lrangef6 Lrangel6 Lalignf6 Lalign86 Lpalign86 LisRVC6 Ldec6 Lcanon7 Lvpndef7 Lident7 Lbit07 Lbit17 Lalign47 La8canon7 La8vpndef7 La8ident7 Lmatchf7 Lexecf7 Lmatchl7 Lread7 Lrangef7 Lrangel7 Lalignf7 Lalign87 Lpalign87 LisRVC7 Ldec7 Lcanon8 Lvpndef8 Lident8 Lbit08 Lbit18 Lalign48 La8canon8 La8vpndef8 La8ident8 Lmatchf8 Lexecf8 Lmatchl8 Lread8 Lrangef8 Lrangel8 Lalignf8 Lalign88 Lpalign88 LisRVC8 Ldec8 Lcanon9 Lvpndef9 Lident9 Lbit09 Lbit19 Lalign49 La8canon9 La8vpndef9 La8ident9 Lmatchf9 Lexecf9 Lmatchl9 Lread9 Lrangef9 Lrangel9 Lalignf9 Lalign89 Lpalign89 LisRVC9 Ldec9 Lcanon10 Lvpndef10 Lident10 Lbit010 Lbit110 Lalign410 La8canon10 La8vpndef10 La8ident10 Lmatchf10 Lexecf10 Lmatchl10 Lread10 Lrangef10 Lrangel10 Lalignf10 Lalign810 Lpalign810 LisRVC10 Ldec10 Lcanon11 Lvpndef11 Lident11 Lbit011 Lbit111 Lalign411 La8canon11 La8vpndef11 La8ident11 Lmatchf11 Lexecf11 Lmatchl11 Lread11 Lrangef11 Lrangel11 Lalignf11 Lalign811 Lpalign811 LisRVC11 Ldec11 Lcanon12 Lvpndef12 Lident12 Lbit012 Lbit112 Lalign412 La8canon12 La8vpndef12 La8ident12 Lmatchf12 Lexecf12 Lmatchl12 Lread12 Lrangef12 Lrangel12 Lalignf12 Lalign812 Lpalign812 LisRVC12 Ldec12 Lcanon13 Lvpndef13 Lident13 Lbit013 Lbit113 Lalign413 La8canon13 La8vpndef13 La8ident13 Lmatchf13 Lexecf13 Lmatchl13 Lread13 Lrangef13 Lrangel13 Lalignf13 Lalign813 Lpalign813 LisRVC13 Ldec13 Lcanon14 Lvpndef14 Lident14 Lbit014 Lbit114 Lalign414 La8canon14 La8vpndef14 La8ident14 Lmatchf14 Lexecf14 Lmatchl14 Lread14 Lrangef14 Lrangel14 Lalignf14 Lalign814 Lpalign814 LisRVC14 Ldec14 Lcanon15 Lvpndef15 Lident15 Lbit015 Lbit115 Lalign415 La8canon15 La8vpndef15 La8ident15 Lmatchf15 Lexecf15 Lmatchl15 Lread15 Lrangef15 Lrangel15 Lalignf15 Lalign815 Lpalign815 LisRVC15 Ldec15 Lcanon16 Lvpndef16 Lident16 Lbit016 Lbit116 Lalign416 La8canon16 La8vpndef16 La8ident16 Lmatchf16 Lexecf16 Lmatchl16 Lread16 Lrangef16 Lrangel16 Lalignf16 Lalign816 Lpalign816 LisRVC16 Ldec16 Acanon Avpndef Aident Abit0 Abit1 Aalign4 Amatchf Aexecf Arangef Aalignf AisRVC Adec Scanon Svpndef Sident Sbit0 Sbit1 Salign4 Smatchf Sexecf Srangef Salignf SisRVC Sdec.
    iIntros "#Hinv Hpc Hfile Hmisa' Hnpc Hpriv Hhs Hmdl Hms Hsatp Htlb Hmenv Hsec Hmie Help' Hmcinh Hmcfg Hpmpc Hpmpaddr Hpma Hhtif Hsepc Hjbytes Hcell0 Hcell1 Hcell2 Hcell3 Hcell4 Hcell5 Hcell6 Hcell7 Hcell8 Hcell9 Hcell10 Hcell11 Hcell12 Hcell13 Hcell14 Hcell15 Hcell16 Hib0 Hib1 Hib2 Hib3 Hib4 Hib5 Hib6 Hib7 Hib8 Hib9 Hib10 Hib11 Hib12 Hib13 Hib14 Hib15 Hib16 HibA HibS Hcont".
    iApply (wp_kv_jal_kerneltrap va wj imm m vsp vd misa0 mdv0 mstatus0 menvcfg0 mseccfg0 satp0 mie_v b1 npc0 mc mcfg pmpcfg0 pmpaddr00 pmar0 elp0 tlbvec region_j vLval0 vLval1 vLval2 vLval3 vLval4 vLval5 vLval6 vLval7 vLval8 vLval9 vLval10 vLval11 vLval12 vLval13 vLval14 vLval15 vLval16 paL0 paL1 paL2 paL3 paL4 paL5 paL6 paL7 paL8 paL9 paL10 paL11 paL12 paL13 paL14 paL15 paL16 E (dq:=DfracOwn 1) Phi
              HN Hsp Hra Htgt HSXL Hmode Hasid Hvec5 jcanon jvpndef jident jbit0 jbit1 jalign4 jmatchf jexecf HA0 Hord0 jrangef HX0 jalignf HmisaC HmisaS jisRVC jdec jal0 Hb1 Hmie_mdl HSIE Help
              with "Hinv Hpc Hfile Hmisa' Hnpc Hpriv Hhs Hmdl Hms Hsatp Htlb Hmenv Hsec Hmie Help' Hmcinh Hmcfg Hpmpc Hpmpaddr Hpma Hhtif Hjbytes Hcell0 Hcell1 Hcell2 Hcell3 Hcell4 Hcell5 Hcell6 Hcell7 Hcell8 Hcell9 Hcell10 Hcell11 Hcell12 Hcell13 Hcell14 Hcell15 Hcell16").
    iNext.
    iIntros (m' npc') "%Hsp' %Hdom' Hpc Hnpc Hfile #Hinv2 Hcsrs Hcell0 Hcell1 Hcell2 Hcell3 Hcell4 Hcell5 Hcell6 Hcell7 Hcell8 Hcell9 Hcell10 Hcell11 Hcell12 Hcell13 Hcell14 Hcell15 Hcell16 Hjbytes".
    assert (HisL0 : is_Some (m' !! gpr_of_Z 1)).
    { destruct Hor0 as [vo0 Hvo0]. apply elem_of_dom. rewrite Hdom'. rewrite dom_insert_L.
      apply elem_of_union_r. apply elem_of_dom. rewrite Hvo0. eauto. }
    destruct HisL0 as [vdL0 EvdL0].
    assert (HisL1 : is_Some (m' !! gpr_of_Z 3)).
    { destruct Hor1 as [vo1 Hvo1]. apply elem_of_dom. rewrite Hdom'. rewrite dom_insert_L.
      apply elem_of_union_r. apply elem_of_dom. rewrite Hvo1. eauto. }
    destruct HisL1 as [vdL1 EvdL1].
    assert (HisL2 : is_Some (m' !! gpr_of_Z 5)).
    { destruct Hor2 as [vo2 Hvo2]. apply elem_of_dom. rewrite Hdom'. rewrite dom_insert_L.
      apply elem_of_union_r. apply elem_of_dom. rewrite Hvo2. eauto. }
    destruct HisL2 as [vdL2 EvdL2].
    assert (HisL3 : is_Some (m' !! gpr_of_Z 6)).
    { destruct Hor3 as [vo3 Hvo3]. apply elem_of_dom. rewrite Hdom'. rewrite dom_insert_L.
      apply elem_of_union_r. apply elem_of_dom. rewrite Hvo3. eauto. }
    destruct HisL3 as [vdL3 EvdL3].
    assert (HisL4 : is_Some (m' !! gpr_of_Z 7)).
    { destruct Hor4 as [vo4 Hvo4]. apply elem_of_dom. rewrite Hdom'. rewrite dom_insert_L.
      apply elem_of_union_r. apply elem_of_dom. rewrite Hvo4. eauto. }
    destruct HisL4 as [vdL4 EvdL4].
    assert (HisL5 : is_Some (m' !! gpr_of_Z 10)).
    { destruct Hor5 as [vo5 Hvo5]. apply elem_of_dom. rewrite Hdom'. rewrite dom_insert_L.
      apply elem_of_union_r. apply elem_of_dom. rewrite Hvo5. eauto. }
    destruct HisL5 as [vdL5 EvdL5].
    assert (HisL6 : is_Some (m' !! gpr_of_Z 11)).
    { destruct Hor6 as [vo6 Hvo6]. apply elem_of_dom. rewrite Hdom'. rewrite dom_insert_L.
      apply elem_of_union_r. apply elem_of_dom. rewrite Hvo6. eauto. }
    destruct HisL6 as [vdL6 EvdL6].
    assert (HisL7 : is_Some (m' !! gpr_of_Z 12)).
    { destruct Hor7 as [vo7 Hvo7]. apply elem_of_dom. rewrite Hdom'. rewrite dom_insert_L.
      apply elem_of_union_r. apply elem_of_dom. rewrite Hvo7. eauto. }
    destruct HisL7 as [vdL7 EvdL7].
    assert (HisL8 : is_Some (m' !! gpr_of_Z 13)).
    { destruct Hor8 as [vo8 Hvo8]. apply elem_of_dom. rewrite Hdom'. rewrite dom_insert_L.
      apply elem_of_union_r. apply elem_of_dom. rewrite Hvo8. eauto. }
    destruct HisL8 as [vdL8 EvdL8].
    assert (HisL9 : is_Some (m' !! gpr_of_Z 14)).
    { destruct Hor9 as [vo9 Hvo9]. apply elem_of_dom. rewrite Hdom'. rewrite dom_insert_L.
      apply elem_of_union_r. apply elem_of_dom. rewrite Hvo9. eauto. }
    destruct HisL9 as [vdL9 EvdL9].
    assert (HisL10 : is_Some (m' !! gpr_of_Z 15)).
    { destruct Hor10 as [vo10 Hvo10]. apply elem_of_dom. rewrite Hdom'. rewrite dom_insert_L.
      apply elem_of_union_r. apply elem_of_dom. rewrite Hvo10. eauto. }
    destruct HisL10 as [vdL10 EvdL10].
    assert (HisL11 : is_Some (m' !! gpr_of_Z 16)).
    { destruct Hor11 as [vo11 Hvo11]. apply elem_of_dom. rewrite Hdom'. rewrite dom_insert_L.
      apply elem_of_union_r. apply elem_of_dom. rewrite Hvo11. eauto. }
    destruct HisL11 as [vdL11 EvdL11].
    assert (HisL12 : is_Some (m' !! gpr_of_Z 17)).
    { destruct Hor12 as [vo12 Hvo12]. apply elem_of_dom. rewrite Hdom'. rewrite dom_insert_L.
      apply elem_of_union_r. apply elem_of_dom. rewrite Hvo12. eauto. }
    destruct HisL12 as [vdL12 EvdL12].
    assert (HisL13 : is_Some (m' !! gpr_of_Z 28)).
    { destruct Hor13 as [vo13 Hvo13]. apply elem_of_dom. rewrite Hdom'. rewrite dom_insert_L.
      apply elem_of_union_r. apply elem_of_dom. rewrite Hvo13. eauto. }
    destruct HisL13 as [vdL13 EvdL13].
    assert (HisL14 : is_Some (m' !! gpr_of_Z 29)).
    { destruct Hor14 as [vo14 Hvo14]. apply elem_of_dom. rewrite Hdom'. rewrite dom_insert_L.
      apply elem_of_union_r. apply elem_of_dom. rewrite Hvo14. eauto. }
    destruct HisL14 as [vdL14 EvdL14].
    assert (HisL15 : is_Some (m' !! gpr_of_Z 30)).
    { destruct Hor15 as [vo15 Hvo15]. apply elem_of_dom. rewrite Hdom'. rewrite dom_insert_L.
      apply elem_of_union_r. apply elem_of_dom. rewrite Hvo15. eauto. }
    destruct HisL15 as [vdL15 EvdL15].
    assert (HisL16 : is_Some (m' !! gpr_of_Z 31)).
    { destruct Hor16 as [vo16 Hvo16]. apply elem_of_dom. rewrite Hdom'. rewrite dom_insert_L.
      apply elem_of_union_r. apply elem_of_dom. rewrite Hvo16. eauto. }
    destruct HisL16 as [vdL16 EvdL16].
    iDestruct "Hcsrs" as "(Hmisa' & Hpriv & Hhs & Hmdl & Hms & Hsatp & Htlb & Hmenv & Hsec & Hmie & Help' & Hmcinh & Hmcfg & Hpmpc & Hpmpaddr & Hpma & Hhtif)".
    unfold kv_cell.
    iApply (wp_kv_loads_all root_ppn (add_vec_int va 4) wL0 wL1 wL2 wL3 wL4 wL5 wL6 wL7 wL8 wL9 wL10 wL11 wL12 wL13 wL14 wL15 wL16 svpn m' vsp vdL0 vdL1 vdL2 vdL3 vdL4 vdL5 vdL6 vdL7 vdL8 vdL9 vdL10 vdL11 vdL12 vdL13 vdL14 vdL15 vdL16 misa0 mdv0 mstatus0 menvcfg0 mseccfg0 satp0 mie_v b1 vLval0 vLval1 vLval2 vLval3 vLval4 vLval5 vLval6 vLval7 vLval8 vLval9 vLval10 vLval11 vLval12 vLval13 vLval14 vLval15 vLval16 npc' mc mcfg pmpcfg0 pmpaddr00 pmar0 elp0 tlbvec region_lL0 region_lL1 region_lL2 region_lL3 region_lL4 region_lL5 region_lL6 region_lL7 region_lL8 region_lL9 region_lL10 region_lL11 region_lL12 region_lL13 region_lL14 region_lL15 region_lL16 region_fL0 region_fL1 region_fL2 region_fL3 region_fL4 region_fL5 region_fL6 region_fL7 region_fL8 region_fL9 region_fL10 region_fL11 region_fL12 region_fL13 region_fL14 region_fL15 region_fL16 E (dq:=DfracOwn 1) Phi
              HN Hsp' EvdL0 EvdL1 EvdL2 EvdL3 EvdL4 EvdL5 EvdL6 EvdL7 EvdL8 EvdL9 EvdL10 EvdL11 EvdL12 EvdL13 EvdL14 EvdL15 EvdL16 HSXL Hmode Hasid Hvec5 Hvecld Hmask Hpmm HA0 Hord0 HX0 HR0 HmisaC HmisaS HMPRV HMXR Hb1 Hmie_mdl HSIE Help Lcanon0 Lvpndef0 Lident0 Lbit00 Lbit10 Lalign40 La8canon0 La8vpndef0 La8ident0 Lmatchf0 Lexecf0 Lmatchl0 Lread0 Lrangef0 Lrangel0 Lalignf0 Lalign80 Lpalign80 LisRVC0 Ldec0 Lcanon1 Lvpndef1 Lident1 Lbit01 Lbit11 Lalign41 La8canon1 La8vpndef1 La8ident1 Lmatchf1 Lexecf1 Lmatchl1 Lread1 Lrangef1 Lrangel1 Lalignf1 Lalign81 Lpalign81 LisRVC1 Ldec1 Lcanon2 Lvpndef2 Lident2 Lbit02 Lbit12 Lalign42 La8canon2 La8vpndef2 La8ident2 Lmatchf2 Lexecf2 Lmatchl2 Lread2 Lrangef2 Lrangel2 Lalignf2 Lalign82 Lpalign82 LisRVC2 Ldec2 Lcanon3 Lvpndef3 Lident3 Lbit03 Lbit13 Lalign43 La8canon3 La8vpndef3 La8ident3 Lmatchf3 Lexecf3 Lmatchl3 Lread3 Lrangef3 Lrangel3 Lalignf3 Lalign83 Lpalign83 LisRVC3 Ldec3 Lcanon4 Lvpndef4 Lident4 Lbit04 Lbit14 Lalign44 La8canon4 La8vpndef4 La8ident4 Lmatchf4 Lexecf4 Lmatchl4 Lread4 Lrangef4 Lrangel4 Lalignf4 Lalign84 Lpalign84 LisRVC4 Ldec4 Lcanon5 Lvpndef5 Lident5 Lbit05 Lbit15 Lalign45 La8canon5 La8vpndef5 La8ident5 Lmatchf5 Lexecf5 Lmatchl5 Lread5 Lrangef5 Lrangel5 Lalignf5 Lalign85 Lpalign85 LisRVC5 Ldec5 Lcanon6 Lvpndef6 Lident6 Lbit06 Lbit16 Lalign46 La8canon6 La8vpndef6 La8ident6 Lmatchf6 Lexecf6 Lmatchl6 Lread6 Lrangef6 Lrangel6 Lalignf6 Lalign86 Lpalign86 LisRVC6 Ldec6 Lcanon7 Lvpndef7 Lident7 Lbit07 Lbit17 Lalign47 La8canon7 La8vpndef7 La8ident7 Lmatchf7 Lexecf7 Lmatchl7 Lread7 Lrangef7 Lrangel7 Lalignf7 Lalign87 Lpalign87 LisRVC7 Ldec7 Lcanon8 Lvpndef8 Lident8 Lbit08 Lbit18 Lalign48 La8canon8 La8vpndef8 La8ident8 Lmatchf8 Lexecf8 Lmatchl8 Lread8 Lrangef8 Lrangel8 Lalignf8 Lalign88 Lpalign88 LisRVC8 Ldec8 Lcanon9 Lvpndef9 Lident9 Lbit09 Lbit19 Lalign49 La8canon9 La8vpndef9 La8ident9 Lmatchf9 Lexecf9 Lmatchl9 Lread9 Lrangef9 Lrangel9 Lalignf9 Lalign89 Lpalign89 LisRVC9 Ldec9 Lcanon10 Lvpndef10 Lident10 Lbit010 Lbit110 Lalign410 La8canon10 La8vpndef10 La8ident10 Lmatchf10 Lexecf10 Lmatchl10 Lread10 Lrangef10 Lrangel10 Lalignf10 Lalign810 Lpalign810 LisRVC10 Ldec10 Lcanon11 Lvpndef11 Lident11 Lbit011 Lbit111 Lalign411 La8canon11 La8vpndef11 La8ident11 Lmatchf11 Lexecf11 Lmatchl11 Lread11 Lrangef11 Lrangel11 Lalignf11 Lalign811 Lpalign811 LisRVC11 Ldec11 Lcanon12 Lvpndef12 Lident12 Lbit012 Lbit112 Lalign412 La8canon12 La8vpndef12 La8ident12 Lmatchf12 Lexecf12 Lmatchl12 Lread12 Lrangef12 Lrangel12 Lalignf12 Lalign812 Lpalign812 LisRVC12 Ldec12 Lcanon13 Lvpndef13 Lident13 Lbit013 Lbit113 Lalign413 La8canon13 La8vpndef13 La8ident13 Lmatchf13 Lexecf13 Lmatchl13 Lread13 Lrangef13 Lrangel13 Lalignf13 Lalign813 Lpalign813 LisRVC13 Ldec13 Lcanon14 Lvpndef14 Lident14 Lbit014 Lbit114 Lalign414 La8canon14 La8vpndef14 La8ident14 Lmatchf14 Lexecf14 Lmatchl14 Lread14 Lrangef14 Lrangel14 Lalignf14 Lalign814 Lpalign814 LisRVC14 Ldec14 Lcanon15 Lvpndef15 Lident15 Lbit015 Lbit115 Lalign415 La8canon15 La8vpndef15 La8ident15 Lmatchf15 Lexecf15 Lmatchl15 Lread15 Lrangef15 Lrangel15 Lalignf15 Lalign815 Lpalign815 LisRVC15 Ldec15 Lcanon16 Lvpndef16 Lident16 Lbit016 Lbit116 Lalign416 La8canon16 La8vpndef16 La8ident16 Lmatchf16 Lexecf16 Lmatchl16 Lread16 Lrangef16 Lrangel16 Lalignf16 Lalign816 Lpalign816 LisRVC16 Ldec16
              with "Hinv2 Hpc Hfile Hmisa' Hnpc Hpriv Hhs Hmdl Hms Hsatp Htlb Hmenv Hsec Hmie Help' Hmcinh Hmcfg Hpmpc Hpmpaddr Hpma Hhtif Hcell0 Hcell1 Hcell2 Hcell3 Hcell4 Hcell5 Hcell6 Hcell7 Hcell8 Hcell9 Hcell10 Hcell11 Hcell12 Hcell13 Hcell14 Hcell15 Hcell16 Hib0 Hib1 Hib2 Hib3 Hib4 Hib5 Hib6 Hib7 Hib8 Hib9 Hib10 Hib11 Hib12 Hib13 Hib14 Hib15 Hib16").
    iNext.
    iIntros "Hpc Hfile Hmisa' Hnpc Hpriv Hhs Hmdl Hms Hsatp Htlb Hmenv Hsec Hmie Help' Hmcinh Hmcfg Hpmpc Hpmpaddr Hpma Hhtif Hcell0 Hcell1 Hcell2 Hcell3 Hcell4 Hcell5 Hcell6 Hcell7 Hcell8 Hcell9 Hcell10 Hcell11 Hcell12 Hcell13 Hcell14 Hcell15 Hcell16 Hib0 Hib1 Hib2 Hib3 Hib4 Hib5 Hib6 Hib7 Hib8 Hib9 Hib10 Hib11 Hib12 Hib13 Hib14 Hib15 Hib16".
    iApply (wp_kv_addi_sret (add_vec_int vL16 2) wA immA wS _ vsp misa0 mdv0 mstatus0 satp0 mie_v sepc0 b1 lpe (add_vec_int vL16 2) mc mcfg pmpcfg0 pmpaddr00 pmar0 elp0 tlbvec region_A region_S E Phi
              HN _
              HSXL Hmode Hasid Hvec5 Acanon Avpndef Aident Abit0 Abit1 Aalign4 Amatchf Aexecf Arangef Aalignf AisRVC Adec Scanon Svpndef Sident Sbit0 Sbit1 Salign4 Smatchf Sexecf Srangef Salignf SisRVC HTSR0 Hlpe Sdec HA0 Hord0 HX0 HmisaC HmisaS Hb1 Hmie_mdl HSIE Help
              with "Hinv2 Hpc Hfile Hmisa' Hnpc Hpriv Hhs Hmdl Hms Hsatp Htlb Hmie Hsepc Help' Hmcinh Hmcfg Hpmpc Hpmpaddr Hpma Hhtif HibA HibS").
    iNext.
    iIntros "Hpc Hfile Hmisa' Hnpc Hpriv Hhs Hmdl Hms Hsatp Htlb Hmie Hsepc Help' Hmcinh Hmcfg Hpmpc Hpmpaddr Hpma Hhtif HibA HibS".
    iApply ("Hcont" $! m' npc' with "[%] [%] Hpc Hfile Hmisa' Hnpc Hpriv Hhs Hmdl Hms Hsatp Htlb Hmie Hsepc Help' Hmcinh Hmcfg Hpmpc Hpmpaddr Hpma Hhtif Hjbytes Hcell0 Hcell1 Hcell2 Hcell3 Hcell4 Hcell5 Hcell6 Hcell7 Hcell8 Hcell9 Hcell10 Hcell11 Hcell12 Hcell13 Hcell14 Hcell15 Hcell16 Hib0 Hib1 Hib2 Hib3 Hib4 Hib5 Hib6 Hib7 Hib8 Hib9 Hib10 Hib11 Hib12 Hib13 Hib14 Hib15 Hib16 HibA HibS").
    - exact Hsp'.
    - exact Hdom'.
    Unshelve. all: (repeat (rewrite lookup_insert_ne; [|vm_compute; discriminate]); exact Hsp').
  Qed.


End KVCOMPOSE.
