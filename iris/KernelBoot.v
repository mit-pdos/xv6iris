(* KernelBoot.v -- imports the xv6 kernel image and states/proves wp_kernel_first_two,
   the WP for executing the kernel's first two instructions (auipc; ld). *)
From Stdlib Require Import Eqdep_dec ZArith Lia.
From stdpp Require Import gmap list list_monad bitvector.definitions bitvector.tactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes.
Require Import SailStdpp.Base SailStdpp.TypeCasts.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvTryStep RiscvFetchExec RiscvExtras WpAdd WpAuipc WpLoad.
From Kernel Require KernelInstrs KernelData KernelSyms.
Local Open Scope Z_scope.

(* ---- the kernel image, imported from the dump ---- *)
(* ---------------------------------------------------------------------- *)
(* 1. The kernel image, imported from the dump.                            *)
(* ---------------------------------------------------------------------- *)

(* Entry address, taken from the dumped symbol table. *)
Definition kentry : Z := 0x80000000.

Lemma kentry_is_entry : KernelSyms.sym "_entry"%string = kentry.
Proof. vm_compute. reflexivity. Qed.

(* The first two instruction encodings, read straight off the dumped image
   (head of chunk 0).  [option_map ki_enc (nth_error _ i)] avoids forcing the
   8423-element tail, so these check by [reflexivity]. *)
Lemma kernel_first_two_encs :
  option_map KernelInstrs.ki_enc
    (List.nth_error KernelInstrs.kernel_instrs_chunk0 0) = Some 0xa117 /\
  option_map KernelInstrs.ki_enc
    (List.nth_error KernelInstrs.kernel_instrs_chunk0 1) = Some 0x1d813103.
Proof. split; reflexivity. Qed.

(* The instruction words handed to the Sail decoder (little-endian integer
   exactly as [ki_enc]). *)
Definition w_auipc : mword 32 := mword_of_int 0xa117.       (* auipc sp,0xa     *)
Definition w_ld    : mword 32 := mword_of_int 0x1d813103.   (* ld sp,472(sp)    *)

(* Program counters across the two-instruction window (both are 4-byte). *)
Definition kpc0 : mword 64 := mword_of_int  kentry.         (* 0x80000000 *)
Definition kpc1 : mword 64 := mword_of_int (kentry + 4).    (* 0x80000004 *)
Definition kpc2 : mword 64 := mword_of_int (kentry + 8).    (* 0x80000008 *)

(* auipc sp,0xa writes sp := pc + (0xa << 12) = 0x80000000 + 0xa000. *)
Definition sp_auipc : mword 64 := mword_of_int 0x8000a000.

Section KernelBootWP.
  Context `{!riscvGS Σ}.

  (* Booting-Machine config (same shape as [wp_add_real_final]'s bundle).   *)
  Context (sp0 mst0 mstatus0 : mword 64) (mi0 : bool) (elp0 : mword 1).

  (* The value the `ld` loads from the GOT slot at sp_auipc+472 = 0x8000a1d8;
     left abstract here (it depends on the kernel's data/relocations, which
     `forward_exec_ld` below will read out of the owned memory bytes). *)
  Context (gotval mstF : mword 64) (miF : bool).

  (* ---------------------------------------------------------------------- *)
  (* Single-step WP for `auipc rd,imm` (rd=x2), via wp_exec_step +           *)
  (* forward_exec_auipc + sFa_eq.  Mirror of wp_add_real_final.              *)

  Lemma wp_kernel_first_two
      (w_a : mword 32) (imm_a : mword 20) (i_a : mword 5)
      (w_l : mword 32) (imm_l : mword 12) (i_l : mword 5)
      (region : PMA_Region) (v : bv 64)
      (mc : mword 32) (mcfg : mword 64)
      (mseccfg0 : mword 64) (pmpcfg0 : type_of_register pmpcfg_n) (pmar0 : list PMA_Region)
      E (Φ : mval -> iProp Σ) :
    (* `should_inc` for both steps is DETERMINED by the mcountinhibit/minstretcfg
       cells (owned below) — no per-step exec-hypothesis is needed. *)
    let bb     := andb (eq_vec (_get_Counterin_IR mc) ('b"0"))
                       (eq_vec (counter_priv_filter_bit mcfg Machine) ('b"0")) in
    let sp1    := regval_into_reg (add_vec kpc0 (auipc_off imm_a)) in
    let offl   := sign_extend' 64 imm_l in
    let eal    := add_vec sp1 offl in
    let a8l    := zero_extend' 64 (subrange_vec_dec eal (xlen - 0 - 1) 0) in
    let pal    := zero_extend' 64 (add_vec_int a8l (0 * 8)) in
    let data2l := update_subrange_vec_dec (zeros' (8*1*8)) (8*(0+1)*8-1) (8*0*8) v in
    let mst1   := if bb then add_vec_int mst0 1 else mst0 in
    uint i_a = 2 ->
    (forall s0, register_lookup PC s0.(sregs) = kpc0 ->
       register_lookup cur_privilege s0.(sregs) = Machine ->
       exec (fetch tt) s0 = Some (F_Base w_a, s0)) ->
    (forall s0, exec (ext_decode w_a) s0 = Some (UTYPE (imm_a, Regidx i_a, AUIPC), s0)) ->
    uint i_l = 2 ->
    (forall s0, register_lookup PC s0.(sregs) = kpc1 ->
       register_lookup cur_privilege s0.(sregs) = Machine ->
       exec (fetch tt) s0 = Some (F_Base w_l, s0)) ->
    (forall s0, exec (ext_decode w_l) s0 = Some (LOAD (imm_l, Regidx i_l, Regidx i_l, false, 8), s0)) ->
    eq_vec (_get_Mstatus_MIE mstatus0) ('b"1") = false ->
    eq_vec elp0 (landing_pad_bits_backwards LP_EXPECTED) = false ->
    eq_vec (_get_Mstatus_MPRV mstatus0) ('b"1") = false ->
    pmm_mode_backwards (_get_Seccfg_PMM mseccfg0) = PMM_Disabled ->
    is_aligned_vaddr (Virtaddr a8l) 8 = true ->
    (forall j, pmpAddrMatchType_encdec_backwards
       (_get_Pmpcfg_ent_A (vec_access_dec pmpcfg0 j)) = OFF) ->
    matching_pma_region pmar0 (Physaddr pal) 8 = Some region ->
    is_aligned_paddr (Physaddr pal) 8 = true ->
    (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_readable) = true ->
    (* within_clint/within_sig discharged from the RAM bytes; within_htif from
       the owned [htif_tohost_base |-> None]. *)
    PC ↦ᵣ kpc0 -∗ (R_bitvector_64 x2) ↦ᵣ sp0 -∗ nextPC ↦ᵣ kpc0 -∗
    (R_bool minstret_increment) ↦ᵣ mi0 -∗ minstret ↦ᵣ mst0 -∗
    cur_privilege ↦ᵣ Machine -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
    (R_bitvector_64 mideleg) ↦ᵣ zeros' 64 -∗ (R_bitvector_64 mstatus) ↦ᵣ mstatus0 -∗
    elp ↦ᵣ elp0 -∗ mseccfg ↦ᵣ mseccfg0 -∗ pmpcfg_n ↦ᵣ pmpcfg0 -∗ pma_regions ↦ᵣ pmar0 -∗
    mcountinhibit ↦ᵣ mc -∗ minstretcfg ↦ᵣ mcfg -∗ htif_tohost_base ↦ᵣ None -∗
    ([∗ list] j ∈ seq 0 8, (pa_add pal j) ↦ₘ nth_byte v j) -∗
    ▷ ( PC ↦ᵣ kpc2 -∗
        (R_bitvector_64 x2) ↦ᵣ regval_into_reg (extend_value false data2l) -∗
        nextPC ↦ᵣ kpc2 -∗ (R_bool minstret_increment) ↦ᵣ bb -∗
        minstret ↦ᵣ (if bb then add_vec_int mst1 1 else mst1) -∗
        cur_privilege ↦ᵣ Machine -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
        (R_bitvector_64 mideleg) ↦ᵣ zeros' 64 -∗ (R_bitvector_64 mstatus) ↦ᵣ mstatus0 -∗
        elp ↦ᵣ elp0 -∗ mseccfg ↦ᵣ mseccfg0 -∗ pmpcfg_n ↦ᵣ pmpcfg0 -∗ pma_regions ↦ᵣ pmar0 -∗
        mcountinhibit ↦ᵣ mc -∗ minstretcfg ↦ᵣ mcfg -∗ htif_tohost_base ↦ᵣ None -∗
        ([∗ list] j ∈ seq 0 8, (pa_add pal j) ↦ₘ nth_byte v j) -∗
        WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intros bb sp1 offl eal a8l pal data2l mst1
      Hia Hfa Hda Hil Hfl Hdl HmIE Hlp HMPRV Hpmm Halign Hpmp Hmatch Hpalign Hread.
    iIntros "Hpc Hx2 Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hsec Hpmpc Hpma Hmcinh Hmcfg Hhtif Hbytes Hcont".
    (* Step 1: auipc.  b1 := bb, determined by the owned mcountinhibit/minstretcfg. *)
    iApply (wp_step_auipc kpc0 w_a imm_a i_a bb sp0 kpc0 mst0 mstatus0 mc mcfg mi0 elp0 E Φ
              Hia Hfa Hda eq_refl HmIE Hlp
              with "Hpc Hx2 Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg").
    iNext. iIntros "Hpc Hx2 Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg".
    replace (add_vec_int kpc0 4) with kpc1 by (vm_compute; reflexivity).
    (* Step 2: ld.  base register x2 holds sp1 = the auipc result. *)
    iApply (wp_step_ld kpc1 w_l imm_l i_l bb region v sp1 kpc1 mst1 mstatus0 mc mcfg
              mseccfg0 pmpcfg0 pmar0 bb elp0 E Φ
              Hil Hfl Hdl eq_refl HmIE Hlp HMPRV Hpmm Halign Hpmp Hmatch Hpalign Hread
              with "Hpc Hx2 Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hsec Hpmpc Hpma Hmcinh Hmcfg Hhtif Hbytes").
    iNext. iIntros "Hpc Hx2 Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hsec Hpmpc Hpma Hmcinh Hmcfg Hhtif Hbytes".
    replace (add_vec_int kpc1 4) with kpc2 by (vm_compute; reflexivity).
    iApply ("Hcont" with "Hpc Hx2 Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hsec Hpmpc Hpma Hmcinh Hmcfg Hhtif Hbytes").
  Qed.

End KernelBootWP.
