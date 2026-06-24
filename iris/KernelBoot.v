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
Require Import RiscvLang RiscvPtsto RiscvExec RiscvTryStep RiscvFetchExec RiscvExtras WpAdd WpAuipc WpLoad WpDecode.
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

(* The instruction words handed to the Sail decoder ([w_auipc]/[w_ld], with the
   decoded fields [imm_auipc]/[i_auipc]/[imm_ld]/[i_ld] and the fully-discharged
   decode lemmas [decode_auipc]/[decode_ld]) live in WpDecode. *)

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

  (* The instruction words [w_auipc]/[w_ld] and decoded fields are now CONCRETE
     (from WpDecode), and the two decode side-conditions are DISCHARGED here via
     [decode_auipc]/[decode_ld] — so this top-level theorem carries NO decode
     hypothesis at all. *)
  Lemma wp_kernel_first_two
      (region region_fa region_fl : PMA_Region) (v : bv 64)
      (mc : mword 32) (mcfg : mword 64)
      (mseccfg0 : mword 64) (pmpcfg0 : type_of_register pmpcfg_n) (pmar0 : list PMA_Region)
      E (Φ : mval -> iProp Σ) :
    (* `should_inc` for both steps is DETERMINED by the mcountinhibit/minstretcfg
       cells (owned below) — no per-step exec-hypothesis is needed. *)
    let bb     := andb (eq_vec (_get_Counterin_IR mc) ('b"0"))
                       (eq_vec (counter_priv_filter_bit mcfg Machine) ('b"0")) in
    let sp1    := regval_into_reg (add_vec kpc0 (auipc_off imm_auipc)) in
    let offl   := sign_extend' 64 imm_ld in
    let eal    := add_vec sp1 offl in
    let a8l    := zero_extend' 64 (subrange_vec_dec eal (xlen - 0 - 1) 0) in
    let pal    := zero_extend' 64 (add_vec_int a8l (0 * 8)) in
    let data2l := update_subrange_vec_dec (zeros' (8*1*8)) (8*(0+1)*8-1) (8*0*8) v in
    let mst1   := if bb then add_vec_int mst0 1 else mst0 in
    (* auipc fetch side-conditions (instruction word [w_auipc] at [fetch_pa kpc0]) *)
    matching_pma_region pmar0 (Physaddr (fetch_pa kpc0)) 4 = Some region_fa ->
    (override_PMA (PMA_Region_attributes region_fa) PBMT_PMA).(PMA_executable) = true ->
    is_aligned_paddr (Physaddr (fetch_pa kpc0)) 4 = true ->
    neq_vec (access_vec_dec kpc0 0) ('b"0") = false ->
    neq_vec (access_vec_dec kpc0 1) ('b"0") = false ->
    is_aligned_vaddr (Virtaddr kpc0) 4 = true ->
    (* ld fetch side-conditions (instruction word [w_ld] at [fetch_pa kpc1]) *)
    matching_pma_region pmar0 (Physaddr (fetch_pa kpc1)) 4 = Some region_fl ->
    (override_PMA (PMA_Region_attributes region_fl) PBMT_PMA).(PMA_executable) = true ->
    is_aligned_paddr (Physaddr (fetch_pa kpc1)) 4 = true ->
    neq_vec (access_vec_dec kpc1 0) ('b"0") = false ->
    neq_vec (access_vec_dec kpc1 1) ('b"0") = false ->
    is_aligned_vaddr (Virtaddr kpc1) 4 = true ->
    (* the shared PMP-off fact (used by both fetch discharges) *)
    (forall i, pmpAddrMatchType_encdec_backwards
       (_get_Pmpcfg_ent_A (vec_access_dec pmpcfg0 i)) = OFF) ->
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
    ([∗ list] j ∈ seq 0 4, (pa_add (fetch_pa kpc0) j) ↦ₘ nth_byte w_auipc j) -∗
    ([∗ list] j ∈ seq 0 4, (pa_add (fetch_pa kpc1) j) ↦ₘ nth_byte w_ld j) -∗
    ▷ ( PC ↦ᵣ kpc2 -∗
        (R_bitvector_64 x2) ↦ᵣ regval_into_reg (extend_value false data2l) -∗
        nextPC ↦ᵣ kpc2 -∗ (R_bool minstret_increment) ↦ᵣ bb -∗
        minstret ↦ᵣ (if bb then add_vec_int mst1 1 else mst1) -∗
        cur_privilege ↦ᵣ Machine -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
        (R_bitvector_64 mideleg) ↦ᵣ zeros' 64 -∗ (R_bitvector_64 mstatus) ↦ᵣ mstatus0 -∗
        elp ↦ᵣ elp0 -∗ mseccfg ↦ᵣ mseccfg0 -∗ pmpcfg_n ↦ᵣ pmpcfg0 -∗ pma_regions ↦ᵣ pmar0 -∗
        mcountinhibit ↦ᵣ mc -∗ minstretcfg ↦ᵣ mcfg -∗ htif_tohost_base ↦ᵣ None -∗
        ([∗ list] j ∈ seq 0 8, (pa_add pal j) ↦ₘ nth_byte v j) -∗
        ([∗ list] j ∈ seq 0 4, (pa_add (fetch_pa kpc0) j) ↦ₘ nth_byte w_auipc j) -∗
        ([∗ list] j ∈ seq 0 4, (pa_add (fetch_pa kpc1) j) ↦ₘ nth_byte w_ld j) -∗
        WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intros bb sp1 offl eal a8l pal data2l mst1
      Hmatchfa Hexecfa Halignfa Hbit0fa Hbit1fa Hvalignfa
      Hmatchfl Hexecfl Halignfl Hbit0fl Hbit1fl Hvalignfl Hpmpf
      HmIE Hlp HMPRV Hpmm Halign Hpmp Hmatch Hpalign Hread.
    iIntros "Hpc Hx2 Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hsec Hpmpc Hpma Hmcinh Hmcfg Hhtif Hbytes Hibytesa Hibytesl Hcont".
    (* Step 1: auipc.  uint i_auipc = 2 and isRVC are now concrete facts; decode is
       discharged by [decode_auipc].  Owns the auipc bytes + fetch CSRs. *)
    iApply (wp_step_auipc kpc0 w_auipc imm_auipc i_auipc bb sp0 kpc0 mst0 mstatus0 mc mcfg
              region_fa pmpcfg0 pmar0 mi0 elp0 E Φ
              ltac:(vm_compute; reflexivity) Hmatchfa Hexecfa Hpmpf Halignfa Hbit0fa Hbit1fa Hvalignfa
              ltac:(vm_compute; reflexivity) decode_auipc eq_refl HmIE Hlp
              with "Hpc Hx2 Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif Hibytesa").
    iNext. iIntros "Hpc Hx2 Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif Hibytesa".
    replace (add_vec_int kpc0 4) with kpc1 by (vm_compute; reflexivity).
    (* Step 2: ld.  base register x2 holds sp1 = the auipc result.  decode is
       discharged by [decode_ld].  Owns the ld bytes at [fetch_pa kpc1]. *)
    iApply (wp_step_ld kpc1 w_ld imm_ld i_ld bb region region_fl v sp1 kpc1 mst1 mstatus0 mc mcfg
              mseccfg0 pmpcfg0 pmar0 bb elp0 E Φ
              ltac:(vm_compute; reflexivity) Hmatchfl Hexecfl Hpmpf Halignfl Hbit0fl Hbit1fl Hvalignfl
              ltac:(vm_compute; reflexivity) decode_ld eq_refl
              HmIE Hlp HMPRV Hpmm Halign Hpmp Hmatch Hpalign Hread
              with "Hpc Hx2 Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hsec Hpmpc Hpma Hmcinh Hmcfg Hhtif Hbytes Hibytesl").
    iNext. iIntros "Hpc Hx2 Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hsec Hpmpc Hpma Hmcinh Hmcfg Hhtif Hbytes Hibytesl".
    replace (add_vec_int kpc1 4) with kpc2 by (vm_compute; reflexivity).
    iApply ("Hcont" with "Hpc Hx2 Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hsec Hpmpc Hpma Hmcinh Hmcfg Hhtif Hbytes Hibytesa Hibytesl").
  Qed.

End KernelBootWP.
