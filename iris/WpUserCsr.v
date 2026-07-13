(* WpUserCsr.v -- U-mode CSR-access USTEP arms (privileged CSR -> illegal).

   A CSR instruction (CSRReg/CSRImm) naming a CSR above User privilege traps
   in User mode.  These arms are thin specialisations of the privilege-
   conditioned illegal arm ustep_illegal_st: they fix ii to CSRReg/CSRImm and
   discharge its execute premise with UmodeCsr's exec_execute_CSR{Reg,Imm}_illegal_u.
   The single CSR-specific side condition is that the CSR's privilege field
   (bits [9:8]) is above User: zopz0zKzJ_u 'b"00" (csrPriv csr) = false. *)
From Stdlib Require Import ZArith Bool Lia.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import RiscvModelBytes.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvFetchExec RiscvExtras.
Require Import MinstretInv InstrBytes WpLeafCommon WpGpr.
Require Import SmodeCore WpIntrCore WpDecodeBridge.
Require Import UmodeTrap UmodeFetch UmodeFetchC UmodeStep UmodeEcall UmodeFetchFault.
Require Import UptInv UmodeCsr.
Require Import WpUserEcall WpUserTrap.
Local Open Scope Z_scope.
Import Defs.

Require Import WpUserBase.

Section WpUserCsr.
  Context `{!riscvGS Σ}.
  Context `{CID : CpuId}.
  Context (U : uctx).

  Local Notation satp0 := (WpUserBase.satp0 U).
  Local Notation root := (WpUserBase.root U).
  Local Notation slots := (WpUserBase.slots U).
  Local Notation spec := (WpUserBase.spec U).
  Local Notation code := (WpUserBase.code U).
  Local Notation dq := (WpUserBase.dq U).
  Local Notation user_cfg := (WpUserBase.user_cfg U).
  Local Notation user_code := (WpUserBase.user_code U).
  Local Notation user_data := (WpUserBase.user_data U).
  Local Notation user_trap_frame := (WpUserBase.user_trap_frame U).
  Local Notation ustep_illegal_st := (WpUserTrap.ustep_illegal_st U).

  (* CSRReg (csrrw/csrrs/csrrc) naming a privileged CSR, in User mode: traps. *)
  Lemma ustep_csrreg_illegal (csr : mword 12) (rs1 rd : mword 5) (op : csrop)
      (va : mword 64) (vpn : mword 27) (ie : uwalk_info) (w : mword 32)
      (ms_v sc_v stval_v sepc_v : mword 64)
      (g : gmap regidx (mword 64))
      (tlbvec : vec (option TLB_Entry) (2 ^ 6))
      E (Φ : mval -> iProp Σ) :
    zopz0zKzJ_u ('b"00" : mword 2) (csrPriv csr) = false ->
    ↑minstretN ⊆ E ->
    upt_tlb_ok spec tlbvec ->
    vec_access_dec tlbvec (tlb_hash (__id 39) vpn) = Some (upt_entry vpn ie) ->
    uw_check_ok (InstructionFetch tt) ie ->
    update_PTE_Bits (uw_pte0 ie) (InstructionFetch tt) = None ->
    _get_PTE_Ext_PBMT (ext_bits_of_PTE (uw_pte0 ie)) = ('b"00" : mword 2) ->
    (forall j : nat, (j < 4)%nat ->
       code !! pa_add (u_pa (upt_entry vpn ie) va vpn) j = Some (nth_byte w j)) ->
    _get_Mstatus_SXL ms_v = 'b"10" ->
    is_aligned_vaddr (Virtaddr va) 4 = true ->
    neq_vec (bits_of_virtaddr (Virtaddr va))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn ->
    is_aligned_paddr (Physaddr (u_pa (upt_entry vpn ie) va vpn)) 4 = true ->
    isRVC (subrange_vec_dec w 15 0) = false ->
    (forall s0, agree_on D_u s0 dstateU ->
       exec (ext_decode w) s0 = Some (CSRReg (csr, Regidx rs1, Regidx rd, op), s0)) ->
    hw_config -∗
    minstret_inv -∗
    hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ User -∗
    mstatus ↦ᵣ ms_v -∗
    scause ↦ᵣ sc_v -∗
    stval ↦ᵣ stval_v -∗
    sepc ↦ᵣ sepc_v -∗
    tlb ↦ᵣ tlbvec -∗
    pc_is va -∗
    gpr_file g -∗
    upt_inv root slots spec -∗
    user_code -∗
    user_data -∗
    user_cfg -∗
    ▷ (user_trap_frame -∗ WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intros Hpriv HN Hok Hvec Hchk0 HupdN Hpbmt0 Hcw HSXL Hval Hcanon Hvpn_def Hpaal HnotRVC Hdec.
    iApply (ustep_illegal_st (CSRReg (csr, Regidx rs1, Regidx rd, op)) va vpn ie w
              ms_v sc_v stval_v sepc_v g tlbvec E Φ HN
              (fun s Hs => exec_execute_CSRReg_illegal_u csr rs1 rd op s Hs Hpriv)
              eq_refl Hok Hvec Hchk0 HupdN Hpbmt0 Hcw HSXL Hval Hcanon Hvpn_def Hpaal HnotRVC Hdec).
  Qed.

  (* CSRImm (csrrwi/csrrsi/csrrci) naming a privileged CSR, in User mode: traps. *)
  Lemma ustep_csrimm_illegal (csr : mword 12) (imm rd : mword 5) (op : csrop)
      (va : mword 64) (vpn : mword 27) (ie : uwalk_info) (w : mword 32)
      (ms_v sc_v stval_v sepc_v : mword 64)
      (g : gmap regidx (mword 64))
      (tlbvec : vec (option TLB_Entry) (2 ^ 6))
      E (Φ : mval -> iProp Σ) :
    zopz0zKzJ_u ('b"00" : mword 2) (csrPriv csr) = false ->
    ↑minstretN ⊆ E ->
    upt_tlb_ok spec tlbvec ->
    vec_access_dec tlbvec (tlb_hash (__id 39) vpn) = Some (upt_entry vpn ie) ->
    uw_check_ok (InstructionFetch tt) ie ->
    update_PTE_Bits (uw_pte0 ie) (InstructionFetch tt) = None ->
    _get_PTE_Ext_PBMT (ext_bits_of_PTE (uw_pte0 ie)) = ('b"00" : mword 2) ->
    (forall j : nat, (j < 4)%nat ->
       code !! pa_add (u_pa (upt_entry vpn ie) va vpn) j = Some (nth_byte w j)) ->
    _get_Mstatus_SXL ms_v = 'b"10" ->
    is_aligned_vaddr (Virtaddr va) 4 = true ->
    neq_vec (bits_of_virtaddr (Virtaddr va))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn ->
    is_aligned_paddr (Physaddr (u_pa (upt_entry vpn ie) va vpn)) 4 = true ->
    isRVC (subrange_vec_dec w 15 0) = false ->
    (forall s0, agree_on D_u s0 dstateU ->
       exec (ext_decode w) s0 = Some (CSRImm (csr, imm, Regidx rd, op), s0)) ->
    hw_config -∗
    minstret_inv -∗
    hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ User -∗
    mstatus ↦ᵣ ms_v -∗
    scause ↦ᵣ sc_v -∗
    stval ↦ᵣ stval_v -∗
    sepc ↦ᵣ sepc_v -∗
    tlb ↦ᵣ tlbvec -∗
    pc_is va -∗
    gpr_file g -∗
    upt_inv root slots spec -∗
    user_code -∗
    user_data -∗
    user_cfg -∗
    ▷ (user_trap_frame -∗ WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intros Hpriv HN Hok Hvec Hchk0 HupdN Hpbmt0 Hcw HSXL Hval Hcanon Hvpn_def Hpaal HnotRVC Hdec.
    iApply (ustep_illegal_st (CSRImm (csr, imm, Regidx rd, op)) va vpn ie w
              ms_v sc_v stval_v sepc_v g tlbvec E Φ HN
              (fun s Hs => exec_execute_CSRImm_illegal_u csr imm rd op s Hs Hpriv)
              eq_refl Hok Hvec Hchk0 HupdN Hpbmt0 Hcw HSXL Hval Hcanon Hvpn_def Hpaal HnotRVC Hdec).
  Qed.

End WpUserCsr.
