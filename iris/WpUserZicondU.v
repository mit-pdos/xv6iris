(* WpUserZicondU.v -- the COMBINED (hit+miss) U-mode Zicond arm.
   ZICOND_RTYPE ported to the combined fetch engine: it rides the combined
   two-source arm [ustep_rtype2_u] exactly as [ustep_zicond] rides
   [ustep_rtype2], so it carries NO fetch-hit precondition. *)
From Stdlib Require Import ZArith Bool Lia.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import RiscvModelBytes.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvFetchExec.
Require Import MinstretInv InstrBytes WpGpr.
Require Import WpDecodeBridge.
Require Import UmodeFetch UmodeEcall.
Require Import UptInv ZicondGpr.
Require Import WpUserZicond.
Require Import WpUserComputeMiss.
Local Open Scope Z_scope.
Import Defs.

Require Import WpUserBase.

Section WpUserZicondU.
  Context `{!riscvGS Σ}.
  Context `{CID : CpuId}.
  Context (U : uctx).

  Local Notation root := (WpUserBase.root U).
  Local Notation slots := (WpUserBase.slots U).
  Local Notation spec := (WpUserBase.spec U).
  Local Notation code := (WpUserBase.code U).
  Local Notation dq := (WpUserBase.dq U).
  Local Notation user_cfg := (WpUserBase.user_cfg U).
  Local Notation user_code := (WpUserBase.user_code U).
  Local Notation user_data := (WpUserBase.user_data U).
  Local Notation user_frame := (WpUserBase.user_frame U).
  Local Notation ustep_rtype2_u := (WpUserComputeMiss.ustep_rtype2_u U).

  Lemma ustep_zicond_u (op : zicondop) (rs2 rs1 rd : mword 5)
      (va : mword 64) (vpn : mword 27) (ie : uwalk_info) (w : mword 32)
      (ms_v sc_v stval_v sepc_v : mword 64)
      (g : gmap regidx (mword 64))
      (tlbvec : vec (option TLB_Entry) (2 ^ 6))
      E (Φ : mval -> iProp Σ) :
    ↑minstretN ⊆ E ->
    upt_tlb_ok spec tlbvec ->
    spec !! vpn = Some ie ->
    uw_check_ok (InstructionFetch tt) ie ->
    update_PTE_Bits (uw_pte0 ie) (InstructionFetch tt) = None ->
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
       exec (ext_decode w) s0 = Some (ZICOND_RTYPE (Regidx rs2, Regidx rs1, Regidx rd, op), s0)) ->
    uint rd <> 0 ->
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
    ▷ (user_frame -∗ WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intros HN Hok Hsome Hchk0 HupdN Hcw HSXL Hval Hcanon Hvpn_def Hpaal HnotRVC Hdec Hrd.
    iApply (ustep_rtype2_u
              (fun rs2' rs1' rd' => ZICOND_RTYPE (Regidx rs2', Regidx rs1', Regidx rd', op))
              (zicond_f op)
              va vpn ie w rs2 rs1 rd ms_v sc_v stval_v sepc_v g tlbvec E Φ HN
              (fun rs2' rs1' rd' s Hrd' =>
                 exec_execute_ZICOND_RTYPE_gpr_nz rs2' rs1' rd' op s Hrd')
              eq_refl Hok Hsome Hchk0 HupdN Hcw HSXL Hval Hcanon
              Hvpn_def Hpaal HnotRVC Hdec Hrd).
  Qed.

End WpUserZicondU.
