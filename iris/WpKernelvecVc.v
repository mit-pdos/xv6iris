(* WpKernelvecVc.v -- the LONG straight-line runs of kernelvec as single
   VCgen blocks (agreement interface): the 17-instruction c.sdsp register
   save (+0x2..+0x22) and the 17-instruction c.ldsp restore (+0x28..+0x48).
   These are the block shapes the VCgen is built for: one seam pair and one
   vm_compute'd symbolic run amortized over 17 instructions, versus 17
   hand-chained leaf applications in WpKernelvecNew.  All code below the
   two run lemmas is seam glue generated mechanically from the offset/
   register pair list. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import RiscvModelBytes.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvExtras RiscvTryStep RiscvFetchExec.
Require Import MinstretInv InstrBytes.
Require Import WpAdd WpFetch WpLoad WpDecode WpLeafCommon WpEntry WpEntryNew WpAuipc.
Require Import WpGpr WpGprAddi WpGprRvc WpGprShift WpGprJalr WpGprStore WpGprLogic WpGprAuipc WpGprLoad.
Require Import SmodeCore WpSmodeGpr WpMemsetS WpSpinNew WpKernelvecNew WpPushOff.
Require Import WpPushOffMem WpKvInstr.
Require Import VcGen VcGenS.
From Kernel Require KernelInstrs.
From Kernel Require KernelSyms.
From iris.base_logic.lib Require Import invariants.
Local Open Scope Z_scope.

Notation KV := KernelSyms.kernelvec.

Definition kv_store_prog : list vop_s :=
  [ VScsdsp (mword_of_int 0) (mword_of_int 1);
    VScsdsp (mword_of_int 2) (mword_of_int 3);
    VScsdsp (mword_of_int 4) (mword_of_int 5);
    VScsdsp (mword_of_int 5) (mword_of_int 6);
    VScsdsp (mword_of_int 6) (mword_of_int 7);
    VScsdsp (mword_of_int 9) (mword_of_int 10);
    VScsdsp (mword_of_int 10) (mword_of_int 11);
    VScsdsp (mword_of_int 11) (mword_of_int 12);
    VScsdsp (mword_of_int 12) (mword_of_int 13);
    VScsdsp (mword_of_int 13) (mword_of_int 14);
    VScsdsp (mword_of_int 14) (mword_of_int 15);
    VScsdsp (mword_of_int 15) (mword_of_int 16);
    VScsdsp (mword_of_int 16) (mword_of_int 17);
    VScsdsp (mword_of_int 27) (mword_of_int 28);
    VScsdsp (mword_of_int 28) (mword_of_int 29);
    VScsdsp (mword_of_int 29) (mword_of_int 30);
    VScsdsp (mword_of_int 30) (mword_of_int 31) ].
Definition kv_load_prog : list vop_s :=
  [ VScldsp (mword_of_int 0) (mword_of_int 1);
    VScldsp (mword_of_int 2) (mword_of_int 3);
    VScldsp (mword_of_int 4) (mword_of_int 5);
    VScldsp (mword_of_int 5) (mword_of_int 6);
    VScldsp (mword_of_int 6) (mword_of_int 7);
    VScldsp (mword_of_int 9) (mword_of_int 10);
    VScldsp (mword_of_int 10) (mword_of_int 11);
    VScldsp (mword_of_int 11) (mword_of_int 12);
    VScldsp (mword_of_int 12) (mword_of_int 13);
    VScldsp (mword_of_int 13) (mword_of_int 14);
    VScldsp (mword_of_int 14) (mword_of_int 15);
    VScldsp (mword_of_int 15) (mword_of_int 16);
    VScldsp (mword_of_int 16) (mword_of_int 17);
    VScldsp (mword_of_int 27) (mword_of_int 28);
    VScldsp (mword_of_int 28) (mword_of_int 29);
    VScldsp (mword_of_int 29) (mword_of_int 30);
    VScldsp (mword_of_int 30) (mword_of_int 31) ].
Definition kv_store_regs0 : gmap regidx sval :=
  <[Regidx csp_rs1 := SX 2 0]>
  (<[Regidx (mword_of_int 1 : mword 5) := SX 1 0]>
  (<[Regidx (mword_of_int 3 : mword 5) := SX 3 0]>
  (<[Regidx (mword_of_int 5 : mword 5) := SX 5 0]>
  (<[Regidx (mword_of_int 6 : mword 5) := SX 6 0]>
  (<[Regidx (mword_of_int 7 : mword 5) := SX 7 0]>
  (<[Regidx (mword_of_int 10 : mword 5) := SX 10 0]>
  (<[Regidx (mword_of_int 11 : mword 5) := SX 11 0]>
  (<[Regidx (mword_of_int 12 : mword 5) := SX 12 0]>
  (<[Regidx (mword_of_int 13 : mword 5) := SX 13 0]>
  (<[Regidx (mword_of_int 14 : mword 5) := SX 14 0]>
  (<[Regidx (mword_of_int 15 : mword 5) := SX 15 0]>
  (<[Regidx (mword_of_int 16 : mword 5) := SX 16 0]>
  (<[Regidx (mword_of_int 17 : mword 5) := SX 17 0]>
  (<[Regidx (mword_of_int 28 : mword 5) := SX 28 0]>
  (<[Regidx (mword_of_int 29 : mword 5) := SX 29 0]>
  (<[Regidx (mword_of_int 30 : mword 5) := SX 30 0]>
  (<[Regidx (mword_of_int 31 : mword 5) := SX 31 0]> ∅))))))))))))))))).
Definition kv_store_heap0 : list (sval * sval) :=
  [ (SX 2 0, SX 33 0);
    (SX 2 16, SX 34 0);
    (SX 2 32, SX 35 0);
    (SX 2 40, SX 36 0);
    (SX 2 48, SX 37 0);
    (SX 2 72, SX 38 0);
    (SX 2 80, SX 39 0);
    (SX 2 88, SX 40 0);
    (SX 2 96, SX 41 0);
    (SX 2 104, SX 42 0);
    (SX 2 112, SX 43 0);
    (SX 2 120, SX 44 0);
    (SX 2 128, SX 45 0);
    (SX 2 216, SX 46 0);
    (SX 2 224, SX 47 0);
    (SX 2 232, SX 48 0);
    (SX 2 240, SX 49 0) ].
Definition kv_store_heap1 : list (sval * sval) :=
  [ (SX 2 0, SX 1 0);
    (SX 2 16, SX 3 0);
    (SX 2 32, SX 5 0);
    (SX 2 40, SX 6 0);
    (SX 2 48, SX 7 0);
    (SX 2 72, SX 10 0);
    (SX 2 80, SX 11 0);
    (SX 2 88, SX 12 0);
    (SX 2 96, SX 13 0);
    (SX 2 104, SX 14 0);
    (SX 2 112, SX 15 0);
    (SX 2 120, SX 16 0);
    (SX 2 128, SX 17 0);
    (SX 2 216, SX 28 0);
    (SX 2 224, SX 29 0);
    (SX 2 232, SX 30 0);
    (SX 2 240, SX 31 0) ].
Definition kv_load_regs0 : gmap regidx sval :=
  <[Regidx csp_rs1 := SX 2 0]> ∅.
Definition kv_load_regs1 : gmap regidx sval :=
  <[Regidx (mword_of_int 31 : mword 5) := SX 49 0]>
  (<[Regidx (mword_of_int 30 : mword 5) := SX 48 0]>
  (<[Regidx (mword_of_int 29 : mword 5) := SX 47 0]>
  (<[Regidx (mword_of_int 28 : mword 5) := SX 46 0]>
  (<[Regidx (mword_of_int 17 : mword 5) := SX 45 0]>
  (<[Regidx (mword_of_int 16 : mword 5) := SX 44 0]>
  (<[Regidx (mword_of_int 15 : mword 5) := SX 43 0]>
  (<[Regidx (mword_of_int 14 : mword 5) := SX 42 0]>
  (<[Regidx (mword_of_int 13 : mword 5) := SX 41 0]>
  (<[Regidx (mword_of_int 12 : mword 5) := SX 40 0]>
  (<[Regidx (mword_of_int 11 : mword 5) := SX 39 0]>
  (<[Regidx (mword_of_int 10 : mword 5) := SX 38 0]>
  (<[Regidx (mword_of_int 7 : mword 5) := SX 37 0]>
  (<[Regidx (mword_of_int 6 : mword 5) := SX 36 0]>
  (<[Regidx (mword_of_int 5 : mword 5) := SX 35 0]>
  (<[Regidx (mword_of_int 3 : mword 5) := SX 34 0]>
  (<[Regidx (mword_of_int 1 : mword 5) := SX 33 0]> kv_load_regs0)))))))))))))))).

Lemma kv_store_run :
  vc_block_s (VSt (KV + 0x2) kv_store_regs0 kv_store_heap0 []) kv_store_prog
  = Some (VSt (KV + 0x24) kv_store_regs0 kv_store_heap1 []).
Proof. vm_compute. reflexivity. Qed.

Lemma kv_load_run :
  vc_block_s (VSt (KV + 0x28) kv_load_regs0 kv_store_heap0 []) kv_load_prog
  = Some (VSt (KV + 0x4a) kv_load_regs1 kv_store_heap0 []).
Proof. vm_compute. reflexivity. Qed.

Section WpKernelvecVc.
  Context `{!riscvGS Σ}.
  Context `{CID : CpuId}.

  Lemma kv_store_instrs :
    kernel_text -∗ block_instrs_s (KV + 0x2) kv_store_prog.
  Proof.
    iIntros "#Ht". cbn [block_instrs_s kv_store_prog vop_s_ast].
    iSplitR; [by iApply kv_i2|].
    replace (KV + 0x2 + 2) with (KV + 0x4) by lia.
    iSplitR; [by iApply kv_i3|].
    replace (KV + 0x4 + 2) with (KV + 0x6) by lia.
    iSplitR; [by iApply kv_i4|].
    replace (KV + 0x6 + 2) with (KV + 0x8) by lia.
    iSplitR; [by iApply kv_i5|].
    replace (KV + 0x8 + 2) with (KV + 0xa) by lia.
    iSplitR; [by iApply kv_i6|].
    replace (KV + 0xa + 2) with (KV + 0xc) by lia.
    iSplitR; [by iApply kv_i7|].
    replace (KV + 0xc + 2) with (KV + 0xe) by lia.
    iSplitR; [by iApply kv_i8|].
    replace (KV + 0xe + 2) with (KV + 0x10) by lia.
    iSplitR; [by iApply kv_i9|].
    replace (KV + 0x10 + 2) with (KV + 0x12) by lia.
    iSplitR; [by iApply kv_i10|].
    replace (KV + 0x12 + 2) with (KV + 0x14) by lia.
    iSplitR; [by iApply kv_i11|].
    replace (KV + 0x14 + 2) with (KV + 0x16) by lia.
    iSplitR; [by iApply kv_i12|].
    replace (KV + 0x16 + 2) with (KV + 0x18) by lia.
    iSplitR; [by iApply kv_i13|].
    replace (KV + 0x18 + 2) with (KV + 0x1a) by lia.
    iSplitR; [by iApply kv_i14|].
    replace (KV + 0x1a + 2) with (KV + 0x1c) by lia.
    iSplitR; [by iApply kv_i15|].
    replace (KV + 0x1c + 2) with (KV + 0x1e) by lia.
    iSplitR; [by iApply kv_i16|].
    replace (KV + 0x1e + 2) with (KV + 0x20) by lia.
    iSplitR; [by iApply kv_i17|].
    replace (KV + 0x20 + 2) with (KV + 0x22) by lia.
    iSplitR; [by iApply kv_i18|].
    done.
  Qed.

  Lemma kv_load_instrs :
    kernel_text -∗ block_instrs_s (KV + 0x28) kv_load_prog.
  Proof.
    iIntros "#Ht". cbn [block_instrs_s kv_load_prog vop_s_ast].
    iSplitR; [by iApply kv_i20|].
    replace (KV + 0x28 + 2) with (KV + 0x2a) by lia.
    iSplitR; [by iApply kv_i21|].
    replace (KV + 0x2a + 2) with (KV + 0x2c) by lia.
    iSplitR; [by iApply kv_i22|].
    replace (KV + 0x2c + 2) with (KV + 0x2e) by lia.
    iSplitR; [by iApply kv_i23|].
    replace (KV + 0x2e + 2) with (KV + 0x30) by lia.
    iSplitR; [by iApply kv_i24|].
    replace (KV + 0x30 + 2) with (KV + 0x32) by lia.
    iSplitR; [by iApply kv_i25|].
    replace (KV + 0x32 + 2) with (KV + 0x34) by lia.
    iSplitR; [by iApply kv_i26|].
    replace (KV + 0x34 + 2) with (KV + 0x36) by lia.
    iSplitR; [by iApply kv_i27|].
    replace (KV + 0x36 + 2) with (KV + 0x38) by lia.
    iSplitR; [by iApply kv_i28|].
    replace (KV + 0x38 + 2) with (KV + 0x3a) by lia.
    iSplitR; [by iApply kv_i29|].
    replace (KV + 0x3a + 2) with (KV + 0x3c) by lia.
    iSplitR; [by iApply kv_i30|].
    replace (KV + 0x3c + 2) with (KV + 0x3e) by lia.
    iSplitR; [by iApply kv_i31|].
    replace (KV + 0x3e + 2) with (KV + 0x40) by lia.
    iSplitR; [by iApply kv_i32|].
    replace (KV + 0x40 + 2) with (KV + 0x42) by lia.
    iSplitR; [by iApply kv_i33|].
    replace (KV + 0x42 + 2) with (KV + 0x44) by lia.
    iSplitR; [by iApply kv_i34|].
    replace (KV + 0x44 + 2) with (KV + 0x46) by lia.
    iSplitR; [by iApply kv_i35|].
    replace (KV + 0x46 + 2) with (KV + 0x48) by lia.
    iSplitR; [by iApply kv_i36|].
    done.
  Qed.

  (* the 17-instruction register-save run, as ONE block. *)
  Lemma wp_kv_store_block_vc (root_ppn : mword 44) E (Φ : mval -> iProp Σ)
      (m : gmap regidx (mword 64))
      (vold1 vold2 vold3 vold4 vold5 vold6 vold7 vold8 vold9 vold10 vold11 vold12 vold13 vold14 vold15 vold16 vold17 : bv 64)
      (mstatus0 mie_v mdv0 menvcfg0 : mword 64)
      {dq : dfrac} :
    ↑minstretN ⊆ E ->
    eq_vec (_get_Mstatus_SIE mstatus0) ('b"1") = false ->
    eq_vec (_get_Mstatus_MPRV mstatus0) ('b"1") = false ->
    _get_Mstatus_SXL mstatus0 = 'b"10" ->
    and_vec mie_v (not_vec mdv0) = zeros' 64 ->
    eq_vec (_get_Mstatus_MXR mstatus0) ('b"0") = true ->
    pmm_mode_backwards (_get_MEnvcfg_PMM menvcfg0) = PMM_Disabled ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    hw_config -∗ minstret_inv -∗
    hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ{ dq } Supervisor -∗ mstatus ↦ᵣ{ dq } mstatus0 -∗
    mie ↦ᵣ{ dq } mie_v -∗ mideleg ↦ᵣ{ dq } mdv0 -∗ menvcfg ↦ᵣ{ dq } menvcfg0 -∗
    tlb_inv root_ppn -∗
    pc_is (mword_of_int (KV + 0x2)) -∗
    gpr_file m -∗
    kernel_text -∗
    (m !!! Regidx csp_rs1) ↦₈ vold1 -∗
    (add_vec (m !!! Regidx csp_rs1) (mword_of_int 16)) ↦₈ vold2 -∗
    (add_vec (m !!! Regidx csp_rs1) (mword_of_int 32)) ↦₈ vold3 -∗
    (add_vec (m !!! Regidx csp_rs1) (mword_of_int 40)) ↦₈ vold4 -∗
    (add_vec (m !!! Regidx csp_rs1) (mword_of_int 48)) ↦₈ vold5 -∗
    (add_vec (m !!! Regidx csp_rs1) (mword_of_int 72)) ↦₈ vold6 -∗
    (add_vec (m !!! Regidx csp_rs1) (mword_of_int 80)) ↦₈ vold7 -∗
    (add_vec (m !!! Regidx csp_rs1) (mword_of_int 88)) ↦₈ vold8 -∗
    (add_vec (m !!! Regidx csp_rs1) (mword_of_int 96)) ↦₈ vold9 -∗
    (add_vec (m !!! Regidx csp_rs1) (mword_of_int 104)) ↦₈ vold10 -∗
    (add_vec (m !!! Regidx csp_rs1) (mword_of_int 112)) ↦₈ vold11 -∗
    (add_vec (m !!! Regidx csp_rs1) (mword_of_int 120)) ↦₈ vold12 -∗
    (add_vec (m !!! Regidx csp_rs1) (mword_of_int 128)) ↦₈ vold13 -∗
    (add_vec (m !!! Regidx csp_rs1) (mword_of_int 216)) ↦₈ vold14 -∗
    (add_vec (m !!! Regidx csp_rs1) (mword_of_int 224)) ↦₈ vold15 -∗
    (add_vec (m !!! Regidx csp_rs1) (mword_of_int 232)) ↦₈ vold16 -∗
    (add_vec (m !!! Regidx csp_rs1) (mword_of_int 240)) ↦₈ vold17 -∗
    ( ∀ mf : gmap regidx (mword 64),
      ⌜ mf !!! Regidx csp_rs1 = m !!! Regidx csp_rs1 /\
          mf !!! Regidx (mword_of_int 1 : mword 5) = m !!! Regidx (mword_of_int 1 : mword 5) /\
          mf !!! Regidx (mword_of_int 3 : mword 5) = m !!! Regidx (mword_of_int 3 : mword 5) /\
          mf !!! Regidx (mword_of_int 5 : mword 5) = m !!! Regidx (mword_of_int 5 : mword 5) /\
          mf !!! Regidx (mword_of_int 6 : mword 5) = m !!! Regidx (mword_of_int 6 : mword 5) /\
          mf !!! Regidx (mword_of_int 7 : mword 5) = m !!! Regidx (mword_of_int 7 : mword 5) /\
          mf !!! Regidx (mword_of_int 10 : mword 5) = m !!! Regidx (mword_of_int 10 : mword 5) /\
          mf !!! Regidx (mword_of_int 11 : mword 5) = m !!! Regidx (mword_of_int 11 : mword 5) /\
          mf !!! Regidx (mword_of_int 12 : mword 5) = m !!! Regidx (mword_of_int 12 : mword 5) /\
          mf !!! Regidx (mword_of_int 13 : mword 5) = m !!! Regidx (mword_of_int 13 : mword 5) /\
          mf !!! Regidx (mword_of_int 14 : mword 5) = m !!! Regidx (mword_of_int 14 : mword 5) /\
          mf !!! Regidx (mword_of_int 15 : mword 5) = m !!! Regidx (mword_of_int 15 : mword 5) /\
          mf !!! Regidx (mword_of_int 16 : mword 5) = m !!! Regidx (mword_of_int 16 : mword 5) /\
          mf !!! Regidx (mword_of_int 17 : mword 5) = m !!! Regidx (mword_of_int 17 : mword 5) /\
          mf !!! Regidx (mword_of_int 28 : mword 5) = m !!! Regidx (mword_of_int 28 : mword 5) /\
          mf !!! Regidx (mword_of_int 29 : mword 5) = m !!! Regidx (mword_of_int 29 : mword 5) /\
          mf !!! Regidx (mword_of_int 30 : mword 5) = m !!! Regidx (mword_of_int 30 : mword 5) /\
          mf !!! Regidx (mword_of_int 31 : mword 5) = m !!! Regidx (mword_of_int 31 : mword 5) ⌝ -∗
      hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
      cur_privilege ↦ᵣ{ dq } Supervisor -∗ mstatus ↦ᵣ{ dq } mstatus0 -∗
      mie ↦ᵣ{ dq } mie_v -∗ mideleg ↦ᵣ{ dq } mdv0 -∗ menvcfg ↦ᵣ{ dq } menvcfg0 -∗
      tlb_inv root_ppn -∗
      pc_is (mword_of_int (KV + 0x24)) -∗
      gpr_file mf -∗
      (m !!! Regidx csp_rs1) ↦₈ (m !!! Regidx (mword_of_int 1 : mword 5)) -∗
      (add_vec (m !!! Regidx csp_rs1) (mword_of_int 16)) ↦₈ (m !!! Regidx (mword_of_int 3 : mword 5)) -∗
      (add_vec (m !!! Regidx csp_rs1) (mword_of_int 32)) ↦₈ (m !!! Regidx (mword_of_int 5 : mword 5)) -∗
      (add_vec (m !!! Regidx csp_rs1) (mword_of_int 40)) ↦₈ (m !!! Regidx (mword_of_int 6 : mword 5)) -∗
      (add_vec (m !!! Regidx csp_rs1) (mword_of_int 48)) ↦₈ (m !!! Regidx (mword_of_int 7 : mword 5)) -∗
      (add_vec (m !!! Regidx csp_rs1) (mword_of_int 72)) ↦₈ (m !!! Regidx (mword_of_int 10 : mword 5)) -∗
      (add_vec (m !!! Regidx csp_rs1) (mword_of_int 80)) ↦₈ (m !!! Regidx (mword_of_int 11 : mword 5)) -∗
      (add_vec (m !!! Regidx csp_rs1) (mword_of_int 88)) ↦₈ (m !!! Regidx (mword_of_int 12 : mword 5)) -∗
      (add_vec (m !!! Regidx csp_rs1) (mword_of_int 96)) ↦₈ (m !!! Regidx (mword_of_int 13 : mword 5)) -∗
      (add_vec (m !!! Regidx csp_rs1) (mword_of_int 104)) ↦₈ (m !!! Regidx (mword_of_int 14 : mword 5)) -∗
      (add_vec (m !!! Regidx csp_rs1) (mword_of_int 112)) ↦₈ (m !!! Regidx (mword_of_int 15 : mword 5)) -∗
      (add_vec (m !!! Regidx csp_rs1) (mword_of_int 120)) ↦₈ (m !!! Regidx (mword_of_int 16 : mword 5)) -∗
      (add_vec (m !!! Regidx csp_rs1) (mword_of_int 128)) ↦₈ (m !!! Regidx (mword_of_int 17 : mword 5)) -∗
      (add_vec (m !!! Regidx csp_rs1) (mword_of_int 216)) ↦₈ (m !!! Regidx (mword_of_int 28 : mword 5)) -∗
      (add_vec (m !!! Regidx csp_rs1) (mword_of_int 224)) ↦₈ (m !!! Regidx (mword_of_int 29 : mword 5)) -∗
      (add_vec (m !!! Regidx csp_rs1) (mword_of_int 232)) ↦₈ (m !!! Regidx (mword_of_int 30 : mword 5)) -∗
      (add_vec (m !!! Regidx csp_rs1) (mword_of_int 240)) ↦₈ (m !!! Regidx (mword_of_int 31 : mword 5)) -∗
      WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intros HN HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE.
    iIntros "#Hhw #Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv
             Hpc Hfile #Htext Hw1 Hw2 Hw3 Hw4 Hw5 Hw6 Hw7 Hw8 Hw9 Hw10 Hw11 Hw12 Hw13 Hw14 Hw15 Hw16 Hw17 Hcont".
    pose (ρ := fun k : nat => match k with
           | 2%nat => m !!! Regidx csp_rs1
           | 1%nat => m !!! Regidx (mword_of_int 1 : mword 5)
           | 3%nat => m !!! Regidx (mword_of_int 3 : mword 5)
           | 5%nat => m !!! Regidx (mword_of_int 5 : mword 5)
           | 6%nat => m !!! Regidx (mword_of_int 6 : mword 5)
           | 7%nat => m !!! Regidx (mword_of_int 7 : mword 5)
           | 10%nat => m !!! Regidx (mword_of_int 10 : mword 5)
           | 11%nat => m !!! Regidx (mword_of_int 11 : mword 5)
           | 12%nat => m !!! Regidx (mword_of_int 12 : mword 5)
           | 13%nat => m !!! Regidx (mword_of_int 13 : mword 5)
           | 14%nat => m !!! Regidx (mword_of_int 14 : mword 5)
           | 15%nat => m !!! Regidx (mword_of_int 15 : mword 5)
           | 16%nat => m !!! Regidx (mword_of_int 16 : mword 5)
           | 17%nat => m !!! Regidx (mword_of_int 17 : mword 5)
           | 28%nat => m !!! Regidx (mword_of_int 28 : mword 5)
           | 29%nat => m !!! Regidx (mword_of_int 29 : mword 5)
           | 30%nat => m !!! Regidx (mword_of_int 30 : mword 5)
           | 31%nat => m !!! Regidx (mword_of_int 31 : mword 5)
           | 33%nat => (vold1 : mword 64)
           | 34%nat => (vold2 : mword 64)
           | 35%nat => (vold3 : mword 64)
           | 36%nat => (vold4 : mword 64)
           | 37%nat => (vold5 : mword 64)
           | 38%nat => (vold6 : mword 64)
           | 39%nat => (vold7 : mword 64)
           | 40%nat => (vold8 : mword 64)
           | 41%nat => (vold9 : mword 64)
           | 42%nat => (vold10 : mword 64)
           | 43%nat => (vold11 : mword 64)
           | 44%nat => (vold12 : mword 64)
           | 45%nat => (vold13 : mword 64)
           | 46%nat => (vold14 : mword 64)
           | 47%nat => (vold15 : mword 64)
           | 48%nat => (vold16 : mword 64)
           | 49%nat => (vold17 : mword 64)
           | _ => zero_reg
           end).
    assert (HmS : gpr_matches ρ kv_store_regs0 m).
    { unfold kv_store_regs0.
      repeat (apply gpr_matches_ins; [rewrite sval_den_SX0; reflexivity|]).
      apply gpr_matches_empty. }
    assert (HR2 : ρ 2%nat = m !!! Regidx csp_rs1) by reflexivity.
    assert (HVo1 : ρ 33%nat = (vold1 : mword 64)) by reflexivity.
    assert (HVo2 : ρ 34%nat = (vold2 : mword 64)) by reflexivity.
    assert (HVo3 : ρ 35%nat = (vold3 : mword 64)) by reflexivity.
    assert (HVo4 : ρ 36%nat = (vold4 : mword 64)) by reflexivity.
    assert (HVo5 : ρ 37%nat = (vold5 : mword 64)) by reflexivity.
    assert (HVo6 : ρ 38%nat = (vold6 : mword 64)) by reflexivity.
    assert (HVo7 : ρ 39%nat = (vold7 : mword 64)) by reflexivity.
    assert (HVo8 : ρ 40%nat = (vold8 : mword 64)) by reflexivity.
    assert (HVo9 : ρ 41%nat = (vold9 : mword 64)) by reflexivity.
    assert (HVo10 : ρ 42%nat = (vold10 : mword 64)) by reflexivity.
    assert (HVo11 : ρ 43%nat = (vold11 : mword 64)) by reflexivity.
    assert (HVo12 : ρ 44%nat = (vold12 : mword 64)) by reflexivity.
    assert (HVo13 : ρ 45%nat = (vold13 : mword 64)) by reflexivity.
    assert (HVo14 : ρ 46%nat = (vold14 : mword 64)) by reflexivity.
    assert (HVo15 : ρ 47%nat = (vold15 : mword 64)) by reflexivity.
    assert (HVo16 : ρ 48%nat = (vold16 : mword 64)) by reflexivity.
    assert (HVo17 : ρ 49%nat = (vold17 : mword 64)) by reflexivity.
    assert (HVr1 : ρ 1%nat = m !!! Regidx (mword_of_int 1 : mword 5)) by reflexivity.
    assert (HVr3 : ρ 3%nat = m !!! Regidx (mword_of_int 3 : mword 5)) by reflexivity.
    assert (HVr5 : ρ 5%nat = m !!! Regidx (mword_of_int 5 : mword 5)) by reflexivity.
    assert (HVr6 : ρ 6%nat = m !!! Regidx (mword_of_int 6 : mword 5)) by reflexivity.
    assert (HVr7 : ρ 7%nat = m !!! Regidx (mword_of_int 7 : mword 5)) by reflexivity.
    assert (HVr10 : ρ 10%nat = m !!! Regidx (mword_of_int 10 : mword 5)) by reflexivity.
    assert (HVr11 : ρ 11%nat = m !!! Regidx (mword_of_int 11 : mword 5)) by reflexivity.
    assert (HVr12 : ρ 12%nat = m !!! Regidx (mword_of_int 12 : mword 5)) by reflexivity.
    assert (HVr13 : ρ 13%nat = m !!! Regidx (mword_of_int 13 : mword 5)) by reflexivity.
    assert (HVr14 : ρ 14%nat = m !!! Regidx (mword_of_int 14 : mword 5)) by reflexivity.
    assert (HVr15 : ρ 15%nat = m !!! Regidx (mword_of_int 15 : mword 5)) by reflexivity.
    assert (HVr16 : ρ 16%nat = m !!! Regidx (mword_of_int 16 : mword 5)) by reflexivity.
    assert (HVr17 : ρ 17%nat = m !!! Regidx (mword_of_int 17 : mword 5)) by reflexivity.
    assert (HVr28 : ρ 28%nat = m !!! Regidx (mword_of_int 28 : mword 5)) by reflexivity.
    assert (HVr29 : ρ 29%nat = m !!! Regidx (mword_of_int 29 : mword 5)) by reflexivity.
    assert (HVr30 : ρ 30%nat = m !!! Regidx (mword_of_int 30 : mword 5)) by reflexivity.
    assert (HVr31 : ρ 31%nat = m !!! Regidx (mword_of_int 31 : mword 5)) by reflexivity.
    iDestruct (kv_store_instrs with "Htext") as "Hbi".
    iApply (wp_vc_block_s root_ppn kv_store_prog E Φ
              (VSt (KV + 0x2) kv_store_regs0 kv_store_heap0 [])
              (VSt (KV + 0x24) kv_store_regs0 kv_store_heap1 [])
              ρ m mstatus0 mie_v mdv0 menvcfg0
              (dq:=dq)
              HN HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE kv_store_run HmS
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv
                    Hpc Hfile Hbi [Hw1 Hw2 Hw3 Hw4 Hw5 Hw6 Hw7 Hw8 Hw9 Hw10 Hw11 Hw12 Hw13 Hw14 Hw15 Hw16 Hw17] []").
    { rewrite /vheap_own. cbn [vheap]. rewrite /kv_store_heap0.
      cbn [big_opL fst snd].
      rewrite !sval_den_SX0. cbn [sval_den].
      rewrite !HR2 HVo1 HVo2 HVo3 HVo4 HVo5 HVo6 HVo7 HVo8 HVo9 HVo10 HVo11 HVo12 HVo13 HVo14 HVo15 HVo16 HVo17.
      iFrame "Hw1 Hw2 Hw3 Hw4 Hw5 Hw6 Hw7 Hw8 Hw9 Hw10 Hw11 Hw12 Hw13 Hw14 Hw15 Hw16 Hw17". }
    { rewrite /vheap4_own. cbn [vheap4]. done. }
    iIntros (mf) "%Hmf Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hheap _".
    iEval (rewrite /vheap_own; cbn [vheap]; rewrite /kv_store_heap1;
           cbn [big_opL fst snd];
           rewrite !sval_den_SX0; cbn [sval_den];
           rewrite !HR2 HVr1 HVr3 HVr5 HVr6 HVr7 HVr10 HVr11 HVr12 HVr13 HVr14 HVr15 HVr16 HVr17 HVr28 HVr29 HVr30 HVr31) in "Hheap".
    iDestruct "Hheap" as "(Hw1 & Hw2 & Hw3 & Hw4 & Hw5 & Hw6 & Hw7 & Hw8 & Hw9 & Hw10 & Hw11 & Hw12 & Hw13 & Hw14 & Hw15 & Hw16 & Hw17 & _)".
    assert (F2 : mf !!! Regidx csp_rs1 = m !!! Regidx csp_rs1).
    { assert (Hl : kv_store_regs0 !! Regidx csp_rs1 = Some (SX 2 0))
        by (vm_compute; reflexivity).
      rewrite (Hmf _ _ Hl) sval_den_SX0. reflexivity. }
    assert (F1 : mf !!! Regidx (mword_of_int 1 : mword 5) = m !!! Regidx (mword_of_int 1 : mword 5)).
    { assert (Hl : kv_store_regs0 !! Regidx (mword_of_int 1 : mword 5) = Some (SX 1 0))
        by (vm_compute; reflexivity).
      rewrite (Hmf _ _ Hl) sval_den_SX0. reflexivity. }
    assert (F3 : mf !!! Regidx (mword_of_int 3 : mword 5) = m !!! Regidx (mword_of_int 3 : mword 5)).
    { assert (Hl : kv_store_regs0 !! Regidx (mword_of_int 3 : mword 5) = Some (SX 3 0))
        by (vm_compute; reflexivity).
      rewrite (Hmf _ _ Hl) sval_den_SX0. reflexivity. }
    assert (F5 : mf !!! Regidx (mword_of_int 5 : mword 5) = m !!! Regidx (mword_of_int 5 : mword 5)).
    { assert (Hl : kv_store_regs0 !! Regidx (mword_of_int 5 : mword 5) = Some (SX 5 0))
        by (vm_compute; reflexivity).
      rewrite (Hmf _ _ Hl) sval_den_SX0. reflexivity. }
    assert (F6 : mf !!! Regidx (mword_of_int 6 : mword 5) = m !!! Regidx (mword_of_int 6 : mword 5)).
    { assert (Hl : kv_store_regs0 !! Regidx (mword_of_int 6 : mword 5) = Some (SX 6 0))
        by (vm_compute; reflexivity).
      rewrite (Hmf _ _ Hl) sval_den_SX0. reflexivity. }
    assert (F7 : mf !!! Regidx (mword_of_int 7 : mword 5) = m !!! Regidx (mword_of_int 7 : mword 5)).
    { assert (Hl : kv_store_regs0 !! Regidx (mword_of_int 7 : mword 5) = Some (SX 7 0))
        by (vm_compute; reflexivity).
      rewrite (Hmf _ _ Hl) sval_den_SX0. reflexivity. }
    assert (F10 : mf !!! Regidx (mword_of_int 10 : mword 5) = m !!! Regidx (mword_of_int 10 : mword 5)).
    { assert (Hl : kv_store_regs0 !! Regidx (mword_of_int 10 : mword 5) = Some (SX 10 0))
        by (vm_compute; reflexivity).
      rewrite (Hmf _ _ Hl) sval_den_SX0. reflexivity. }
    assert (F11 : mf !!! Regidx (mword_of_int 11 : mword 5) = m !!! Regidx (mword_of_int 11 : mword 5)).
    { assert (Hl : kv_store_regs0 !! Regidx (mword_of_int 11 : mword 5) = Some (SX 11 0))
        by (vm_compute; reflexivity).
      rewrite (Hmf _ _ Hl) sval_den_SX0. reflexivity. }
    assert (F12 : mf !!! Regidx (mword_of_int 12 : mword 5) = m !!! Regidx (mword_of_int 12 : mword 5)).
    { assert (Hl : kv_store_regs0 !! Regidx (mword_of_int 12 : mword 5) = Some (SX 12 0))
        by (vm_compute; reflexivity).
      rewrite (Hmf _ _ Hl) sval_den_SX0. reflexivity. }
    assert (F13 : mf !!! Regidx (mword_of_int 13 : mword 5) = m !!! Regidx (mword_of_int 13 : mword 5)).
    { assert (Hl : kv_store_regs0 !! Regidx (mword_of_int 13 : mword 5) = Some (SX 13 0))
        by (vm_compute; reflexivity).
      rewrite (Hmf _ _ Hl) sval_den_SX0. reflexivity. }
    assert (F14 : mf !!! Regidx (mword_of_int 14 : mword 5) = m !!! Regidx (mword_of_int 14 : mword 5)).
    { assert (Hl : kv_store_regs0 !! Regidx (mword_of_int 14 : mword 5) = Some (SX 14 0))
        by (vm_compute; reflexivity).
      rewrite (Hmf _ _ Hl) sval_den_SX0. reflexivity. }
    assert (F15 : mf !!! Regidx (mword_of_int 15 : mword 5) = m !!! Regidx (mword_of_int 15 : mword 5)).
    { assert (Hl : kv_store_regs0 !! Regidx (mword_of_int 15 : mword 5) = Some (SX 15 0))
        by (vm_compute; reflexivity).
      rewrite (Hmf _ _ Hl) sval_den_SX0. reflexivity. }
    assert (F16 : mf !!! Regidx (mword_of_int 16 : mword 5) = m !!! Regidx (mword_of_int 16 : mword 5)).
    { assert (Hl : kv_store_regs0 !! Regidx (mword_of_int 16 : mword 5) = Some (SX 16 0))
        by (vm_compute; reflexivity).
      rewrite (Hmf _ _ Hl) sval_den_SX0. reflexivity. }
    assert (F17 : mf !!! Regidx (mword_of_int 17 : mword 5) = m !!! Regidx (mword_of_int 17 : mword 5)).
    { assert (Hl : kv_store_regs0 !! Regidx (mword_of_int 17 : mword 5) = Some (SX 17 0))
        by (vm_compute; reflexivity).
      rewrite (Hmf _ _ Hl) sval_den_SX0. reflexivity. }
    assert (F28 : mf !!! Regidx (mword_of_int 28 : mword 5) = m !!! Regidx (mword_of_int 28 : mword 5)).
    { assert (Hl : kv_store_regs0 !! Regidx (mword_of_int 28 : mword 5) = Some (SX 28 0))
        by (vm_compute; reflexivity).
      rewrite (Hmf _ _ Hl) sval_den_SX0. reflexivity. }
    assert (F29 : mf !!! Regidx (mword_of_int 29 : mword 5) = m !!! Regidx (mword_of_int 29 : mword 5)).
    { assert (Hl : kv_store_regs0 !! Regidx (mword_of_int 29 : mword 5) = Some (SX 29 0))
        by (vm_compute; reflexivity).
      rewrite (Hmf _ _ Hl) sval_den_SX0. reflexivity. }
    assert (F30 : mf !!! Regidx (mword_of_int 30 : mword 5) = m !!! Regidx (mword_of_int 30 : mword 5)).
    { assert (Hl : kv_store_regs0 !! Regidx (mword_of_int 30 : mword 5) = Some (SX 30 0))
        by (vm_compute; reflexivity).
      rewrite (Hmf _ _ Hl) sval_den_SX0. reflexivity. }
    assert (F31 : mf !!! Regidx (mword_of_int 31 : mword 5) = m !!! Regidx (mword_of_int 31 : mword 5)).
    { assert (Hl : kv_store_regs0 !! Regidx (mword_of_int 31 : mword 5) = Some (SX 31 0))
        by (vm_compute; reflexivity).
      rewrite (Hmf _ _ Hl) sval_den_SX0. reflexivity. }
    iApply ("Hcont" $! mf with "[%] Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hw1 Hw2 Hw3 Hw4 Hw5 Hw6 Hw7 Hw8 Hw9 Hw10 Hw11 Hw12 Hw13 Hw14 Hw15 Hw16 Hw17").
    exact (conj F2 (conj F1 (conj F3 (conj F5 (conj F6 (conj F7 (conj F10 (conj F11 (conj F12 (conj F13 (conj F14 (conj F15 (conj F16 (conj F17 (conj F28 (conj F29 (conj F30 F31))))))))))))))))).
  Qed.

  (* the 17-instruction register-restore run, as ONE block. *)
  Lemma wp_kv_load_block_vc (root_ppn : mword 44) E (Φ : mval -> iProp Σ)
      (m : gmap regidx (mword 64))
      (w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : bv 64)
      (mstatus0 mie_v mdv0 menvcfg0 : mword 64)
      {dq : dfrac} :
    ↑minstretN ⊆ E ->
    eq_vec (_get_Mstatus_SIE mstatus0) ('b"1") = false ->
    eq_vec (_get_Mstatus_MPRV mstatus0) ('b"1") = false ->
    _get_Mstatus_SXL mstatus0 = 'b"10" ->
    and_vec mie_v (not_vec mdv0) = zeros' 64 ->
    eq_vec (_get_Mstatus_MXR mstatus0) ('b"0") = true ->
    pmm_mode_backwards (_get_MEnvcfg_PMM menvcfg0) = PMM_Disabled ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    hw_config -∗ minstret_inv -∗
    hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ{ dq } Supervisor -∗ mstatus ↦ᵣ{ dq } mstatus0 -∗
    mie ↦ᵣ{ dq } mie_v -∗ mideleg ↦ᵣ{ dq } mdv0 -∗ menvcfg ↦ᵣ{ dq } menvcfg0 -∗
    tlb_inv root_ppn -∗
    pc_is (mword_of_int (KV + 0x28)) -∗
    gpr_file m -∗
    kernel_text -∗
    (m !!! Regidx csp_rs1) ↦₈ w1 -∗
    (add_vec (m !!! Regidx csp_rs1) (mword_of_int 16)) ↦₈ w2 -∗
    (add_vec (m !!! Regidx csp_rs1) (mword_of_int 32)) ↦₈ w3 -∗
    (add_vec (m !!! Regidx csp_rs1) (mword_of_int 40)) ↦₈ w4 -∗
    (add_vec (m !!! Regidx csp_rs1) (mword_of_int 48)) ↦₈ w5 -∗
    (add_vec (m !!! Regidx csp_rs1) (mword_of_int 72)) ↦₈ w6 -∗
    (add_vec (m !!! Regidx csp_rs1) (mword_of_int 80)) ↦₈ w7 -∗
    (add_vec (m !!! Regidx csp_rs1) (mword_of_int 88)) ↦₈ w8 -∗
    (add_vec (m !!! Regidx csp_rs1) (mword_of_int 96)) ↦₈ w9 -∗
    (add_vec (m !!! Regidx csp_rs1) (mword_of_int 104)) ↦₈ w10 -∗
    (add_vec (m !!! Regidx csp_rs1) (mword_of_int 112)) ↦₈ w11 -∗
    (add_vec (m !!! Regidx csp_rs1) (mword_of_int 120)) ↦₈ w12 -∗
    (add_vec (m !!! Regidx csp_rs1) (mword_of_int 128)) ↦₈ w13 -∗
    (add_vec (m !!! Regidx csp_rs1) (mword_of_int 216)) ↦₈ w14 -∗
    (add_vec (m !!! Regidx csp_rs1) (mword_of_int 224)) ↦₈ w15 -∗
    (add_vec (m !!! Regidx csp_rs1) (mword_of_int 232)) ↦₈ w16 -∗
    (add_vec (m !!! Regidx csp_rs1) (mword_of_int 240)) ↦₈ w17 -∗
    ( ∀ mf : gmap regidx (mword 64),
      ⌜ mf !!! Regidx csp_rs1 = m !!! Regidx csp_rs1 /\
          mf !!! Regidx (mword_of_int 1 : mword 5) = (w1 : mword 64) /\
          mf !!! Regidx (mword_of_int 3 : mword 5) = (w2 : mword 64) /\
          mf !!! Regidx (mword_of_int 5 : mword 5) = (w3 : mword 64) /\
          mf !!! Regidx (mword_of_int 6 : mword 5) = (w4 : mword 64) /\
          mf !!! Regidx (mword_of_int 7 : mword 5) = (w5 : mword 64) /\
          mf !!! Regidx (mword_of_int 10 : mword 5) = (w6 : mword 64) /\
          mf !!! Regidx (mword_of_int 11 : mword 5) = (w7 : mword 64) /\
          mf !!! Regidx (mword_of_int 12 : mword 5) = (w8 : mword 64) /\
          mf !!! Regidx (mword_of_int 13 : mword 5) = (w9 : mword 64) /\
          mf !!! Regidx (mword_of_int 14 : mword 5) = (w10 : mword 64) /\
          mf !!! Regidx (mword_of_int 15 : mword 5) = (w11 : mword 64) /\
          mf !!! Regidx (mword_of_int 16 : mword 5) = (w12 : mword 64) /\
          mf !!! Regidx (mword_of_int 17 : mword 5) = (w13 : mword 64) /\
          mf !!! Regidx (mword_of_int 28 : mword 5) = (w14 : mword 64) /\
          mf !!! Regidx (mword_of_int 29 : mword 5) = (w15 : mword 64) /\
          mf !!! Regidx (mword_of_int 30 : mword 5) = (w16 : mword 64) /\
          mf !!! Regidx (mword_of_int 31 : mword 5) = (w17 : mword 64) ⌝ -∗
      hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
      cur_privilege ↦ᵣ{ dq } Supervisor -∗ mstatus ↦ᵣ{ dq } mstatus0 -∗
      mie ↦ᵣ{ dq } mie_v -∗ mideleg ↦ᵣ{ dq } mdv0 -∗ menvcfg ↦ᵣ{ dq } menvcfg0 -∗
      tlb_inv root_ppn -∗
      pc_is (mword_of_int (KV + 0x4a)) -∗
      gpr_file mf -∗
      (m !!! Regidx csp_rs1) ↦₈ w1 -∗
      (add_vec (m !!! Regidx csp_rs1) (mword_of_int 16)) ↦₈ w2 -∗
      (add_vec (m !!! Regidx csp_rs1) (mword_of_int 32)) ↦₈ w3 -∗
      (add_vec (m !!! Regidx csp_rs1) (mword_of_int 40)) ↦₈ w4 -∗
      (add_vec (m !!! Regidx csp_rs1) (mword_of_int 48)) ↦₈ w5 -∗
      (add_vec (m !!! Regidx csp_rs1) (mword_of_int 72)) ↦₈ w6 -∗
      (add_vec (m !!! Regidx csp_rs1) (mword_of_int 80)) ↦₈ w7 -∗
      (add_vec (m !!! Regidx csp_rs1) (mword_of_int 88)) ↦₈ w8 -∗
      (add_vec (m !!! Regidx csp_rs1) (mword_of_int 96)) ↦₈ w9 -∗
      (add_vec (m !!! Regidx csp_rs1) (mword_of_int 104)) ↦₈ w10 -∗
      (add_vec (m !!! Regidx csp_rs1) (mword_of_int 112)) ↦₈ w11 -∗
      (add_vec (m !!! Regidx csp_rs1) (mword_of_int 120)) ↦₈ w12 -∗
      (add_vec (m !!! Regidx csp_rs1) (mword_of_int 128)) ↦₈ w13 -∗
      (add_vec (m !!! Regidx csp_rs1) (mword_of_int 216)) ↦₈ w14 -∗
      (add_vec (m !!! Regidx csp_rs1) (mword_of_int 224)) ↦₈ w15 -∗
      (add_vec (m !!! Regidx csp_rs1) (mword_of_int 232)) ↦₈ w16 -∗
      (add_vec (m !!! Regidx csp_rs1) (mword_of_int 240)) ↦₈ w17 -∗
      WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intros HN HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE.
    iIntros "#Hhw #Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv
             Hpc Hfile #Htext Hw1 Hw2 Hw3 Hw4 Hw5 Hw6 Hw7 Hw8 Hw9 Hw10 Hw11 Hw12 Hw13 Hw14 Hw15 Hw16 Hw17 Hcont".
    pose (ρ := fun k : nat => match k with
           | 2%nat => m !!! Regidx csp_rs1
           | 33%nat => (w1 : mword 64)
           | 34%nat => (w2 : mword 64)
           | 35%nat => (w3 : mword 64)
           | 36%nat => (w4 : mword 64)
           | 37%nat => (w5 : mword 64)
           | 38%nat => (w6 : mword 64)
           | 39%nat => (w7 : mword 64)
           | 40%nat => (w8 : mword 64)
           | 41%nat => (w9 : mword 64)
           | 42%nat => (w10 : mword 64)
           | 43%nat => (w11 : mword 64)
           | 44%nat => (w12 : mword 64)
           | 45%nat => (w13 : mword 64)
           | 46%nat => (w14 : mword 64)
           | 47%nat => (w15 : mword 64)
           | 48%nat => (w16 : mword 64)
           | 49%nat => (w17 : mword 64)
           | _ => zero_reg
           end).
    assert (HmL : gpr_matches ρ kv_load_regs0 m).
    { unfold kv_load_regs0.
      repeat (apply gpr_matches_ins; [rewrite sval_den_SX0; reflexivity|]).
      apply gpr_matches_empty. }
    assert (HR2 : ρ 2%nat = m !!! Regidx csp_rs1) by reflexivity.
    assert (HVw1 : ρ 33%nat = (w1 : mword 64)) by reflexivity.
    assert (HVw2 : ρ 34%nat = (w2 : mword 64)) by reflexivity.
    assert (HVw3 : ρ 35%nat = (w3 : mword 64)) by reflexivity.
    assert (HVw4 : ρ 36%nat = (w4 : mword 64)) by reflexivity.
    assert (HVw5 : ρ 37%nat = (w5 : mword 64)) by reflexivity.
    assert (HVw6 : ρ 38%nat = (w6 : mword 64)) by reflexivity.
    assert (HVw7 : ρ 39%nat = (w7 : mword 64)) by reflexivity.
    assert (HVw8 : ρ 40%nat = (w8 : mword 64)) by reflexivity.
    assert (HVw9 : ρ 41%nat = (w9 : mword 64)) by reflexivity.
    assert (HVw10 : ρ 42%nat = (w10 : mword 64)) by reflexivity.
    assert (HVw11 : ρ 43%nat = (w11 : mword 64)) by reflexivity.
    assert (HVw12 : ρ 44%nat = (w12 : mword 64)) by reflexivity.
    assert (HVw13 : ρ 45%nat = (w13 : mword 64)) by reflexivity.
    assert (HVw14 : ρ 46%nat = (w14 : mword 64)) by reflexivity.
    assert (HVw15 : ρ 47%nat = (w15 : mword 64)) by reflexivity.
    assert (HVw16 : ρ 48%nat = (w16 : mword 64)) by reflexivity.
    assert (HVw17 : ρ 49%nat = (w17 : mword 64)) by reflexivity.
    iDestruct (kv_load_instrs with "Htext") as "Hbi".
    iApply (wp_vc_block_s root_ppn kv_load_prog E Φ
              (VSt (KV + 0x28) kv_load_regs0 kv_store_heap0 [])
              (VSt (KV + 0x4a) kv_load_regs1 kv_store_heap0 [])
              ρ m mstatus0 mie_v mdv0 menvcfg0
              (dq:=dq)
              HN HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE kv_load_run HmL
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv
                    Hpc Hfile Hbi [Hw1 Hw2 Hw3 Hw4 Hw5 Hw6 Hw7 Hw8 Hw9 Hw10 Hw11 Hw12 Hw13 Hw14 Hw15 Hw16 Hw17] []").
    { rewrite /vheap_own. cbn [vheap]. rewrite /kv_store_heap0.
      cbn [big_opL fst snd].
      rewrite !sval_den_SX0. cbn [sval_den].
      rewrite !HR2 HVw1 HVw2 HVw3 HVw4 HVw5 HVw6 HVw7 HVw8 HVw9 HVw10 HVw11 HVw12 HVw13 HVw14 HVw15 HVw16 HVw17.
      iFrame "Hw1 Hw2 Hw3 Hw4 Hw5 Hw6 Hw7 Hw8 Hw9 Hw10 Hw11 Hw12 Hw13 Hw14 Hw15 Hw16 Hw17". }
    { rewrite /vheap4_own. cbn [vheap4]. done. }
    iIntros (mf) "%Hmf Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hheap _".
    iEval (rewrite /vheap_own; cbn [vheap]; rewrite /kv_store_heap0;
           cbn [big_opL fst snd];
           rewrite !sval_den_SX0; cbn [sval_den];
           rewrite !HR2 HVw1 HVw2 HVw3 HVw4 HVw5 HVw6 HVw7 HVw8 HVw9 HVw10 HVw11 HVw12 HVw13 HVw14 HVw15 HVw16 HVw17) in "Hheap".
    iDestruct "Hheap" as "(Hw1 & Hw2 & Hw3 & Hw4 & Hw5 & Hw6 & Hw7 & Hw8 & Hw9 & Hw10 & Hw11 & Hw12 & Hw13 & Hw14 & Hw15 & Hw16 & Hw17 & _)".
    assert (F2 : mf !!! Regidx csp_rs1 = m !!! Regidx csp_rs1).
    { assert (Hl : kv_load_regs1 !! Regidx csp_rs1 = Some (SX 2 0))
        by (vm_compute; reflexivity).
      rewrite (Hmf _ _ Hl) sval_den_SX0. reflexivity. }
    assert (F1 : mf !!! Regidx (mword_of_int 1 : mword 5) = (w1 : mword 64)).
    { assert (Hl : kv_load_regs1 !! Regidx (mword_of_int 1 : mword 5) = Some (SX 33 0))
        by (vm_compute; reflexivity).
      rewrite (Hmf _ _ Hl) sval_den_SX0. reflexivity. }
    assert (F3 : mf !!! Regidx (mword_of_int 3 : mword 5) = (w2 : mword 64)).
    { assert (Hl : kv_load_regs1 !! Regidx (mword_of_int 3 : mword 5) = Some (SX 34 0))
        by (vm_compute; reflexivity).
      rewrite (Hmf _ _ Hl) sval_den_SX0. reflexivity. }
    assert (F5 : mf !!! Regidx (mword_of_int 5 : mword 5) = (w3 : mword 64)).
    { assert (Hl : kv_load_regs1 !! Regidx (mword_of_int 5 : mword 5) = Some (SX 35 0))
        by (vm_compute; reflexivity).
      rewrite (Hmf _ _ Hl) sval_den_SX0. reflexivity. }
    assert (F6 : mf !!! Regidx (mword_of_int 6 : mword 5) = (w4 : mword 64)).
    { assert (Hl : kv_load_regs1 !! Regidx (mword_of_int 6 : mword 5) = Some (SX 36 0))
        by (vm_compute; reflexivity).
      rewrite (Hmf _ _ Hl) sval_den_SX0. reflexivity. }
    assert (F7 : mf !!! Regidx (mword_of_int 7 : mword 5) = (w5 : mword 64)).
    { assert (Hl : kv_load_regs1 !! Regidx (mword_of_int 7 : mword 5) = Some (SX 37 0))
        by (vm_compute; reflexivity).
      rewrite (Hmf _ _ Hl) sval_den_SX0. reflexivity. }
    assert (F10 : mf !!! Regidx (mword_of_int 10 : mword 5) = (w6 : mword 64)).
    { assert (Hl : kv_load_regs1 !! Regidx (mword_of_int 10 : mword 5) = Some (SX 38 0))
        by (vm_compute; reflexivity).
      rewrite (Hmf _ _ Hl) sval_den_SX0. reflexivity. }
    assert (F11 : mf !!! Regidx (mword_of_int 11 : mword 5) = (w7 : mword 64)).
    { assert (Hl : kv_load_regs1 !! Regidx (mword_of_int 11 : mword 5) = Some (SX 39 0))
        by (vm_compute; reflexivity).
      rewrite (Hmf _ _ Hl) sval_den_SX0. reflexivity. }
    assert (F12 : mf !!! Regidx (mword_of_int 12 : mword 5) = (w8 : mword 64)).
    { assert (Hl : kv_load_regs1 !! Regidx (mword_of_int 12 : mword 5) = Some (SX 40 0))
        by (vm_compute; reflexivity).
      rewrite (Hmf _ _ Hl) sval_den_SX0. reflexivity. }
    assert (F13 : mf !!! Regidx (mword_of_int 13 : mword 5) = (w9 : mword 64)).
    { assert (Hl : kv_load_regs1 !! Regidx (mword_of_int 13 : mword 5) = Some (SX 41 0))
        by (vm_compute; reflexivity).
      rewrite (Hmf _ _ Hl) sval_den_SX0. reflexivity. }
    assert (F14 : mf !!! Regidx (mword_of_int 14 : mword 5) = (w10 : mword 64)).
    { assert (Hl : kv_load_regs1 !! Regidx (mword_of_int 14 : mword 5) = Some (SX 42 0))
        by (vm_compute; reflexivity).
      rewrite (Hmf _ _ Hl) sval_den_SX0. reflexivity. }
    assert (F15 : mf !!! Regidx (mword_of_int 15 : mword 5) = (w11 : mword 64)).
    { assert (Hl : kv_load_regs1 !! Regidx (mword_of_int 15 : mword 5) = Some (SX 43 0))
        by (vm_compute; reflexivity).
      rewrite (Hmf _ _ Hl) sval_den_SX0. reflexivity. }
    assert (F16 : mf !!! Regidx (mword_of_int 16 : mword 5) = (w12 : mword 64)).
    { assert (Hl : kv_load_regs1 !! Regidx (mword_of_int 16 : mword 5) = Some (SX 44 0))
        by (vm_compute; reflexivity).
      rewrite (Hmf _ _ Hl) sval_den_SX0. reflexivity. }
    assert (F17 : mf !!! Regidx (mword_of_int 17 : mword 5) = (w13 : mword 64)).
    { assert (Hl : kv_load_regs1 !! Regidx (mword_of_int 17 : mword 5) = Some (SX 45 0))
        by (vm_compute; reflexivity).
      rewrite (Hmf _ _ Hl) sval_den_SX0. reflexivity. }
    assert (F28 : mf !!! Regidx (mword_of_int 28 : mword 5) = (w14 : mword 64)).
    { assert (Hl : kv_load_regs1 !! Regidx (mword_of_int 28 : mword 5) = Some (SX 46 0))
        by (vm_compute; reflexivity).
      rewrite (Hmf _ _ Hl) sval_den_SX0. reflexivity. }
    assert (F29 : mf !!! Regidx (mword_of_int 29 : mword 5) = (w15 : mword 64)).
    { assert (Hl : kv_load_regs1 !! Regidx (mword_of_int 29 : mword 5) = Some (SX 47 0))
        by (vm_compute; reflexivity).
      rewrite (Hmf _ _ Hl) sval_den_SX0. reflexivity. }
    assert (F30 : mf !!! Regidx (mword_of_int 30 : mword 5) = (w16 : mword 64)).
    { assert (Hl : kv_load_regs1 !! Regidx (mword_of_int 30 : mword 5) = Some (SX 48 0))
        by (vm_compute; reflexivity).
      rewrite (Hmf _ _ Hl) sval_den_SX0. reflexivity. }
    assert (F31 : mf !!! Regidx (mword_of_int 31 : mword 5) = (w17 : mword 64)).
    { assert (Hl : kv_load_regs1 !! Regidx (mword_of_int 31 : mword 5) = Some (SX 49 0))
        by (vm_compute; reflexivity).
      rewrite (Hmf _ _ Hl) sval_den_SX0. reflexivity. }
    iApply ("Hcont" $! mf with "[%] Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hw1 Hw2 Hw3 Hw4 Hw5 Hw6 Hw7 Hw8 Hw9 Hw10 Hw11 Hw12 Hw13 Hw14 Hw15 Hw16 Hw17").
    exact (conj F2 (conj F1 (conj F3 (conj F5 (conj F6 (conj F7 (conj F10 (conj F11 (conj F12 (conj F13 (conj F14 (conj F15 (conj F16 (conj F17 (conj F28 (conj F29 (conj F30 F31))))))))))))))))).
  Qed.

End WpKernelvecVc.
