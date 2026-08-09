(* SpecUserret.v -- the public interface of userret (trampoline.S), stated
   independently of its proof.

   userret is the second half of the trampoline page: entered at VIRTUAL
   address [uva 0x9c] (= TRAMPOLINE + 0x9c) on the KERNEL page table, it
   switches satp to the USER table (the pt2 window), restores the 31 saved
   user registers from the TRAPFRAME page, and sret's to User mode at the
   process's sepc.  The continuation therefore receives a USER-privilege
   machine over [utlb_inv_pt] -- exactly what [userret_to_user_inv]
   (UserKernelBridge.v) repackages into [user_inv] for the user-execution
   capstone -- with the kernel table parked as [kpt_frame kroot] for
   uservec's return trip.

   Spec vocabulary shared with uservec/usertrap:
     [tf_pa tfp off]  the PHYSICAL address of the trapframe word at byte
                      offset [off]: the trapframe page frame [tfp]
                      concatenated with the page offset of the virtual
                      address TRAPFRAME + off.  The trapframe is accessed
                      at the USER table's translate output, so it is owned
                      as physical words ([↦ₚ₈]).
     [userret_gpr m vra ... va0f]
                      the register file userret hands to user mode: every
                      restorable register overwritten with its trapframe
                      word, a0 last (it doubles as the TRAPFRAME base
                      register while the loads run). *)
From Stdlib Require Import ZArith.
From stdpp Require Import bitvector.definitions gmap.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvExtras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvFetchExec.
Require Import RegFile.
Require Import MinstretInv InstrBytes.
Require Import WpGpr.
Require Import KernelText MstatusBits.
Require Import SmodeCore.
Require Import PtTree.
Require Import TrampPt KptTree UptTree TransPt UserretDefs.
From Kernel Require KernelSyms.
Local Open Scope Z_scope.
Import Defs.

(* the physical address of the trapframe word at byte offset [off] *)
Definition tf_pa (tfp : mword 44) (off : Z) : mword 64 :=
  zero_extend' 64 (concat_vec tfp
    (subrange_vec_dec (bits_of_virtaddr (Virtaddr (mword_of_int (TRAPFRAME + off))))
       (Z.sub pagesize_bits 1) 0)).

(* the register file after userret's 31 restores (insert order = execution
   order; a0 is loaded LAST -- it holds the TRAPFRAME base until then) *)
Definition userret_gpr (m : regfile)
    (vra vsp vgp vtp vt0 vt1 vt2 vs0 vs1 va1 va2 va3 va4 va5 va6 va7
     vs2 vs3 vs4 vs5 vs6 vs7 vs8 vs9 vs10 vs11 vt3 vt4 vt5 vt6 va0f : bv 64)
    : regfile :=
  <[Regidx (mword_of_int 10) := regval_into_reg va0f]> (<[Regidx (mword_of_int 31) := regval_into_reg vt6]> (<[Regidx (mword_of_int 30) := regval_into_reg vt5]> (<[Regidx (mword_of_int 29) := regval_into_reg vt4]> (<[Regidx (mword_of_int 28) := regval_into_reg vt3]> (<[Regidx (mword_of_int 27) := regval_into_reg vs11]> (<[Regidx (mword_of_int 26) := regval_into_reg vs10]> (<[Regidx (mword_of_int 25) := regval_into_reg vs9]> (<[Regidx (mword_of_int 24) := regval_into_reg vs8]> (<[Regidx (mword_of_int 23) := regval_into_reg vs7]> (<[Regidx (mword_of_int 22) := regval_into_reg vs6]> (<[Regidx (mword_of_int 21) := regval_into_reg vs5]> (<[Regidx (mword_of_int 20) := regval_into_reg vs4]> (<[Regidx (mword_of_int 19) := regval_into_reg vs3]> (<[Regidx (mword_of_int 18) := regval_into_reg vs2]> (<[Regidx (mword_of_int 17) := regval_into_reg va7]> (<[Regidx (mword_of_int 16) := regval_into_reg va6]> (<[Regidx (mword_of_int 15) := regval_into_reg va5]> (<[Regidx (mword_of_int 14) := regval_into_reg va4]> (<[Regidx (mword_of_int 13) := regval_into_reg va3]> (<[Regidx (mword_of_int 12) := regval_into_reg va2]> (<[Regidx (mword_of_int 11) := regval_into_reg va1]> (<[Regidx (mword_of_int 9) := regval_into_reg vs1]> (<[Regidx (mword_of_int 8) := regval_into_reg vs0]> (<[Regidx (mword_of_int 7) := regval_into_reg vt2]> (<[Regidx (mword_of_int 6) := regval_into_reg vt1]> (<[Regidx (mword_of_int 5) := regval_into_reg vt0]> (<[Regidx (mword_of_int 4) := regval_into_reg vtp]> (<[Regidx (mword_of_int 3) := regval_into_reg vgp]> (<[Regidx (mword_of_int 2) := regval_into_reg vsp]> (<[Regidx (mword_of_int 1) := regval_into_reg vra]> (<[Regidx (mword_of_int 10) := mword_of_int TRAPFRAME]> m))))))))))))))))))))))))))))))).

Definition wp_userret_pt_body `{!riscvGS Σ, !sieG Σ} `{GEN : GenId} `{CID : CpuId}
    (kroot uroot tfp : mword 44)
    (um : gmap (mword 27) (mword 64))
    (m : regfile) (usatp : mword 64)
    (mstatus0 mie_v mdv0 menvcfg0 senvcfg0 sepc0 : mword 64)
    (vra vsp vgp vtp vt0 vt1 vt2 vs0 vs1 va1 va2 va3 va4 va5 va6 va7
     vs2 vs3 vs4 vs5 vs6 vs7 vs8 vs9 vs10 vs11 vt3 vt4 vt5 vt6 va0f : bv 64)
    (dqm : dfrac) :=
  (* S-mode config facts *)
  eq_vec (_get_Mstatus_SIE mstatus0) ('b"1") = false ->
  eq_vec (_get_Mstatus_MPRV mstatus0) ('b"1") = false ->
  _get_Mstatus_SXL mstatus0 = 'b"10" ->
  eq_vec (_get_Mstatus_TVM mstatus0) ('b"1") = false ->
  eq_vec (_get_Mstatus_MXR mstatus0) ('b"0") = true ->
  and_vec mie_v (not_vec mdv0) = zeros' 64 ->
  pmm_mode_backwards (_get_MEnvcfg_PMM menvcfg0) = PMM_Disabled ->
  eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
  menvcfg0 = MENVCFG_S ->
  senvcfg0 = mword_of_int 0 ->
  upt_map_wf um ->
  (* SRET decodes to USER and does not trap *)
  eq_vec (_get_Mstatus_TSR mstatus0) ('b"1") = false ->
  sret_newpriv mstatus0 = User ->
  (* a0 holds the USER satp value *)
  m !!! Regidx (mword_of_int 10) = usatp ->
  _get_Satp64_Mode (Mk_Satp64 usatp) = ('b"1000" : mword 4) ->
  zero_extend' 16 (satp_to_asid (autocast (T := mword) usatp : mword 64)) = (mword_of_int 0 : mword 16) ->
  autocast (T := mword) (satp_to_ppn (autocast (T := mword) usatp : mword 64)) = uroot ->
  kernel_text -∗
  hw_config -∗
  minstret_inv -∗
  hart_state ↦ᵣ HART_ACTIVE tt -∗
  cur_privilege ↦ᵣ Supervisor -∗
  mstatus ↦ᵣ mstatus0 -∗
  mie ↦ᵣ mie_v -∗
  mideleg ↦ᵣ mdv0 -∗
  menvcfg ↦ᵣ menvcfg0 -∗
  senvcfg ↦ᵣ senvcfg0 -∗
  sepc ↦ᵣ sepc0 -∗
  (* the trampoline claim, threaded to the entry switch *)
  kmap_at tramp_vpn tramp_ppn KP_rx -∗
  tlb_inv_pt kroot -∗
  pt_frame (upt_tree_spec uroot tfp um) -∗
  pc_is (uva 0x9c) -∗
  gpr_file m -∗
  tf_pa tfp 40 ↦ₚ₈{ dqm } vra -∗
  tf_pa tfp 48 ↦ₚ₈{ dqm } vsp -∗
  tf_pa tfp 56 ↦ₚ₈{ dqm } vgp -∗
  tf_pa tfp 64 ↦ₚ₈{ dqm } vtp -∗
  tf_pa tfp 72 ↦ₚ₈{ dqm } vt0 -∗
  tf_pa tfp 80 ↦ₚ₈{ dqm } vt1 -∗
  tf_pa tfp 88 ↦ₚ₈{ dqm } vt2 -∗
  tf_pa tfp 96 ↦ₚ₈{ dqm } vs0 -∗
  tf_pa tfp 104 ↦ₚ₈{ dqm } vs1 -∗
  tf_pa tfp 120 ↦ₚ₈{ dqm } va1 -∗
  tf_pa tfp 128 ↦ₚ₈{ dqm } va2 -∗
  tf_pa tfp 136 ↦ₚ₈{ dqm } va3 -∗
  tf_pa tfp 144 ↦ₚ₈{ dqm } va4 -∗
  tf_pa tfp 152 ↦ₚ₈{ dqm } va5 -∗
  tf_pa tfp 160 ↦ₚ₈{ dqm } va6 -∗
  tf_pa tfp 168 ↦ₚ₈{ dqm } va7 -∗
  tf_pa tfp 176 ↦ₚ₈{ dqm } vs2 -∗
  tf_pa tfp 184 ↦ₚ₈{ dqm } vs3 -∗
  tf_pa tfp 192 ↦ₚ₈{ dqm } vs4 -∗
  tf_pa tfp 200 ↦ₚ₈{ dqm } vs5 -∗
  tf_pa tfp 208 ↦ₚ₈{ dqm } vs6 -∗
  tf_pa tfp 216 ↦ₚ₈{ dqm } vs7 -∗
  tf_pa tfp 224 ↦ₚ₈{ dqm } vs8 -∗
  tf_pa tfp 232 ↦ₚ₈{ dqm } vs9 -∗
  tf_pa tfp 240 ↦ₚ₈{ dqm } vs10 -∗
  tf_pa tfp 248 ↦ₚ₈{ dqm } vs11 -∗
  tf_pa tfp 256 ↦ₚ₈{ dqm } vt3 -∗
  tf_pa tfp 264 ↦ₚ₈{ dqm } vt4 -∗
  tf_pa tfp 272 ↦ₚ₈{ dqm } vt5 -∗
  tf_pa tfp 280 ↦ₚ₈{ dqm } vt6 -∗
  tf_pa tfp 112 ↦ₚ₈{ dqm } va0f -∗
  ( hart_state ↦ᵣ HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ User -∗
    mstatus ↦ᵣ sret_ms5 mstatus0 -∗
    mie ↦ᵣ mie_v -∗
    mideleg ↦ᵣ mdv0 -∗
    menvcfg ↦ᵣ menvcfg0 -∗
    senvcfg ↦ᵣ senvcfg0 -∗
    sepc ↦ᵣ sepc0 -∗
    utlb_inv_pt uroot tfp um -∗
    pc_is (ret_pc sepc0) -∗
    gpr_file (userret_gpr m vra vsp vgp vtp vt0 vt1 vt2 vs0 vs1 va1 va2 va3
                va4 va5 va6 va7 vs2 vs3 vs4 vs5 vs6 vs7 vs8 vs9 vs10 vs11
                vt3 vt4 vt5 vt6 va0f) -∗
    tf_pa tfp 40 ↦ₚ₈{ dqm } vra -∗
    tf_pa tfp 48 ↦ₚ₈{ dqm } vsp -∗
    tf_pa tfp 56 ↦ₚ₈{ dqm } vgp -∗
    tf_pa tfp 64 ↦ₚ₈{ dqm } vtp -∗
    tf_pa tfp 72 ↦ₚ₈{ dqm } vt0 -∗
    tf_pa tfp 80 ↦ₚ₈{ dqm } vt1 -∗
    tf_pa tfp 88 ↦ₚ₈{ dqm } vt2 -∗
    tf_pa tfp 96 ↦ₚ₈{ dqm } vs0 -∗
    tf_pa tfp 104 ↦ₚ₈{ dqm } vs1 -∗
    tf_pa tfp 120 ↦ₚ₈{ dqm } va1 -∗
    tf_pa tfp 128 ↦ₚ₈{ dqm } va2 -∗
    tf_pa tfp 136 ↦ₚ₈{ dqm } va3 -∗
    tf_pa tfp 144 ↦ₚ₈{ dqm } va4 -∗
    tf_pa tfp 152 ↦ₚ₈{ dqm } va5 -∗
    tf_pa tfp 160 ↦ₚ₈{ dqm } va6 -∗
    tf_pa tfp 168 ↦ₚ₈{ dqm } va7 -∗
    tf_pa tfp 176 ↦ₚ₈{ dqm } vs2 -∗
    tf_pa tfp 184 ↦ₚ₈{ dqm } vs3 -∗
    tf_pa tfp 192 ↦ₚ₈{ dqm } vs4 -∗
    tf_pa tfp 200 ↦ₚ₈{ dqm } vs5 -∗
    tf_pa tfp 208 ↦ₚ₈{ dqm } vs6 -∗
    tf_pa tfp 216 ↦ₚ₈{ dqm } vs7 -∗
    tf_pa tfp 224 ↦ₚ₈{ dqm } vs8 -∗
    tf_pa tfp 232 ↦ₚ₈{ dqm } vs9 -∗
    tf_pa tfp 240 ↦ₚ₈{ dqm } vs10 -∗
    tf_pa tfp 248 ↦ₚ₈{ dqm } vs11 -∗
    tf_pa tfp 256 ↦ₚ₈{ dqm } vt3 -∗
    tf_pa tfp 264 ↦ₚ₈{ dqm } vt4 -∗
    tf_pa tfp 272 ↦ₚ₈{ dqm } vt5 -∗
    tf_pa tfp 280 ↦ₚ₈{ dqm } vt6 -∗
    tf_pa tfp 112 ↦ₚ₈{ dqm } va0f -∗
    kpt_frame kroot -∗
    WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

Module Type USERRET.
  Parameter wp_userret_pt :
    forall `{!riscvGS Σ, !sieG Σ} `{GEN : GenId} `{CID : CpuId}
      (kroot uroot tfp : mword 44)
      (um : gmap (mword 27) (mword 64)) (m : regfile) (usatp : mword 64)
      (mstatus0 mie_v mdv0 menvcfg0 senvcfg0 sepc0 : mword 64)
      (vra vsp vgp vtp vt0 vt1 vt2 vs0 vs1 va1 va2 va3 va4 va5 va6 va7
       vs2 vs3 vs4 vs5 vs6 vs7 vs8 vs9 vs10 vs11 vt3 vt4 vt5 vt6 va0f : bv 64)
      (dqm : dfrac),
      wp_userret_pt_body kroot uroot tfp um m usatp
        mstatus0 mie_v mdv0 menvcfg0 senvcfg0 sepc0
        vra vsp vgp vtp vt0 vt1 vt2 vs0 vs1 va1 va2 va3 va4 va5 va6 va7
        vs2 vs3 vs4 vs5 vs6 vs7 vs8 vs9 vs10 vs11 vt3 vt4 vt5 vt6 va0f dqm.
End USERRET.
