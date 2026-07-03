(* WpKvHit.v -- wp_kernelvec_hit: the STEADY-STATE (TLB-hit) variant of the
   complete kernelvec entry-to-SRET theorem.

   WpKernelvecNew.wp_kernelvec is the FIRST-ENTRY theorem: it requires TLB
   slots 5 / tlb_hash(svpn) to be EMPTY, page-walks on the first fetch and
   the first store, and returns the TLB with the two slots FILLED.  A second
   entry (the interrupt round trip of the WpIntrStep capstone re-enters
   kernelvec with the slots already filled) cannot reuse it.  This file
   re-runs the prologue with the HIT WPs at instrs #1 (wp_caddi16sp_gpr_s)
   and #2 (wp_csdsp_gpr_s) -- the epilogue was already all-hit -- giving:

   [wp_kernelvec_hit]: premises say slots 5 and tlb_hash(svpn) ALREADY hold
   the identity superpage entry; no pte_super_bytes footprint; the TLB is
   returned UNCHANGED.  Everything else (17 stores, kerneltrap call via the
   kerneltrap_returns axiom, 17 restores, sp cancel, SRET, gpr file fully
   preserved) is as in wp_kernelvec. *)
From Stdlib Require Import Eqdep_dec ZArith Lia List.
From stdpp Require Import gmap list list_monad bitvector.definitions bitvector.tactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap invariants.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvExtras RiscvTryStep RiscvFetchExec.
Require Import MinstretInv InstrBytes.
Require Import WpAdd WpFetch WpLoad WpDecode WpLeafCommon WpEntry.
Require Import WpGpr WpGprRvc.
Require Import SmodeCore WpSmodeGpr WpSmodeSret WpEntryNew WpKvInstr.
Require Import WpKernelvecNew.
From Kernel Require KernelInstrs.
From Kernel Require KernelSyms.
Local Open Scope Z_scope.
Import Defs.

Section WpKvHit.
  Context `{!riscvGS Σ}.

  Lemma wp_kv_prologue_hit (root_ppn : mword 44) (svpn : mword 27)
      (m : gmap regidx (mword 64))
      (satp0 mstatus0 mie_v mdv0 menvcfg0 : mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (pmpaddr00 : type_of_register pmpaddr_n)
      (tlbvec : vec (option TLB_Entry) (2 ^ 6))
      (vold1 vold2 vold3 vold4 vold5 vold6 vold7 vold8 vold9 vold10 vold11 vold12
       vold13 vold14 vold15 vold16 vold17 : bv 64)
      E (Φ : mval -> iProp Σ) :
    ↑minstretN ⊆ E ->
    _get_Satp64_Mode (Mk_Satp64 satp0) = ('b"1000" : mword 4) ->
    zero_extend' 16 (satp_to_asid (autocast (T := mword) satp0 : mword 64)) = (mword_of_int 0 : mword 16) ->
    eq_vec (_get_Mstatus_SIE mstatus0) ('b"1") = false ->
    eq_vec (_get_Mstatus_MPRV mstatus0) ('b"1") = false ->
    _get_Mstatus_SXL mstatus0 = 'b"10" ->
    and_vec mie_v (not_vec mdv0) = zeros' 64 ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    eq_vec (_get_Mstatus_MXR mstatus0) ('b"0") = true ->
    pmm_mode_backwards (_get_MEnvcfg_PMM menvcfg0) = PMM_Disabled ->
    vec_access_dec tlbvec 5 = Some (pw_tlb_entry root_ppn (mword_of_int 0)) ->
    vec_access_dec tlbvec (tlb_hash (__id 39) svpn) = Some (pw_tlb_entry root_ppn (mword_of_int 0)) ->
    (forall A : Z, kv_text_pc A = true -> pmp_tor0_sfetch_all pmpcfg0 pmpaddr00 (mword_of_int A)) ->
    eq_vec (_get_Pmpcfg_ent_W (vec_access_dec pmpcfg0 0)) ('b"1") = true ->
    and_vec (sign_extend' (57 - 12) svpn) (not_vec (mword_of_int 0x3FFFF : mword 45)) = (mword_of_int 0x80000 : mword 45) ->
    (* slot 1: x1 at sp+0 *)
    neq_vec (bits_of_virtaddr (Virtaddr (((kv_sp1 m))))) (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr (((kv_sp1 m))))) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec (subrange_vec_dec (bits_of_virtaddr (Virtaddr (((kv_sp1 m))))) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = svpn ->
    zero_extend' 64 (concat_vec (tlb_get_ppn 39 (pw_tlb_entry root_ppn (mword_of_int 0)) svpn) (subrange_vec_dec (bits_of_virtaddr (Virtaddr (((kv_sp1 m))))) (Z.sub pagesize_bits 1) 0)) = ((kv_sp1 m)) ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4) (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4) (uint (add_vec_int (((kv_sp1 m))) (0 * 8))) (uint (to_bits 64 8)) = PMP_Match ->
    is_aligned_vaddr (Virtaddr (((kv_sp1 m)))) 8 = true ->
    is_aligned_paddr (Physaddr (add_vec_int (((kv_sp1 m))) (0 * 8))) 8 = true ->
    (* slot 2: x3 at sp+16 *)
    neq_vec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000"))))))) (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000"))))))) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec (subrange_vec_dec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000"))))))) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = svpn ->
    zero_extend' 64 (concat_vec (tlb_get_ppn 39 (pw_tlb_entry root_ppn (mword_of_int 0)) svpn) (subrange_vec_dec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000"))))))) (Z.sub pagesize_bits 1) 0)) = (add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000")))) ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4) (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4) (uint (add_vec_int ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000"))))) (0 * 8))) (uint (to_bits 64 8)) = PMP_Match ->
    is_aligned_vaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000")))))) 8 = true ->
    is_aligned_paddr (Physaddr (add_vec_int ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000"))))) (0 * 8))) 8 = true ->
    (* slot 3: x5 at sp+32 *)
    neq_vec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 4 : mword 6) ('b"000"))))))) (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 4 : mword 6) ('b"000"))))))) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec (subrange_vec_dec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 4 : mword 6) ('b"000"))))))) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = svpn ->
    zero_extend' 64 (concat_vec (tlb_get_ppn 39 (pw_tlb_entry root_ppn (mword_of_int 0)) svpn) (subrange_vec_dec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 4 : mword 6) ('b"000"))))))) (Z.sub pagesize_bits 1) 0)) = (add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 4 : mword 6) ('b"000")))) ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4) (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4) (uint (add_vec_int ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 4 : mword 6) ('b"000"))))) (0 * 8))) (uint (to_bits 64 8)) = PMP_Match ->
    is_aligned_vaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 4 : mword 6) ('b"000")))))) 8 = true ->
    is_aligned_paddr (Physaddr (add_vec_int ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 4 : mword 6) ('b"000"))))) (0 * 8))) 8 = true ->
    (* slot 4: x6 at sp+40 *)
    neq_vec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 5 : mword 6) ('b"000"))))))) (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 5 : mword 6) ('b"000"))))))) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec (subrange_vec_dec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 5 : mword 6) ('b"000"))))))) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = svpn ->
    zero_extend' 64 (concat_vec (tlb_get_ppn 39 (pw_tlb_entry root_ppn (mword_of_int 0)) svpn) (subrange_vec_dec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 5 : mword 6) ('b"000"))))))) (Z.sub pagesize_bits 1) 0)) = (add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 5 : mword 6) ('b"000")))) ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4) (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4) (uint (add_vec_int ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 5 : mword 6) ('b"000"))))) (0 * 8))) (uint (to_bits 64 8)) = PMP_Match ->
    is_aligned_vaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 5 : mword 6) ('b"000")))))) 8 = true ->
    is_aligned_paddr (Physaddr (add_vec_int ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 5 : mword 6) ('b"000"))))) (0 * 8))) 8 = true ->
    (* slot 5: x7 at sp+48 *)
    neq_vec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 6 : mword 6) ('b"000"))))))) (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 6 : mword 6) ('b"000"))))))) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec (subrange_vec_dec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 6 : mword 6) ('b"000"))))))) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = svpn ->
    zero_extend' 64 (concat_vec (tlb_get_ppn 39 (pw_tlb_entry root_ppn (mword_of_int 0)) svpn) (subrange_vec_dec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 6 : mword 6) ('b"000"))))))) (Z.sub pagesize_bits 1) 0)) = (add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 6 : mword 6) ('b"000")))) ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4) (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4) (uint (add_vec_int ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 6 : mword 6) ('b"000"))))) (0 * 8))) (uint (to_bits 64 8)) = PMP_Match ->
    is_aligned_vaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 6 : mword 6) ('b"000")))))) 8 = true ->
    is_aligned_paddr (Physaddr (add_vec_int ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 6 : mword 6) ('b"000"))))) (0 * 8))) 8 = true ->
    (* slot 6: x10 at sp+72 *)
    neq_vec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 9 : mword 6) ('b"000"))))))) (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 9 : mword 6) ('b"000"))))))) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec (subrange_vec_dec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 9 : mword 6) ('b"000"))))))) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = svpn ->
    zero_extend' 64 (concat_vec (tlb_get_ppn 39 (pw_tlb_entry root_ppn (mword_of_int 0)) svpn) (subrange_vec_dec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 9 : mword 6) ('b"000"))))))) (Z.sub pagesize_bits 1) 0)) = (add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 9 : mword 6) ('b"000")))) ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4) (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4) (uint (add_vec_int ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 9 : mword 6) ('b"000"))))) (0 * 8))) (uint (to_bits 64 8)) = PMP_Match ->
    is_aligned_vaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 9 : mword 6) ('b"000")))))) 8 = true ->
    is_aligned_paddr (Physaddr (add_vec_int ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 9 : mword 6) ('b"000"))))) (0 * 8))) 8 = true ->
    (* slot 7: x11 at sp+80 *)
    neq_vec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 10 : mword 6) ('b"000"))))))) (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 10 : mword 6) ('b"000"))))))) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec (subrange_vec_dec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 10 : mword 6) ('b"000"))))))) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = svpn ->
    zero_extend' 64 (concat_vec (tlb_get_ppn 39 (pw_tlb_entry root_ppn (mword_of_int 0)) svpn) (subrange_vec_dec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 10 : mword 6) ('b"000"))))))) (Z.sub pagesize_bits 1) 0)) = (add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 10 : mword 6) ('b"000")))) ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4) (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4) (uint (add_vec_int ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 10 : mword 6) ('b"000"))))) (0 * 8))) (uint (to_bits 64 8)) = PMP_Match ->
    is_aligned_vaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 10 : mword 6) ('b"000")))))) 8 = true ->
    is_aligned_paddr (Physaddr (add_vec_int ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 10 : mword 6) ('b"000"))))) (0 * 8))) 8 = true ->
    (* slot 8: x12 at sp+88 *)
    neq_vec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 11 : mword 6) ('b"000"))))))) (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 11 : mword 6) ('b"000"))))))) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec (subrange_vec_dec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 11 : mword 6) ('b"000"))))))) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = svpn ->
    zero_extend' 64 (concat_vec (tlb_get_ppn 39 (pw_tlb_entry root_ppn (mword_of_int 0)) svpn) (subrange_vec_dec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 11 : mword 6) ('b"000"))))))) (Z.sub pagesize_bits 1) 0)) = (add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 11 : mword 6) ('b"000")))) ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4) (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4) (uint (add_vec_int ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 11 : mword 6) ('b"000"))))) (0 * 8))) (uint (to_bits 64 8)) = PMP_Match ->
    is_aligned_vaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 11 : mword 6) ('b"000")))))) 8 = true ->
    is_aligned_paddr (Physaddr (add_vec_int ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 11 : mword 6) ('b"000"))))) (0 * 8))) 8 = true ->
    (* slot 9: x13 at sp+96 *)
    neq_vec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 12 : mword 6) ('b"000"))))))) (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 12 : mword 6) ('b"000"))))))) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec (subrange_vec_dec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 12 : mword 6) ('b"000"))))))) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = svpn ->
    zero_extend' 64 (concat_vec (tlb_get_ppn 39 (pw_tlb_entry root_ppn (mword_of_int 0)) svpn) (subrange_vec_dec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 12 : mword 6) ('b"000"))))))) (Z.sub pagesize_bits 1) 0)) = (add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 12 : mword 6) ('b"000")))) ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4) (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4) (uint (add_vec_int ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 12 : mword 6) ('b"000"))))) (0 * 8))) (uint (to_bits 64 8)) = PMP_Match ->
    is_aligned_vaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 12 : mword 6) ('b"000")))))) 8 = true ->
    is_aligned_paddr (Physaddr (add_vec_int ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 12 : mword 6) ('b"000"))))) (0 * 8))) 8 = true ->
    (* slot 10: x14 at sp+104 *)
    neq_vec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 13 : mword 6) ('b"000"))))))) (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 13 : mword 6) ('b"000"))))))) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec (subrange_vec_dec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 13 : mword 6) ('b"000"))))))) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = svpn ->
    zero_extend' 64 (concat_vec (tlb_get_ppn 39 (pw_tlb_entry root_ppn (mword_of_int 0)) svpn) (subrange_vec_dec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 13 : mword 6) ('b"000"))))))) (Z.sub pagesize_bits 1) 0)) = (add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 13 : mword 6) ('b"000")))) ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4) (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4) (uint (add_vec_int ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 13 : mword 6) ('b"000"))))) (0 * 8))) (uint (to_bits 64 8)) = PMP_Match ->
    is_aligned_vaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 13 : mword 6) ('b"000")))))) 8 = true ->
    is_aligned_paddr (Physaddr (add_vec_int ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 13 : mword 6) ('b"000"))))) (0 * 8))) 8 = true ->
    (* slot 11: x15 at sp+112 *)
    neq_vec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 14 : mword 6) ('b"000"))))))) (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 14 : mword 6) ('b"000"))))))) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec (subrange_vec_dec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 14 : mword 6) ('b"000"))))))) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = svpn ->
    zero_extend' 64 (concat_vec (tlb_get_ppn 39 (pw_tlb_entry root_ppn (mword_of_int 0)) svpn) (subrange_vec_dec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 14 : mword 6) ('b"000"))))))) (Z.sub pagesize_bits 1) 0)) = (add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 14 : mword 6) ('b"000")))) ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4) (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4) (uint (add_vec_int ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 14 : mword 6) ('b"000"))))) (0 * 8))) (uint (to_bits 64 8)) = PMP_Match ->
    is_aligned_vaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 14 : mword 6) ('b"000")))))) 8 = true ->
    is_aligned_paddr (Physaddr (add_vec_int ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 14 : mword 6) ('b"000"))))) (0 * 8))) 8 = true ->
    (* slot 12: x16 at sp+120 *)
    neq_vec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 15 : mword 6) ('b"000"))))))) (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 15 : mword 6) ('b"000"))))))) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec (subrange_vec_dec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 15 : mword 6) ('b"000"))))))) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = svpn ->
    zero_extend' 64 (concat_vec (tlb_get_ppn 39 (pw_tlb_entry root_ppn (mword_of_int 0)) svpn) (subrange_vec_dec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 15 : mword 6) ('b"000"))))))) (Z.sub pagesize_bits 1) 0)) = (add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 15 : mword 6) ('b"000")))) ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4) (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4) (uint (add_vec_int ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 15 : mword 6) ('b"000"))))) (0 * 8))) (uint (to_bits 64 8)) = PMP_Match ->
    is_aligned_vaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 15 : mword 6) ('b"000")))))) 8 = true ->
    is_aligned_paddr (Physaddr (add_vec_int ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 15 : mword 6) ('b"000"))))) (0 * 8))) 8 = true ->
    (* slot 13: x17 at sp+128 *)
    neq_vec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 16 : mword 6) ('b"000"))))))) (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 16 : mword 6) ('b"000"))))))) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec (subrange_vec_dec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 16 : mword 6) ('b"000"))))))) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = svpn ->
    zero_extend' 64 (concat_vec (tlb_get_ppn 39 (pw_tlb_entry root_ppn (mword_of_int 0)) svpn) (subrange_vec_dec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 16 : mword 6) ('b"000"))))))) (Z.sub pagesize_bits 1) 0)) = (add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 16 : mword 6) ('b"000")))) ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4) (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4) (uint (add_vec_int ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 16 : mword 6) ('b"000"))))) (0 * 8))) (uint (to_bits 64 8)) = PMP_Match ->
    is_aligned_vaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 16 : mword 6) ('b"000")))))) 8 = true ->
    is_aligned_paddr (Physaddr (add_vec_int ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 16 : mword 6) ('b"000"))))) (0 * 8))) 8 = true ->
    (* slot 14: x28 at sp+216 *)
    neq_vec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 27 : mword 6) ('b"000"))))))) (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 27 : mword 6) ('b"000"))))))) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec (subrange_vec_dec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 27 : mword 6) ('b"000"))))))) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = svpn ->
    zero_extend' 64 (concat_vec (tlb_get_ppn 39 (pw_tlb_entry root_ppn (mword_of_int 0)) svpn) (subrange_vec_dec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 27 : mword 6) ('b"000"))))))) (Z.sub pagesize_bits 1) 0)) = (add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 27 : mword 6) ('b"000")))) ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4) (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4) (uint (add_vec_int ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 27 : mword 6) ('b"000"))))) (0 * 8))) (uint (to_bits 64 8)) = PMP_Match ->
    is_aligned_vaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 27 : mword 6) ('b"000")))))) 8 = true ->
    is_aligned_paddr (Physaddr (add_vec_int ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 27 : mword 6) ('b"000"))))) (0 * 8))) 8 = true ->
    (* slot 15: x29 at sp+224 *)
    neq_vec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 28 : mword 6) ('b"000"))))))) (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 28 : mword 6) ('b"000"))))))) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec (subrange_vec_dec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 28 : mword 6) ('b"000"))))))) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = svpn ->
    zero_extend' 64 (concat_vec (tlb_get_ppn 39 (pw_tlb_entry root_ppn (mword_of_int 0)) svpn) (subrange_vec_dec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 28 : mword 6) ('b"000"))))))) (Z.sub pagesize_bits 1) 0)) = (add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 28 : mword 6) ('b"000")))) ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4) (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4) (uint (add_vec_int ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 28 : mword 6) ('b"000"))))) (0 * 8))) (uint (to_bits 64 8)) = PMP_Match ->
    is_aligned_vaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 28 : mword 6) ('b"000")))))) 8 = true ->
    is_aligned_paddr (Physaddr (add_vec_int ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 28 : mword 6) ('b"000"))))) (0 * 8))) 8 = true ->
    (* slot 16: x30 at sp+232 *)
    neq_vec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 29 : mword 6) ('b"000"))))))) (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 29 : mword 6) ('b"000"))))))) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec (subrange_vec_dec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 29 : mword 6) ('b"000"))))))) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = svpn ->
    zero_extend' 64 (concat_vec (tlb_get_ppn 39 (pw_tlb_entry root_ppn (mword_of_int 0)) svpn) (subrange_vec_dec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 29 : mword 6) ('b"000"))))))) (Z.sub pagesize_bits 1) 0)) = (add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 29 : mword 6) ('b"000")))) ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4) (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4) (uint (add_vec_int ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 29 : mword 6) ('b"000"))))) (0 * 8))) (uint (to_bits 64 8)) = PMP_Match ->
    is_aligned_vaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 29 : mword 6) ('b"000")))))) 8 = true ->
    is_aligned_paddr (Physaddr (add_vec_int ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 29 : mword 6) ('b"000"))))) (0 * 8))) 8 = true ->
    (* slot 17: x31 at sp+240 *)
    neq_vec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 30 : mword 6) ('b"000"))))))) (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 30 : mword 6) ('b"000"))))))) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec (subrange_vec_dec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 30 : mword 6) ('b"000"))))))) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = svpn ->
    zero_extend' 64 (concat_vec (tlb_get_ppn 39 (pw_tlb_entry root_ppn (mword_of_int 0)) svpn) (subrange_vec_dec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 30 : mword 6) ('b"000"))))))) (Z.sub pagesize_bits 1) 0)) = (add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 30 : mword 6) ('b"000")))) ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4) (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4) (uint (add_vec_int ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 30 : mword 6) ('b"000"))))) (0 * 8))) (uint (to_bits 64 8)) = PMP_Match ->
    is_aligned_vaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 30 : mword 6) ('b"000")))))) 8 = true ->
    is_aligned_paddr (Physaddr (add_vec_int ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 30 : mword 6) ('b"000"))))) (0 * 8))) 8 = true ->
    hw_config -∗ minstret_inv -∗
    hart_state ↦ᵣ HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ Supervisor -∗
    satp ↦ᵣ satp0 -∗
    mstatus ↦ᵣ mstatus0 -∗
    mie ↦ᵣ mie_v -∗
    mideleg ↦ᵣ mdv0 -∗
    menvcfg ↦ᵣ menvcfg0 -∗
    pmpcfg_n ↦ᵣ pmpcfg0 -∗
    pmpaddr_n ↦ᵣ pmpaddr00 -∗
    tlb ↦ᵣ tlbvec -∗
    pc_is (mword_of_int KernelSyms.kernelvec : mword 64) -∗
    gpr_file m -∗
    kernel_text -∗
    ([∗ list] j ∈ seq 0 8, (pa_add (add_vec_int (((kv_sp1 m))) (0 * 8)) j) ↦ₘ nth_byte vold1 j) -∗
    ([∗ list] j ∈ seq 0 8, (pa_add (add_vec_int ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000"))))) (0 * 8)) j) ↦ₘ nth_byte vold2 j) -∗
    ([∗ list] j ∈ seq 0 8, (pa_add (add_vec_int ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 4 : mword 6) ('b"000"))))) (0 * 8)) j) ↦ₘ nth_byte vold3 j) -∗
    ([∗ list] j ∈ seq 0 8, (pa_add (add_vec_int ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 5 : mword 6) ('b"000"))))) (0 * 8)) j) ↦ₘ nth_byte vold4 j) -∗
    ([∗ list] j ∈ seq 0 8, (pa_add (add_vec_int ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 6 : mword 6) ('b"000"))))) (0 * 8)) j) ↦ₘ nth_byte vold5 j) -∗
    ([∗ list] j ∈ seq 0 8, (pa_add (add_vec_int ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 9 : mword 6) ('b"000"))))) (0 * 8)) j) ↦ₘ nth_byte vold6 j) -∗
    ([∗ list] j ∈ seq 0 8, (pa_add (add_vec_int ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 10 : mword 6) ('b"000"))))) (0 * 8)) j) ↦ₘ nth_byte vold7 j) -∗
    ([∗ list] j ∈ seq 0 8, (pa_add (add_vec_int ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 11 : mword 6) ('b"000"))))) (0 * 8)) j) ↦ₘ nth_byte vold8 j) -∗
    ([∗ list] j ∈ seq 0 8, (pa_add (add_vec_int ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 12 : mword 6) ('b"000"))))) (0 * 8)) j) ↦ₘ nth_byte vold9 j) -∗
    ([∗ list] j ∈ seq 0 8, (pa_add (add_vec_int ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 13 : mword 6) ('b"000"))))) (0 * 8)) j) ↦ₘ nth_byte vold10 j) -∗
    ([∗ list] j ∈ seq 0 8, (pa_add (add_vec_int ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 14 : mword 6) ('b"000"))))) (0 * 8)) j) ↦ₘ nth_byte vold11 j) -∗
    ([∗ list] j ∈ seq 0 8, (pa_add (add_vec_int ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 15 : mword 6) ('b"000"))))) (0 * 8)) j) ↦ₘ nth_byte vold12 j) -∗
    ([∗ list] j ∈ seq 0 8, (pa_add (add_vec_int ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 16 : mword 6) ('b"000"))))) (0 * 8)) j) ↦ₘ nth_byte vold13 j) -∗
    ([∗ list] j ∈ seq 0 8, (pa_add (add_vec_int ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 27 : mword 6) ('b"000"))))) (0 * 8)) j) ↦ₘ nth_byte vold14 j) -∗
    ([∗ list] j ∈ seq 0 8, (pa_add (add_vec_int ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 28 : mword 6) ('b"000"))))) (0 * 8)) j) ↦ₘ nth_byte vold15 j) -∗
    ([∗ list] j ∈ seq 0 8, (pa_add (add_vec_int ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 29 : mword 6) ('b"000"))))) (0 * 8)) j) ↦ₘ nth_byte vold16 j) -∗
    ([∗ list] j ∈ seq 0 8, (pa_add (add_vec_int ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 30 : mword 6) ('b"000"))))) (0 * 8)) j) ↦ₘ nth_byte vold17 j) -∗
    ( hart_state ↦ᵣ HART_ACTIVE tt -∗
      cur_privilege ↦ᵣ Supervisor -∗
      satp ↦ᵣ satp0 -∗
      mstatus ↦ᵣ mstatus0 -∗
      mie ↦ᵣ mie_v -∗
      mideleg ↦ᵣ mdv0 -∗
      menvcfg ↦ᵣ menvcfg0 -∗
      pmpcfg_n ↦ᵣ pmpcfg0 -∗
      pmpaddr_n ↦ᵣ pmpaddr00 -∗
      tlb ↦ᵣ tlbvec -∗
      pc_is (mword_of_int KernelSyms.kerneltrap : mword 64) -∗
      gpr_file (kv_m2 m) -∗
        ([∗ list] j ∈ seq 0 8, (pa_add (add_vec_int (((kv_sp1 m))) (0 * 8)) j) ↦ₘ nth_byte (m !!! Regidx (mword_of_int 1 : mword 5)) j) -∗
      ([∗ list] j ∈ seq 0 8, (pa_add (add_vec_int ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000"))))) (0 * 8)) j) ↦ₘ nth_byte (m !!! Regidx (mword_of_int 3 : mword 5)) j) -∗
      ([∗ list] j ∈ seq 0 8, (pa_add (add_vec_int ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 4 : mword 6) ('b"000"))))) (0 * 8)) j) ↦ₘ nth_byte (m !!! Regidx (mword_of_int 5 : mword 5)) j) -∗
      ([∗ list] j ∈ seq 0 8, (pa_add (add_vec_int ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 5 : mword 6) ('b"000"))))) (0 * 8)) j) ↦ₘ nth_byte (m !!! Regidx (mword_of_int 6 : mword 5)) j) -∗
      ([∗ list] j ∈ seq 0 8, (pa_add (add_vec_int ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 6 : mword 6) ('b"000"))))) (0 * 8)) j) ↦ₘ nth_byte (m !!! Regidx (mword_of_int 7 : mword 5)) j) -∗
      ([∗ list] j ∈ seq 0 8, (pa_add (add_vec_int ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 9 : mword 6) ('b"000"))))) (0 * 8)) j) ↦ₘ nth_byte (m !!! Regidx (mword_of_int 10 : mword 5)) j) -∗
      ([∗ list] j ∈ seq 0 8, (pa_add (add_vec_int ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 10 : mword 6) ('b"000"))))) (0 * 8)) j) ↦ₘ nth_byte (m !!! Regidx (mword_of_int 11 : mword 5)) j) -∗
      ([∗ list] j ∈ seq 0 8, (pa_add (add_vec_int ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 11 : mword 6) ('b"000"))))) (0 * 8)) j) ↦ₘ nth_byte (m !!! Regidx (mword_of_int 12 : mword 5)) j) -∗
      ([∗ list] j ∈ seq 0 8, (pa_add (add_vec_int ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 12 : mword 6) ('b"000"))))) (0 * 8)) j) ↦ₘ nth_byte (m !!! Regidx (mword_of_int 13 : mword 5)) j) -∗
      ([∗ list] j ∈ seq 0 8, (pa_add (add_vec_int ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 13 : mword 6) ('b"000"))))) (0 * 8)) j) ↦ₘ nth_byte (m !!! Regidx (mword_of_int 14 : mword 5)) j) -∗
      ([∗ list] j ∈ seq 0 8, (pa_add (add_vec_int ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 14 : mword 6) ('b"000"))))) (0 * 8)) j) ↦ₘ nth_byte (m !!! Regidx (mword_of_int 15 : mword 5)) j) -∗
      ([∗ list] j ∈ seq 0 8, (pa_add (add_vec_int ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 15 : mword 6) ('b"000"))))) (0 * 8)) j) ↦ₘ nth_byte (m !!! Regidx (mword_of_int 16 : mword 5)) j) -∗
      ([∗ list] j ∈ seq 0 8, (pa_add (add_vec_int ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 16 : mword 6) ('b"000"))))) (0 * 8)) j) ↦ₘ nth_byte (m !!! Regidx (mword_of_int 17 : mword 5)) j) -∗
      ([∗ list] j ∈ seq 0 8, (pa_add (add_vec_int ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 27 : mword 6) ('b"000"))))) (0 * 8)) j) ↦ₘ nth_byte (m !!! Regidx (mword_of_int 28 : mword 5)) j) -∗
      ([∗ list] j ∈ seq 0 8, (pa_add (add_vec_int ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 28 : mword 6) ('b"000"))))) (0 * 8)) j) ↦ₘ nth_byte (m !!! Regidx (mword_of_int 29 : mword 5)) j) -∗
      ([∗ list] j ∈ seq 0 8, (pa_add (add_vec_int ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 29 : mword 6) ('b"000"))))) (0 * 8)) j) ↦ₘ nth_byte (m !!! Regidx (mword_of_int 30 : mword 5)) j) -∗
      ([∗ list] j ∈ seq 0 8, (pa_add (add_vec_int ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 30 : mword 6) ('b"000"))))) (0 * 8)) j) ↦ₘ nth_byte (m !!! Regidx (mword_of_int 31 : mword 5)) j) -∗
      WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intros HN Hmode Hasid HSIE HMPRV HSXL Hmm HPBMTE HMXR Hpmm
      Hhit5 Hhith Hpmpf HW
      Hmask
      Hcanon1 Hvpn1 Hident1 Hrange1 Halv1 Halp1 Hcanon2 Hvpn2 Hident2 Hrange2 Halv2 Halp2 Hcanon3 Hvpn3 Hident3 Hrange3 Halv3 Halp3 Hcanon4 Hvpn4 Hident4 Hrange4 Halv4 Halp4 Hcanon5 Hvpn5 Hident5 Hrange5 Halv5 Halp5 Hcanon6 Hvpn6 Hident6 Hrange6 Halv6 Halp6 Hcanon7 Hvpn7 Hident7 Hrange7 Halv7 Halp7 Hcanon8 Hvpn8 Hident8 Hrange8 Halv8 Halp8 Hcanon9 Hvpn9 Hident9 Hrange9 Halv9 Halp9 Hcanon10 Hvpn10 Hident10 Hrange10 Halv10 Halp10 Hcanon11 Hvpn11 Hident11 Hrange11 Halv11 Halp11 Hcanon12 Hvpn12 Hident12 Hrange12 Halv12 Halp12 Hcanon13 Hvpn13 Hident13 Hrange13 Halv13 Halp13 Hcanon14 Hvpn14 Hident14 Hrange14 Halv14 Halp14 Hcanon15 Hvpn15 Hident15 Hrange15 Halv15 Halp15 Hcanon16 Hvpn16 Hident16 Hrange16 Halv16 Halp16 Hcanon17 Hvpn17 Hident17 Hrange17 Halv17 Halp17.
    iIntros "#Hhw #Hinv Hhs Hpriv Hsatp Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlb Hpc Hfile
             #Htext Hw1 Hw2 Hw3 Hw4 Hw5 Hw6 Hw7 Hw8 Hw9 Hw10 Hw11 Hw12 Hw13 Hw14 Hw15 Hw16 Hw17 Hcont".
    (* split: bundle(1/2) for the caddi16sp/jal WPs + retained halves *)
    iPoseProof (kv_cfg_split satp0 mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00
                  Hmode Hasid HSIE HMPRV HSXL Hmm HPBMTE
                  with "Hhw Hinv Hhs Hpriv Hsatp Hms Hmie Hmdl Hmenv Hpmpc Hpmpa")
      as "(Hsm & Hpmpc1 & Hpmpa1 & Hhs2 & Hpriv2 & Hsatp2 & Hms2 & Hmie2 & Hmdl2 & Hmenv2 & Hpmpc2 & Hpmpa2)".
    (* ---- #1: c.addi16sp sp,-256 @ 0x800053e0 (fetch page-walk, fills slot 5) ---- *)
    iPoseProof (kv_instr1 with "Htext") as "Hi1".
    assert (Hg1 : kv_fetch_geom (mword_of_int KernelSyms.kernelvec : mword 64)) by kv_geom.
    assert (Hpc1 : add_vec_int (mword_of_int KernelSyms.kernelvec : mword 64) 2 = (mword_of_int (KernelSyms.kernelvec + 0x2) : mword 64))
      by (vm_compute; reflexivity).
    iApply (wp_caddi16sp_gpr_s root_ppn E Φ (mword_of_int KernelSyms.kernelvec) kv_imm1 m
              satp0 pmpcfg0 pmpaddr00 tlbvec (1/2)%Qp
              HN Hhit5 Hg1 (Hpmpf KernelSyms.kernelvec eq_refl)
              with "Hsm Hpmpc1 Hpmpa1 Htlb Hpc Hfile Hi1").
    iEval (rewrite Hpc1).
    iIntros "Hsm Hpmpc1 Hpmpa1 Htlb Hpc Hfile".
    (* the sp-lookup / clobbered-lookup facts over kv_m1 *)
    assert (Hm1sp : kv_m1 m !!! Regidx csp_rs1 = kv_sp1 m)
      by (unfold kv_m1; rewrite lookup_total_insert; reflexivity).
    assert (Hmr1 : kv_m1 m !!! Regidx (mword_of_int 1 : mword 5) = m !!! Regidx (mword_of_int 1 : mword 5))
      by (unfold kv_m1; rewrite lookup_total_insert_ne; [reflexivity | kv_regne]).
    assert (Hmr2 : kv_m1 m !!! Regidx (mword_of_int 3 : mword 5) = m !!! Regidx (mword_of_int 3 : mword 5))
      by (unfold kv_m1; rewrite lookup_total_insert_ne; [reflexivity | kv_regne]).
    assert (Hmr3 : kv_m1 m !!! Regidx (mword_of_int 5 : mword 5) = m !!! Regidx (mword_of_int 5 : mword 5))
      by (unfold kv_m1; rewrite lookup_total_insert_ne; [reflexivity | kv_regne]).
    assert (Hmr4 : kv_m1 m !!! Regidx (mword_of_int 6 : mword 5) = m !!! Regidx (mword_of_int 6 : mword 5))
      by (unfold kv_m1; rewrite lookup_total_insert_ne; [reflexivity | kv_regne]).
    assert (Hmr5 : kv_m1 m !!! Regidx (mword_of_int 7 : mword 5) = m !!! Regidx (mword_of_int 7 : mword 5))
      by (unfold kv_m1; rewrite lookup_total_insert_ne; [reflexivity | kv_regne]).
    assert (Hmr6 : kv_m1 m !!! Regidx (mword_of_int 10 : mword 5) = m !!! Regidx (mword_of_int 10 : mword 5))
      by (unfold kv_m1; rewrite lookup_total_insert_ne; [reflexivity | kv_regne]).
    assert (Hmr7 : kv_m1 m !!! Regidx (mword_of_int 11 : mword 5) = m !!! Regidx (mword_of_int 11 : mword 5))
      by (unfold kv_m1; rewrite lookup_total_insert_ne; [reflexivity | kv_regne]).
    assert (Hmr8 : kv_m1 m !!! Regidx (mword_of_int 12 : mword 5) = m !!! Regidx (mword_of_int 12 : mword 5))
      by (unfold kv_m1; rewrite lookup_total_insert_ne; [reflexivity | kv_regne]).
    assert (Hmr9 : kv_m1 m !!! Regidx (mword_of_int 13 : mword 5) = m !!! Regidx (mword_of_int 13 : mword 5))
      by (unfold kv_m1; rewrite lookup_total_insert_ne; [reflexivity | kv_regne]).
    assert (Hmr10 : kv_m1 m !!! Regidx (mword_of_int 14 : mword 5) = m !!! Regidx (mword_of_int 14 : mword 5))
      by (unfold kv_m1; rewrite lookup_total_insert_ne; [reflexivity | kv_regne]).
    assert (Hmr11 : kv_m1 m !!! Regidx (mword_of_int 15 : mword 5) = m !!! Regidx (mword_of_int 15 : mword 5))
      by (unfold kv_m1; rewrite lookup_total_insert_ne; [reflexivity | kv_regne]).
    assert (Hmr12 : kv_m1 m !!! Regidx (mword_of_int 16 : mword 5) = m !!! Regidx (mword_of_int 16 : mword 5))
      by (unfold kv_m1; rewrite lookup_total_insert_ne; [reflexivity | kv_regne]).
    assert (Hmr13 : kv_m1 m !!! Regidx (mword_of_int 17 : mword 5) = m !!! Regidx (mword_of_int 17 : mword 5))
      by (unfold kv_m1; rewrite lookup_total_insert_ne; [reflexivity | kv_regne]).
    assert (Hmr14 : kv_m1 m !!! Regidx (mword_of_int 28 : mword 5) = m !!! Regidx (mword_of_int 28 : mword 5))
      by (unfold kv_m1; rewrite lookup_total_insert_ne; [reflexivity | kv_regne]).
    assert (Hmr15 : kv_m1 m !!! Regidx (mword_of_int 29 : mword 5) = m !!! Regidx (mword_of_int 29 : mword 5))
      by (unfold kv_m1; rewrite lookup_total_insert_ne; [reflexivity | kv_regne]).
    assert (Hmr16 : kv_m1 m !!! Regidx (mword_of_int 30 : mword 5) = m !!! Regidx (mword_of_int 30 : mword 5))
      by (unfold kv_m1; rewrite lookup_total_insert_ne; [reflexivity | kv_regne]).
    assert (Hmr17 : kv_m1 m !!! Regidx (mword_of_int 31 : mword 5) = m !!! Regidx (mword_of_int 31 : mword 5))
      by (unfold kv_m1; rewrite lookup_total_insert_ne; [reflexivity | kv_regne]).
    (* ---- #2: c.sdsp x1, 0(sp) @ 0x800053e2 -- the data WALK, fills slot tlb_hash svpn ---- *)
    iPoseProof (kv_i2 with "Htext") as "Hi2".
    assert (Hg2 : kv_fetch_geom (mword_of_int (KernelSyms.kernelvec + 0x2) : mword 64)) by kv_geom.
    assert (Hpc2 : add_vec_int (mword_of_int (KernelSyms.kernelvec + 0x2) : mword 64) 2 = (mword_of_int (KernelSyms.kernelvec + 0x4) : mword 64))
      by (vm_compute; reflexivity).
    assert (Heq0f : kv_sp1 m = add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 0 : mword 6) ('b"000"))))
      by (symmetry; apply add_vec_slot0_zero).
    iEval (rewrite Heq0f) in "Hw1".
    iEval (rewrite <- Hm1sp) in "Hw1".
    iApply (wp_csdsp_gpr_s root_ppn E Φ (mword_of_int (KernelSyms.kernelvec + 0x2)) (mword_of_int 0) (mword_of_int 1) svpn
              (kv_m1 m) vold1 satp0 mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 tlbvec
              HN Hmode Hasid HSIE HMPRV HSXL Hmm HMXR Hpmm Hhit5 Hg2 (Hpmpf (KernelSyms.kernelvec + 0x2) eq_refl)
              ltac:(rewrite Hm1sp add_vec_slot0_zero; exact Hcanon1) ltac:(rewrite Hm1sp add_vec_slot0_zero; exact Hvpn1)
              ltac:(rewrite Hm1sp add_vec_slot0_zero; exact Hident1) Hmask Hhith
              ltac:(rewrite Hm1sp add_vec_slot0_zero; exact Hrange1) HW
              ltac:(rewrite Hm1sp add_vec_slot0_zero; exact Halv1) ltac:(rewrite Hm1sp add_vec_slot0_zero; exact Halp1)
              with "Hhw Hinv Hhs2 Hpriv2 Hsatp2 Hms2 Hmie2 Hmdl2 Hmenv2 Hpmpc2 Hpmpa2 Htlb Hpc Hfile Hi2 Hw1").
    iEval (rewrite Hpc2).
    iIntros "Hhs2 Hpriv2 Hsatp2 Hms2 Hmie2 Hmdl2 Hmenv2 Hpmpc2 Hpmpa2 Htlb Hpc Hfile Hw1".
    iEval (rewrite Hm1sp add_vec_slot0_zero Hmr1) in "Hw1".
    (* ---- #3: c.sdsp x3, 16(sp) @ 0x800053e4 (TLB hits) ---- *)
    iPoseProof (kv_i3 with "Htext") as "Hi3".
    assert (Hg3 : kv_fetch_geom (mword_of_int (KernelSyms.kernelvec + 0x4) : mword 64)) by kv_geom.
    assert (Hpc3 : add_vec_int (mword_of_int (KernelSyms.kernelvec + 0x4) : mword 64) 2 = (mword_of_int (KernelSyms.kernelvec + 0x6) : mword 64))
      by (vm_compute; reflexivity).
    iEval (rewrite <- Hm1sp) in "Hw2".
    iApply (wp_csdsp_gpr_s root_ppn E Φ (mword_of_int (KernelSyms.kernelvec + 0x4)) (mword_of_int 2) (mword_of_int 3) svpn
              (kv_m1 m) vold2 satp0 mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 tlbvec
              HN Hmode Hasid HSIE HMPRV HSXL Hmm HMXR Hpmm Hhit5 Hg3 (Hpmpf (KernelSyms.kernelvec + 0x4) eq_refl)
              ltac:(rewrite Hm1sp; exact Hcanon2) ltac:(rewrite Hm1sp; exact Hvpn2)
              ltac:(rewrite Hm1sp; exact Hident2) Hmask Hhith
              ltac:(rewrite Hm1sp; exact Hrange2) HW
              ltac:(rewrite Hm1sp; exact Halv2) ltac:(rewrite Hm1sp; exact Halp2)
              with "Hhw Hinv Hhs2 Hpriv2 Hsatp2 Hms2 Hmie2 Hmdl2 Hmenv2 Hpmpc2 Hpmpa2 Htlb Hpc Hfile Hi3 Hw2").
    iEval (rewrite Hpc3).
    iIntros "Hhs2 Hpriv2 Hsatp2 Hms2 Hmie2 Hmdl2 Hmenv2 Hpmpc2 Hpmpa2 Htlb Hpc Hfile Hw2".
    iEval (rewrite Hm1sp Hmr2) in "Hw2".
    (* ---- #4: c.sdsp x5, 32(sp) @ 0x800053e6 (TLB hits) ---- *)
    iPoseProof (kv_i4 with "Htext") as "Hi4".
    assert (Hg4 : kv_fetch_geom (mword_of_int (KernelSyms.kernelvec + 0x6) : mword 64)) by kv_geom.
    assert (Hpc4 : add_vec_int (mword_of_int (KernelSyms.kernelvec + 0x6) : mword 64) 2 = (mword_of_int (KernelSyms.kernelvec + 0x8) : mword 64))
      by (vm_compute; reflexivity).
    iEval (rewrite <- Hm1sp) in "Hw3".
    iApply (wp_csdsp_gpr_s root_ppn E Φ (mword_of_int (KernelSyms.kernelvec + 0x6)) (mword_of_int 4) (mword_of_int 5) svpn
              (kv_m1 m) vold3 satp0 mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 tlbvec
              HN Hmode Hasid HSIE HMPRV HSXL Hmm HMXR Hpmm Hhit5 Hg4 (Hpmpf (KernelSyms.kernelvec + 0x6) eq_refl)
              ltac:(rewrite Hm1sp; exact Hcanon3) ltac:(rewrite Hm1sp; exact Hvpn3)
              ltac:(rewrite Hm1sp; exact Hident3) Hmask Hhith
              ltac:(rewrite Hm1sp; exact Hrange3) HW
              ltac:(rewrite Hm1sp; exact Halv3) ltac:(rewrite Hm1sp; exact Halp3)
              with "Hhw Hinv Hhs2 Hpriv2 Hsatp2 Hms2 Hmie2 Hmdl2 Hmenv2 Hpmpc2 Hpmpa2 Htlb Hpc Hfile Hi4 Hw3").
    iEval (rewrite Hpc4).
    iIntros "Hhs2 Hpriv2 Hsatp2 Hms2 Hmie2 Hmdl2 Hmenv2 Hpmpc2 Hpmpa2 Htlb Hpc Hfile Hw3".
    iEval (rewrite Hm1sp Hmr3) in "Hw3".
    (* ---- #5: c.sdsp x6, 40(sp) @ 0x800053e8 (TLB hits) ---- *)
    iPoseProof (kv_i5 with "Htext") as "Hi5".
    assert (Hg5 : kv_fetch_geom (mword_of_int (KernelSyms.kernelvec + 0x8) : mword 64)) by kv_geom.
    assert (Hpc5 : add_vec_int (mword_of_int (KernelSyms.kernelvec + 0x8) : mword 64) 2 = (mword_of_int (KernelSyms.kernelvec + 0xa) : mword 64))
      by (vm_compute; reflexivity).
    iEval (rewrite <- Hm1sp) in "Hw4".
    iApply (wp_csdsp_gpr_s root_ppn E Φ (mword_of_int (KernelSyms.kernelvec + 0x8)) (mword_of_int 5) (mword_of_int 6) svpn
              (kv_m1 m) vold4 satp0 mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 tlbvec
              HN Hmode Hasid HSIE HMPRV HSXL Hmm HMXR Hpmm Hhit5 Hg5 (Hpmpf (KernelSyms.kernelvec + 0x8) eq_refl)
              ltac:(rewrite Hm1sp; exact Hcanon4) ltac:(rewrite Hm1sp; exact Hvpn4)
              ltac:(rewrite Hm1sp; exact Hident4) Hmask Hhith
              ltac:(rewrite Hm1sp; exact Hrange4) HW
              ltac:(rewrite Hm1sp; exact Halv4) ltac:(rewrite Hm1sp; exact Halp4)
              with "Hhw Hinv Hhs2 Hpriv2 Hsatp2 Hms2 Hmie2 Hmdl2 Hmenv2 Hpmpc2 Hpmpa2 Htlb Hpc Hfile Hi5 Hw4").
    iEval (rewrite Hpc5).
    iIntros "Hhs2 Hpriv2 Hsatp2 Hms2 Hmie2 Hmdl2 Hmenv2 Hpmpc2 Hpmpa2 Htlb Hpc Hfile Hw4".
    iEval (rewrite Hm1sp Hmr4) in "Hw4".
    (* ---- #6: c.sdsp x7, 48(sp) @ 0x800053ea (TLB hits) ---- *)
    iPoseProof (kv_i6 with "Htext") as "Hi6".
    assert (Hg6 : kv_fetch_geom (mword_of_int (KernelSyms.kernelvec + 0xa) : mword 64)) by kv_geom.
    assert (Hpc6 : add_vec_int (mword_of_int (KernelSyms.kernelvec + 0xa) : mword 64) 2 = (mword_of_int (KernelSyms.kernelvec + 0xc) : mword 64))
      by (vm_compute; reflexivity).
    iEval (rewrite <- Hm1sp) in "Hw5".
    iApply (wp_csdsp_gpr_s root_ppn E Φ (mword_of_int (KernelSyms.kernelvec + 0xa)) (mword_of_int 6) (mword_of_int 7) svpn
              (kv_m1 m) vold5 satp0 mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 tlbvec
              HN Hmode Hasid HSIE HMPRV HSXL Hmm HMXR Hpmm Hhit5 Hg6 (Hpmpf (KernelSyms.kernelvec + 0xa) eq_refl)
              ltac:(rewrite Hm1sp; exact Hcanon5) ltac:(rewrite Hm1sp; exact Hvpn5)
              ltac:(rewrite Hm1sp; exact Hident5) Hmask Hhith
              ltac:(rewrite Hm1sp; exact Hrange5) HW
              ltac:(rewrite Hm1sp; exact Halv5) ltac:(rewrite Hm1sp; exact Halp5)
              with "Hhw Hinv Hhs2 Hpriv2 Hsatp2 Hms2 Hmie2 Hmdl2 Hmenv2 Hpmpc2 Hpmpa2 Htlb Hpc Hfile Hi6 Hw5").
    iEval (rewrite Hpc6).
    iIntros "Hhs2 Hpriv2 Hsatp2 Hms2 Hmie2 Hmdl2 Hmenv2 Hpmpc2 Hpmpa2 Htlb Hpc Hfile Hw5".
    iEval (rewrite Hm1sp Hmr5) in "Hw5".
    (* ---- #7: c.sdsp x10, 72(sp) @ 0x800053ec (TLB hits) ---- *)
    iPoseProof (kv_i7 with "Htext") as "Hi7".
    assert (Hg7 : kv_fetch_geom (mword_of_int (KernelSyms.kernelvec + 0xc) : mword 64)) by kv_geom.
    assert (Hpc7 : add_vec_int (mword_of_int (KernelSyms.kernelvec + 0xc) : mword 64) 2 = (mword_of_int (KernelSyms.kernelvec + 0xe) : mword 64))
      by (vm_compute; reflexivity).
    iEval (rewrite <- Hm1sp) in "Hw6".
    iApply (wp_csdsp_gpr_s root_ppn E Φ (mword_of_int (KernelSyms.kernelvec + 0xc)) (mword_of_int 9) (mword_of_int 10) svpn
              (kv_m1 m) vold6 satp0 mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 tlbvec
              HN Hmode Hasid HSIE HMPRV HSXL Hmm HMXR Hpmm Hhit5 Hg7 (Hpmpf (KernelSyms.kernelvec + 0xc) eq_refl)
              ltac:(rewrite Hm1sp; exact Hcanon6) ltac:(rewrite Hm1sp; exact Hvpn6)
              ltac:(rewrite Hm1sp; exact Hident6) Hmask Hhith
              ltac:(rewrite Hm1sp; exact Hrange6) HW
              ltac:(rewrite Hm1sp; exact Halv6) ltac:(rewrite Hm1sp; exact Halp6)
              with "Hhw Hinv Hhs2 Hpriv2 Hsatp2 Hms2 Hmie2 Hmdl2 Hmenv2 Hpmpc2 Hpmpa2 Htlb Hpc Hfile Hi7 Hw6").
    iEval (rewrite Hpc7).
    iIntros "Hhs2 Hpriv2 Hsatp2 Hms2 Hmie2 Hmdl2 Hmenv2 Hpmpc2 Hpmpa2 Htlb Hpc Hfile Hw6".
    iEval (rewrite Hm1sp Hmr6) in "Hw6".
    (* ---- #8: c.sdsp x11, 80(sp) @ 0x800053ee (TLB hits) ---- *)
    iPoseProof (kv_i8 with "Htext") as "Hi8".
    assert (Hg8 : kv_fetch_geom (mword_of_int (KernelSyms.kernelvec + 0xe) : mword 64)) by kv_geom.
    assert (Hpc8 : add_vec_int (mword_of_int (KernelSyms.kernelvec + 0xe) : mword 64) 2 = (mword_of_int (KernelSyms.kernelvec + 0x10) : mword 64))
      by (vm_compute; reflexivity).
    iEval (rewrite <- Hm1sp) in "Hw7".
    iApply (wp_csdsp_gpr_s root_ppn E Φ (mword_of_int (KernelSyms.kernelvec + 0xe)) (mword_of_int 10) (mword_of_int 11) svpn
              (kv_m1 m) vold7 satp0 mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 tlbvec
              HN Hmode Hasid HSIE HMPRV HSXL Hmm HMXR Hpmm Hhit5 Hg8 (Hpmpf (KernelSyms.kernelvec + 0xe) eq_refl)
              ltac:(rewrite Hm1sp; exact Hcanon7) ltac:(rewrite Hm1sp; exact Hvpn7)
              ltac:(rewrite Hm1sp; exact Hident7) Hmask Hhith
              ltac:(rewrite Hm1sp; exact Hrange7) HW
              ltac:(rewrite Hm1sp; exact Halv7) ltac:(rewrite Hm1sp; exact Halp7)
              with "Hhw Hinv Hhs2 Hpriv2 Hsatp2 Hms2 Hmie2 Hmdl2 Hmenv2 Hpmpc2 Hpmpa2 Htlb Hpc Hfile Hi8 Hw7").
    iEval (rewrite Hpc8).
    iIntros "Hhs2 Hpriv2 Hsatp2 Hms2 Hmie2 Hmdl2 Hmenv2 Hpmpc2 Hpmpa2 Htlb Hpc Hfile Hw7".
    iEval (rewrite Hm1sp Hmr7) in "Hw7".
    (* ---- #9: c.sdsp x12, 88(sp) @ 0x800053f0 (TLB hits) ---- *)
    iPoseProof (kv_i9 with "Htext") as "Hi9".
    assert (Hg9 : kv_fetch_geom (mword_of_int (KernelSyms.kernelvec + 0x10) : mword 64)) by kv_geom.
    assert (Hpc9 : add_vec_int (mword_of_int (KernelSyms.kernelvec + 0x10) : mword 64) 2 = (mword_of_int (KernelSyms.kernelvec + 0x12) : mword 64))
      by (vm_compute; reflexivity).
    iEval (rewrite <- Hm1sp) in "Hw8".
    iApply (wp_csdsp_gpr_s root_ppn E Φ (mword_of_int (KernelSyms.kernelvec + 0x10)) (mword_of_int 11) (mword_of_int 12) svpn
              (kv_m1 m) vold8 satp0 mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 tlbvec
              HN Hmode Hasid HSIE HMPRV HSXL Hmm HMXR Hpmm Hhit5 Hg9 (Hpmpf (KernelSyms.kernelvec + 0x10) eq_refl)
              ltac:(rewrite Hm1sp; exact Hcanon8) ltac:(rewrite Hm1sp; exact Hvpn8)
              ltac:(rewrite Hm1sp; exact Hident8) Hmask Hhith
              ltac:(rewrite Hm1sp; exact Hrange8) HW
              ltac:(rewrite Hm1sp; exact Halv8) ltac:(rewrite Hm1sp; exact Halp8)
              with "Hhw Hinv Hhs2 Hpriv2 Hsatp2 Hms2 Hmie2 Hmdl2 Hmenv2 Hpmpc2 Hpmpa2 Htlb Hpc Hfile Hi9 Hw8").
    iEval (rewrite Hpc9).
    iIntros "Hhs2 Hpriv2 Hsatp2 Hms2 Hmie2 Hmdl2 Hmenv2 Hpmpc2 Hpmpa2 Htlb Hpc Hfile Hw8".
    iEval (rewrite Hm1sp Hmr8) in "Hw8".
    (* ---- #10: c.sdsp x13, 96(sp) @ 0x800053f2 (TLB hits) ---- *)
    iPoseProof (kv_i10 with "Htext") as "Hi10".
    assert (Hg10 : kv_fetch_geom (mword_of_int (KernelSyms.kernelvec + 0x12) : mword 64)) by kv_geom.
    assert (Hpc10 : add_vec_int (mword_of_int (KernelSyms.kernelvec + 0x12) : mword 64) 2 = (mword_of_int (KernelSyms.kernelvec + 0x14) : mword 64))
      by (vm_compute; reflexivity).
    iEval (rewrite <- Hm1sp) in "Hw9".
    iApply (wp_csdsp_gpr_s root_ppn E Φ (mword_of_int (KernelSyms.kernelvec + 0x12)) (mword_of_int 12) (mword_of_int 13) svpn
              (kv_m1 m) vold9 satp0 mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 tlbvec
              HN Hmode Hasid HSIE HMPRV HSXL Hmm HMXR Hpmm Hhit5 Hg10 (Hpmpf (KernelSyms.kernelvec + 0x12) eq_refl)
              ltac:(rewrite Hm1sp; exact Hcanon9) ltac:(rewrite Hm1sp; exact Hvpn9)
              ltac:(rewrite Hm1sp; exact Hident9) Hmask Hhith
              ltac:(rewrite Hm1sp; exact Hrange9) HW
              ltac:(rewrite Hm1sp; exact Halv9) ltac:(rewrite Hm1sp; exact Halp9)
              with "Hhw Hinv Hhs2 Hpriv2 Hsatp2 Hms2 Hmie2 Hmdl2 Hmenv2 Hpmpc2 Hpmpa2 Htlb Hpc Hfile Hi10 Hw9").
    iEval (rewrite Hpc10).
    iIntros "Hhs2 Hpriv2 Hsatp2 Hms2 Hmie2 Hmdl2 Hmenv2 Hpmpc2 Hpmpa2 Htlb Hpc Hfile Hw9".
    iEval (rewrite Hm1sp Hmr9) in "Hw9".
    (* ---- #11: c.sdsp x14, 104(sp) @ 0x800053f4 (TLB hits) ---- *)
    iPoseProof (kv_i11 with "Htext") as "Hi11".
    assert (Hg11 : kv_fetch_geom (mword_of_int (KernelSyms.kernelvec + 0x14) : mword 64)) by kv_geom.
    assert (Hpc11 : add_vec_int (mword_of_int (KernelSyms.kernelvec + 0x14) : mword 64) 2 = (mword_of_int (KernelSyms.kernelvec + 0x16) : mword 64))
      by (vm_compute; reflexivity).
    iEval (rewrite <- Hm1sp) in "Hw10".
    iApply (wp_csdsp_gpr_s root_ppn E Φ (mword_of_int (KernelSyms.kernelvec + 0x14)) (mword_of_int 13) (mword_of_int 14) svpn
              (kv_m1 m) vold10 satp0 mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 tlbvec
              HN Hmode Hasid HSIE HMPRV HSXL Hmm HMXR Hpmm Hhit5 Hg11 (Hpmpf (KernelSyms.kernelvec + 0x14) eq_refl)
              ltac:(rewrite Hm1sp; exact Hcanon10) ltac:(rewrite Hm1sp; exact Hvpn10)
              ltac:(rewrite Hm1sp; exact Hident10) Hmask Hhith
              ltac:(rewrite Hm1sp; exact Hrange10) HW
              ltac:(rewrite Hm1sp; exact Halv10) ltac:(rewrite Hm1sp; exact Halp10)
              with "Hhw Hinv Hhs2 Hpriv2 Hsatp2 Hms2 Hmie2 Hmdl2 Hmenv2 Hpmpc2 Hpmpa2 Htlb Hpc Hfile Hi11 Hw10").
    iEval (rewrite Hpc11).
    iIntros "Hhs2 Hpriv2 Hsatp2 Hms2 Hmie2 Hmdl2 Hmenv2 Hpmpc2 Hpmpa2 Htlb Hpc Hfile Hw10".
    iEval (rewrite Hm1sp Hmr10) in "Hw10".
    (* ---- #12: c.sdsp x15, 112(sp) @ 0x800053f6 (TLB hits) ---- *)
    iPoseProof (kv_i12 with "Htext") as "Hi12".
    assert (Hg12 : kv_fetch_geom (mword_of_int (KernelSyms.kernelvec + 0x16) : mword 64)) by kv_geom.
    assert (Hpc12 : add_vec_int (mword_of_int (KernelSyms.kernelvec + 0x16) : mword 64) 2 = (mword_of_int (KernelSyms.kernelvec + 0x18) : mword 64))
      by (vm_compute; reflexivity).
    iEval (rewrite <- Hm1sp) in "Hw11".
    iApply (wp_csdsp_gpr_s root_ppn E Φ (mword_of_int (KernelSyms.kernelvec + 0x16)) (mword_of_int 14) (mword_of_int 15) svpn
              (kv_m1 m) vold11 satp0 mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 tlbvec
              HN Hmode Hasid HSIE HMPRV HSXL Hmm HMXR Hpmm Hhit5 Hg12 (Hpmpf (KernelSyms.kernelvec + 0x16) eq_refl)
              ltac:(rewrite Hm1sp; exact Hcanon11) ltac:(rewrite Hm1sp; exact Hvpn11)
              ltac:(rewrite Hm1sp; exact Hident11) Hmask Hhith
              ltac:(rewrite Hm1sp; exact Hrange11) HW
              ltac:(rewrite Hm1sp; exact Halv11) ltac:(rewrite Hm1sp; exact Halp11)
              with "Hhw Hinv Hhs2 Hpriv2 Hsatp2 Hms2 Hmie2 Hmdl2 Hmenv2 Hpmpc2 Hpmpa2 Htlb Hpc Hfile Hi12 Hw11").
    iEval (rewrite Hpc12).
    iIntros "Hhs2 Hpriv2 Hsatp2 Hms2 Hmie2 Hmdl2 Hmenv2 Hpmpc2 Hpmpa2 Htlb Hpc Hfile Hw11".
    iEval (rewrite Hm1sp Hmr11) in "Hw11".
    (* ---- #13: c.sdsp x16, 120(sp) @ 0x800053f8 (TLB hits) ---- *)
    iPoseProof (kv_i13 with "Htext") as "Hi13".
    assert (Hg13 : kv_fetch_geom (mword_of_int (KernelSyms.kernelvec + 0x18) : mword 64)) by kv_geom.
    assert (Hpc13 : add_vec_int (mword_of_int (KernelSyms.kernelvec + 0x18) : mword 64) 2 = (mword_of_int (KernelSyms.kernelvec + 0x1a) : mword 64))
      by (vm_compute; reflexivity).
    iEval (rewrite <- Hm1sp) in "Hw12".
    iApply (wp_csdsp_gpr_s root_ppn E Φ (mword_of_int (KernelSyms.kernelvec + 0x18)) (mword_of_int 15) (mword_of_int 16) svpn
              (kv_m1 m) vold12 satp0 mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 tlbvec
              HN Hmode Hasid HSIE HMPRV HSXL Hmm HMXR Hpmm Hhit5 Hg13 (Hpmpf (KernelSyms.kernelvec + 0x18) eq_refl)
              ltac:(rewrite Hm1sp; exact Hcanon12) ltac:(rewrite Hm1sp; exact Hvpn12)
              ltac:(rewrite Hm1sp; exact Hident12) Hmask Hhith
              ltac:(rewrite Hm1sp; exact Hrange12) HW
              ltac:(rewrite Hm1sp; exact Halv12) ltac:(rewrite Hm1sp; exact Halp12)
              with "Hhw Hinv Hhs2 Hpriv2 Hsatp2 Hms2 Hmie2 Hmdl2 Hmenv2 Hpmpc2 Hpmpa2 Htlb Hpc Hfile Hi13 Hw12").
    iEval (rewrite Hpc13).
    iIntros "Hhs2 Hpriv2 Hsatp2 Hms2 Hmie2 Hmdl2 Hmenv2 Hpmpc2 Hpmpa2 Htlb Hpc Hfile Hw12".
    iEval (rewrite Hm1sp Hmr12) in "Hw12".
    (* ---- #14: c.sdsp x17, 128(sp) @ 0x800053fa (TLB hits) ---- *)
    iPoseProof (kv_i14 with "Htext") as "Hi14".
    assert (Hg14 : kv_fetch_geom (mword_of_int (KernelSyms.kernelvec + 0x1a) : mword 64)) by kv_geom.
    assert (Hpc14 : add_vec_int (mword_of_int (KernelSyms.kernelvec + 0x1a) : mword 64) 2 = (mword_of_int (KernelSyms.kernelvec + 0x1c) : mword 64))
      by (vm_compute; reflexivity).
    iEval (rewrite <- Hm1sp) in "Hw13".
    iApply (wp_csdsp_gpr_s root_ppn E Φ (mword_of_int (KernelSyms.kernelvec + 0x1a)) (mword_of_int 16) (mword_of_int 17) svpn
              (kv_m1 m) vold13 satp0 mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 tlbvec
              HN Hmode Hasid HSIE HMPRV HSXL Hmm HMXR Hpmm Hhit5 Hg14 (Hpmpf (KernelSyms.kernelvec + 0x1a) eq_refl)
              ltac:(rewrite Hm1sp; exact Hcanon13) ltac:(rewrite Hm1sp; exact Hvpn13)
              ltac:(rewrite Hm1sp; exact Hident13) Hmask Hhith
              ltac:(rewrite Hm1sp; exact Hrange13) HW
              ltac:(rewrite Hm1sp; exact Halv13) ltac:(rewrite Hm1sp; exact Halp13)
              with "Hhw Hinv Hhs2 Hpriv2 Hsatp2 Hms2 Hmie2 Hmdl2 Hmenv2 Hpmpc2 Hpmpa2 Htlb Hpc Hfile Hi14 Hw13").
    iEval (rewrite Hpc14).
    iIntros "Hhs2 Hpriv2 Hsatp2 Hms2 Hmie2 Hmdl2 Hmenv2 Hpmpc2 Hpmpa2 Htlb Hpc Hfile Hw13".
    iEval (rewrite Hm1sp Hmr13) in "Hw13".
    (* ---- #15: c.sdsp x28, 216(sp) @ 0x800053fc (TLB hits) ---- *)
    iPoseProof (kv_i15 with "Htext") as "Hi15".
    assert (Hg15 : kv_fetch_geom (mword_of_int (KernelSyms.kernelvec + 0x1c) : mword 64)) by kv_geom.
    assert (Hpc15 : add_vec_int (mword_of_int (KernelSyms.kernelvec + 0x1c) : mword 64) 2 = (mword_of_int (KernelSyms.kernelvec + 0x1e) : mword 64))
      by (vm_compute; reflexivity).
    iEval (rewrite <- Hm1sp) in "Hw14".
    iApply (wp_csdsp_gpr_s root_ppn E Φ (mword_of_int (KernelSyms.kernelvec + 0x1c)) (mword_of_int 27) (mword_of_int 28) svpn
              (kv_m1 m) vold14 satp0 mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 tlbvec
              HN Hmode Hasid HSIE HMPRV HSXL Hmm HMXR Hpmm Hhit5 Hg15 (Hpmpf (KernelSyms.kernelvec + 0x1c) eq_refl)
              ltac:(rewrite Hm1sp; exact Hcanon14) ltac:(rewrite Hm1sp; exact Hvpn14)
              ltac:(rewrite Hm1sp; exact Hident14) Hmask Hhith
              ltac:(rewrite Hm1sp; exact Hrange14) HW
              ltac:(rewrite Hm1sp; exact Halv14) ltac:(rewrite Hm1sp; exact Halp14)
              with "Hhw Hinv Hhs2 Hpriv2 Hsatp2 Hms2 Hmie2 Hmdl2 Hmenv2 Hpmpc2 Hpmpa2 Htlb Hpc Hfile Hi15 Hw14").
    iEval (rewrite Hpc15).
    iIntros "Hhs2 Hpriv2 Hsatp2 Hms2 Hmie2 Hmdl2 Hmenv2 Hpmpc2 Hpmpa2 Htlb Hpc Hfile Hw14".
    iEval (rewrite Hm1sp Hmr14) in "Hw14".
    (* ---- #16: c.sdsp x29, 224(sp) @ 0x800053fe (TLB hits) ---- *)
    iPoseProof (kv_i16 with "Htext") as "Hi16".
    assert (Hg16 : kv_fetch_geom (mword_of_int (KernelSyms.kernelvec + 0x1e) : mword 64)) by kv_geom.
    assert (Hpc16 : add_vec_int (mword_of_int (KernelSyms.kernelvec + 0x1e) : mword 64) 2 = (mword_of_int (KernelSyms.kernelvec + 0x20) : mword 64))
      by (vm_compute; reflexivity).
    iEval (rewrite <- Hm1sp) in "Hw15".
    iApply (wp_csdsp_gpr_s root_ppn E Φ (mword_of_int (KernelSyms.kernelvec + 0x1e)) (mword_of_int 28) (mword_of_int 29) svpn
              (kv_m1 m) vold15 satp0 mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 tlbvec
              HN Hmode Hasid HSIE HMPRV HSXL Hmm HMXR Hpmm Hhit5 Hg16 (Hpmpf (KernelSyms.kernelvec + 0x1e) eq_refl)
              ltac:(rewrite Hm1sp; exact Hcanon15) ltac:(rewrite Hm1sp; exact Hvpn15)
              ltac:(rewrite Hm1sp; exact Hident15) Hmask Hhith
              ltac:(rewrite Hm1sp; exact Hrange15) HW
              ltac:(rewrite Hm1sp; exact Halv15) ltac:(rewrite Hm1sp; exact Halp15)
              with "Hhw Hinv Hhs2 Hpriv2 Hsatp2 Hms2 Hmie2 Hmdl2 Hmenv2 Hpmpc2 Hpmpa2 Htlb Hpc Hfile Hi16 Hw15").
    iEval (rewrite Hpc16).
    iIntros "Hhs2 Hpriv2 Hsatp2 Hms2 Hmie2 Hmdl2 Hmenv2 Hpmpc2 Hpmpa2 Htlb Hpc Hfile Hw15".
    iEval (rewrite Hm1sp Hmr15) in "Hw15".
    (* ---- #17: c.sdsp x30, 232(sp) @ 0x80005400 (TLB hits) ---- *)
    iPoseProof (kv_i17 with "Htext") as "Hi17".
    assert (Hg17 : kv_fetch_geom (mword_of_int (KernelSyms.kernelvec + 0x20) : mword 64)) by kv_geom.
    assert (Hpc17 : add_vec_int (mword_of_int (KernelSyms.kernelvec + 0x20) : mword 64) 2 = (mword_of_int (KernelSyms.kernelvec + 0x22) : mword 64))
      by (vm_compute; reflexivity).
    iEval (rewrite <- Hm1sp) in "Hw16".
    iApply (wp_csdsp_gpr_s root_ppn E Φ (mword_of_int (KernelSyms.kernelvec + 0x20)) (mword_of_int 29) (mword_of_int 30) svpn
              (kv_m1 m) vold16 satp0 mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 tlbvec
              HN Hmode Hasid HSIE HMPRV HSXL Hmm HMXR Hpmm Hhit5 Hg17 (Hpmpf (KernelSyms.kernelvec + 0x20) eq_refl)
              ltac:(rewrite Hm1sp; exact Hcanon16) ltac:(rewrite Hm1sp; exact Hvpn16)
              ltac:(rewrite Hm1sp; exact Hident16) Hmask Hhith
              ltac:(rewrite Hm1sp; exact Hrange16) HW
              ltac:(rewrite Hm1sp; exact Halv16) ltac:(rewrite Hm1sp; exact Halp16)
              with "Hhw Hinv Hhs2 Hpriv2 Hsatp2 Hms2 Hmie2 Hmdl2 Hmenv2 Hpmpc2 Hpmpa2 Htlb Hpc Hfile Hi17 Hw16").
    iEval (rewrite Hpc17).
    iIntros "Hhs2 Hpriv2 Hsatp2 Hms2 Hmie2 Hmdl2 Hmenv2 Hpmpc2 Hpmpa2 Htlb Hpc Hfile Hw16".
    iEval (rewrite Hm1sp Hmr16) in "Hw16".
    (* ---- #18: c.sdsp x31, 240(sp) @ 0x80005402 (TLB hits) ---- *)
    iPoseProof (kv_i18 with "Htext") as "Hi18".
    assert (Hg18 : kv_fetch_geom (mword_of_int (KernelSyms.kernelvec + 0x22) : mword 64)) by kv_geom.
    assert (Hpc18 : add_vec_int (mword_of_int (KernelSyms.kernelvec + 0x22) : mword 64) 2 = (mword_of_int (KernelSyms.kernelvec + 0x24) : mword 64))
      by (vm_compute; reflexivity).
    iEval (rewrite <- Hm1sp) in "Hw17".
    iApply (wp_csdsp_gpr_s root_ppn E Φ (mword_of_int (KernelSyms.kernelvec + 0x22)) (mword_of_int 30) (mword_of_int 31) svpn
              (kv_m1 m) vold17 satp0 mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 tlbvec
              HN Hmode Hasid HSIE HMPRV HSXL Hmm HMXR Hpmm Hhit5 Hg18 (Hpmpf (KernelSyms.kernelvec + 0x22) eq_refl)
              ltac:(rewrite Hm1sp; exact Hcanon17) ltac:(rewrite Hm1sp; exact Hvpn17)
              ltac:(rewrite Hm1sp; exact Hident17) Hmask Hhith
              ltac:(rewrite Hm1sp; exact Hrange17) HW
              ltac:(rewrite Hm1sp; exact Halv17) ltac:(rewrite Hm1sp; exact Halp17)
              with "Hhw Hinv Hhs2 Hpriv2 Hsatp2 Hms2 Hmie2 Hmdl2 Hmenv2 Hpmpc2 Hpmpa2 Htlb Hpc Hfile Hi18 Hw17").
    iEval (rewrite Hpc18).
    iIntros "Hhs2 Hpriv2 Hsatp2 Hms2 Hmie2 Hmdl2 Hmenv2 Hpmpc2 Hpmpa2 Htlb Hpc Hfile Hw17".
    iEval (rewrite Hm1sp Hmr17) in "Hw17".
    (* ---- #19: jal ra, kerneltrap @ 0x80005404 ---- *)
    iPoseProof (kv_i19 with "Htext") as "Hi19".
    assert (Hg19 : kv_fetch_geom (mword_of_int (KernelSyms.kernelvec + 0x24) : mword 64)) by kv_geom.
    assert (Hg19b : kv_fetch_geom (add_vec_int (mword_of_int (KernelSyms.kernelvec + 0x24) : mword 64) 2)) by kv_geom.
    assert (Hrd19 : uint (mword_of_int 1 : mword 5) <> 0) by (vm_compute; discriminate).
    assert (Hal19 : eq_vec (access_vec_dec (add_vec (mword_of_int (KernelSyms.kernelvec + 0x24) : mword 64)
                      (sign_extend' 64 (mword_of_int 0x1fd246 : mword 21))) 0) ('b"0") = true)
      by (vm_compute; reflexivity).
    iApply (wp_jal_gpr_s2 root_ppn E Φ (mword_of_int (KernelSyms.kernelvec + 0x24)) (mword_of_int 1) (mword_of_int 0x1fd246)
              (kv_m1 m) satp0 pmpcfg0 pmpaddr00 tlbvec (1/2)%Qp
              HN Hhit5 Hg19 Hg19b (Hpmpf (KernelSyms.kernelvec + 0x24) eq_refl) Hrd19 Hal19
              with "Hhw Hsm Hpmpc1 Hpmpa1 Htlb Hpc Hfile Hi19").
    iEval (rewrite kv_jal_tgt kv_ra_val).
    iIntros "Hsm Hpmpc1 Hpmpa1 Htlb Hpc Hfile".
    (* recombine to full raw cells for the caller *)
    iPoseProof (kv_cfg_recombine satp0 mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00
                  with "Hsm Hpmpc1 Hpmpa1 Hhs2 Hpriv2 Hsatp2 Hms2 Hmie2 Hmdl2 Hmenv2 Hpmpc2 Hpmpa2")
      as "(Hhs & Hpriv & Hsatp & Hms & Hmie & Hmdl & Hmenv & Hpmpc & Hpmpa)".
    iApply ("Hcont" with "Hhs Hpriv Hsatp Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlb Hpc Hfile Hw1 Hw2 Hw3 Hw4 Hw5 Hw6 Hw7 Hw8 Hw9 Hw10 Hw11 Hw12 Hw13 Hw14 Hw15 Hw16 Hw17").
  Qed.



  Lemma wp_kernelvec_hit (root_ppn : mword 44) (svpn : mword 27)
      (m : gmap regidx (mword 64))
      (satp0 mstatus0 mie_v mdv0 menvcfg0 sepc0 : mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (pmpaddr00 : type_of_register pmpaddr_n)
      (tlbvec : vec (option TLB_Entry) (2 ^ 6))
      (vold1 vold2 vold3 vold4 vold5 vold6 vold7 vold8 vold9 vold10 vold11 vold12
       vold13 vold14 vold15 vold16 vold17 : bv 64)
      E (Φ : mval -> iProp Σ) :
    ↑minstretN ⊆ E ->
    (* S-mode config facts (satp0 = the Sv39 kernel satp) *)
    _get_Satp64_Mode (Mk_Satp64 satp0) = ('b"1000" : mword 4) ->
    zero_extend' 16 (satp_to_asid (autocast (T := mword) satp0 : mword 64)) = (mword_of_int 0 : mword 16) ->
    eq_vec (_get_Mstatus_SIE mstatus0) ('b"1") = false ->
    eq_vec (_get_Mstatus_MPRV mstatus0) ('b"1") = false ->
    _get_Mstatus_SXL mstatus0 = 'b"10" ->
    and_vec mie_v (not_vec mdv0) = zeros' 64 ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    eq_vec (_get_Mstatus_MXR mstatus0) ('b"0") = true ->
    pmm_mode_backwards (_get_MEnvcfg_PMM menvcfg0) = PMM_Disabled ->
    (* TLB: HIT state at both slots (post-first-entry steady state) *)
    vec_access_dec tlbvec 5 = Some (pw_tlb_entry root_ppn (mword_of_int 0)) ->
    vec_access_dec tlbvec (tlb_hash (__id 39) svpn) = Some (pw_tlb_entry root_ppn (mword_of_int 0)) ->
    (* PMP: TOR entry 0 grants X on the whole kernelvec text + R/W on the frame *)
    (forall A : Z, kv_text_pc A = true -> pmp_tor0_sfetch_all pmpcfg0 pmpaddr00 (mword_of_int A)) ->
    eq_vec (_get_Pmpcfg_ent_W (vec_access_dec pmpcfg0 0)) ('b"1") = true ->
    eq_vec (_get_Pmpcfg_ent_R (vec_access_dec pmpcfg0 0)) ('b"1") = true ->
    (* stack-page geometry (symbolic sp; svpn = its Sv39 VPN) *)
    and_vec (sign_extend' (57 - 12) svpn) (not_vec (mword_of_int 0x3FFFF : mword 45)) = (mword_of_int 0x80000 : mword 45) ->
    (* SRET facts *)
    eq_vec (_get_Mstatus_TSR mstatus0) ('b"1") = false ->
    sret_newpriv mstatus0 = Supervisor ->
    _get_MEnvcfg_LPE menvcfg0 = ('b"0") ->
    (* slot 1: x1 at sp+0 *)
    neq_vec (bits_of_virtaddr (Virtaddr (((kv_sp1 m))))) (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr (((kv_sp1 m))))) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec (subrange_vec_dec (bits_of_virtaddr (Virtaddr (((kv_sp1 m))))) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = svpn ->
    zero_extend' 64 (concat_vec (tlb_get_ppn 39 (pw_tlb_entry root_ppn (mword_of_int 0)) svpn) (subrange_vec_dec (bits_of_virtaddr (Virtaddr (((kv_sp1 m))))) (Z.sub pagesize_bits 1) 0)) = ((kv_sp1 m)) ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4) (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4) (uint (add_vec_int (((kv_sp1 m))) (0 * 8))) (uint (to_bits 64 8)) = PMP_Match ->
    is_aligned_vaddr (Virtaddr (((kv_sp1 m)))) 8 = true ->
    is_aligned_paddr (Physaddr (add_vec_int (((kv_sp1 m))) (0 * 8))) 8 = true ->
    (* slot 2: x3 at sp+16 *)
    neq_vec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000"))))))) (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000"))))))) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec (subrange_vec_dec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000"))))))) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = svpn ->
    zero_extend' 64 (concat_vec (tlb_get_ppn 39 (pw_tlb_entry root_ppn (mword_of_int 0)) svpn) (subrange_vec_dec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000"))))))) (Z.sub pagesize_bits 1) 0)) = (add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000")))) ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4) (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4) (uint (add_vec_int ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000"))))) (0 * 8))) (uint (to_bits 64 8)) = PMP_Match ->
    is_aligned_vaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000")))))) 8 = true ->
    is_aligned_paddr (Physaddr (add_vec_int ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000"))))) (0 * 8))) 8 = true ->
    (* slot 3: x5 at sp+32 *)
    neq_vec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 4 : mword 6) ('b"000"))))))) (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 4 : mword 6) ('b"000"))))))) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec (subrange_vec_dec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 4 : mword 6) ('b"000"))))))) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = svpn ->
    zero_extend' 64 (concat_vec (tlb_get_ppn 39 (pw_tlb_entry root_ppn (mword_of_int 0)) svpn) (subrange_vec_dec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 4 : mword 6) ('b"000"))))))) (Z.sub pagesize_bits 1) 0)) = (add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 4 : mword 6) ('b"000")))) ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4) (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4) (uint (add_vec_int ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 4 : mword 6) ('b"000"))))) (0 * 8))) (uint (to_bits 64 8)) = PMP_Match ->
    is_aligned_vaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 4 : mword 6) ('b"000")))))) 8 = true ->
    is_aligned_paddr (Physaddr (add_vec_int ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 4 : mword 6) ('b"000"))))) (0 * 8))) 8 = true ->
    (* slot 4: x6 at sp+40 *)
    neq_vec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 5 : mword 6) ('b"000"))))))) (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 5 : mword 6) ('b"000"))))))) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec (subrange_vec_dec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 5 : mword 6) ('b"000"))))))) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = svpn ->
    zero_extend' 64 (concat_vec (tlb_get_ppn 39 (pw_tlb_entry root_ppn (mword_of_int 0)) svpn) (subrange_vec_dec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 5 : mword 6) ('b"000"))))))) (Z.sub pagesize_bits 1) 0)) = (add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 5 : mword 6) ('b"000")))) ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4) (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4) (uint (add_vec_int ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 5 : mword 6) ('b"000"))))) (0 * 8))) (uint (to_bits 64 8)) = PMP_Match ->
    is_aligned_vaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 5 : mword 6) ('b"000")))))) 8 = true ->
    is_aligned_paddr (Physaddr (add_vec_int ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 5 : mword 6) ('b"000"))))) (0 * 8))) 8 = true ->
    (* slot 5: x7 at sp+48 *)
    neq_vec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 6 : mword 6) ('b"000"))))))) (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 6 : mword 6) ('b"000"))))))) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec (subrange_vec_dec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 6 : mword 6) ('b"000"))))))) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = svpn ->
    zero_extend' 64 (concat_vec (tlb_get_ppn 39 (pw_tlb_entry root_ppn (mword_of_int 0)) svpn) (subrange_vec_dec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 6 : mword 6) ('b"000"))))))) (Z.sub pagesize_bits 1) 0)) = (add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 6 : mword 6) ('b"000")))) ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4) (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4) (uint (add_vec_int ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 6 : mword 6) ('b"000"))))) (0 * 8))) (uint (to_bits 64 8)) = PMP_Match ->
    is_aligned_vaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 6 : mword 6) ('b"000")))))) 8 = true ->
    is_aligned_paddr (Physaddr (add_vec_int ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 6 : mword 6) ('b"000"))))) (0 * 8))) 8 = true ->
    (* slot 6: x10 at sp+72 *)
    neq_vec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 9 : mword 6) ('b"000"))))))) (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 9 : mword 6) ('b"000"))))))) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec (subrange_vec_dec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 9 : mword 6) ('b"000"))))))) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = svpn ->
    zero_extend' 64 (concat_vec (tlb_get_ppn 39 (pw_tlb_entry root_ppn (mword_of_int 0)) svpn) (subrange_vec_dec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 9 : mword 6) ('b"000"))))))) (Z.sub pagesize_bits 1) 0)) = (add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 9 : mword 6) ('b"000")))) ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4) (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4) (uint (add_vec_int ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 9 : mword 6) ('b"000"))))) (0 * 8))) (uint (to_bits 64 8)) = PMP_Match ->
    is_aligned_vaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 9 : mword 6) ('b"000")))))) 8 = true ->
    is_aligned_paddr (Physaddr (add_vec_int ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 9 : mword 6) ('b"000"))))) (0 * 8))) 8 = true ->
    (* slot 7: x11 at sp+80 *)
    neq_vec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 10 : mword 6) ('b"000"))))))) (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 10 : mword 6) ('b"000"))))))) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec (subrange_vec_dec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 10 : mword 6) ('b"000"))))))) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = svpn ->
    zero_extend' 64 (concat_vec (tlb_get_ppn 39 (pw_tlb_entry root_ppn (mword_of_int 0)) svpn) (subrange_vec_dec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 10 : mword 6) ('b"000"))))))) (Z.sub pagesize_bits 1) 0)) = (add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 10 : mword 6) ('b"000")))) ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4) (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4) (uint (add_vec_int ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 10 : mword 6) ('b"000"))))) (0 * 8))) (uint (to_bits 64 8)) = PMP_Match ->
    is_aligned_vaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 10 : mword 6) ('b"000")))))) 8 = true ->
    is_aligned_paddr (Physaddr (add_vec_int ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 10 : mword 6) ('b"000"))))) (0 * 8))) 8 = true ->
    (* slot 8: x12 at sp+88 *)
    neq_vec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 11 : mword 6) ('b"000"))))))) (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 11 : mword 6) ('b"000"))))))) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec (subrange_vec_dec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 11 : mword 6) ('b"000"))))))) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = svpn ->
    zero_extend' 64 (concat_vec (tlb_get_ppn 39 (pw_tlb_entry root_ppn (mword_of_int 0)) svpn) (subrange_vec_dec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 11 : mword 6) ('b"000"))))))) (Z.sub pagesize_bits 1) 0)) = (add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 11 : mword 6) ('b"000")))) ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4) (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4) (uint (add_vec_int ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 11 : mword 6) ('b"000"))))) (0 * 8))) (uint (to_bits 64 8)) = PMP_Match ->
    is_aligned_vaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 11 : mword 6) ('b"000")))))) 8 = true ->
    is_aligned_paddr (Physaddr (add_vec_int ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 11 : mword 6) ('b"000"))))) (0 * 8))) 8 = true ->
    (* slot 9: x13 at sp+96 *)
    neq_vec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 12 : mword 6) ('b"000"))))))) (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 12 : mword 6) ('b"000"))))))) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec (subrange_vec_dec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 12 : mword 6) ('b"000"))))))) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = svpn ->
    zero_extend' 64 (concat_vec (tlb_get_ppn 39 (pw_tlb_entry root_ppn (mword_of_int 0)) svpn) (subrange_vec_dec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 12 : mword 6) ('b"000"))))))) (Z.sub pagesize_bits 1) 0)) = (add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 12 : mword 6) ('b"000")))) ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4) (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4) (uint (add_vec_int ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 12 : mword 6) ('b"000"))))) (0 * 8))) (uint (to_bits 64 8)) = PMP_Match ->
    is_aligned_vaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 12 : mword 6) ('b"000")))))) 8 = true ->
    is_aligned_paddr (Physaddr (add_vec_int ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 12 : mword 6) ('b"000"))))) (0 * 8))) 8 = true ->
    (* slot 10: x14 at sp+104 *)
    neq_vec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 13 : mword 6) ('b"000"))))))) (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 13 : mword 6) ('b"000"))))))) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec (subrange_vec_dec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 13 : mword 6) ('b"000"))))))) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = svpn ->
    zero_extend' 64 (concat_vec (tlb_get_ppn 39 (pw_tlb_entry root_ppn (mword_of_int 0)) svpn) (subrange_vec_dec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 13 : mword 6) ('b"000"))))))) (Z.sub pagesize_bits 1) 0)) = (add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 13 : mword 6) ('b"000")))) ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4) (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4) (uint (add_vec_int ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 13 : mword 6) ('b"000"))))) (0 * 8))) (uint (to_bits 64 8)) = PMP_Match ->
    is_aligned_vaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 13 : mword 6) ('b"000")))))) 8 = true ->
    is_aligned_paddr (Physaddr (add_vec_int ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 13 : mword 6) ('b"000"))))) (0 * 8))) 8 = true ->
    (* slot 11: x15 at sp+112 *)
    neq_vec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 14 : mword 6) ('b"000"))))))) (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 14 : mword 6) ('b"000"))))))) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec (subrange_vec_dec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 14 : mword 6) ('b"000"))))))) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = svpn ->
    zero_extend' 64 (concat_vec (tlb_get_ppn 39 (pw_tlb_entry root_ppn (mword_of_int 0)) svpn) (subrange_vec_dec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 14 : mword 6) ('b"000"))))))) (Z.sub pagesize_bits 1) 0)) = (add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 14 : mword 6) ('b"000")))) ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4) (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4) (uint (add_vec_int ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 14 : mword 6) ('b"000"))))) (0 * 8))) (uint (to_bits 64 8)) = PMP_Match ->
    is_aligned_vaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 14 : mword 6) ('b"000")))))) 8 = true ->
    is_aligned_paddr (Physaddr (add_vec_int ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 14 : mword 6) ('b"000"))))) (0 * 8))) 8 = true ->
    (* slot 12: x16 at sp+120 *)
    neq_vec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 15 : mword 6) ('b"000"))))))) (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 15 : mword 6) ('b"000"))))))) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec (subrange_vec_dec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 15 : mword 6) ('b"000"))))))) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = svpn ->
    zero_extend' 64 (concat_vec (tlb_get_ppn 39 (pw_tlb_entry root_ppn (mword_of_int 0)) svpn) (subrange_vec_dec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 15 : mword 6) ('b"000"))))))) (Z.sub pagesize_bits 1) 0)) = (add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 15 : mword 6) ('b"000")))) ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4) (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4) (uint (add_vec_int ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 15 : mword 6) ('b"000"))))) (0 * 8))) (uint (to_bits 64 8)) = PMP_Match ->
    is_aligned_vaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 15 : mword 6) ('b"000")))))) 8 = true ->
    is_aligned_paddr (Physaddr (add_vec_int ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 15 : mword 6) ('b"000"))))) (0 * 8))) 8 = true ->
    (* slot 13: x17 at sp+128 *)
    neq_vec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 16 : mword 6) ('b"000"))))))) (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 16 : mword 6) ('b"000"))))))) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec (subrange_vec_dec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 16 : mword 6) ('b"000"))))))) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = svpn ->
    zero_extend' 64 (concat_vec (tlb_get_ppn 39 (pw_tlb_entry root_ppn (mword_of_int 0)) svpn) (subrange_vec_dec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 16 : mword 6) ('b"000"))))))) (Z.sub pagesize_bits 1) 0)) = (add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 16 : mword 6) ('b"000")))) ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4) (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4) (uint (add_vec_int ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 16 : mword 6) ('b"000"))))) (0 * 8))) (uint (to_bits 64 8)) = PMP_Match ->
    is_aligned_vaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 16 : mword 6) ('b"000")))))) 8 = true ->
    is_aligned_paddr (Physaddr (add_vec_int ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 16 : mword 6) ('b"000"))))) (0 * 8))) 8 = true ->
    (* slot 14: x28 at sp+216 *)
    neq_vec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 27 : mword 6) ('b"000"))))))) (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 27 : mword 6) ('b"000"))))))) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec (subrange_vec_dec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 27 : mword 6) ('b"000"))))))) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = svpn ->
    zero_extend' 64 (concat_vec (tlb_get_ppn 39 (pw_tlb_entry root_ppn (mword_of_int 0)) svpn) (subrange_vec_dec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 27 : mword 6) ('b"000"))))))) (Z.sub pagesize_bits 1) 0)) = (add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 27 : mword 6) ('b"000")))) ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4) (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4) (uint (add_vec_int ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 27 : mword 6) ('b"000"))))) (0 * 8))) (uint (to_bits 64 8)) = PMP_Match ->
    is_aligned_vaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 27 : mword 6) ('b"000")))))) 8 = true ->
    is_aligned_paddr (Physaddr (add_vec_int ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 27 : mword 6) ('b"000"))))) (0 * 8))) 8 = true ->
    (* slot 15: x29 at sp+224 *)
    neq_vec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 28 : mword 6) ('b"000"))))))) (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 28 : mword 6) ('b"000"))))))) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec (subrange_vec_dec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 28 : mword 6) ('b"000"))))))) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = svpn ->
    zero_extend' 64 (concat_vec (tlb_get_ppn 39 (pw_tlb_entry root_ppn (mword_of_int 0)) svpn) (subrange_vec_dec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 28 : mword 6) ('b"000"))))))) (Z.sub pagesize_bits 1) 0)) = (add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 28 : mword 6) ('b"000")))) ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4) (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4) (uint (add_vec_int ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 28 : mword 6) ('b"000"))))) (0 * 8))) (uint (to_bits 64 8)) = PMP_Match ->
    is_aligned_vaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 28 : mword 6) ('b"000")))))) 8 = true ->
    is_aligned_paddr (Physaddr (add_vec_int ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 28 : mword 6) ('b"000"))))) (0 * 8))) 8 = true ->
    (* slot 16: x30 at sp+232 *)
    neq_vec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 29 : mword 6) ('b"000"))))))) (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 29 : mword 6) ('b"000"))))))) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec (subrange_vec_dec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 29 : mword 6) ('b"000"))))))) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = svpn ->
    zero_extend' 64 (concat_vec (tlb_get_ppn 39 (pw_tlb_entry root_ppn (mword_of_int 0)) svpn) (subrange_vec_dec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 29 : mword 6) ('b"000"))))))) (Z.sub pagesize_bits 1) 0)) = (add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 29 : mword 6) ('b"000")))) ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4) (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4) (uint (add_vec_int ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 29 : mword 6) ('b"000"))))) (0 * 8))) (uint (to_bits 64 8)) = PMP_Match ->
    is_aligned_vaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 29 : mword 6) ('b"000")))))) 8 = true ->
    is_aligned_paddr (Physaddr (add_vec_int ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 29 : mword 6) ('b"000"))))) (0 * 8))) 8 = true ->
    (* slot 17: x31 at sp+240 *)
    neq_vec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 30 : mword 6) ('b"000"))))))) (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 30 : mword 6) ('b"000"))))))) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec (subrange_vec_dec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 30 : mword 6) ('b"000"))))))) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = svpn ->
    zero_extend' 64 (concat_vec (tlb_get_ppn 39 (pw_tlb_entry root_ppn (mword_of_int 0)) svpn) (subrange_vec_dec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 30 : mword 6) ('b"000"))))))) (Z.sub pagesize_bits 1) 0)) = (add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 30 : mword 6) ('b"000")))) ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4) (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4) (uint (add_vec_int ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 30 : mword 6) ('b"000"))))) (0 * 8))) (uint (to_bits 64 8)) = PMP_Match ->
    is_aligned_vaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 30 : mword 6) ('b"000")))))) 8 = true ->
    is_aligned_paddr (Physaddr (add_vec_int ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 30 : mword 6) ('b"000"))))) (0 * 8))) 8 = true ->
    hw_config -∗ minstret_inv -∗
    hart_state ↦ᵣ HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ Supervisor -∗
    satp ↦ᵣ satp0 -∗
    mstatus ↦ᵣ mstatus0 -∗
    mie ↦ᵣ mie_v -∗
    mideleg ↦ᵣ mdv0 -∗
    menvcfg ↦ᵣ menvcfg0 -∗
    pmpcfg_n ↦ᵣ pmpcfg0 -∗
    pmpaddr_n ↦ᵣ pmpaddr00 -∗
    tlb ↦ᵣ tlbvec -∗
    sepc ↦ᵣ sepc0 -∗
    pc_is (mword_of_int KernelSyms.kernelvec : mword 64) -∗
    gpr_file m -∗
    kernel_text -∗
    ([∗ list] j ∈ seq 0 8, (pa_add (add_vec_int (((kv_sp1 m))) (0 * 8)) j) ↦ₘ nth_byte vold1 j) -∗
    ([∗ list] j ∈ seq 0 8, (pa_add (add_vec_int ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000"))))) (0 * 8)) j) ↦ₘ nth_byte vold2 j) -∗
    ([∗ list] j ∈ seq 0 8, (pa_add (add_vec_int ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 4 : mword 6) ('b"000"))))) (0 * 8)) j) ↦ₘ nth_byte vold3 j) -∗
    ([∗ list] j ∈ seq 0 8, (pa_add (add_vec_int ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 5 : mword 6) ('b"000"))))) (0 * 8)) j) ↦ₘ nth_byte vold4 j) -∗
    ([∗ list] j ∈ seq 0 8, (pa_add (add_vec_int ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 6 : mword 6) ('b"000"))))) (0 * 8)) j) ↦ₘ nth_byte vold5 j) -∗
    ([∗ list] j ∈ seq 0 8, (pa_add (add_vec_int ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 9 : mword 6) ('b"000"))))) (0 * 8)) j) ↦ₘ nth_byte vold6 j) -∗
    ([∗ list] j ∈ seq 0 8, (pa_add (add_vec_int ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 10 : mword 6) ('b"000"))))) (0 * 8)) j) ↦ₘ nth_byte vold7 j) -∗
    ([∗ list] j ∈ seq 0 8, (pa_add (add_vec_int ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 11 : mword 6) ('b"000"))))) (0 * 8)) j) ↦ₘ nth_byte vold8 j) -∗
    ([∗ list] j ∈ seq 0 8, (pa_add (add_vec_int ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 12 : mword 6) ('b"000"))))) (0 * 8)) j) ↦ₘ nth_byte vold9 j) -∗
    ([∗ list] j ∈ seq 0 8, (pa_add (add_vec_int ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 13 : mword 6) ('b"000"))))) (0 * 8)) j) ↦ₘ nth_byte vold10 j) -∗
    ([∗ list] j ∈ seq 0 8, (pa_add (add_vec_int ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 14 : mword 6) ('b"000"))))) (0 * 8)) j) ↦ₘ nth_byte vold11 j) -∗
    ([∗ list] j ∈ seq 0 8, (pa_add (add_vec_int ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 15 : mword 6) ('b"000"))))) (0 * 8)) j) ↦ₘ nth_byte vold12 j) -∗
    ([∗ list] j ∈ seq 0 8, (pa_add (add_vec_int ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 16 : mword 6) ('b"000"))))) (0 * 8)) j) ↦ₘ nth_byte vold13 j) -∗
    ([∗ list] j ∈ seq 0 8, (pa_add (add_vec_int ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 27 : mword 6) ('b"000"))))) (0 * 8)) j) ↦ₘ nth_byte vold14 j) -∗
    ([∗ list] j ∈ seq 0 8, (pa_add (add_vec_int ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 28 : mword 6) ('b"000"))))) (0 * 8)) j) ↦ₘ nth_byte vold15 j) -∗
    ([∗ list] j ∈ seq 0 8, (pa_add (add_vec_int ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 29 : mword 6) ('b"000"))))) (0 * 8)) j) ↦ₘ nth_byte vold16 j) -∗
    ([∗ list] j ∈ seq 0 8, (pa_add (add_vec_int ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 30 : mword 6) ('b"000"))))) (0 * 8)) j) ↦ₘ nth_byte vold17 j) -∗
    ( hart_state ↦ᵣ HART_ACTIVE tt -∗
      cur_privilege ↦ᵣ Supervisor -∗
      satp ↦ᵣ satp0 -∗
      mstatus ↦ᵣ sret_ms5 mstatus0 -∗
      mie ↦ᵣ mie_v -∗
      mideleg ↦ᵣ mdv0 -∗
      menvcfg ↦ᵣ menvcfg0 -∗
      pmpcfg_n ↦ᵣ pmpcfg0 -∗
      pmpaddr_n ↦ᵣ pmpaddr00 -∗
      tlb ↦ᵣ tlbvec -∗
      sepc ↦ᵣ sepc0 -∗
      pc_is (sret_tgt sepc0) -∗
      gpr_file m -∗
        ([∗ list] j ∈ seq 0 8, (pa_add (add_vec_int (((kv_sp1 m))) (0 * 8)) j) ↦ₘ nth_byte (m !!! Regidx (mword_of_int 1 : mword 5)) j) -∗
      ([∗ list] j ∈ seq 0 8, (pa_add (add_vec_int ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000"))))) (0 * 8)) j) ↦ₘ nth_byte (m !!! Regidx (mword_of_int 3 : mword 5)) j) -∗
      ([∗ list] j ∈ seq 0 8, (pa_add (add_vec_int ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 4 : mword 6) ('b"000"))))) (0 * 8)) j) ↦ₘ nth_byte (m !!! Regidx (mword_of_int 5 : mword 5)) j) -∗
      ([∗ list] j ∈ seq 0 8, (pa_add (add_vec_int ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 5 : mword 6) ('b"000"))))) (0 * 8)) j) ↦ₘ nth_byte (m !!! Regidx (mword_of_int 6 : mword 5)) j) -∗
      ([∗ list] j ∈ seq 0 8, (pa_add (add_vec_int ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 6 : mword 6) ('b"000"))))) (0 * 8)) j) ↦ₘ nth_byte (m !!! Regidx (mword_of_int 7 : mword 5)) j) -∗
      ([∗ list] j ∈ seq 0 8, (pa_add (add_vec_int ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 9 : mword 6) ('b"000"))))) (0 * 8)) j) ↦ₘ nth_byte (m !!! Regidx (mword_of_int 10 : mword 5)) j) -∗
      ([∗ list] j ∈ seq 0 8, (pa_add (add_vec_int ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 10 : mword 6) ('b"000"))))) (0 * 8)) j) ↦ₘ nth_byte (m !!! Regidx (mword_of_int 11 : mword 5)) j) -∗
      ([∗ list] j ∈ seq 0 8, (pa_add (add_vec_int ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 11 : mword 6) ('b"000"))))) (0 * 8)) j) ↦ₘ nth_byte (m !!! Regidx (mword_of_int 12 : mword 5)) j) -∗
      ([∗ list] j ∈ seq 0 8, (pa_add (add_vec_int ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 12 : mword 6) ('b"000"))))) (0 * 8)) j) ↦ₘ nth_byte (m !!! Regidx (mword_of_int 13 : mword 5)) j) -∗
      ([∗ list] j ∈ seq 0 8, (pa_add (add_vec_int ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 13 : mword 6) ('b"000"))))) (0 * 8)) j) ↦ₘ nth_byte (m !!! Regidx (mword_of_int 14 : mword 5)) j) -∗
      ([∗ list] j ∈ seq 0 8, (pa_add (add_vec_int ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 14 : mword 6) ('b"000"))))) (0 * 8)) j) ↦ₘ nth_byte (m !!! Regidx (mword_of_int 15 : mword 5)) j) -∗
      ([∗ list] j ∈ seq 0 8, (pa_add (add_vec_int ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 15 : mword 6) ('b"000"))))) (0 * 8)) j) ↦ₘ nth_byte (m !!! Regidx (mword_of_int 16 : mword 5)) j) -∗
      ([∗ list] j ∈ seq 0 8, (pa_add (add_vec_int ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 16 : mword 6) ('b"000"))))) (0 * 8)) j) ↦ₘ nth_byte (m !!! Regidx (mword_of_int 17 : mword 5)) j) -∗
      ([∗ list] j ∈ seq 0 8, (pa_add (add_vec_int ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 27 : mword 6) ('b"000"))))) (0 * 8)) j) ↦ₘ nth_byte (m !!! Regidx (mword_of_int 28 : mword 5)) j) -∗
      ([∗ list] j ∈ seq 0 8, (pa_add (add_vec_int ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 28 : mword 6) ('b"000"))))) (0 * 8)) j) ↦ₘ nth_byte (m !!! Regidx (mword_of_int 29 : mword 5)) j) -∗
      ([∗ list] j ∈ seq 0 8, (pa_add (add_vec_int ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 29 : mword 6) ('b"000"))))) (0 * 8)) j) ↦ₘ nth_byte (m !!! Regidx (mword_of_int 30 : mword 5)) j) -∗
      ([∗ list] j ∈ seq 0 8, (pa_add (add_vec_int ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 30 : mword 6) ('b"000"))))) (0 * 8)) j) ↦ₘ nth_byte (m !!! Regidx (mword_of_int 31 : mword 5)) j) -∗
      WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intros HN Hmode Hasid HSIE HMPRV HSXL Hmm HPBMTE HMXR Hpmm
      Hhit5 Hhith Hpmpf HW HR
      Hmask HTSR Hsup Hlpe0
      Hcanon1 Hvpn1 Hident1 Hrange1 Halv1 Halp1 Hcanon2 Hvpn2 Hident2 Hrange2 Halv2 Halp2 Hcanon3 Hvpn3 Hident3 Hrange3 Halv3 Halp3 Hcanon4 Hvpn4 Hident4 Hrange4 Halv4 Halp4 Hcanon5 Hvpn5 Hident5 Hrange5 Halv5 Halp5 Hcanon6 Hvpn6 Hident6 Hrange6 Halv6 Halp6 Hcanon7 Hvpn7 Hident7 Hrange7 Halv7 Halp7 Hcanon8 Hvpn8 Hident8 Hrange8 Halv8 Halp8 Hcanon9 Hvpn9 Hident9 Hrange9 Halv9 Halp9 Hcanon10 Hvpn10 Hident10 Hrange10 Halv10 Halp10 Hcanon11 Hvpn11 Hident11 Hrange11 Halv11 Halp11 Hcanon12 Hvpn12 Hident12 Hrange12 Halv12 Halp12 Hcanon13 Hvpn13 Hident13 Hrange13 Halv13 Halp13 Hcanon14 Hvpn14 Hident14 Hrange14 Halv14 Halp14 Hcanon15 Hvpn15 Hident15 Hrange15 Halv15 Halp15 Hcanon16 Hvpn16 Hident16 Hrange16 Halv16 Halp16 Hcanon17 Hvpn17 Hident17 Hrange17 Halv17 Halp17.
    iIntros "#Hhw #Hinv Hhs Hpriv Hsatp Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlb Hsepc Hpc Hfile
             #Htext Hw1 Hw2 Hw3 Hw4 Hw5 Hw6 Hw7 Hw8 Hw9 Hw10 Hw11 Hw12 Hw13 Hw14 Hw15 Hw16 Hw17 Hcont".
    (* totality of the entry file (for the final map_eq) *)
    iDestruct "Hfile" as "[%HdomM Hfmap]".
    iAssert (gpr_file m) with "[Hfmap]" as "Hfile".
    { iSplitR; [iPureIntro; exact HdomM |]. iExact "Hfmap". }
    (* ---- instrs #1..#19: prologue (fills + saves + jal) ---- *)
    iApply (wp_kv_prologue_hit root_ppn svpn m satp0 mstatus0 mie_v mdv0 menvcfg0
              pmpcfg0 pmpaddr00 tlbvec vold1 vold2 vold3 vold4 vold5 vold6 vold7 vold8 vold9 vold10 vold11 vold12 vold13 vold14 vold15 vold16 vold17 E Φ
              HN Hmode Hasid HSIE HMPRV HSXL Hmm HPBMTE HMXR Hpmm
              Hhit5 Hhith Hpmpf HW
              Hmask
              Hcanon1 Hvpn1 Hident1 Hrange1 Halv1 Halp1 Hcanon2 Hvpn2 Hident2 Hrange2 Halv2 Halp2 Hcanon3 Hvpn3 Hident3 Hrange3 Halv3 Halp3 Hcanon4 Hvpn4 Hident4 Hrange4 Halv4 Halp4 Hcanon5 Hvpn5 Hident5 Hrange5 Halv5 Halp5 Hcanon6 Hvpn6 Hident6 Hrange6 Halv6 Halp6 Hcanon7 Hvpn7 Hident7 Hrange7 Halv7 Halp7 Hcanon8 Hvpn8 Hident8 Hrange8 Halv8 Halp8 Hcanon9 Hvpn9 Hident9 Hrange9 Halv9 Halp9 Hcanon10 Hvpn10 Hident10 Hrange10 Halv10 Halp10 Hcanon11 Hvpn11 Hident11 Hrange11 Halv11 Halp11 Hcanon12 Hvpn12 Hident12 Hrange12 Halv12 Halp12 Hcanon13 Hvpn13 Hident13 Hrange13 Halv13 Halp13 Hcanon14 Hvpn14 Hident14 Hrange14 Halv14 Halp14 Hcanon15 Hvpn15 Hident15 Hrange15 Halv15 Halp15 Hcanon16 Hvpn16 Hident16 Hrange16 Halv16 Halp16 Hcanon17 Hvpn17 Hident17 Hrange17 Halv17 Halp17
              with "Hhw Hinv Hhs Hpriv Hsatp Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlb Hpc Hfile
                    Htext Hw1 Hw2 Hw3 Hw4 Hw5 Hw6 Hw7 Hw8 Hw9 Hw10 Hw11 Hw12 Hw13 Hw14 Hw15 Hw16 Hw17").
    iIntros "Hhs Hpriv Hsatp Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlb Hpc Hfile Hw1 Hw2 Hw3 Hw4 Hw5 Hw6 Hw7 Hw8 Hw9 Hw10 Hw11 Hw12 Hw13 Hw14 Hw15 Hw16 Hw17".
    (* ---- the kerneltrap call (THE axiom) ---- *)
    assert (Hsp_l : kv_m2 m !! Regidx csp_rs1 = Some (kv_sp1 m)).
    { unfold kv_m2. rewrite lookup_insert_ne; [| kv_regne]. unfold kv_m1. apply lookup_insert. }
    assert (Hra_l : kv_m2 m !! Regidx (mword_of_int 1 : mword 5)
                    = Some (regval_into_reg (mword_of_int (KernelSyms.kernelvec + 0x28) : mword 64))).
    { unfold kv_m2. apply lookup_insert. }
    iApply (kerneltrap_returns (kv_m2 m) (kv_sp1 m)
              (regval_into_reg (mword_of_int (KernelSyms.kernelvec + 0x28) : mword 64))
              satp0 mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 tlbvec
              (add_vec_int (((kv_sp1 m))) (0 * 8)) (add_vec_int ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000"))))) (0 * 8)) (add_vec_int ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 4 : mword 6) ('b"000"))))) (0 * 8)) (add_vec_int ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 5 : mword 6) ('b"000"))))) (0 * 8)) (add_vec_int ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 6 : mword 6) ('b"000"))))) (0 * 8)) (add_vec_int ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 9 : mword 6) ('b"000"))))) (0 * 8)) (add_vec_int ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 10 : mword 6) ('b"000"))))) (0 * 8)) (add_vec_int ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 11 : mword 6) ('b"000"))))) (0 * 8)) (add_vec_int ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 12 : mword 6) ('b"000"))))) (0 * 8)) (add_vec_int ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 13 : mword 6) ('b"000"))))) (0 * 8)) (add_vec_int ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 14 : mword 6) ('b"000"))))) (0 * 8)) (add_vec_int ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 15 : mword 6) ('b"000"))))) (0 * 8)) (add_vec_int ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 16 : mword 6) ('b"000"))))) (0 * 8)) (add_vec_int ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 27 : mword 6) ('b"000"))))) (0 * 8)) (add_vec_int ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 28 : mword 6) ('b"000"))))) (0 * 8)) (add_vec_int ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 29 : mword 6) ('b"000"))))) (0 * 8)) (add_vec_int ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 30 : mword 6) ('b"000"))))) (0 * 8))
              (m !!! Regidx (mword_of_int 1 : mword 5)) (m !!! Regidx (mword_of_int 3 : mword 5)) (m !!! Regidx (mword_of_int 5 : mword 5)) (m !!! Regidx (mword_of_int 6 : mword 5)) (m !!! Regidx (mword_of_int 7 : mword 5)) (m !!! Regidx (mword_of_int 10 : mword 5)) (m !!! Regidx (mword_of_int 11 : mword 5)) (m !!! Regidx (mword_of_int 12 : mword 5)) (m !!! Regidx (mword_of_int 13 : mword 5)) (m !!! Regidx (mword_of_int 14 : mword 5)) (m !!! Regidx (mword_of_int 15 : mword 5)) (m !!! Regidx (mword_of_int 16 : mword 5)) (m !!! Regidx (mword_of_int 17 : mword 5)) (m !!! Regidx (mword_of_int 28 : mword 5)) (m !!! Regidx (mword_of_int 29 : mword 5)) (m !!! Regidx (mword_of_int 30 : mword 5)) (m !!! Regidx (mword_of_int 31 : mword 5))
              E Φ Hsp_l Hra_l
              with "Hhw Hinv Hhs Hpriv Hsatp Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlb Hpc Hfile Hw1 Hw2 Hw3 Hw4 Hw5 Hw6 Hw7 Hw8 Hw9 Hw10 Hw11 Hw12 Hw13 Hw14 Hw15 Hw16 Hw17").
    iNext.
    iIntros (m') "%Hdom' %Hpres Hhs Hpriv Hsatp Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlb Hpc Hfile Hw1 Hw2 Hw3 Hw4 Hw5 Hw6 Hw7 Hw8 Hw9 Hw10 Hw11 Hw12 Hw13 Hw14 Hw15 Hw16 Hw17".
    iEval (rewrite kv_rvr) in "Hpc".
    (* sp is callee-saved: the post-kerneltrap file still maps sp to kv_sp1 m *)
    assert (Hsp_nc : Regidx csp_rs1 ∉ kt_clobbered).
    { apply (bool_decide_eq_false_1 (Regidx csp_rs1 ∈ kt_clobbered)).
      vm_compute. reflexivity. }
    assert (Hsp'' : m' !!! Regidx csp_rs1 = kv_sp1 m).
    { apply lookup_total_correct. rewrite (Hpres _ Hsp_nc). exact Hsp_l. }
    (* ---- instrs #20..#38: epilogue (restores + sp cancel + sret) ---- *)
    iApply (wp_kv_epilogue root_ppn svpn m' (kv_sp1 m) satp0 mstatus0 mie_v mdv0 menvcfg0 sepc0
              pmpcfg0 pmpaddr00 tlbvec
              (m !!! Regidx (mword_of_int 1 : mword 5)) (m !!! Regidx (mword_of_int 3 : mword 5)) (m !!! Regidx (mword_of_int 5 : mword 5)) (m !!! Regidx (mword_of_int 6 : mword 5)) (m !!! Regidx (mword_of_int 7 : mword 5)) (m !!! Regidx (mword_of_int 10 : mword 5)) (m !!! Regidx (mword_of_int 11 : mword 5)) (m !!! Regidx (mword_of_int 12 : mword 5)) (m !!! Regidx (mword_of_int 13 : mword 5)) (m !!! Regidx (mword_of_int 14 : mword 5)) (m !!! Regidx (mword_of_int 15 : mword 5)) (m !!! Regidx (mword_of_int 16 : mword 5)) (m !!! Regidx (mword_of_int 17 : mword 5)) (m !!! Regidx (mword_of_int 28 : mword 5)) (m !!! Regidx (mword_of_int 29 : mword 5)) (m !!! Regidx (mword_of_int 30 : mword 5)) (m !!! Regidx (mword_of_int 31 : mword 5))
              E Φ
              HN Hmode Hasid HSIE HMPRV HSXL Hmm HPBMTE HMXR Hpmm
              Hhit5 Hhith Hpmpf HR Hmask Hsp'' HTSR Hsup Hlpe0
              Hcanon1 Hvpn1 Hident1 Hrange1 Halv1 Halp1 Hcanon2 Hvpn2 Hident2 Hrange2 Halv2 Halp2 Hcanon3 Hvpn3 Hident3 Hrange3 Halv3 Halp3 Hcanon4 Hvpn4 Hident4 Hrange4 Halv4 Halp4 Hcanon5 Hvpn5 Hident5 Hrange5 Halv5 Halp5 Hcanon6 Hvpn6 Hident6 Hrange6 Halv6 Halp6 Hcanon7 Hvpn7 Hident7 Hrange7 Halv7 Halp7 Hcanon8 Hvpn8 Hident8 Hrange8 Halv8 Halp8 Hcanon9 Hvpn9 Hident9 Hrange9 Halv9 Halp9 Hcanon10 Hvpn10 Hident10 Hrange10 Halv10 Halp10 Hcanon11 Hvpn11 Hident11 Hrange11 Halv11 Halp11 Hcanon12 Hvpn12 Hident12 Hrange12 Halv12 Halp12 Hcanon13 Hvpn13 Hident13 Hrange13 Halv13 Halp13 Hcanon14 Hvpn14 Hident14 Hrange14 Halv14 Halp14 Hcanon15 Hvpn15 Hident15 Hrange15 Halv15 Halp15 Hcanon16 Hvpn16 Hident16 Hrange16 Halv16 Halp16 Hcanon17 Hvpn17 Hident17 Hrange17 Halv17 Halp17
              with "Hhw Hinv Hhs Hpriv Hsatp Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlb Hsepc Hpc Hfile
                    Htext Hw1 Hw2 Hw3 Hw4 Hw5 Hw6 Hw7 Hw8 Hw9 Hw10 Hw11 Hw12 Hw13 Hw14 Hw15 Hw16 Hw17").
    iIntros "Hhs Hpriv Hsatp Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlb Hsepc Hpc Hfile Hw1 Hw2 Hw3 Hw4 Hw5 Hw6 Hw7 Hw8 Hw9 Hw10 Hw11 Hw12 Hw13 Hw14 Hw15 Hw16 Hw17".
    (* ---- the round-trip: the final file IS the entry file ---- *)
    assert (Hbig : (<[Regidx csp_rs1 := regval_into_reg (add_vec (kv_sp1 m) (sign_extend' 64 (caddi16sp_imm (mword_of_int 16 : mword 6))))]> (<[Regidx (mword_of_int 31 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 31 : mword 5))]> (<[Regidx (mword_of_int 30 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 30 : mword 5))]> (<[Regidx (mword_of_int 29 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 29 : mword 5))]> (<[Regidx (mword_of_int 28 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 28 : mword 5))]> (<[Regidx (mword_of_int 17 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 17 : mword 5))]> (<[Regidx (mword_of_int 16 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 16 : mword 5))]> (<[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 15 : mword 5))]> (<[Regidx (mword_of_int 14 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 14 : mword 5))]> (<[Regidx (mword_of_int 13 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 13 : mword 5))]> (<[Regidx (mword_of_int 12 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 12 : mword 5))]> (<[Regidx (mword_of_int 11 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 11 : mword 5))]> (<[Regidx (mword_of_int 10 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 10 : mword 5))]> (<[Regidx (mword_of_int 7 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 7 : mword 5))]> (<[Regidx (mword_of_int 6 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 6 : mword 5))]> (<[Regidx (mword_of_int 5 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 5 : mword 5))]> (<[Regidx (mword_of_int 3 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 3 : mword 5))]> (<[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 1 : mword 5))]> (m'))))))))))))))))))) = m).
    { clear - HdomM Hpres.
      assert (Hspval : add_vec (kv_sp1 m) (sign_extend' 64 (caddi16sp_imm (mword_of_int 16 : mword 6)))
                       = m !!! Regidx csp_rs1).
      { unfold kv_sp1, regval_into_reg. rewrite kv_addv_assoc kv_cancel. apply kv_addv_zero. }
      assert (Hin_sp : Regidx csp_rs1 ∈ kv_saved)
        by (apply (bool_decide_eq_true_1 (Regidx csp_rs1 ∈ kv_saved)); vm_compute; reflexivity).
      assert (Hin_1 : Regidx (mword_of_int 1 : mword 5) ∈ kv_saved)
        by (apply (bool_decide_eq_true_1 (Regidx (mword_of_int 1 : mword 5) ∈ kv_saved)); vm_compute; reflexivity).
      assert (Hin_3 : Regidx (mword_of_int 3 : mword 5) ∈ kv_saved)
        by (apply (bool_decide_eq_true_1 (Regidx (mword_of_int 3 : mword 5) ∈ kv_saved)); vm_compute; reflexivity).
      assert (Hin_5 : Regidx (mword_of_int 5 : mword 5) ∈ kv_saved)
        by (apply (bool_decide_eq_true_1 (Regidx (mword_of_int 5 : mword 5) ∈ kv_saved)); vm_compute; reflexivity).
      assert (Hin_6 : Regidx (mword_of_int 6 : mword 5) ∈ kv_saved)
        by (apply (bool_decide_eq_true_1 (Regidx (mword_of_int 6 : mword 5) ∈ kv_saved)); vm_compute; reflexivity).
      assert (Hin_7 : Regidx (mword_of_int 7 : mword 5) ∈ kv_saved)
        by (apply (bool_decide_eq_true_1 (Regidx (mword_of_int 7 : mword 5) ∈ kv_saved)); vm_compute; reflexivity).
      assert (Hin_10 : Regidx (mword_of_int 10 : mword 5) ∈ kv_saved)
        by (apply (bool_decide_eq_true_1 (Regidx (mword_of_int 10 : mword 5) ∈ kv_saved)); vm_compute; reflexivity).
      assert (Hin_11 : Regidx (mword_of_int 11 : mword 5) ∈ kv_saved)
        by (apply (bool_decide_eq_true_1 (Regidx (mword_of_int 11 : mword 5) ∈ kv_saved)); vm_compute; reflexivity).
      assert (Hin_12 : Regidx (mword_of_int 12 : mword 5) ∈ kv_saved)
        by (apply (bool_decide_eq_true_1 (Regidx (mword_of_int 12 : mword 5) ∈ kv_saved)); vm_compute; reflexivity).
      assert (Hin_13 : Regidx (mword_of_int 13 : mword 5) ∈ kv_saved)
        by (apply (bool_decide_eq_true_1 (Regidx (mword_of_int 13 : mword 5) ∈ kv_saved)); vm_compute; reflexivity).
      assert (Hin_14 : Regidx (mword_of_int 14 : mword 5) ∈ kv_saved)
        by (apply (bool_decide_eq_true_1 (Regidx (mword_of_int 14 : mword 5) ∈ kv_saved)); vm_compute; reflexivity).
      assert (Hin_15 : Regidx (mword_of_int 15 : mword 5) ∈ kv_saved)
        by (apply (bool_decide_eq_true_1 (Regidx (mword_of_int 15 : mword 5) ∈ kv_saved)); vm_compute; reflexivity).
      assert (Hin_16 : Regidx (mword_of_int 16 : mword 5) ∈ kv_saved)
        by (apply (bool_decide_eq_true_1 (Regidx (mword_of_int 16 : mword 5) ∈ kv_saved)); vm_compute; reflexivity).
      assert (Hin_17 : Regidx (mword_of_int 17 : mword 5) ∈ kv_saved)
        by (apply (bool_decide_eq_true_1 (Regidx (mword_of_int 17 : mword 5) ∈ kv_saved)); vm_compute; reflexivity).
      assert (Hin_28 : Regidx (mword_of_int 28 : mword 5) ∈ kv_saved)
        by (apply (bool_decide_eq_true_1 (Regidx (mword_of_int 28 : mword 5) ∈ kv_saved)); vm_compute; reflexivity).
      assert (Hin_29 : Regidx (mword_of_int 29 : mword 5) ∈ kv_saved)
        by (apply (bool_decide_eq_true_1 (Regidx (mword_of_int 29 : mword 5) ∈ kv_saved)); vm_compute; reflexivity).
      assert (Hin_30 : Regidx (mword_of_int 30 : mword 5) ∈ kv_saved)
        by (apply (bool_decide_eq_true_1 (Regidx (mword_of_int 30 : mword 5) ∈ kv_saved)); vm_compute; reflexivity).
      assert (Hin_31 : Regidx (mword_of_int 31 : mword 5) ∈ kv_saved)
        by (apply (bool_decide_eq_true_1 (Regidx (mword_of_int 31 : mword 5) ∈ kv_saved)); vm_compute; reflexivity).
      assert (Hsub : kt_clobbered ⊆ kv_saved)
        by (apply (bool_decide_eq_true_1 (kt_clobbered ⊆ kv_saved)); vm_compute; reflexivity).
      unfold regval_into_reg. rewrite Hspval.
      apply map_eq. intros i.
      destruct (decide (i ∈ kv_saved)) as [Hin|Hout].
      - unfold kv_saved in Hin.
        rewrite !elem_of_union !elem_of_singleton in Hin.
        repeat match goal with HH : _ ∨ _ |- _ => destruct HH end;
          subst i;
          repeat (rewrite lookup_insert_ne; [| kv_regne]);
          rewrite lookup_insert;
          symmetry; apply lookup_lookup_total_dom; apply HdomM.
      - (* i outside the written set: peel all 18 inserts, then the axiom's
           callee-saved preservation + the two prologue inserts. *)
        rewrite lookup_insert_ne;
          [| let HeqK := fresh in intros HeqK; apply Hout; rewrite <- HeqK; exact Hin_sp ].
        rewrite lookup_insert_ne;
          [| let HeqK := fresh in intros HeqK; apply Hout; rewrite <- HeqK; exact Hin_31 ].
        rewrite lookup_insert_ne;
          [| let HeqK := fresh in intros HeqK; apply Hout; rewrite <- HeqK; exact Hin_30 ].
        rewrite lookup_insert_ne;
          [| let HeqK := fresh in intros HeqK; apply Hout; rewrite <- HeqK; exact Hin_29 ].
        rewrite lookup_insert_ne;
          [| let HeqK := fresh in intros HeqK; apply Hout; rewrite <- HeqK; exact Hin_28 ].
        rewrite lookup_insert_ne;
          [| let HeqK := fresh in intros HeqK; apply Hout; rewrite <- HeqK; exact Hin_17 ].
        rewrite lookup_insert_ne;
          [| let HeqK := fresh in intros HeqK; apply Hout; rewrite <- HeqK; exact Hin_16 ].
        rewrite lookup_insert_ne;
          [| let HeqK := fresh in intros HeqK; apply Hout; rewrite <- HeqK; exact Hin_15 ].
        rewrite lookup_insert_ne;
          [| let HeqK := fresh in intros HeqK; apply Hout; rewrite <- HeqK; exact Hin_14 ].
        rewrite lookup_insert_ne;
          [| let HeqK := fresh in intros HeqK; apply Hout; rewrite <- HeqK; exact Hin_13 ].
        rewrite lookup_insert_ne;
          [| let HeqK := fresh in intros HeqK; apply Hout; rewrite <- HeqK; exact Hin_12 ].
        rewrite lookup_insert_ne;
          [| let HeqK := fresh in intros HeqK; apply Hout; rewrite <- HeqK; exact Hin_11 ].
        rewrite lookup_insert_ne;
          [| let HeqK := fresh in intros HeqK; apply Hout; rewrite <- HeqK; exact Hin_10 ].
        rewrite lookup_insert_ne;
          [| let HeqK := fresh in intros HeqK; apply Hout; rewrite <- HeqK; exact Hin_7 ].
        rewrite lookup_insert_ne;
          [| let HeqK := fresh in intros HeqK; apply Hout; rewrite <- HeqK; exact Hin_6 ].
        rewrite lookup_insert_ne;
          [| let HeqK := fresh in intros HeqK; apply Hout; rewrite <- HeqK; exact Hin_5 ].
        rewrite lookup_insert_ne;
          [| let HeqK := fresh in intros HeqK; apply Hout; rewrite <- HeqK; exact Hin_3 ].
        rewrite lookup_insert_ne;
          [| let HeqK := fresh in intros HeqK; apply Hout; rewrite <- HeqK; exact Hin_1 ].
        rewrite (Hpres i);
          [| let HinC := fresh in intros HinC; apply Hout; exact (Hsub _ HinC) ].
        unfold kv_m2, kv_m1.
        rewrite lookup_insert_ne;
          [| let HeqK := fresh in intros HeqK; apply Hout; rewrite <- HeqK; exact Hin_1 ].
        rewrite lookup_insert_ne;
          [| let HeqK := fresh in intros HeqK; apply Hout; rewrite <- HeqK; exact Hin_sp ].
        reflexivity. }
    iEval (rewrite Hbig) in "Hfile".
    iApply ("Hcont" with "Hhs Hpriv Hsatp Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlb Hsepc Hpc Hfile Hw1 Hw2 Hw3 Hw4 Hw5 Hw6 Hw7 Hw8 Hw9 Hw10 Hw11 Hw12 Hw13 Hw14 Hw15 Hw16 Hw17").
  Qed.


End WpKvHit.
