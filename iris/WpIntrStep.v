(* WpIntrStep.v -- THE INTERRUPT-SAFETY CAPSTONE.

   [wp_acquire1_intr]: executing acquire's first instruction
   (c.addi sp,-32 = 0x1101 @ 0x80000c04, RVC, 4-aligned) in S-mode with
   INTERRUPTS ENABLED (sstatus.SIE = 1) and stvec -> kernelvec (0x800053e0,
   direct mode).  The machine step either
     - retires the instruction (dispatchInterrupt = None), or
     - takes the pending S-level interrupt: traps to kernelvec, runs the
       COMPLETE handler (wp_kernelvec_hit: 17 saves, kerneltrap, 17
       restores, SRET) and returns to the SAME pc with SIE RE-ENABLED --
       where the theorem applies its own Loeb induction hypothesis.
   The single outcome is therefore "the instruction executed"; the
   precondition is a ROUND-TRIP INVARIANT [acq_frame] re-established by
   every interrupt round trip:
     - mstatus is EXISTENTIAL with the fact set [acq_ms_facts] (SIE=1,
       MPRV=0, SXL=2, MXR=0, TSR=0), preserved by the trap+SRET tower
       (the SIE=1 restoration is WpIntrBits.roundtrip_SIE);
     - sepc / scause / stval and the 17 stack windows are existential
       (the round trip rewrites them);
     - the TLB is in the steady HIT state (slots 5, tlb_hash svpn, and the
       acquire page's slot 0 all hold the identity superpage entry), so the
       handler is the no-fill [wp_kernelvec_hit] and the TLB is invariant.
   Only [kerneltrap_returns] + the model's platform externs are assumed. *)
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
Require Import WpGpr WpGprRvc WpGprAddi WpGprMret.
Require Import SmodeCore WpSmodeGpr WpSmodeSret WpEntryNew WpKvInstr.
Require Import WpKernelvecNew WpKvHit.
Require Import WpIntrBits WpIntrCore.
From Kernel Require KernelInstrs.
From Kernel Require KernelSyms.
Local Open Scope Z_scope.
Import Defs.

Section WpIntrStep.
  Context `{!riscvGS Sig}.

  (* the mstatus fact set carried through the round trip *)
  Definition acq_ms_facts (ms : mword 64) : Prop :=
    eq_vec (_get_Mstatus_SIE ms) ('b"1") = true /\
    eq_vec (_get_Mstatus_MPRV ms) ('b"1") = false /\
    _get_Mstatus_SXL ms = 'b"10" /\
    eq_vec (_get_Mstatus_MXR ms) ('b"0") = true /\
    eq_vec (_get_Mstatus_TSR ms) ('b"1") = false.

  (* the round trip preserves the fact set (SIE=1 is RESTORED -- the
     headline [roundtrip_SIE]; MPRV is cleared by SRET; SXL/MXR/TSR live in
     untouched bits). *)
  Lemma acq_ms_facts_roundtrip (elp_v : mword 1) (ms : mword 64) :
    acq_ms_facts ms -> acq_ms_facts (sret_ms5 (trap_ms elp_v ms)).
  Proof.
    intros (H1 & H2 & H3 & H4 & H5).
    split; [exact (roundtrip_SIE_true elp_v ms H1) |].
    split; [exact (roundtrip_MPRV_false elp_v ms) |].
    split; [exact (roundtrip_SXL_eq elp_v ms H3) |].
    split; [exact (roundtrip_MXR_true elp_v ms H4) |].
    exact (roundtrip_TSR_false elp_v ms H5).
  Qed.

  (* THE ROUND-TRIP INVARIANT (all resources except pc_is / gpr_file,
     which change across the executed instruction and are threaded
     separately). *)
  Definition acq_frame (m : gmap regidx (mword 64))
      (satp0 mie_v mdv0 menvcfg0 mip_v : mword 64) (meip seip : mword 1)
      (pmpcfg0 : type_of_register pmpcfg_n) (pmpaddr00 : type_of_register pmpaddr_n)
      (tlbvec : vec (option TLB_Entry) (2 ^ 6)) : iProp Sig :=
    (hart_state ↦ᵣ HART_ACTIVE tt ∗
     cur_privilege ↦ᵣ Supervisor ∗
     satp ↦ᵣ satp0 ∗
     (∃ ms : mword 64, mstatus ↦ᵣ ms ∗ ⌜ acq_ms_facts ms ⌝) ∗
     mie ↦ᵣ mie_v ∗
     mideleg ↦ᵣ mdv0 ∗
     menvcfg ↦ᵣ menvcfg0 ∗
     mip ↦ᵣ mip_v ∗
     sig_meip ↦ᵣ meip ∗
     sig_seip ↦ᵣ seip ∗
     stvec ↦ᵣ (mword_of_int KernelSyms.kernelvec : mword 64) ∗
     (∃ v : mword 64, sepc ↦ᵣ v) ∗
     (∃ v : mword 64, scause ↦ᵣ v) ∗
     (∃ v : mword 64, stval ↦ᵣ v) ∗
     pmpcfg_n ↦ᵣ pmpcfg0 ∗
     pmpaddr_n ↦ᵣ pmpaddr00 ∗
     tlb ↦ᵣ tlbvec ∗
     (∃ w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : bv 64,
        ([∗ list] j ∈ seq 0 8, (pa_add ((((kv_sp1 m)))) j) ↦ₘ nth_byte w1 j) ∗
        ([∗ list] j ∈ seq 0 8, (pa_add (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000")))))) j) ↦ₘ nth_byte w2 j) ∗
        ([∗ list] j ∈ seq 0 8, (pa_add (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 4 : mword 6) ('b"000")))))) j) ↦ₘ nth_byte w3 j) ∗
        ([∗ list] j ∈ seq 0 8, (pa_add (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 5 : mword 6) ('b"000")))))) j) ↦ₘ nth_byte w4 j) ∗
        ([∗ list] j ∈ seq 0 8, (pa_add (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 6 : mword 6) ('b"000")))))) j) ↦ₘ nth_byte w5 j) ∗
        ([∗ list] j ∈ seq 0 8, (pa_add (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 9 : mword 6) ('b"000")))))) j) ↦ₘ nth_byte w6 j) ∗
        ([∗ list] j ∈ seq 0 8, (pa_add (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 10 : mword 6) ('b"000")))))) j) ↦ₘ nth_byte w7 j) ∗
        ([∗ list] j ∈ seq 0 8, (pa_add (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 11 : mword 6) ('b"000")))))) j) ↦ₘ nth_byte w8 j) ∗
        ([∗ list] j ∈ seq 0 8, (pa_add (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 12 : mword 6) ('b"000")))))) j) ↦ₘ nth_byte w9 j) ∗
        ([∗ list] j ∈ seq 0 8, (pa_add (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 13 : mword 6) ('b"000")))))) j) ↦ₘ nth_byte w10 j) ∗
        ([∗ list] j ∈ seq 0 8, (pa_add (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 14 : mword 6) ('b"000")))))) j) ↦ₘ nth_byte w11 j) ∗
        ([∗ list] j ∈ seq 0 8, (pa_add (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 15 : mword 6) ('b"000")))))) j) ↦ₘ nth_byte w12 j) ∗
        ([∗ list] j ∈ seq 0 8, (pa_add (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 16 : mword 6) ('b"000")))))) j) ↦ₘ nth_byte w13 j) ∗
        ([∗ list] j ∈ seq 0 8, (pa_add (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 27 : mword 6) ('b"000")))))) j) ↦ₘ nth_byte w14 j) ∗
        ([∗ list] j ∈ seq 0 8, (pa_add (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 28 : mword 6) ('b"000")))))) j) ↦ₘ nth_byte w15 j) ∗
        ([∗ list] j ∈ seq 0 8, (pa_add (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 29 : mword 6) ('b"000")))))) j) ↦ₘ nth_byte w16 j) ∗
        ([∗ list] j ∈ seq 0 8, (pa_add (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 30 : mword 6) ('b"000")))))) j) ↦ₘ nth_byte w17 j)))%I.

  (* the executed instruction's register-file effect: sp -= 32 *)
  Definition acq_m1 (m : gmap regidx (mword 64)) : gmap regidx (mword 64) :=
    <[Regidx csp_rs1 := regval_into_reg
        (add_vec (m !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 acq_i1)))]> m.

  Lemma wp_acquire1_intr (root_ppn : mword 44) (svpn : mword 27)
      (m : gmap regidx (mword 64))
      (satp0 mie_v mdv0 menvcfg0 mip_v : mword 64) (meip seip : mword 1)
      (pmpcfg0 : type_of_register pmpcfg_n) (pmpaddr00 : type_of_register pmpaddr_n)
      (tlbvec : vec (option TLB_Entry) (2 ^ 6))
      E (Phi : mval -> iProp Sig) :
    ↑minstretN ⊆ E ->
    (* S-mode config facts *)
    _get_Satp64_Mode (Mk_Satp64 satp0) = ('b"1000" : mword 4) ->
    zero_extend' 16 (satp_to_asid (autocast (T := mword) satp0 : mword 64)) = (mword_of_int 0 : mword 16) ->
    and_vec mie_v (not_vec mdv0) = zeros' 64 ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    pmm_mode_backwards (_get_MEnvcfg_PMM menvcfg0) = PMM_Disabled ->
    (* TLB: steady HIT state at all three slots *)
    vec_access_dec tlbvec 5 = Some (pw_tlb_entry root_ppn (mword_of_int 0)) ->
    vec_access_dec tlbvec (tlb_hash (__id 39) svpn) = Some (pw_tlb_entry root_ppn (mword_of_int 0)) ->
    vec_access_dec tlbvec 0 = Some (pw_tlb_entry root_ppn (mword_of_int 0)) ->
    (* PMP: kernelvec text + frame + the acquire pc *)
    (forall A : Z, kv_text_pc A = true -> pmp_tor0_sfetch_all pmpcfg0 pmpaddr00 (mword_of_int A)) ->
    eq_vec (_get_Pmpcfg_ent_W (vec_access_dec pmpcfg0 0)) ('b"1") = true ->
    eq_vec (_get_Pmpcfg_ent_R (vec_access_dec pmpcfg0 0)) ('b"1") = true ->
    pmp_tor0_sfetch_all pmpcfg0 pmpaddr00 acq_pc1 ->
    (* stack-page geometry *)
    and_vec (sign_extend' (57 - 12) svpn) (not_vec (mword_of_int 0x3FFFF : mword 45)) = (mword_of_int 0x80000 : mword 45) ->
    (* SRET *)
    _get_MEnvcfg_LPE menvcfg0 = ('b"0") ->
    (* slot 1: x1 at sp+0 *)
    neq_vec (bits_of_virtaddr (Virtaddr (((kv_sp1 m))))) (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr (((kv_sp1 m))))) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec (subrange_vec_dec (bits_of_virtaddr (Virtaddr (((kv_sp1 m))))) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = svpn ->
    zero_extend' 64 (concat_vec (tlb_get_ppn 39 (pw_tlb_entry root_ppn (mword_of_int 0)) svpn) (subrange_vec_dec (bits_of_virtaddr (Virtaddr (((kv_sp1 m))))) (Z.sub pagesize_bits 1) 0)) = ((kv_sp1 m)) ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4) (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4) (uint ((((kv_sp1 m))))) (uint (to_bits 64 8)) = PMP_Match ->
    is_aligned_vaddr (Virtaddr (((kv_sp1 m)))) 8 = true ->
    is_aligned_paddr (Physaddr ((((kv_sp1 m))))) 8 = true ->
    (* slot 2: x3 at sp+16 *)
    neq_vec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000"))))))) (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000"))))))) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec (subrange_vec_dec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000"))))))) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = svpn ->
    zero_extend' 64 (concat_vec (tlb_get_ppn 39 (pw_tlb_entry root_ppn (mword_of_int 0)) svpn) (subrange_vec_dec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000"))))))) (Z.sub pagesize_bits 1) 0)) = (add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000")))) ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4) (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4) (uint (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000"))))))) (uint (to_bits 64 8)) = PMP_Match ->
    is_aligned_vaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000")))))) 8 = true ->
    is_aligned_paddr (Physaddr (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000"))))))) 8 = true ->
    (* slot 3: x5 at sp+32 *)
    neq_vec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 4 : mword 6) ('b"000"))))))) (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 4 : mword 6) ('b"000"))))))) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec (subrange_vec_dec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 4 : mword 6) ('b"000"))))))) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = svpn ->
    zero_extend' 64 (concat_vec (tlb_get_ppn 39 (pw_tlb_entry root_ppn (mword_of_int 0)) svpn) (subrange_vec_dec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 4 : mword 6) ('b"000"))))))) (Z.sub pagesize_bits 1) 0)) = (add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 4 : mword 6) ('b"000")))) ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4) (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4) (uint (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 4 : mword 6) ('b"000"))))))) (uint (to_bits 64 8)) = PMP_Match ->
    is_aligned_vaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 4 : mword 6) ('b"000")))))) 8 = true ->
    is_aligned_paddr (Physaddr (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 4 : mword 6) ('b"000"))))))) 8 = true ->
    (* slot 4: x6 at sp+40 *)
    neq_vec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 5 : mword 6) ('b"000"))))))) (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 5 : mword 6) ('b"000"))))))) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec (subrange_vec_dec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 5 : mword 6) ('b"000"))))))) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = svpn ->
    zero_extend' 64 (concat_vec (tlb_get_ppn 39 (pw_tlb_entry root_ppn (mword_of_int 0)) svpn) (subrange_vec_dec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 5 : mword 6) ('b"000"))))))) (Z.sub pagesize_bits 1) 0)) = (add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 5 : mword 6) ('b"000")))) ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4) (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4) (uint (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 5 : mword 6) ('b"000"))))))) (uint (to_bits 64 8)) = PMP_Match ->
    is_aligned_vaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 5 : mword 6) ('b"000")))))) 8 = true ->
    is_aligned_paddr (Physaddr (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 5 : mword 6) ('b"000"))))))) 8 = true ->
    (* slot 5: x7 at sp+48 *)
    neq_vec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 6 : mword 6) ('b"000"))))))) (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 6 : mword 6) ('b"000"))))))) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec (subrange_vec_dec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 6 : mword 6) ('b"000"))))))) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = svpn ->
    zero_extend' 64 (concat_vec (tlb_get_ppn 39 (pw_tlb_entry root_ppn (mword_of_int 0)) svpn) (subrange_vec_dec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 6 : mword 6) ('b"000"))))))) (Z.sub pagesize_bits 1) 0)) = (add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 6 : mword 6) ('b"000")))) ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4) (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4) (uint (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 6 : mword 6) ('b"000"))))))) (uint (to_bits 64 8)) = PMP_Match ->
    is_aligned_vaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 6 : mword 6) ('b"000")))))) 8 = true ->
    is_aligned_paddr (Physaddr (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 6 : mword 6) ('b"000"))))))) 8 = true ->
    (* slot 6: x10 at sp+72 *)
    neq_vec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 9 : mword 6) ('b"000"))))))) (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 9 : mword 6) ('b"000"))))))) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec (subrange_vec_dec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 9 : mword 6) ('b"000"))))))) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = svpn ->
    zero_extend' 64 (concat_vec (tlb_get_ppn 39 (pw_tlb_entry root_ppn (mword_of_int 0)) svpn) (subrange_vec_dec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 9 : mword 6) ('b"000"))))))) (Z.sub pagesize_bits 1) 0)) = (add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 9 : mword 6) ('b"000")))) ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4) (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4) (uint (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 9 : mword 6) ('b"000"))))))) (uint (to_bits 64 8)) = PMP_Match ->
    is_aligned_vaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 9 : mword 6) ('b"000")))))) 8 = true ->
    is_aligned_paddr (Physaddr (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 9 : mword 6) ('b"000"))))))) 8 = true ->
    (* slot 7: x11 at sp+80 *)
    neq_vec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 10 : mword 6) ('b"000"))))))) (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 10 : mword 6) ('b"000"))))))) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec (subrange_vec_dec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 10 : mword 6) ('b"000"))))))) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = svpn ->
    zero_extend' 64 (concat_vec (tlb_get_ppn 39 (pw_tlb_entry root_ppn (mword_of_int 0)) svpn) (subrange_vec_dec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 10 : mword 6) ('b"000"))))))) (Z.sub pagesize_bits 1) 0)) = (add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 10 : mword 6) ('b"000")))) ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4) (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4) (uint (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 10 : mword 6) ('b"000"))))))) (uint (to_bits 64 8)) = PMP_Match ->
    is_aligned_vaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 10 : mword 6) ('b"000")))))) 8 = true ->
    is_aligned_paddr (Physaddr (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 10 : mword 6) ('b"000"))))))) 8 = true ->
    (* slot 8: x12 at sp+88 *)
    neq_vec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 11 : mword 6) ('b"000"))))))) (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 11 : mword 6) ('b"000"))))))) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec (subrange_vec_dec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 11 : mword 6) ('b"000"))))))) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = svpn ->
    zero_extend' 64 (concat_vec (tlb_get_ppn 39 (pw_tlb_entry root_ppn (mword_of_int 0)) svpn) (subrange_vec_dec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 11 : mword 6) ('b"000"))))))) (Z.sub pagesize_bits 1) 0)) = (add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 11 : mword 6) ('b"000")))) ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4) (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4) (uint (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 11 : mword 6) ('b"000"))))))) (uint (to_bits 64 8)) = PMP_Match ->
    is_aligned_vaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 11 : mword 6) ('b"000")))))) 8 = true ->
    is_aligned_paddr (Physaddr (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 11 : mword 6) ('b"000"))))))) 8 = true ->
    (* slot 9: x13 at sp+96 *)
    neq_vec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 12 : mword 6) ('b"000"))))))) (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 12 : mword 6) ('b"000"))))))) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec (subrange_vec_dec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 12 : mword 6) ('b"000"))))))) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = svpn ->
    zero_extend' 64 (concat_vec (tlb_get_ppn 39 (pw_tlb_entry root_ppn (mword_of_int 0)) svpn) (subrange_vec_dec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 12 : mword 6) ('b"000"))))))) (Z.sub pagesize_bits 1) 0)) = (add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 12 : mword 6) ('b"000")))) ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4) (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4) (uint (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 12 : mword 6) ('b"000"))))))) (uint (to_bits 64 8)) = PMP_Match ->
    is_aligned_vaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 12 : mword 6) ('b"000")))))) 8 = true ->
    is_aligned_paddr (Physaddr (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 12 : mword 6) ('b"000"))))))) 8 = true ->
    (* slot 10: x14 at sp+104 *)
    neq_vec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 13 : mword 6) ('b"000"))))))) (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 13 : mword 6) ('b"000"))))))) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec (subrange_vec_dec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 13 : mword 6) ('b"000"))))))) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = svpn ->
    zero_extend' 64 (concat_vec (tlb_get_ppn 39 (pw_tlb_entry root_ppn (mword_of_int 0)) svpn) (subrange_vec_dec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 13 : mword 6) ('b"000"))))))) (Z.sub pagesize_bits 1) 0)) = (add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 13 : mword 6) ('b"000")))) ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4) (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4) (uint (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 13 : mword 6) ('b"000"))))))) (uint (to_bits 64 8)) = PMP_Match ->
    is_aligned_vaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 13 : mword 6) ('b"000")))))) 8 = true ->
    is_aligned_paddr (Physaddr (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 13 : mword 6) ('b"000"))))))) 8 = true ->
    (* slot 11: x15 at sp+112 *)
    neq_vec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 14 : mword 6) ('b"000"))))))) (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 14 : mword 6) ('b"000"))))))) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec (subrange_vec_dec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 14 : mword 6) ('b"000"))))))) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = svpn ->
    zero_extend' 64 (concat_vec (tlb_get_ppn 39 (pw_tlb_entry root_ppn (mword_of_int 0)) svpn) (subrange_vec_dec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 14 : mword 6) ('b"000"))))))) (Z.sub pagesize_bits 1) 0)) = (add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 14 : mword 6) ('b"000")))) ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4) (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4) (uint (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 14 : mword 6) ('b"000"))))))) (uint (to_bits 64 8)) = PMP_Match ->
    is_aligned_vaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 14 : mword 6) ('b"000")))))) 8 = true ->
    is_aligned_paddr (Physaddr (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 14 : mword 6) ('b"000"))))))) 8 = true ->
    (* slot 12: x16 at sp+120 *)
    neq_vec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 15 : mword 6) ('b"000"))))))) (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 15 : mword 6) ('b"000"))))))) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec (subrange_vec_dec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 15 : mword 6) ('b"000"))))))) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = svpn ->
    zero_extend' 64 (concat_vec (tlb_get_ppn 39 (pw_tlb_entry root_ppn (mword_of_int 0)) svpn) (subrange_vec_dec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 15 : mword 6) ('b"000"))))))) (Z.sub pagesize_bits 1) 0)) = (add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 15 : mword 6) ('b"000")))) ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4) (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4) (uint (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 15 : mword 6) ('b"000"))))))) (uint (to_bits 64 8)) = PMP_Match ->
    is_aligned_vaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 15 : mword 6) ('b"000")))))) 8 = true ->
    is_aligned_paddr (Physaddr (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 15 : mword 6) ('b"000"))))))) 8 = true ->
    (* slot 13: x17 at sp+128 *)
    neq_vec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 16 : mword 6) ('b"000"))))))) (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 16 : mword 6) ('b"000"))))))) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec (subrange_vec_dec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 16 : mword 6) ('b"000"))))))) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = svpn ->
    zero_extend' 64 (concat_vec (tlb_get_ppn 39 (pw_tlb_entry root_ppn (mword_of_int 0)) svpn) (subrange_vec_dec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 16 : mword 6) ('b"000"))))))) (Z.sub pagesize_bits 1) 0)) = (add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 16 : mword 6) ('b"000")))) ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4) (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4) (uint (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 16 : mword 6) ('b"000"))))))) (uint (to_bits 64 8)) = PMP_Match ->
    is_aligned_vaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 16 : mword 6) ('b"000")))))) 8 = true ->
    is_aligned_paddr (Physaddr (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 16 : mword 6) ('b"000"))))))) 8 = true ->
    (* slot 14: x28 at sp+216 *)
    neq_vec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 27 : mword 6) ('b"000"))))))) (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 27 : mword 6) ('b"000"))))))) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec (subrange_vec_dec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 27 : mword 6) ('b"000"))))))) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = svpn ->
    zero_extend' 64 (concat_vec (tlb_get_ppn 39 (pw_tlb_entry root_ppn (mword_of_int 0)) svpn) (subrange_vec_dec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 27 : mword 6) ('b"000"))))))) (Z.sub pagesize_bits 1) 0)) = (add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 27 : mword 6) ('b"000")))) ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4) (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4) (uint (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 27 : mword 6) ('b"000"))))))) (uint (to_bits 64 8)) = PMP_Match ->
    is_aligned_vaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 27 : mword 6) ('b"000")))))) 8 = true ->
    is_aligned_paddr (Physaddr (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 27 : mword 6) ('b"000"))))))) 8 = true ->
    (* slot 15: x29 at sp+224 *)
    neq_vec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 28 : mword 6) ('b"000"))))))) (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 28 : mword 6) ('b"000"))))))) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec (subrange_vec_dec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 28 : mword 6) ('b"000"))))))) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = svpn ->
    zero_extend' 64 (concat_vec (tlb_get_ppn 39 (pw_tlb_entry root_ppn (mword_of_int 0)) svpn) (subrange_vec_dec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 28 : mword 6) ('b"000"))))))) (Z.sub pagesize_bits 1) 0)) = (add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 28 : mword 6) ('b"000")))) ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4) (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4) (uint (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 28 : mword 6) ('b"000"))))))) (uint (to_bits 64 8)) = PMP_Match ->
    is_aligned_vaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 28 : mword 6) ('b"000")))))) 8 = true ->
    is_aligned_paddr (Physaddr (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 28 : mword 6) ('b"000"))))))) 8 = true ->
    (* slot 16: x30 at sp+232 *)
    neq_vec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 29 : mword 6) ('b"000"))))))) (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 29 : mword 6) ('b"000"))))))) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec (subrange_vec_dec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 29 : mword 6) ('b"000"))))))) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = svpn ->
    zero_extend' 64 (concat_vec (tlb_get_ppn 39 (pw_tlb_entry root_ppn (mword_of_int 0)) svpn) (subrange_vec_dec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 29 : mword 6) ('b"000"))))))) (Z.sub pagesize_bits 1) 0)) = (add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 29 : mword 6) ('b"000")))) ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4) (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4) (uint (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 29 : mword 6) ('b"000"))))))) (uint (to_bits 64 8)) = PMP_Match ->
    is_aligned_vaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 29 : mword 6) ('b"000")))))) 8 = true ->
    is_aligned_paddr (Physaddr (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 29 : mword 6) ('b"000"))))))) 8 = true ->
    (* slot 17: x31 at sp+240 *)
    neq_vec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 30 : mword 6) ('b"000"))))))) (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 30 : mword 6) ('b"000"))))))) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec (subrange_vec_dec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 30 : mword 6) ('b"000"))))))) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = svpn ->
    zero_extend' 64 (concat_vec (tlb_get_ppn 39 (pw_tlb_entry root_ppn (mword_of_int 0)) svpn) (subrange_vec_dec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 30 : mword 6) ('b"000"))))))) (Z.sub pagesize_bits 1) 0)) = (add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 30 : mword 6) ('b"000")))) ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4) (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4) (uint (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 30 : mword 6) ('b"000"))))))) (uint (to_bits 64 8)) = PMP_Match ->
    is_aligned_vaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 30 : mword 6) ('b"000")))))) 8 = true ->
    is_aligned_paddr (Physaddr (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 30 : mword 6) ('b"000"))))))) 8 = true ->
    hw_config -∗
    minstret_inv -∗
    kernel_text -∗
    acq_frame m satp0 mie_v mdv0 menvcfg0 mip_v meip seip pmpcfg0 pmpaddr00 tlbvec -∗
    pc_is acq_pc1 -∗
    gpr_file m -∗
    ( acq_frame m satp0 mie_v mdv0 menvcfg0 mip_v meip seip pmpcfg0 pmpaddr00 tlbvec -∗
      pc_is (mword_of_int (KernelSyms.acquire + 0x2) : mword 64) -∗
      gpr_file (acq_m1 m) -∗
      WP (Loop : expr riscv_lang) @ E {{ Phi }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Phi }}.
  Proof.
    intros HN Hmode Hasid Hmm HPBMTE Hpmm Hhit5 Hhith Hhit0 Hpmpf HW HR Hpmpacq Hmask Hlpe0
      Hcanon1 Hvpn1 Hident1 Hrange1 Halv1 Halp1 Hcanon2 Hvpn2 Hident2 Hrange2 Halv2 Halp2 Hcanon3 Hvpn3 Hident3 Hrange3 Halv3 Halp3 Hcanon4 Hvpn4 Hident4 Hrange4 Halv4 Halp4 Hcanon5 Hvpn5 Hident5 Hrange5 Halv5 Halp5 Hcanon6 Hvpn6 Hident6 Hrange6 Halv6 Halp6 Hcanon7 Hvpn7 Hident7 Hrange7 Halv7 Halp7 Hcanon8 Hvpn8 Hident8 Hrange8 Halv8 Halp8 Hcanon9 Hvpn9 Hident9 Hrange9 Halv9 Halp9 Hcanon10 Hvpn10 Hident10 Hrange10 Halv10 Halp10 Hcanon11 Hvpn11 Hident11 Hrange11 Halv11 Halp11 Hcanon12 Hvpn12 Hident12 Hrange12 Halv12 Halp12 Hcanon13 Hvpn13 Hident13 Hrange13 Halv13 Halp13 Hcanon14 Hvpn14 Hident14 Hrange14 Halv14 Halp14 Hcanon15 Hvpn15 Hident15 Hrange15 Halv15 Halp15 Hcanon16 Hvpn16 Hident16 Hrange16 Halv16 Halp16 Hcanon17 Hvpn17 Hident17 Hrange17 Halv17 Halp17.
    iIntros "#Hhw #Hinv #Htext HP Hpc Hfile Hcont".
    iRevert "HP Hpc Hfile Hcont".
    iLöb as "IH".
    iIntros "HP Hpc Hfile Hcont".
    iDestruct "HP" as "(Hhs & Hpriv & Hsatp & Hmsx & Hmie & Hmdl & Hmenv & Hmip & Hmeip & Hseip
                       & Hstvec & Hsepcx & Hscausex & Hstvalx & Hpmpc & Hpmpa & Htlb & Hwins)".
    iDestruct "Hmsx" as (ms) "[Hms %Hmsf]".
    pose proof Hmsf as Hmsf'. destruct Hmsf' as (HSIE1 & HMPRV0 & HSXL & HMXR & HTSR).
    iDestruct "Hsepcx" as (sepc_old) "Hsepc".
    iDestruct "Hscausex" as (scause_old) "Hscause".
    iDestruct "Hstvalx" as (stval_old) "Hstval".
    iDestruct "Hwins" as (w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17) "(Hw1 & Hw2 & Hw3 & Hw4 & Hw5 & Hw6 & Hw7 & Hw8 & Hw9 & Hw10 & Hw11 & Hw12 & Hw13 & Hw14 & Hw15 & Hw16 & Hw17)".
    destruct (s_dispatch mip_v meip seip mie_v mdv0 ms) as [[i p] |] eqn:Hdres.
    - (* ---- the interrupt fires: trap -> kernelvec -> SRET -> Löb ---- *)
      pose proof (s_dispatch_Some_S _ _ _ _ _ _ _ _ Hdres); subst p.
      iPoseProof "Hhw" as "#Hhwc".
      iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
        "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & %HmisaS & %HmisaC &
          %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np)".
      pose proof (elp_no_lp elp0 Help_np) as Help0.
      iDestruct "Hpc" as "[Hpcr Hnpc]".
      iApply (wp_exec_step_interrupt_inv E Phi HN with "Hinv Hhs").
      iIntros (σ ns κs nt) "Hsi".
      iDestruct (dispatch_S_from_regs σ ns κs nt misa0 mip_v mie_v mdv0 ms meip seip
                   HmisaS Hmm
                   with "Hsi Hmisa Hmip Hmeip Hseip Hmie Hmdl Hms") as %Hdisp0.
      rewrite Hdres in Hdisp0.
      iDestruct "Hsi" as "[Hreg Hmem]".
      iDestruct (reg_valid with "Hreg Hpcr") as %Lpc.
      iDestruct (reg_valid with "Hreg Hpriv") as %Lpriv.
      iDestruct (reg_valid with "Hreg Hms") as %Lms.
      iDestruct (reg_valid with "Hreg Hscause") as %Lsc.
      iDestruct (reg_valid with "Hreg Hstvec") as %Lstvec.
      iDestruct (reg_valid_dq with "Hreg Help") as %Lelp.
      iDestruct (reg_valid_dq with "Hreg Hmisa") as %Lmisa.
      assert (HmisaS' : eq_vec (_get_Misa_S (register_lookup misa σ.(sregs))) ('b"1") = true)
        by (rewrite Lmisa; exact HmisaS).
      assert (Htvd : trapVectorMode_forwards
                       (_get_Mtvec_Mode (mword_of_int KernelSyms.kernelvec : mword 64)) = TV_Direct)
        by (vm_compute; reflexivity).
      pose proof (exec_run_hart_active_pending σ i Supervisor Lpriv Hdisp0) as Hha.
      pose proof (exec_handle_interrupt_S σ i acq_pc1 ms scause_old
                    (mword_of_int KernelSyms.kernelvec) elp0
                    Lpriv Lms Lsc Lstvec Lelp HmisaS' Htvd Lpc) as Hhi.
      match type of Hhi with _ = Some (_, ?T) => set (s_trap := T) in Hhi end.
      (* thread the trap's writes through the ghost cells, in tower order *)
      pose (ms_e := update_subrange_vec_dec ms 23 23 elp0).
      pose (c1v := update_subrange_vec_dec scause_old (64 - 1) (64 - 1)
                     (bool_to_bit (trapCause_is_interrupt (Interrupt i)))).
      pose (c2v := update_subrange_vec_dec c1v (64 - 2) 0
                     (zero_extend' (64 - 1) (trapCause_bits_forwards (Interrupt i)))).
      pose (ms_a := update_subrange_vec_dec ms_e 5 5 (_get_Mstatus_SIE ms_e)).
      pose (ms_b := update_subrange_vec_dec ms_a 1 1 ('b"0")).
      pose (ms_c := update_subrange_vec_dec ms_b 8 8 ('b"1")).
      iMod (reg_update _ mstatus _ ms_e with "Hreg Hms") as "[Hreg Hms]".
      assert (Hlkelp : register_lookup elp (register_set mstatus ms_e σ.(sregs))
                       = landing_pad_bits_backwards NO_LP_EXPECTED).
      { rewrite irrelevant_register_set; [ rewrite Lelp; exact Help0 | vm_compute; reflexivity ]. }
      iDestruct (reg_interp_set_same _ elp _ Hlkelp with "Hreg") as "Hreg".
      iMod (reg_update _ scause _ c1v with "Hreg Hscause") as "[Hreg Hscause]".
      iMod (reg_update _ scause _ c2v with "Hreg Hscause") as "[Hreg Hscause]".
      iMod (reg_update _ mstatus _ ms_a with "Hreg Hms") as "[Hreg Hms]".
      iMod (reg_update _ mstatus _ ms_b with "Hreg Hms") as "[Hreg Hms]".
      iMod (reg_update _ mstatus _ ms_c with "Hreg Hms") as "[Hreg Hms]".
      iMod (reg_update _ stval _ (zeros' 64) with "Hreg Hstval") as "[Hreg Hstval]".
      iMod (reg_update _ sepc _ acq_pc1 with "Hreg Hsepc") as "[Hreg Hsepc]".
      iMod (reg_update _ cur_privilege _ Supervisor with "Hreg Hpriv") as "[Hreg Hpriv]".
      iMod (reg_update _ nextPC _ (stvec_base (mword_of_int KernelSyms.kernelvec : mword 64))
              with "Hreg Hnpc") as "[Hreg Hnpc]".
      iModIntro.
      iExists i, Supervisor, s_trap.
      iSplitR; [iPureIntro; exact Hha |].
      iSplitR; [iPureIntro; exact Hhi |].
      assert (LpcT : register_lookup PC s_trap.(sregs) = acq_pc1).
      { unfold s_trap. lk. exact Lpc. }
      rewrite LpcT.
      iSplitL "Hpcr"; [iExact "Hpcr" |].
      iSplitL "Hreg Hmem".
      { unfold s_trap, set_reg; cbn [sregs mem]. iFrame "Hreg Hmem". }
      iNext.
      iIntros "Hhs Hpcr".
      assert (LnT : register_lookup nextPC s_trap.(sregs)
                    = stvec_base (mword_of_int KernelSyms.kernelvec : mword 64)).
      { unfold s_trap. lk. reflexivity. }
      assert (Hsb : stvec_base (mword_of_int KernelSyms.kernelvec : mword 64)
                    = (mword_of_int KernelSyms.kernelvec : mword 64))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite LnT Hsb) in "Hpcr".
      iEval (rewrite Hsb) in "Hnpc".
      assert (Htm : ms_c = trap_ms elp0 ms) by reflexivity.
      iEval (rewrite Htm) in "Hms".
      assert (Hst : sret_tgt acq_pc1 = acq_pc1) by (apply bv_eq; vm_compute; reflexivity).
      (* ---- the whole kernelvec handler (steady-state, TLB hits) ---- *)
      iApply (wp_kernelvec_hit root_ppn svpn m satp0 (trap_ms elp0 ms) mie_v mdv0 menvcfg0
                acq_pc1 pmpcfg0 pmpaddr00 tlbvec w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 E Phi
                HN Hmode Hasid
                (trap_ms_SIE_false elp0 ms)
                (trap_ms_MPRV_false elp0 ms HMPRV0)
                (trap_ms_SXL_eq elp0 ms HSXL)
                Hmm HPBMTE
                (trap_ms_MXR_true elp0 ms HMXR)
                Hpmm Hhit5 Hhith Hpmpf HW HR Hmask
                (trap_ms_TSR_false elp0 ms HTSR)
                (sret_newpriv_trap_ms elp0 ms)
                Hlpe0
                Hcanon1 Hvpn1 Hident1 Hrange1 Halv1 Hcanon2 Hvpn2 Hident2 Hrange2 Halv2 Hcanon3 Hvpn3 Hident3 Hrange3 Halv3 Hcanon4 Hvpn4 Hident4 Hrange4 Halv4 Hcanon5 Hvpn5 Hident5 Hrange5 Halv5 Hcanon6 Hvpn6 Hident6 Hrange6 Halv6 Hcanon7 Hvpn7 Hident7 Hrange7 Halv7 Hcanon8 Hvpn8 Hident8 Hrange8 Halv8 Hcanon9 Hvpn9 Hident9 Hrange9 Halv9 Hcanon10 Hvpn10 Hident10 Hrange10 Halv10 Hcanon11 Hvpn11 Hident11 Hrange11 Halv11 Hcanon12 Hvpn12 Hident12 Hrange12 Halv12 Hcanon13 Hvpn13 Hident13 Hrange13 Halv13 Hcanon14 Hvpn14 Hident14 Hrange14 Halv14 Hcanon15 Hvpn15 Hident15 Hrange15 Halv15 Hcanon16 Hvpn16 Hident16 Hrange16 Halv16 Hcanon17 Hvpn17 Hident17 Hrange17 Halv17
                with "Hhw Hinv Hhs Hpriv Hsatp Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlb Hsepc
                      [$Hpcr $Hnpc] Hfile Htext Hw1 Hw2 Hw3 Hw4 Hw5 Hw6 Hw7 Hw8 Hw9 Hw10 Hw11 Hw12 Hw13 Hw14 Hw15 Hw16 Hw17").
      iIntros "Hhs Hpriv Hsatp Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlb Hsepc Hpc2 Hfile Hw1 Hw2 Hw3 Hw4 Hw5 Hw6 Hw7 Hw8 Hw9 Hw10 Hw11 Hw12 Hw13 Hw14 Hw15 Hw16 Hw17".
      iEval (rewrite Hst) in "Hpc2".
      (* ---- re-establish the invariant and apply the Löb IH ---- *)
      iApply ("IH" with "[Hhs Hpriv Hsatp Hms Hmie Hmdl Hmenv Hmip Hmeip Hseip Hstvec Hsepc
                          Hscause Hstval Hpmpc Hpmpa Htlb Hw1 Hw2 Hw3 Hw4 Hw5 Hw6 Hw7 Hw8 Hw9 Hw10 Hw11 Hw12 Hw13 Hw14 Hw15 Hw16 Hw17] Hpc2 Hfile Hcont").
      iFrame "Hhs Hpriv Hsatp Hmie Hmdl Hmenv Hmip Hmeip Hseip Hstvec Hpmpc Hpmpa Htlb".
      iSplitL "Hms".
      { iExists (sret_ms5 (trap_ms elp0 ms)). iFrame "Hms".
        iPureIntro. exact (acq_ms_facts_roundtrip elp0 ms Hmsf). }
      iSplitL "Hsepc". { iExists acq_pc1. iFrame "Hsepc". }
      iSplitL "Hscause". { iExists c2v. iFrame "Hscause". }
      iSplitL "Hstval". { iExists (zeros' 64). iFrame "Hstval". }
      iExists (m !!! Regidx (mword_of_int 1 : mword 5)), (m !!! Regidx (mword_of_int 3 : mword 5)), (m !!! Regidx (mword_of_int 5 : mword 5)), (m !!! Regidx (mword_of_int 6 : mword 5)), (m !!! Regidx (mword_of_int 7 : mword 5)), (m !!! Regidx (mword_of_int 10 : mword 5)), (m !!! Regidx (mword_of_int 11 : mword 5)), (m !!! Regidx (mword_of_int 12 : mword 5)), (m !!! Regidx (mword_of_int 13 : mword 5)), (m !!! Regidx (mword_of_int 14 : mword 5)), (m !!! Regidx (mword_of_int 15 : mword 5)), (m !!! Regidx (mword_of_int 16 : mword 5)), (m !!! Regidx (mword_of_int 17 : mword 5)), (m !!! Regidx (mword_of_int 28 : mword 5)), (m !!! Regidx (mword_of_int 29 : mword 5)), (m !!! Regidx (mword_of_int 30 : mword 5)), (m !!! Regidx (mword_of_int 31 : mword 5)).
      iFrame "Hw1 Hw2 Hw3 Hw4 Hw5 Hw6 Hw7 Hw8 Hw9 Hw10 Hw11 Hw12 Hw13 Hw14 Hw15 Hw16 Hw17".
    - (* ---- no interrupt: the instruction executes ---- *)
      iApply (wp_acq_caddi_intr root_ppn E Phi m satp0 ms mie_v mdv0 menvcfg0 mip_v meip seip
                pmpcfg0 pmpaddr00 tlbvec HN Hmode Hasid HSXL Hmm Hdres Hhit0 Hpmpacq
                with "Hhw Hinv Hhs Hpriv Hsatp Hms Hmie Hmdl Hmenv Hmip Hmeip Hseip Hpmpc Hpmpa
                      Htlb Hpc Hfile Htext").
      iIntros "Hhs Hpriv Hsatp Hms Hmie Hmdl Hmenv Hmip Hmeip Hseip Hpmpc Hpmpa Htlb Hpc Hfile".
      iApply ("Hcont" with "[Hhs Hpriv Hsatp Hms Hmie Hmdl Hmenv Hmip Hmeip Hseip Hstvec Hsepc
                             Hscause Hstval Hpmpc Hpmpa Htlb Hw1 Hw2 Hw3 Hw4 Hw5 Hw6 Hw7 Hw8 Hw9 Hw10 Hw11 Hw12 Hw13 Hw14 Hw15 Hw16 Hw17] Hpc [Hfile]").
      2:{ unfold acq_m1. iExact "Hfile". }
      iFrame "Hhs Hpriv Hsatp Hmie Hmdl Hmenv Hmip Hmeip Hseip Hstvec Hpmpc Hpmpa Htlb".
      iSplitL "Hms".
      { iExists ms. iFrame "Hms". iPureIntro. exact Hmsf. }
      iSplitL "Hsepc". { iExists sepc_old. iFrame "Hsepc". }
      iSplitL "Hscause". { iExists scause_old. iFrame "Hscause". }
      iSplitL "Hstval". { iExists stval_old. iFrame "Hstval". }
      iExists w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15, w16, w17.
      iFrame "Hw1 Hw2 Hw3 Hw4 Hw5 Hw6 Hw7 Hw8 Hw9 Hw10 Hw11 Hw12 Hw13 Hw14 Hw15 Hw16 Hw17".
  Qed.

End WpIntrStep.
