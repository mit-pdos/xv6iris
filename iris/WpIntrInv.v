(* WpIntrInv.v -- an ABSTRACT S-mode interrupt invariant.

   The invariant [intr_inv F handler] owns the sstatus (mstatus) and stvec
   registers and states the S-mode interrupt-safety discipline:

     EITHER  interrupts are disabled (sstatus.SIE = 0), so no trap can fire
             and there is nothing more to prove;

     OR      interrupts are enabled (sstatus.SIE = 1 -- together with the
             ambient MPRV/SXL/MXR/TSR facts of [acq_ms_facts]), stvec points
             at [handler], and we hold [intr_handler_spec handler F]: a
             persistent WP obligation saying that taking the interrupt --
             jumping to [handler] in the trapped mstatus -- runs the handler
             and returns IDEMPOTENTLY to the interrupted pc with the SIE=1
             facts (hence the invariant) re-established.  [F] is the frame of
             everything else the handler consumes and hands back unchanged.

   [intr_handler_spec] is a simplified, address-agnostic distillation of what
   kernelvec does (save 17 regs, kerneltrap, restore, SRET): it hides the
   17-slot geometry inside [F] and exposes only the round-trip contract that a
   client needs to close a Loeb loop across an interrupt.

   We prove
     - [intr_inv_establish]: the invariant can be created whenever stvec ->
       kernelvec and kernelvec satisfies the spec; and
     - [kernelvec_handler_spec]: kernelvec's WP ([wp_kernelvec_hit] + the
       [trap_ms]/[sret_ms5] round-trip lemmas) DOES satisfy the spec, for the
       concrete kernelvec frame [F_kv]. *)
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
Require Import WpKernelvecNew.
Require Import WpIntrBits WpIntrCore WpIntrStep.
From Kernel Require KernelInstrs.
From Kernel Require KernelSyms.
Local Open Scope Z_scope.
Import Defs.

Section WpIntrInv.
  Context `{!riscvGS Sig}.

  (* The mstatus fact set carried across the round trip: SIE=1 (interrupts
     enabled), MPRV=0, SXL=2, MXR=0, TSR=0.  Reused from WpIntrStep. *)
  Notation ms_pre_facts := acq_ms_facts.

  (* --------------------------------------------------------------------- *)
  (* The concrete kernelvec frame: everything [wp_kernelvec_hit] consumes and
     returns beyond the mstatus / sepc / stvec / pc / privilege / hart_state
     that the handler spec threads explicitly.  The 17 caller-saved stack
     windows are existential over their CONTENTS (the round trip overwrites
     them with the restored register values), so [F_kv] is preserved as a
     whole.  hw_config / minstret_inv / kernel_text are persistent. *)
  Definition F_kv (root_ppn : mword 44) (svpn : mword 27)
      (m : gmap regidx (mword 64))
      (menvcfg0 : mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (pmpaddr00 : type_of_register pmpaddr_n)
      : iProp Sig :=
    (hw_config ∗ minstret_inv ∗ kernel_text ∗
     menvcfg ↦ᵣ menvcfg0 ∗
     pmpcfg_n ↦ᵣ pmpcfg0 ∗
     pmpaddr_n ↦ᵣ pmpaddr00 ∗
     tlb_inv root_ppn ∗
     gpr_file m ∗
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

  (* --------------------------------------------------------------------- *)
  (* The abstract handler contract.  Persistent (□), so it lives freely inside
     the invariant.  Reading: for any interrupted pc [pc0] (instruction-
     aligned, so [sret_tgt pc0 = pc0]) and any mstatus [ms] with the SIE=1
     fact set, if we are AT [handler] in the trapped mstatus [trap_ms elp_v ms]
     with sepc = pc0 and the frame [F], then the machine returns to pc0 with
     mstatus = [sret_ms5 (trap_ms elp_v ms)] (SIE restored to 1 by
     [roundtrip_SIE]) and [F] intact -- exactly what re-establishing the
     invariant and closing a Loeb loop needs. *)
  Definition intr_handler_spec (handler : mword 64) (F : iProp Sig) : iProp Sig :=
    (□ ∀ (elp_v : mword 1) (ms pc0 mie_v mdv0 : mword 64) E (Φ : mval -> iProp Sig),
        ⌜ ↑minstretN ⊆ E ⌝ -∗
        ⌜ ms_pre_facts ms ⌝ -∗
        ⌜ sret_tgt pc0 = pc0 ⌝ -∗
        ⌜ and_vec mie_v (not_vec mdv0) = zeros' 64 ⌝ -∗
        hart_state ↦ᵣ HART_ACTIVE tt -∗
        cur_privilege ↦ᵣ Supervisor -∗
        mstatus ↦ᵣ trap_ms elp_v ms -∗
        mie ↦ᵣ mie_v -∗
        mideleg ↦ᵣ mdv0 -∗
        sepc ↦ᵣ pc0 -∗
        stvec ↦ᵣ handler -∗
        pc_is handler -∗
        F -∗
        ( hart_state ↦ᵣ HART_ACTIVE tt -∗
          cur_privilege ↦ᵣ Supervisor -∗
          mstatus ↦ᵣ sret_ms5 (trap_ms elp_v ms) -∗
          mie ↦ᵣ mie_v -∗
          mideleg ↦ᵣ mdv0 -∗
          (∃ v : mword 64, sepc ↦ᵣ v) -∗
          stvec ↦ᵣ handler -∗
          pc_is pc0 -∗
          F -∗
          WP (Loop : expr riscv_lang) @ E {{ Φ }} ) -∗
        WP (Loop : expr riscv_lang) @ E {{ Φ }})%I.

  Global Instance intr_handler_spec_persistent handler F :
    Persistent (intr_handler_spec handler F).
  Proof. apply _. Qed.

  (* --------------------------------------------------------------------- *)
  (* THE INVARIANT: owns sstatus (mstatus) and stvec; either interrupts are
     off, or they are on and the handler spec holds at [handler]. *)
  Definition intr_inv (F : iProp Sig) (handler : mword 64) : iProp Sig :=
    (∃ ms : mword 64,
       mstatus ↦ᵣ ms ∗
       ( (⌜ eq_vec (_get_Mstatus_SIE ms) ('b"1") = false ⌝ ∗ (∃ v : mword 64, stvec ↦ᵣ v))
         ∨ (⌜ ms_pre_facts ms ⌝ ∗ stvec ↦ᵣ handler ∗ intr_handler_spec handler F) ))%I.

  (* ===================================================================== *)
  (* Establishing the invariant when stvec -> kernelvec.                    *)
  (* ===================================================================== *)
  Lemma intr_inv_establish (F : iProp Sig) (ms : mword 64) :
    ms_pre_facts ms ->
    intr_handler_spec (mword_of_int KernelSyms.kernelvec : mword 64) F -∗
    mstatus ↦ᵣ ms -∗
    stvec ↦ᵣ (mword_of_int KernelSyms.kernelvec : mword 64) -∗
    intr_inv F (mword_of_int KernelSyms.kernelvec : mword 64).
  Proof.
    intros Hfacts. iIntros "#Hspec Hms Hstvec".
    iExists ms. iFrame "Hms". iRight. iFrame "Hstvec Hspec".
    iPureIntro. exact Hfacts.
  Qed.

  (* ===================================================================== *)
  (* kernelvec satisfies the handler spec.  This is [wp_kernelvec_hit] with
     the entering mstatus specialized to [trap_ms elp_v ms]: the six mstatus /
     SRET-privilege side conditions are DISCHARGED from [ms_pre_facts ms] via
     the WpIntrBits round-trip lemmas, and the returned pc [sret_tgt pc0]
     collapses to [pc0] under the instruction-alignment premise. *)
  Lemma kernelvec_handler_spec (root_ppn : mword 44) (svpn : mword 27)
      (m : gmap regidx (mword 64))
      (menvcfg0 : mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (pmpaddr00 : type_of_register pmpaddr_n)
      (region_pte : PMA_Region) :
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    pmm_mode_backwards (_get_MEnvcfg_PMM menvcfg0) = PMM_Disabled ->
    (* the walk's PTE read *)
    pmp_tor0_pte_read pmpcfg0 pmpaddr00 (pte_paddr root_ppn) ->
    (forall pmar0, pma_allows_all pmar0 ->
       matching_pma_region pmar0 (Physaddr (pte_paddr root_ppn)) 8 = Some region_pte /\
       (override_PMA (PMA_Region_attributes region_pte) PBMT_PMA).(PMA_supports_pte_read) = true) ->
    is_aligned_paddr (Physaddr (pte_paddr root_ppn)) 8 = true ->
    (* PMP: TOR entry 0 grants X on the whole kernelvec text + R/W on the frame *)
    (forall A : Z, kv_text_pc A = true -> pmp_tor0_sfetch_all pmpcfg0 pmpaddr00 (mword_of_int A)) ->
    eq_vec (_get_Pmpcfg_ent_W (vec_access_dec pmpcfg0 0)) ('b"1") = true ->
    eq_vec (_get_Pmpcfg_ent_R (vec_access_dec pmpcfg0 0)) ('b"1") = true ->
    (* stack-page geometry (symbolic sp; svpn = its Sv39 VPN) *)
    and_vec (sign_extend' (57 - 12) svpn) (not_vec (mword_of_int 0x3FFFF : mword 45)) = (mword_of_int 0x80000 : mword 45) ->
    subrange_vec_dec svpn 26 18 = (mword_of_int 2 : mword 9) ->
    sign_extend' 45 (and_vec svpn (not_vec (zero_extend' 27 (ones 18)))) = (mword_of_int 0x80000 : mword 45) ->
    zero_extend' 44 (and_vec (sdata_ppn_out svpn) (not_vec (zero_extend' 44 (ones 18)))) = (mword_of_int 0x80000 : mword 44) ->
    (* SRET facts *)
    _get_MEnvcfg_LPE menvcfg0 = ('b"0") ->
    (* slot 1: x1 at sp+0 *)
    neq_vec (bits_of_virtaddr (Virtaddr (((kv_sp1 m))))) (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr (((kv_sp1 m))))) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec (subrange_vec_dec (bits_of_virtaddr (Virtaddr (((kv_sp1 m))))) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = svpn ->
    zero_extend' 64 (concat_vec (tlb_get_ppn 39 (pw_tlb_entry root_ppn (mword_of_int 0)) svpn) (subrange_vec_dec (bits_of_virtaddr (Virtaddr (((kv_sp1 m))))) (Z.sub pagesize_bits 1) 0)) = ((kv_sp1 m)) ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4) (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4) (uint ((((kv_sp1 m))))) (uint (to_bits 64 8)) = PMP_Match ->
    is_aligned_vaddr (Virtaddr (((kv_sp1 m)))) 8 = true ->
    (* slot 2: x3 at sp+16 *)
    neq_vec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000"))))))) (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000"))))))) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec (subrange_vec_dec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000"))))))) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = svpn ->
    zero_extend' 64 (concat_vec (tlb_get_ppn 39 (pw_tlb_entry root_ppn (mword_of_int 0)) svpn) (subrange_vec_dec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000"))))))) (Z.sub pagesize_bits 1) 0)) = (add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000")))) ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4) (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4) (uint (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000"))))))) (uint (to_bits 64 8)) = PMP_Match ->
    (* slot 3: x5 at sp+32 *)
    neq_vec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 4 : mword 6) ('b"000"))))))) (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 4 : mword 6) ('b"000"))))))) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec (subrange_vec_dec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 4 : mword 6) ('b"000"))))))) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = svpn ->
    zero_extend' 64 (concat_vec (tlb_get_ppn 39 (pw_tlb_entry root_ppn (mword_of_int 0)) svpn) (subrange_vec_dec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 4 : mword 6) ('b"000"))))))) (Z.sub pagesize_bits 1) 0)) = (add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 4 : mword 6) ('b"000")))) ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4) (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4) (uint (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 4 : mword 6) ('b"000"))))))) (uint (to_bits 64 8)) = PMP_Match ->
    (* slot 4: x6 at sp+40 *)
    neq_vec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 5 : mword 6) ('b"000"))))))) (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 5 : mword 6) ('b"000"))))))) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec (subrange_vec_dec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 5 : mword 6) ('b"000"))))))) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = svpn ->
    zero_extend' 64 (concat_vec (tlb_get_ppn 39 (pw_tlb_entry root_ppn (mword_of_int 0)) svpn) (subrange_vec_dec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 5 : mword 6) ('b"000"))))))) (Z.sub pagesize_bits 1) 0)) = (add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 5 : mword 6) ('b"000")))) ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4) (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4) (uint (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 5 : mword 6) ('b"000"))))))) (uint (to_bits 64 8)) = PMP_Match ->
    (* slot 5: x7 at sp+48 *)
    neq_vec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 6 : mword 6) ('b"000"))))))) (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 6 : mword 6) ('b"000"))))))) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec (subrange_vec_dec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 6 : mword 6) ('b"000"))))))) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = svpn ->
    zero_extend' 64 (concat_vec (tlb_get_ppn 39 (pw_tlb_entry root_ppn (mword_of_int 0)) svpn) (subrange_vec_dec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 6 : mword 6) ('b"000"))))))) (Z.sub pagesize_bits 1) 0)) = (add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 6 : mword 6) ('b"000")))) ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4) (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4) (uint (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 6 : mword 6) ('b"000"))))))) (uint (to_bits 64 8)) = PMP_Match ->
    (* slot 6: x10 at sp+72 *)
    neq_vec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 9 : mword 6) ('b"000"))))))) (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 9 : mword 6) ('b"000"))))))) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec (subrange_vec_dec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 9 : mword 6) ('b"000"))))))) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = svpn ->
    zero_extend' 64 (concat_vec (tlb_get_ppn 39 (pw_tlb_entry root_ppn (mword_of_int 0)) svpn) (subrange_vec_dec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 9 : mword 6) ('b"000"))))))) (Z.sub pagesize_bits 1) 0)) = (add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 9 : mword 6) ('b"000")))) ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4) (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4) (uint (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 9 : mword 6) ('b"000"))))))) (uint (to_bits 64 8)) = PMP_Match ->
    (* slot 7: x11 at sp+80 *)
    neq_vec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 10 : mword 6) ('b"000"))))))) (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 10 : mword 6) ('b"000"))))))) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec (subrange_vec_dec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 10 : mword 6) ('b"000"))))))) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = svpn ->
    zero_extend' 64 (concat_vec (tlb_get_ppn 39 (pw_tlb_entry root_ppn (mword_of_int 0)) svpn) (subrange_vec_dec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 10 : mword 6) ('b"000"))))))) (Z.sub pagesize_bits 1) 0)) = (add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 10 : mword 6) ('b"000")))) ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4) (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4) (uint (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 10 : mword 6) ('b"000"))))))) (uint (to_bits 64 8)) = PMP_Match ->
    (* slot 8: x12 at sp+88 *)
    neq_vec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 11 : mword 6) ('b"000"))))))) (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 11 : mword 6) ('b"000"))))))) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec (subrange_vec_dec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 11 : mword 6) ('b"000"))))))) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = svpn ->
    zero_extend' 64 (concat_vec (tlb_get_ppn 39 (pw_tlb_entry root_ppn (mword_of_int 0)) svpn) (subrange_vec_dec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 11 : mword 6) ('b"000"))))))) (Z.sub pagesize_bits 1) 0)) = (add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 11 : mword 6) ('b"000")))) ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4) (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4) (uint (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 11 : mword 6) ('b"000"))))))) (uint (to_bits 64 8)) = PMP_Match ->
    (* slot 9: x13 at sp+96 *)
    neq_vec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 12 : mword 6) ('b"000"))))))) (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 12 : mword 6) ('b"000"))))))) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec (subrange_vec_dec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 12 : mword 6) ('b"000"))))))) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = svpn ->
    zero_extend' 64 (concat_vec (tlb_get_ppn 39 (pw_tlb_entry root_ppn (mword_of_int 0)) svpn) (subrange_vec_dec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 12 : mword 6) ('b"000"))))))) (Z.sub pagesize_bits 1) 0)) = (add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 12 : mword 6) ('b"000")))) ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4) (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4) (uint (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 12 : mword 6) ('b"000"))))))) (uint (to_bits 64 8)) = PMP_Match ->
    (* slot 10: x14 at sp+104 *)
    neq_vec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 13 : mword 6) ('b"000"))))))) (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 13 : mword 6) ('b"000"))))))) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec (subrange_vec_dec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 13 : mword 6) ('b"000"))))))) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = svpn ->
    zero_extend' 64 (concat_vec (tlb_get_ppn 39 (pw_tlb_entry root_ppn (mword_of_int 0)) svpn) (subrange_vec_dec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 13 : mword 6) ('b"000"))))))) (Z.sub pagesize_bits 1) 0)) = (add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 13 : mword 6) ('b"000")))) ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4) (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4) (uint (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 13 : mword 6) ('b"000"))))))) (uint (to_bits 64 8)) = PMP_Match ->
    (* slot 11: x15 at sp+112 *)
    neq_vec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 14 : mword 6) ('b"000"))))))) (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 14 : mword 6) ('b"000"))))))) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec (subrange_vec_dec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 14 : mword 6) ('b"000"))))))) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = svpn ->
    zero_extend' 64 (concat_vec (tlb_get_ppn 39 (pw_tlb_entry root_ppn (mword_of_int 0)) svpn) (subrange_vec_dec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 14 : mword 6) ('b"000"))))))) (Z.sub pagesize_bits 1) 0)) = (add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 14 : mword 6) ('b"000")))) ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4) (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4) (uint (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 14 : mword 6) ('b"000"))))))) (uint (to_bits 64 8)) = PMP_Match ->
    (* slot 12: x16 at sp+120 *)
    neq_vec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 15 : mword 6) ('b"000"))))))) (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 15 : mword 6) ('b"000"))))))) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec (subrange_vec_dec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 15 : mword 6) ('b"000"))))))) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = svpn ->
    zero_extend' 64 (concat_vec (tlb_get_ppn 39 (pw_tlb_entry root_ppn (mword_of_int 0)) svpn) (subrange_vec_dec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 15 : mword 6) ('b"000"))))))) (Z.sub pagesize_bits 1) 0)) = (add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 15 : mword 6) ('b"000")))) ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4) (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4) (uint (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 15 : mword 6) ('b"000"))))))) (uint (to_bits 64 8)) = PMP_Match ->
    (* slot 13: x17 at sp+128 *)
    neq_vec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 16 : mword 6) ('b"000"))))))) (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 16 : mword 6) ('b"000"))))))) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec (subrange_vec_dec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 16 : mword 6) ('b"000"))))))) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = svpn ->
    zero_extend' 64 (concat_vec (tlb_get_ppn 39 (pw_tlb_entry root_ppn (mword_of_int 0)) svpn) (subrange_vec_dec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 16 : mword 6) ('b"000"))))))) (Z.sub pagesize_bits 1) 0)) = (add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 16 : mword 6) ('b"000")))) ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4) (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4) (uint (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 16 : mword 6) ('b"000"))))))) (uint (to_bits 64 8)) = PMP_Match ->
    (* slot 14: x28 at sp+216 *)
    neq_vec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 27 : mword 6) ('b"000"))))))) (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 27 : mword 6) ('b"000"))))))) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec (subrange_vec_dec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 27 : mword 6) ('b"000"))))))) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = svpn ->
    zero_extend' 64 (concat_vec (tlb_get_ppn 39 (pw_tlb_entry root_ppn (mword_of_int 0)) svpn) (subrange_vec_dec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 27 : mword 6) ('b"000"))))))) (Z.sub pagesize_bits 1) 0)) = (add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 27 : mword 6) ('b"000")))) ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4) (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4) (uint (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 27 : mword 6) ('b"000"))))))) (uint (to_bits 64 8)) = PMP_Match ->
    (* slot 15: x29 at sp+224 *)
    neq_vec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 28 : mword 6) ('b"000"))))))) (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 28 : mword 6) ('b"000"))))))) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec (subrange_vec_dec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 28 : mword 6) ('b"000"))))))) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = svpn ->
    zero_extend' 64 (concat_vec (tlb_get_ppn 39 (pw_tlb_entry root_ppn (mword_of_int 0)) svpn) (subrange_vec_dec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 28 : mword 6) ('b"000"))))))) (Z.sub pagesize_bits 1) 0)) = (add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 28 : mword 6) ('b"000")))) ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4) (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4) (uint (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 28 : mword 6) ('b"000"))))))) (uint (to_bits 64 8)) = PMP_Match ->
    (* slot 16: x30 at sp+232 *)
    neq_vec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 29 : mword 6) ('b"000"))))))) (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 29 : mword 6) ('b"000"))))))) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec (subrange_vec_dec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 29 : mword 6) ('b"000"))))))) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = svpn ->
    zero_extend' 64 (concat_vec (tlb_get_ppn 39 (pw_tlb_entry root_ppn (mword_of_int 0)) svpn) (subrange_vec_dec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 29 : mword 6) ('b"000"))))))) (Z.sub pagesize_bits 1) 0)) = (add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 29 : mword 6) ('b"000")))) ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4) (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4) (uint (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 29 : mword 6) ('b"000"))))))) (uint (to_bits 64 8)) = PMP_Match ->
    (* slot 17: x31 at sp+240 *)
    neq_vec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 30 : mword 6) ('b"000"))))))) (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 30 : mword 6) ('b"000"))))))) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec (subrange_vec_dec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 30 : mword 6) ('b"000"))))))) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = svpn ->
    zero_extend' 64 (concat_vec (tlb_get_ppn 39 (pw_tlb_entry root_ppn (mword_of_int 0)) svpn) (subrange_vec_dec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 30 : mword 6) ('b"000"))))))) (Z.sub pagesize_bits 1) 0)) = (add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 30 : mword 6) ('b"000")))) ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4) (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4) (uint (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 30 : mword 6) ('b"000"))))))) (uint (to_bits 64 8)) = PMP_Match ->
    ⊢ intr_handler_spec (mword_of_int KernelSyms.kernelvec : mword 64)
        (F_kv root_ppn svpn m menvcfg0 pmpcfg0 pmpaddr00).
  Proof.
    intros HPBMTE Hpmm Hpmpp Hpteregion Halignp Hpmpf HW HR Hmask Hsvpn2 Hmvpn Hmppn Hlpe0
      Hcanon1 Hvpn1 Hident1 Hrange1 Halv1 Hcanon2 Hvpn2 Hident2 Hrange2 Hcanon3 Hvpn3 Hident3 Hrange3 Hcanon4 Hvpn4 Hident4 Hrange4 Hcanon5 Hvpn5 Hident5 Hrange5 Hcanon6 Hvpn6 Hident6 Hrange6 Hcanon7 Hvpn7 Hident7 Hrange7 Hcanon8 Hvpn8 Hident8 Hrange8 Hcanon9 Hvpn9 Hident9 Hrange9 Hcanon10 Hvpn10 Hident10 Hrange10 Hcanon11 Hvpn11 Hident11 Hrange11 Hcanon12 Hvpn12 Hident12 Hrange12 Hcanon13 Hvpn13 Hident13 Hrange13 Hcanon14 Hvpn14 Hident14 Hrange14 Hcanon15 Hvpn15 Hident15 Hrange15 Hcanon16 Hvpn16 Hident16 Hrange16 Hcanon17 Hvpn17 Hident17 Hrange17.
    iModIntro. iIntros (elp_v ms pc0 mie_v mdv0 E Φ) "%HN %Hfacts %Hpc0 %Hmm Hhs Hpriv Hms Hmie Hmdl Hsepc Hstvec Hpc HF Hcont".
    pose proof Hfacts as (HSIE1 & HMPRV0 & HSXL & HMXR & HTSR).
    iDestruct "HF" as "(#Hhw & #Hinv & #Htext & Hmenv & Hpmpc & Hpmpa & Htlbinv & Hfile & Hwins)".
    iDestruct "Hwins" as (w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17)
      "(Hw1 & Hw2 & Hw3 & Hw4 & Hw5 & Hw6 & Hw7 & Hw8 & Hw9 & Hw10 & Hw11 & Hw12 & Hw13 & Hw14 & Hw15 & Hw16 & Hw17)".
    iApply (wp_kernelvec root_ppn svpn m (trap_ms elp_v ms) mie_v mdv0 menvcfg0 pc0
              pmpcfg0 pmpaddr00 region_pte w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 E Φ
              HN
              (trap_ms_SIE_false elp_v ms)
              (trap_ms_MPRV_false elp_v ms HMPRV0)
              (trap_ms_SXL_eq elp_v ms HSXL)
              Hmm HPBMTE
              (trap_ms_MXR_true elp_v ms HMXR)
              Hpmm Hpmpp Hpteregion Halignp Hpmpf HW HR Hmask Hsvpn2 Hmvpn Hmppn
              (trap_ms_TSR_false elp_v ms HTSR)
              (sret_newpriv_trap_ms elp_v ms)
              Hlpe0
              Hcanon1 Hvpn1 Hident1 Hrange1 Halv1 Hcanon2 Hvpn2 Hident2 Hrange2 Hcanon3 Hvpn3 Hident3 Hrange3 Hcanon4 Hvpn4 Hident4 Hrange4 Hcanon5 Hvpn5 Hident5 Hrange5 Hcanon6 Hvpn6 Hident6 Hrange6 Hcanon7 Hvpn7 Hident7 Hrange7 Hcanon8 Hvpn8 Hident8 Hrange8 Hcanon9 Hvpn9 Hident9 Hrange9 Hcanon10 Hvpn10 Hident10 Hrange10 Hcanon11 Hvpn11 Hident11 Hrange11 Hcanon12 Hvpn12 Hident12 Hrange12 Hcanon13 Hvpn13 Hident13 Hrange13 Hcanon14 Hvpn14 Hident14 Hrange14 Hcanon15 Hvpn15 Hident15 Hrange15 Hcanon16 Hvpn16 Hident16 Hrange16 Hcanon17 Hvpn17 Hident17 Hrange17
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hsepc
                    Hpc Hfile Htext Hw1 Hw2 Hw3 Hw4 Hw5 Hw6 Hw7 Hw8 Hw9 Hw10 Hw11 Hw12 Hw13 Hw14 Hw15 Hw16 Hw17").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hsepc Hpc Hfile
             Hw1 Hw2 Hw3 Hw4 Hw5 Hw6 Hw7 Hw8 Hw9 Hw10 Hw11 Hw12 Hw13 Hw14 Hw15 Hw16 Hw17".
    iEval (rewrite Hpc0) in "Hpc".
    iApply ("Hcont" with "Hhs Hpriv Hms Hmie Hmdl [Hsepc] Hstvec Hpc [-]").
    { iExists pc0. iFrame "Hsepc". }
    iFrame "Hhw Hinv Htext Hmenv Hpmpc Hpmpa Htlbinv Hfile".
    iExists (m !!! Regidx (mword_of_int 1 : mword 5)), (m !!! Regidx (mword_of_int 3 : mword 5)), (m !!! Regidx (mword_of_int 5 : mword 5)), (m !!! Regidx (mword_of_int 6 : mword 5)), (m !!! Regidx (mword_of_int 7 : mword 5)), (m !!! Regidx (mword_of_int 10 : mword 5)), (m !!! Regidx (mword_of_int 11 : mword 5)), (m !!! Regidx (mword_of_int 12 : mword 5)), (m !!! Regidx (mword_of_int 13 : mword 5)), (m !!! Regidx (mword_of_int 14 : mword 5)), (m !!! Regidx (mword_of_int 15 : mword 5)), (m !!! Regidx (mword_of_int 16 : mword 5)), (m !!! Regidx (mword_of_int 17 : mword 5)), (m !!! Regidx (mword_of_int 28 : mword 5)), (m !!! Regidx (mword_of_int 29 : mword 5)), (m !!! Regidx (mword_of_int 30 : mword 5)), (m !!! Regidx (mword_of_int 31 : mword 5)).
    iFrame "Hw1 Hw2 Hw3 Hw4 Hw5 Hw6 Hw7 Hw8 Hw9 Hw10 Hw11 Hw12 Hw13 Hw14 Hw15 Hw16 Hw17".
  Qed.

  (* ===================================================================== *)
  (* §  The interrupt-aware single-step WRAPPER.                            *)
  (*                                                                        *)
  (* [wp_step_intr_inv] wraps the point just before an instruction at [pc0] *)
  (* under the interrupt invariant.  Opening [intr_inv F handler] it either *)
  (*   - finds interrupts disabled (SIE=0), so no interrupt can dispatch; or*)
  (*   - finds them enabled and, if an interrupt is pending, TAKES it: traps*)
  (*     to [handler] (a Direct-mode trap vector), runs the abstract handler*)
  (*     spec, returns idempotently to [pc0], re-establishes the invariant, *)
  (*     and loops (Loeb).                                                   *)
  (* Either way it eventually reaches a state with [s_dispatch = None] and   *)
  (* hands the OPENED invariant (mstatus + the SIE disjunction) plus all the *)
  (* register resources to the body, which then runs the instruction in an  *)
  (* interrupt-free context.  The kernelvec-specific 17-slot geometry lives  *)
  (* entirely inside [F] and the persistent handler spec -- this wrapper is  *)
  (* generic over [handler], [pc0] and [F]. *)
  (* ===================================================================== *)

  Lemma s_dispatch_None_of_SIE_false (mip_v : mword 64) (meip seip : mword 1)
      (mie_v mdv0 ms : mword 64) :
    eq_vec (_get_Mstatus_SIE ms) ('b"1") = false ->
    s_dispatch mip_v meip seip mie_v mdv0 ms = None.
  Proof. intros H. unfold s_dispatch. rewrite H. reflexivity. Qed.

  Lemma wp_step_intr_inv (handler pc0 : mword 64) (F : iProp Sig)
      (mie_v mdv0 mip_v : mword 64) (meip seip : mword 1)
      E (Φ : mval -> iProp Sig) :
    ↑minstretN ⊆ E ->
    and_vec mie_v (not_vec mdv0) = zeros' 64 ->
    sret_tgt pc0 = pc0 ->
    trapVectorMode_forwards (_get_Mtvec_Mode handler) = TV_Direct ->
    stvec_base handler = handler ->
    hw_config -∗
    minstret_inv -∗
    intr_inv F handler -∗
    hart_state ↦ᵣ HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ Supervisor -∗
    mie ↦ᵣ mie_v -∗
    mideleg ↦ᵣ mdv0 -∗
    mip ↦ᵣ mip_v -∗
    sig_meip ↦ᵣ meip -∗
    sig_seip ↦ᵣ seip -∗
    (∃ v : mword 64, sepc ↦ᵣ v) -∗
    (∃ v : mword 64, scause ↦ᵣ v) -∗
    (∃ v : mword 64, stval ↦ᵣ v) -∗
    F -∗
    pc_is pc0 -∗
    (∀ ms : mword 64,
       ⌜ s_dispatch mip_v meip seip mie_v mdv0 ms = None ⌝ -∗
       mstatus ↦ᵣ ms -∗
       ( (⌜ eq_vec (_get_Mstatus_SIE ms) ('b"1") = false ⌝ ∗ (∃ v : mword 64, stvec ↦ᵣ v))
         ∨ (⌜ ms_pre_facts ms ⌝ ∗ stvec ↦ᵣ handler ∗ intr_handler_spec handler F) ) -∗
       hart_state ↦ᵣ HART_ACTIVE tt -∗
       cur_privilege ↦ᵣ Supervisor -∗
       mie ↦ᵣ mie_v -∗
       mideleg ↦ᵣ mdv0 -∗
       mip ↦ᵣ mip_v -∗
       sig_meip ↦ᵣ meip -∗
       sig_seip ↦ᵣ seip -∗
       (∃ v : mword 64, sepc ↦ᵣ v) -∗
       (∃ v : mword 64, scause ↦ᵣ v) -∗
       (∃ v : mword 64, stval ↦ᵣ v) -∗
       F -∗
       pc_is pc0 -∗
       WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intros HN Hmm Hpc0 Htvd Hsb.
    iIntros "#Hhw #Hinv Hinvr Hhs Hpriv Hmie Hmdl Hmip Hmeip Hseip Hsepc Hscause Hstval HF Hpc Hbody".
    iRevert "Hinvr Hhs Hpriv Hmie Hmdl Hmip Hmeip Hseip Hsepc Hscause Hstval HF Hpc Hbody".
    iLöb as "IH".
    iIntros "Hinvr Hhs Hpriv Hmie Hmdl Hmip Hmeip Hseip Hsepc Hscause Hstval HF Hpc Hbody".
    iDestruct "Hinvr" as (ms) "[Hms Hdisj]".
    iDestruct "Hdisj" as "[[%HSIEf Hstv] | (%Hmsf & Hstvec & #Hspec)]".
    - (* ---- interrupts disabled: dispatch is necessarily None ---- *)
      iApply ("Hbody" $! ms with "[%] Hms [Hstv] Hhs Hpriv Hmie Hmdl Hmip Hmeip Hseip
                                   Hsepc Hscause Hstval HF Hpc").
      { exact (s_dispatch_None_of_SIE_false _ _ _ _ _ _ HSIEf). }
      iLeft. iFrame "Hstv". iPureIntro. exact HSIEf.
    - (* ---- interrupts enabled ---- *)
      destruct (s_dispatch mip_v meip seip mie_v mdv0 ms) as [[i p] |] eqn:Hdres.
      + (* an interrupt fires: trap -> handler spec -> loop *)
        pose proof (s_dispatch_Some_S _ _ _ _ _ _ _ _ Hdres); subst p.
        iPoseProof "Hhw" as "#Hhwc".
        iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
          "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & %HmisaS & %HmisaC &
            %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np)".
        pose proof (elp_no_lp elp0 Help_np) as Help0.
        iDestruct "Hsepc" as (sepc_old) "Hsepc".
        iDestruct "Hscause" as (scause_old) "Hscause".
        iDestruct "Hstval" as (stval_old) "Hstval".
        iDestruct "Hpc" as "[Hpcr Hnpc]".
        iApply (wp_exec_step_interrupt_inv E Φ HN with "Hinv Hhs").
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
        pose proof (exec_run_hart_active_pending σ i Supervisor Lpriv Hdisp0) as Hha.
        pose proof (exec_handle_interrupt_S σ i pc0 ms scause_old handler elp0
                      Lpriv Lms Lsc Lstvec Lelp HmisaS' Htvd Lpc) as Hhi.
        match type of Hhi with _ = Some (_, ?T) => set (s_trap := T) in Hhi end.
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
        iMod (reg_update _ sepc _ pc0 with "Hreg Hsepc") as "[Hreg Hsepc]".
        iMod (reg_update _ cur_privilege _ Supervisor with "Hreg Hpriv") as "[Hreg Hpriv]".
        iMod (reg_update _ nextPC _ (stvec_base handler)
                with "Hreg Hnpc") as "[Hreg Hnpc]".
        iModIntro.
        iExists i, Supervisor, s_trap.
        iSplitR; [iPureIntro; exact Hha |].
        iSplitR; [iPureIntro; exact Hhi |].
        assert (LpcT : register_lookup PC s_trap.(sregs) = pc0).
        { unfold s_trap. lk. exact Lpc. }
        rewrite LpcT.
        iSplitL "Hpcr"; [iExact "Hpcr" |].
        iSplitL "Hreg Hmem".
        { unfold s_trap, set_reg; cbn [sregs mem]. iFrame "Hreg Hmem". }
        iNext.
        iIntros "Hhs Hpcr".
        assert (LnT : register_lookup nextPC s_trap.(sregs) = stvec_base handler).
        { unfold s_trap. lk. reflexivity. }
        iEval (rewrite LnT Hsb) in "Hpcr".
        iEval (rewrite Hsb) in "Hnpc".
        assert (Htm : ms_c = trap_ms elp0 ms) by reflexivity.
        iEval (rewrite Htm) in "Hms".
        (* ---- the ABSTRACT handler spec discharges the whole handler ---- *)
        iApply ("Hspec" $! elp0 ms pc0 mie_v mdv0 E Φ
                  with "[%] [%] [%] [%] Hhs Hpriv Hms Hmie Hmdl Hsepc Hstvec
                        [$Hpcr $Hnpc] HF [Hscause Hstval Hmip Hmeip Hseip Hbody]").
        { exact HN. }
        { exact Hmsf. }
        { exact Hpc0. }
        { exact Hmm. }
        (* the handler's return-continuation: re-establish the invariant + Loeb *)
        iIntros "Hhs Hpriv Hms Hmie Hmdl Hsepc Hstvec Hpc HF".
        iApply ("IH" with "[Hms Hstvec] Hhs Hpriv Hmie Hmdl Hmip Hmeip Hseip
                           Hsepc [Hscause] [Hstval] HF Hpc Hbody").
        { iExists (sret_ms5 (trap_ms elp0 ms)). iFrame "Hms". iRight.
          iFrame "Hstvec Hspec". iPureIntro. exact (acq_ms_facts_roundtrip elp0 ms Hmsf). }
        { iExists c2v. iFrame "Hscause". }
        { iExists (zeros' 64). iFrame "Hstval". }
      + (* no interrupt pending: hand the opened invariant to the body *)
        iApply ("Hbody" $! ms with "[%] Hms [Hstvec Hspec] Hhs Hpriv Hmie Hmdl Hmip Hmeip Hseip
                                     Hsepc Hscause Hstval HF Hpc").
        { exact Hdres. }
        iRight. iFrame "Hstvec Hspec". iPureIntro. exact Hmsf.
  Qed.

End WpIntrInv.
