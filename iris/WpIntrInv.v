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
Require Import WpKernelvecNew WpKvHit.
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
      (satp0 mie_v mdv0 menvcfg0 : mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (pmpaddr00 : type_of_register pmpaddr_n)
      (tlbvec : vec (option TLB_Entry) (2 ^ 6)) : iProp Sig :=
    (hw_config ∗ minstret_inv ∗ kernel_text ∗
     satp ↦ᵣ satp0 ∗
     mie ↦ᵣ mie_v ∗
     mideleg ↦ᵣ mdv0 ∗
     menvcfg ↦ᵣ menvcfg0 ∗
     pmpcfg_n ↦ᵣ pmpcfg0 ∗
     pmpaddr_n ↦ᵣ pmpaddr00 ∗
     tlb ↦ᵣ tlbvec ∗
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
    (□ ∀ (elp_v : mword 1) (ms pc0 : mword 64) E (Φ : mval -> iProp Sig),
        ⌜ ↑minstretN ⊆ E ⌝ -∗
        ⌜ ms_pre_facts ms ⌝ -∗
        ⌜ sret_tgt pc0 = pc0 ⌝ -∗
        hart_state ↦ᵣ HART_ACTIVE tt -∗
        cur_privilege ↦ᵣ Supervisor -∗
        mstatus ↦ᵣ trap_ms elp_v ms -∗
        sepc ↦ᵣ pc0 -∗
        stvec ↦ᵣ handler -∗
        pc_is handler -∗
        F -∗
        ( hart_state ↦ᵣ HART_ACTIVE tt -∗
          cur_privilege ↦ᵣ Supervisor -∗
          mstatus ↦ᵣ sret_ms5 (trap_ms elp_v ms) -∗
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
      (satp0 mie_v mdv0 menvcfg0 : mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (pmpaddr00 : type_of_register pmpaddr_n)
      (tlbvec : vec (option TLB_Entry) (2 ^ 6)) :
    _get_Satp64_Mode (Mk_Satp64 satp0) = ('b"1000" : mword 4) ->
    zero_extend' 16 (satp_to_asid (autocast (T := mword) satp0 : mword 64)) = (mword_of_int 0 : mword 16) ->
    and_vec mie_v (not_vec mdv0) = zeros' 64 ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
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
    is_aligned_vaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000")))))) 8 = true ->
    (* slot 3: x5 at sp+32 *)
    neq_vec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 4 : mword 6) ('b"000"))))))) (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 4 : mword 6) ('b"000"))))))) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec (subrange_vec_dec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 4 : mword 6) ('b"000"))))))) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = svpn ->
    zero_extend' 64 (concat_vec (tlb_get_ppn 39 (pw_tlb_entry root_ppn (mword_of_int 0)) svpn) (subrange_vec_dec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 4 : mword 6) ('b"000"))))))) (Z.sub pagesize_bits 1) 0)) = (add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 4 : mword 6) ('b"000")))) ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4) (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4) (uint (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 4 : mword 6) ('b"000"))))))) (uint (to_bits 64 8)) = PMP_Match ->
    is_aligned_vaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 4 : mword 6) ('b"000")))))) 8 = true ->
    (* slot 4: x6 at sp+40 *)
    neq_vec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 5 : mword 6) ('b"000"))))))) (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 5 : mword 6) ('b"000"))))))) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec (subrange_vec_dec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 5 : mword 6) ('b"000"))))))) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = svpn ->
    zero_extend' 64 (concat_vec (tlb_get_ppn 39 (pw_tlb_entry root_ppn (mword_of_int 0)) svpn) (subrange_vec_dec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 5 : mword 6) ('b"000"))))))) (Z.sub pagesize_bits 1) 0)) = (add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 5 : mword 6) ('b"000")))) ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4) (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4) (uint (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 5 : mword 6) ('b"000"))))))) (uint (to_bits 64 8)) = PMP_Match ->
    is_aligned_vaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 5 : mword 6) ('b"000")))))) 8 = true ->
    (* slot 5: x7 at sp+48 *)
    neq_vec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 6 : mword 6) ('b"000"))))))) (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 6 : mword 6) ('b"000"))))))) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec (subrange_vec_dec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 6 : mword 6) ('b"000"))))))) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = svpn ->
    zero_extend' 64 (concat_vec (tlb_get_ppn 39 (pw_tlb_entry root_ppn (mword_of_int 0)) svpn) (subrange_vec_dec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 6 : mword 6) ('b"000"))))))) (Z.sub pagesize_bits 1) 0)) = (add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 6 : mword 6) ('b"000")))) ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4) (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4) (uint (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 6 : mword 6) ('b"000"))))))) (uint (to_bits 64 8)) = PMP_Match ->
    is_aligned_vaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 6 : mword 6) ('b"000")))))) 8 = true ->
    (* slot 6: x10 at sp+72 *)
    neq_vec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 9 : mword 6) ('b"000"))))))) (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 9 : mword 6) ('b"000"))))))) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec (subrange_vec_dec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 9 : mword 6) ('b"000"))))))) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = svpn ->
    zero_extend' 64 (concat_vec (tlb_get_ppn 39 (pw_tlb_entry root_ppn (mword_of_int 0)) svpn) (subrange_vec_dec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 9 : mword 6) ('b"000"))))))) (Z.sub pagesize_bits 1) 0)) = (add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 9 : mword 6) ('b"000")))) ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4) (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4) (uint (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 9 : mword 6) ('b"000"))))))) (uint (to_bits 64 8)) = PMP_Match ->
    is_aligned_vaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 9 : mword 6) ('b"000")))))) 8 = true ->
    (* slot 7: x11 at sp+80 *)
    neq_vec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 10 : mword 6) ('b"000"))))))) (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 10 : mword 6) ('b"000"))))))) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec (subrange_vec_dec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 10 : mword 6) ('b"000"))))))) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = svpn ->
    zero_extend' 64 (concat_vec (tlb_get_ppn 39 (pw_tlb_entry root_ppn (mword_of_int 0)) svpn) (subrange_vec_dec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 10 : mword 6) ('b"000"))))))) (Z.sub pagesize_bits 1) 0)) = (add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 10 : mword 6) ('b"000")))) ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4) (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4) (uint (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 10 : mword 6) ('b"000"))))))) (uint (to_bits 64 8)) = PMP_Match ->
    is_aligned_vaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 10 : mword 6) ('b"000")))))) 8 = true ->
    (* slot 8: x12 at sp+88 *)
    neq_vec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 11 : mword 6) ('b"000"))))))) (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 11 : mword 6) ('b"000"))))))) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec (subrange_vec_dec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 11 : mword 6) ('b"000"))))))) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = svpn ->
    zero_extend' 64 (concat_vec (tlb_get_ppn 39 (pw_tlb_entry root_ppn (mword_of_int 0)) svpn) (subrange_vec_dec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 11 : mword 6) ('b"000"))))))) (Z.sub pagesize_bits 1) 0)) = (add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 11 : mword 6) ('b"000")))) ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4) (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4) (uint (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 11 : mword 6) ('b"000"))))))) (uint (to_bits 64 8)) = PMP_Match ->
    is_aligned_vaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 11 : mword 6) ('b"000")))))) 8 = true ->
    (* slot 9: x13 at sp+96 *)
    neq_vec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 12 : mword 6) ('b"000"))))))) (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 12 : mword 6) ('b"000"))))))) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec (subrange_vec_dec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 12 : mword 6) ('b"000"))))))) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = svpn ->
    zero_extend' 64 (concat_vec (tlb_get_ppn 39 (pw_tlb_entry root_ppn (mword_of_int 0)) svpn) (subrange_vec_dec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 12 : mword 6) ('b"000"))))))) (Z.sub pagesize_bits 1) 0)) = (add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 12 : mword 6) ('b"000")))) ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4) (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4) (uint (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 12 : mword 6) ('b"000"))))))) (uint (to_bits 64 8)) = PMP_Match ->
    is_aligned_vaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 12 : mword 6) ('b"000")))))) 8 = true ->
    (* slot 10: x14 at sp+104 *)
    neq_vec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 13 : mword 6) ('b"000"))))))) (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 13 : mword 6) ('b"000"))))))) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec (subrange_vec_dec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 13 : mword 6) ('b"000"))))))) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = svpn ->
    zero_extend' 64 (concat_vec (tlb_get_ppn 39 (pw_tlb_entry root_ppn (mword_of_int 0)) svpn) (subrange_vec_dec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 13 : mword 6) ('b"000"))))))) (Z.sub pagesize_bits 1) 0)) = (add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 13 : mword 6) ('b"000")))) ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4) (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4) (uint (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 13 : mword 6) ('b"000"))))))) (uint (to_bits 64 8)) = PMP_Match ->
    is_aligned_vaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 13 : mword 6) ('b"000")))))) 8 = true ->
    (* slot 11: x15 at sp+112 *)
    neq_vec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 14 : mword 6) ('b"000"))))))) (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 14 : mword 6) ('b"000"))))))) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec (subrange_vec_dec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 14 : mword 6) ('b"000"))))))) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = svpn ->
    zero_extend' 64 (concat_vec (tlb_get_ppn 39 (pw_tlb_entry root_ppn (mword_of_int 0)) svpn) (subrange_vec_dec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 14 : mword 6) ('b"000"))))))) (Z.sub pagesize_bits 1) 0)) = (add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 14 : mword 6) ('b"000")))) ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4) (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4) (uint (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 14 : mword 6) ('b"000"))))))) (uint (to_bits 64 8)) = PMP_Match ->
    is_aligned_vaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 14 : mword 6) ('b"000")))))) 8 = true ->
    (* slot 12: x16 at sp+120 *)
    neq_vec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 15 : mword 6) ('b"000"))))))) (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 15 : mword 6) ('b"000"))))))) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec (subrange_vec_dec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 15 : mword 6) ('b"000"))))))) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = svpn ->
    zero_extend' 64 (concat_vec (tlb_get_ppn 39 (pw_tlb_entry root_ppn (mword_of_int 0)) svpn) (subrange_vec_dec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 15 : mword 6) ('b"000"))))))) (Z.sub pagesize_bits 1) 0)) = (add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 15 : mword 6) ('b"000")))) ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4) (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4) (uint (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 15 : mword 6) ('b"000"))))))) (uint (to_bits 64 8)) = PMP_Match ->
    is_aligned_vaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 15 : mword 6) ('b"000")))))) 8 = true ->
    (* slot 13: x17 at sp+128 *)
    neq_vec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 16 : mword 6) ('b"000"))))))) (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 16 : mword 6) ('b"000"))))))) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec (subrange_vec_dec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 16 : mword 6) ('b"000"))))))) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = svpn ->
    zero_extend' 64 (concat_vec (tlb_get_ppn 39 (pw_tlb_entry root_ppn (mword_of_int 0)) svpn) (subrange_vec_dec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 16 : mword 6) ('b"000"))))))) (Z.sub pagesize_bits 1) 0)) = (add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 16 : mword 6) ('b"000")))) ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4) (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4) (uint (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 16 : mword 6) ('b"000"))))))) (uint (to_bits 64 8)) = PMP_Match ->
    is_aligned_vaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 16 : mword 6) ('b"000")))))) 8 = true ->
    (* slot 14: x28 at sp+216 *)
    neq_vec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 27 : mword 6) ('b"000"))))))) (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 27 : mword 6) ('b"000"))))))) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec (subrange_vec_dec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 27 : mword 6) ('b"000"))))))) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = svpn ->
    zero_extend' 64 (concat_vec (tlb_get_ppn 39 (pw_tlb_entry root_ppn (mword_of_int 0)) svpn) (subrange_vec_dec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 27 : mword 6) ('b"000"))))))) (Z.sub pagesize_bits 1) 0)) = (add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 27 : mword 6) ('b"000")))) ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4) (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4) (uint (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 27 : mword 6) ('b"000"))))))) (uint (to_bits 64 8)) = PMP_Match ->
    is_aligned_vaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 27 : mword 6) ('b"000")))))) 8 = true ->
    (* slot 15: x29 at sp+224 *)
    neq_vec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 28 : mword 6) ('b"000"))))))) (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 28 : mword 6) ('b"000"))))))) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec (subrange_vec_dec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 28 : mword 6) ('b"000"))))))) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = svpn ->
    zero_extend' 64 (concat_vec (tlb_get_ppn 39 (pw_tlb_entry root_ppn (mword_of_int 0)) svpn) (subrange_vec_dec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 28 : mword 6) ('b"000"))))))) (Z.sub pagesize_bits 1) 0)) = (add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 28 : mword 6) ('b"000")))) ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4) (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4) (uint (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 28 : mword 6) ('b"000"))))))) (uint (to_bits 64 8)) = PMP_Match ->
    is_aligned_vaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 28 : mword 6) ('b"000")))))) 8 = true ->
    (* slot 16: x30 at sp+232 *)
    neq_vec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 29 : mword 6) ('b"000"))))))) (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 29 : mword 6) ('b"000"))))))) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec (subrange_vec_dec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 29 : mword 6) ('b"000"))))))) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = svpn ->
    zero_extend' 64 (concat_vec (tlb_get_ppn 39 (pw_tlb_entry root_ppn (mword_of_int 0)) svpn) (subrange_vec_dec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 29 : mword 6) ('b"000"))))))) (Z.sub pagesize_bits 1) 0)) = (add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 29 : mword 6) ('b"000")))) ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4) (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4) (uint (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 29 : mword 6) ('b"000"))))))) (uint (to_bits 64 8)) = PMP_Match ->
    is_aligned_vaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 29 : mword 6) ('b"000")))))) 8 = true ->
    (* slot 17: x31 at sp+240 *)
    neq_vec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 30 : mword 6) ('b"000"))))))) (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 30 : mword 6) ('b"000"))))))) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec (subrange_vec_dec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 30 : mword 6) ('b"000"))))))) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = svpn ->
    zero_extend' 64 (concat_vec (tlb_get_ppn 39 (pw_tlb_entry root_ppn (mword_of_int 0)) svpn) (subrange_vec_dec (bits_of_virtaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 30 : mword 6) ('b"000"))))))) (Z.sub pagesize_bits 1) 0)) = (add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 30 : mword 6) ('b"000")))) ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4) (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4) (uint (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 30 : mword 6) ('b"000"))))))) (uint (to_bits 64 8)) = PMP_Match ->
    is_aligned_vaddr (Virtaddr ((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 30 : mword 6) ('b"000")))))) 8 = true ->
    ⊢ intr_handler_spec (mword_of_int KernelSyms.kernelvec : mword 64)
        (F_kv root_ppn svpn m satp0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 tlbvec).
  Proof.
    intros Hmode Hasid Hmm HPBMTE Hpmm Hhit5 Hhith Hpmpf HW HR Hmask Hlpe0
      Hcanon1 Hvpn1 Hident1 Hrange1 Halv1 Hcanon2 Hvpn2 Hident2 Hrange2 Halv2 Hcanon3 Hvpn3 Hident3 Hrange3 Halv3 Hcanon4 Hvpn4 Hident4 Hrange4 Halv4 Hcanon5 Hvpn5 Hident5 Hrange5 Halv5 Hcanon6 Hvpn6 Hident6 Hrange6 Halv6 Hcanon7 Hvpn7 Hident7 Hrange7 Halv7 Hcanon8 Hvpn8 Hident8 Hrange8 Halv8 Hcanon9 Hvpn9 Hident9 Hrange9 Halv9 Hcanon10 Hvpn10 Hident10 Hrange10 Halv10 Hcanon11 Hvpn11 Hident11 Hrange11 Halv11 Hcanon12 Hvpn12 Hident12 Hrange12 Halv12 Hcanon13 Hvpn13 Hident13 Hrange13 Halv13 Hcanon14 Hvpn14 Hident14 Hrange14 Halv14 Hcanon15 Hvpn15 Hident15 Hrange15 Halv15 Hcanon16 Hvpn16 Hident16 Hrange16 Halv16 Hcanon17 Hvpn17 Hident17 Hrange17 Halv17.
    iModIntro. iIntros (elp_v ms pc0 E Φ) "%HN %Hfacts %Hpc0 Hhs Hpriv Hms Hsepc Hstvec Hpc HF Hcont".
    pose proof Hfacts as (HSIE1 & HMPRV0 & HSXL & HMXR & HTSR).
    iDestruct "HF" as "(#Hhw & #Hinv & #Htext & Hsatp & Hmie & Hmdl & Hmenv & Hpmpc & Hpmpa & Htlb & Hfile & Hwins)".
    iDestruct "Hwins" as (w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17)
      "(Hw1 & Hw2 & Hw3 & Hw4 & Hw5 & Hw6 & Hw7 & Hw8 & Hw9 & Hw10 & Hw11 & Hw12 & Hw13 & Hw14 & Hw15 & Hw16 & Hw17)".
    iApply (wp_kernelvec_hit root_ppn svpn m satp0 (trap_ms elp_v ms) mie_v mdv0 menvcfg0 pc0
              pmpcfg0 pmpaddr00 tlbvec w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 E Φ
              HN Hmode Hasid
              (trap_ms_SIE_false elp_v ms)
              (trap_ms_MPRV_false elp_v ms HMPRV0)
              (trap_ms_SXL_eq elp_v ms HSXL)
              Hmm HPBMTE
              (trap_ms_MXR_true elp_v ms HMXR)
              Hpmm Hhit5 Hhith Hpmpf HW HR Hmask
              (trap_ms_TSR_false elp_v ms HTSR)
              (sret_newpriv_trap_ms elp_v ms)
              Hlpe0
              Hcanon1 Hvpn1 Hident1 Hrange1 Halv1 Hcanon2 Hvpn2 Hident2 Hrange2 Halv2 Hcanon3 Hvpn3 Hident3 Hrange3 Halv3 Hcanon4 Hvpn4 Hident4 Hrange4 Halv4 Hcanon5 Hvpn5 Hident5 Hrange5 Halv5 Hcanon6 Hvpn6 Hident6 Hrange6 Halv6 Hcanon7 Hvpn7 Hident7 Hrange7 Halv7 Hcanon8 Hvpn8 Hident8 Hrange8 Halv8 Hcanon9 Hvpn9 Hident9 Hrange9 Halv9 Hcanon10 Hvpn10 Hident10 Hrange10 Halv10 Hcanon11 Hvpn11 Hident11 Hrange11 Halv11 Hcanon12 Hvpn12 Hident12 Hrange12 Halv12 Hcanon13 Hvpn13 Hident13 Hrange13 Halv13 Hcanon14 Hvpn14 Hident14 Hrange14 Halv14 Hcanon15 Hvpn15 Hident15 Hrange15 Halv15 Hcanon16 Hvpn16 Hident16 Hrange16 Halv16 Hcanon17 Hvpn17 Hident17 Hrange17 Halv17
              with "Hhw Hinv Hhs Hpriv Hsatp Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlb Hsepc
                    Hpc Hfile Htext Hw1 Hw2 Hw3 Hw4 Hw5 Hw6 Hw7 Hw8 Hw9 Hw10 Hw11 Hw12 Hw13 Hw14 Hw15 Hw16 Hw17").
    iIntros "Hhs Hpriv Hsatp Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlb Hsepc Hpc Hfile
             Hw1 Hw2 Hw3 Hw4 Hw5 Hw6 Hw7 Hw8 Hw9 Hw10 Hw11 Hw12 Hw13 Hw14 Hw15 Hw16 Hw17".
    iEval (rewrite Hpc0) in "Hpc".
    iApply ("Hcont" with "Hhs Hpriv Hms [Hsepc] Hstvec Hpc [-]").
    { iExists pc0. iFrame "Hsepc". }
    iFrame "Hhw Hinv Htext Hsatp Hmie Hmdl Hmenv Hpmpc Hpmpa Htlb Hfile".
    iExists (m !!! Regidx (mword_of_int 1 : mword 5)), (m !!! Regidx (mword_of_int 3 : mword 5)), (m !!! Regidx (mword_of_int 5 : mword 5)), (m !!! Regidx (mword_of_int 6 : mword 5)), (m !!! Regidx (mword_of_int 7 : mword 5)), (m !!! Regidx (mword_of_int 10 : mword 5)), (m !!! Regidx (mword_of_int 11 : mword 5)), (m !!! Regidx (mword_of_int 12 : mword 5)), (m !!! Regidx (mword_of_int 13 : mword 5)), (m !!! Regidx (mword_of_int 14 : mword 5)), (m !!! Regidx (mword_of_int 15 : mword 5)), (m !!! Regidx (mword_of_int 16 : mword 5)), (m !!! Regidx (mword_of_int 17 : mword 5)), (m !!! Regidx (mword_of_int 28 : mword 5)), (m !!! Regidx (mword_of_int 29 : mword 5)), (m !!! Regidx (mword_of_int 30 : mword 5)), (m !!! Regidx (mword_of_int 31 : mword 5)).
    iFrame "Hw1 Hw2 Hw3 Hw4 Hw5 Hw6 Hw7 Hw8 Hw9 Hw10 Hw11 Hw12 Hw13 Hw14 Hw15 Hw16 Hw17".
  Qed.

End WpIntrInv.
