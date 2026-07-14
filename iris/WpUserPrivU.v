(* WpUserPrivU.v -- COMBINED (hit+miss) U-mode illegal-trap arms for the
   privileged and privileged-CSR-access instruction families.

   Each arm rides the combined trap-fetch engine ustep_illegal_st_u
   (WpUserTrapMiss), so it carries NO fetch-hit precondition: it dispatches
   on ONLY upt_tlb_ok + spec!!vpn = Some ie.  The illegal-execute facts are
   the same exec_execute_*_illegal_U / _u lemmas used by the hit-only arms;
   only the fetch scaffolding changed (hit -> combined). *)
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
Require Import WpUserEcall WpUserTrap WpUserTrapMiss.
Local Open Scope Z_scope.
Import Defs.

Require Import WpUserBase.

Section WpUserPrivU.
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
  Local Notation user_trap_frame := (WpUserBase.user_trap_frame U).
  Local Notation ustep_illegal_st_u := (WpUserTrapMiss.ustep_illegal_st_u U).

  (* The shared, fetch-hit-FREE premises of the combined trap-fetch engine,
     abstracted over the nullary instruction [ii] and its decode target. *)
  Definition upriv_illegal_arm_u (ii : instruction)
      (va : mword 64) (vpn : mword 27) (ie : uwalk_info) (w : mword 32)
      (ms_v sc_v stval_v sepc_v : mword 64)
      (g : gmap regidx (mword 64))
      (tlbvec : vec (option TLB_Entry) (2 ^ 6))
      (E : coPset) (Φ : mval -> iProp Σ) : Prop :=
    (↑minstretN ⊆ E) /\
    (upt_tlb_ok spec tlbvec) /\
    (spec !! vpn = Some ie) /\
    (uw_check_ok (InstructionFetch tt) ie) /\
    (update_PTE_Bits (uw_pte0 ie) (InstructionFetch tt) = None) /\
    (forall j : nat, (j < 4)%nat ->
       code !! pa_add (u_pa (upt_entry vpn ie) va vpn) j = Some (nth_byte w j)) /\
    (_get_Mstatus_SXL ms_v = 'b"10") /\
    (is_aligned_vaddr (Virtaddr va) 4 = true) /\
    (neq_vec (bits_of_virtaddr (Virtaddr va))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false) /\
    (autocast (T := mword) (subrange_vec_dec
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn) /\
    (is_aligned_paddr (Physaddr (u_pa (upt_entry vpn ie) va vpn)) 4 = true) /\
    (isRVC (subrange_vec_dec w 15 0) = false) /\
    (forall s0, agree_on D_u s0 dstateU -> exec (ext_decode w) s0 = Some (ii, s0)).

  (* Generic driver: given the abstracted premises, the is_lpad witness and the
     illegal execute fact, run the combined trap-fetch engine. *)
  Lemma upriv_illegal_run_u (ii : instruction)
      (va : mword 64) (vpn : mword 27) (ie : uwalk_info) (w : mword 32)
      (ms_v sc_v stval_v sepc_v : mword 64)
      (g : gmap regidx (mword 64))
      (tlbvec : vec (option TLB_Entry) (2 ^ 6))
      E (Φ : mval -> iProp Σ) :
    upriv_illegal_arm_u ii va vpn ie w ms_v sc_v stval_v sepc_v g tlbvec E Φ ->
    is_lpad_instruction ii = false ->
    (forall s, register_lookup cur_privilege s.(sregs) = User ->
       exec (execute ii) s = Some (Illegal_Instruction tt, s)) ->
    hw_config -∗ minstret_inv -∗ hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ User -∗ mstatus ↦ᵣ ms_v -∗ scause ↦ᵣ sc_v -∗ stval ↦ᵣ stval_v -∗
    sepc ↦ᵣ sepc_v -∗ tlb ↦ᵣ tlbvec -∗ pc_is va -∗ gpr_file g -∗
    upt_inv root slots spec -∗ user_code -∗ user_data -∗ user_cfg -∗
    ▷ (user_trap_frame -∗ WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intros (HN & Hok & Hsome & Hchk0 & HupdN & Hcw & HSXL & Hval &
            Hcanon & Hvpn_def & Hpaal & HnotRVC & Hdec) Hnlpad Hexec.
    iApply (ustep_illegal_st_u ii va vpn ie w ms_v sc_v stval_v sepc_v g tlbvec E Φ HN
              Hexec Hnlpad Hok Hsome Hchk0 HupdN Hcw HSXL Hval Hcanon
              Hvpn_def Hpaal HnotRVC Hdec).
  Qed.

  (* ---- direct privileged ops: execute is Illegal in User ---- *)
  Lemma ustep_sret_illegal_u
      (va : mword 64) (vpn : mword 27) (ie : uwalk_info) (w : mword 32)
      (ms_v sc_v stval_v sepc_v : mword 64)
      (g : gmap regidx (mword 64)) (tlbvec : vec (option TLB_Entry) (2 ^ 6))
      E (Φ : mval -> iProp Σ) :
    upriv_illegal_arm_u (SRET tt) va vpn ie w ms_v sc_v stval_v sepc_v g tlbvec E Φ ->
    hw_config -∗ minstret_inv -∗ hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ User -∗ mstatus ↦ᵣ ms_v -∗ scause ↦ᵣ sc_v -∗ stval ↦ᵣ stval_v -∗
    sepc ↦ᵣ sepc_v -∗ tlb ↦ᵣ tlbvec -∗ pc_is va -∗ gpr_file g -∗
    upt_inv root slots spec -∗ user_code -∗ user_data -∗ user_cfg -∗
    ▷ (user_trap_frame -∗ WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intro Harm.
    iApply (upriv_illegal_run_u (SRET tt) va vpn ie w ms_v sc_v stval_v sepc_v g tlbvec E Φ
              Harm eq_refl (fun s Hs => exec_execute_SRET_illegal_U s Hs)).
  Qed.

  Lemma ustep_mret_illegal_u
      (va : mword 64) (vpn : mword 27) (ie : uwalk_info) (w : mword 32)
      (ms_v sc_v stval_v sepc_v : mword 64)
      (g : gmap regidx (mword 64)) (tlbvec : vec (option TLB_Entry) (2 ^ 6))
      E (Φ : mval -> iProp Σ) :
    upriv_illegal_arm_u (MRET tt) va vpn ie w ms_v sc_v stval_v sepc_v g tlbvec E Φ ->
    hw_config -∗ minstret_inv -∗ hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ User -∗ mstatus ↦ᵣ ms_v -∗ scause ↦ᵣ sc_v -∗ stval ↦ᵣ stval_v -∗
    sepc ↦ᵣ sepc_v -∗ tlb ↦ᵣ tlbvec -∗ pc_is va -∗ gpr_file g -∗
    upt_inv root slots spec -∗ user_code -∗ user_data -∗ user_cfg -∗
    ▷ (user_trap_frame -∗ WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intro Harm.
    iApply (upriv_illegal_run_u (MRET tt) va vpn ie w ms_v sc_v stval_v sepc_v g tlbvec E Φ
              Harm eq_refl (fun s Hs => exec_execute_MRET_illegal_U s Hs)).
  Qed.

  Lemma ustep_wfi_illegal_u
      (va : mword 64) (vpn : mword 27) (ie : uwalk_info) (w : mword 32)
      (ms_v sc_v stval_v sepc_v : mword 64)
      (g : gmap regidx (mword 64)) (tlbvec : vec (option TLB_Entry) (2 ^ 6))
      E (Φ : mval -> iProp Σ) :
    upriv_illegal_arm_u (WFI tt) va vpn ie w ms_v sc_v stval_v sepc_v g tlbvec E Φ ->
    hw_config -∗ minstret_inv -∗ hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ User -∗ mstatus ↦ᵣ ms_v -∗ scause ↦ᵣ sc_v -∗ stval ↦ᵣ stval_v -∗
    sepc ↦ᵣ sepc_v -∗ tlb ↦ᵣ tlbvec -∗ pc_is va -∗ gpr_file g -∗
    upt_inv root slots spec -∗ user_code -∗ user_data -∗ user_cfg -∗
    ▷ (user_trap_frame -∗ WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intro Harm.
    iApply (upriv_illegal_run_u (WFI tt) va vpn ie w ms_v sc_v stval_v sepc_v g tlbvec E Φ
              Harm eq_refl (fun s Hs => exec_execute_WFI_illegal_U s Hs)).
  Qed.

  Lemma ustep_sfence_w_inval_illegal_u
      (va : mword 64) (vpn : mword 27) (ie : uwalk_info) (w : mword 32)
      (ms_v sc_v stval_v sepc_v : mword 64)
      (g : gmap regidx (mword 64)) (tlbvec : vec (option TLB_Entry) (2 ^ 6))
      E (Φ : mval -> iProp Σ) :
    upriv_illegal_arm_u (SFENCE_W_INVAL tt) va vpn ie w ms_v sc_v stval_v sepc_v g tlbvec E Φ ->
    hw_config -∗ minstret_inv -∗ hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ User -∗ mstatus ↦ᵣ ms_v -∗ scause ↦ᵣ sc_v -∗ stval ↦ᵣ stval_v -∗
    sepc ↦ᵣ sepc_v -∗ tlb ↦ᵣ tlbvec -∗ pc_is va -∗ gpr_file g -∗
    upt_inv root slots spec -∗ user_code -∗ user_data -∗ user_cfg -∗
    ▷ (user_trap_frame -∗ WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intro Harm.
    iApply (upriv_illegal_run_u (SFENCE_W_INVAL tt) va vpn ie w ms_v sc_v stval_v sepc_v g tlbvec E Φ
              Harm eq_refl (fun s Hs => exec_execute_SFENCE_W_INVAL_illegal_U s Hs)).
  Qed.

  Lemma ustep_sfence_inval_ir_illegal_u
      (va : mword 64) (vpn : mword 27) (ie : uwalk_info) (w : mword 32)
      (ms_v sc_v stval_v sepc_v : mword 64)
      (g : gmap regidx (mword 64)) (tlbvec : vec (option TLB_Entry) (2 ^ 6))
      E (Φ : mval -> iProp Σ) :
    upriv_illegal_arm_u (SFENCE_INVAL_IR tt) va vpn ie w ms_v sc_v stval_v sepc_v g tlbvec E Φ ->
    hw_config -∗ minstret_inv -∗ hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ User -∗ mstatus ↦ᵣ ms_v -∗ scause ↦ᵣ sc_v -∗ stval ↦ᵣ stval_v -∗
    sepc ↦ᵣ sepc_v -∗ tlb ↦ᵣ tlbvec -∗ pc_is va -∗ gpr_file g -∗
    upt_inv root slots spec -∗ user_code -∗ user_data -∗ user_cfg -∗
    ▷ (user_trap_frame -∗ WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intro Harm.
    iApply (upriv_illegal_run_u (SFENCE_INVAL_IR tt) va vpn ie w ms_v sc_v stval_v sepc_v g tlbvec E Φ
              Harm eq_refl (fun s Hs => exec_execute_SFENCE_INVAL_IR_illegal_U s Hs)).
  Qed.

  Lemma ustep_sfence_vma_illegal_u (rs1 rs2 : mword 5)
      (va : mword 64) (vpn : mword 27) (ie : uwalk_info) (w : mword 32)
      (ms_v sc_v stval_v sepc_v : mword 64)
      (g : gmap regidx (mword 64)) (tlbvec : vec (option TLB_Entry) (2 ^ 6))
      E (Φ : mval -> iProp Σ) :
    upriv_illegal_arm_u (SFENCE_VMA (Regidx rs1, Regidx rs2)) va vpn ie w ms_v sc_v stval_v sepc_v g tlbvec E Φ ->
    hw_config -∗ minstret_inv -∗ hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ User -∗ mstatus ↦ᵣ ms_v -∗ scause ↦ᵣ sc_v -∗ stval ↦ᵣ stval_v -∗
    sepc ↦ᵣ sepc_v -∗ tlb ↦ᵣ tlbvec -∗ pc_is va -∗ gpr_file g -∗
    upt_inv root slots spec -∗ user_code -∗ user_data -∗ user_cfg -∗
    ▷ (user_trap_frame -∗ WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intro Harm.
    iApply (upriv_illegal_run_u (SFENCE_VMA (Regidx rs1, Regidx rs2))
              va vpn ie w ms_v sc_v stval_v sepc_v g tlbvec E Φ
              Harm eq_refl (fun s Hs => exec_execute_SFENCE_VMA_illegal_U rs1 rs2 s Hs)).
  Qed.

  (* ---- privileged-CSR access from User (csrPriv csr not 00): traps ---- *)
  Lemma ustep_csrreg_illegal_u (csr : mword 12) (rs1 rd : mword 5) (op : csrop)
      (va : mword 64) (vpn : mword 27) (ie : uwalk_info) (w : mword 32)
      (ms_v sc_v stval_v sepc_v : mword 64)
      (g : gmap regidx (mword 64)) (tlbvec : vec (option TLB_Entry) (2 ^ 6))
      E (Φ : mval -> iProp Σ) :
    zopz0zKzJ_u ('b"00" : mword 2) (csrPriv csr) = false ->
    upriv_illegal_arm_u (CSRReg (csr, Regidx rs1, Regidx rd, op)) va vpn ie w ms_v sc_v stval_v sepc_v g tlbvec E Φ ->
    hw_config -∗ minstret_inv -∗ hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ User -∗ mstatus ↦ᵣ ms_v -∗ scause ↦ᵣ sc_v -∗ stval ↦ᵣ stval_v -∗
    sepc ↦ᵣ sepc_v -∗ tlb ↦ᵣ tlbvec -∗ pc_is va -∗ gpr_file g -∗
    upt_inv root slots spec -∗ user_code -∗ user_data -∗ user_cfg -∗
    ▷ (user_trap_frame -∗ WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intros Hpriv Harm.
    iApply (upriv_illegal_run_u (CSRReg (csr, Regidx rs1, Regidx rd, op))
              va vpn ie w ms_v sc_v stval_v sepc_v g tlbvec E Φ
              Harm eq_refl
              (fun s Hs => exec_execute_CSRReg_illegal_u csr rs1 rd op s Hs Hpriv)).
  Qed.

  Lemma ustep_csrimm_illegal_u (csr : mword 12) (imm rd : mword 5) (op : csrop)
      (va : mword 64) (vpn : mword 27) (ie : uwalk_info) (w : mword 32)
      (ms_v sc_v stval_v sepc_v : mword 64)
      (g : gmap regidx (mword 64)) (tlbvec : vec (option TLB_Entry) (2 ^ 6))
      E (Φ : mval -> iProp Σ) :
    zopz0zKzJ_u ('b"00" : mword 2) (csrPriv csr) = false ->
    upriv_illegal_arm_u (CSRImm (csr, imm, Regidx rd, op)) va vpn ie w ms_v sc_v stval_v sepc_v g tlbvec E Φ ->
    hw_config -∗ minstret_inv -∗ hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ User -∗ mstatus ↦ᵣ ms_v -∗ scause ↦ᵣ sc_v -∗ stval ↦ᵣ stval_v -∗
    sepc ↦ᵣ sepc_v -∗ tlb ↦ᵣ tlbvec -∗ pc_is va -∗ gpr_file g -∗
    upt_inv root slots spec -∗ user_code -∗ user_data -∗ user_cfg -∗
    ▷ (user_trap_frame -∗ WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intros Hpriv Harm.
    iApply (upriv_illegal_run_u (CSRImm (csr, imm, Regidx rd, op))
              va vpn ie w ms_v sc_v stval_v sepc_v g tlbvec E Φ
              Harm eq_refl
              (fun s Hs => exec_execute_CSRImm_illegal_u csr imm rd op s Hs Hpriv)).
  Qed.

End WpUserPrivU.
