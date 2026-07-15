(* WpUserPriv.v -- U-mode USTEP arms for the privileged/supervisor
   instructions that trap to Illegal unconditionally in User mode: SRET,
   MRET, WFI, SFENCE.W.INVAL, SFENCE.INVAL.IR, SFENCE.VMA.  Each reads
   cur_privilege and, seeing User, yields Illegal_Instruction with no state
   change (config-independent -- unlike the counter CSRs, no frame bit is
   consulted).  These are thin instances of ustep_illegal_st discharging its
   execute premise with the exec_execute_*_illegal_U facts (UmodeFetchC.v). *)
From Stdlib Require Import ZArith Bool Lia.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import RiscvModelBytes.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvFetchExec RiscvTryStep.
Require Import MinstretInv InstrBytes WpGpr.
Require Import SmodeCore WpIntrCore WpDecodeBridge.
Require Import UmodeFetch UmodeFetchC UmodeEcall.
Require Import UptInv HartActiveExecuteAs CboIllegal.
Require Import WpUserTrap.
Local Open Scope Z_scope.
Import Defs.

Require Import WpUserBase.

(* SINVAL.VMA executes AS SFENCE.VMA: its execute yields ExecuteAs, not a
   direct ExecutionResult.  (The dispatch is [returnM (execute_SINVAL_VMA …)]
   and execute_SINVAL_VMA = ExecuteAs (SFENCE_VMA …).) *)
Lemma exec_execute_SINVAL_VMA_ExecuteAs (rs1 rs2 : regidx) s :
  exec (execute (SINVAL_VMA (rs1, rs2))) s
  = Some (ExecuteAs (SFENCE_VMA (rs1, rs2)), s).
Proof.
  change (execute (SINVAL_VMA (rs1, rs2)))
    with (returnM (execute_SINVAL_VMA rs1 rs2) : M ExecutionResult).
  unfold execute_SINVAL_VMA. apply exec_returnM.
Qed.

Section WpUserPriv.
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
  Local Notation ustep_illegal_st := (WpUserTrap.ustep_illegal_st U).
  Local Notation ustep_illegal_run_st := (WpUserTrap.ustep_illegal_run_st U).

  (* The shared fetch/decode premises of ustep_illegal_st, abstracted over
     the (nullary) instruction [ii] and its decode target. *)
  Definition upriv_illegal_arm (ii : instruction)
      (va : mword 64) (vpn : mword 27) (ie : uwalk_info) (w : mword 32)
      (ms_v sc_v stval_v sepc_v : mword 64)
      (g : gmap regidx (mword 64))
      (tlbvec : vec (option TLB_Entry) (2 ^ 6))
      (E : coPset) (Φ : mval -> iProp Σ) : Prop :=
    (↑minstretN ⊆ E) /\
    (upt_tlb_ok spec tlbvec) /\
    (vec_access_dec tlbvec (tlb_hash (__id 39) vpn) = Some (upt_entry vpn ie)) /\
    (uw_check_ok (InstructionFetch tt) ie) /\
    (update_PTE_Bits (uw_pte0 ie) (InstructionFetch tt) = None) /\
    (_get_PTE_Ext_PBMT (ext_bits_of_PTE (uw_pte0 ie)) = ('b"00" : mword 2)) /\
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

  (* Generic driver: given the abstracted premises, the is_lpad witness, and
     the illegal execute fact, run ustep_illegal_st. *)
  Lemma upriv_illegal_run (ii : instruction)
      (va : mword 64) (vpn : mword 27) (ie : uwalk_info) (w : mword 32)
      (ms_v sc_v stval_v sepc_v : mword 64)
      (g : gmap regidx (mword 64))
      (tlbvec : vec (option TLB_Entry) (2 ^ 6))
      E (Φ : mval -> iProp Σ) :
    upriv_illegal_arm ii va vpn ie w ms_v sc_v stval_v sepc_v g tlbvec E Φ ->
    is_lpad_instruction ii = false ->
    (forall s, register_lookup cur_privilege s.(sregs) = User ->
       exec (execute ii) s = Some (Illegal_Instruction tt, s)) ->
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
    intros (HN & Hok & Hvec & Hchk0 & HupdN & Hpbmt0 & Hcw & HSXL & Hval &
            Hcanon & Hvpn_def & Hpaal & HnotRVC & Hdec) Hnlpad Hexec.
    iApply (ustep_illegal_st ii va vpn ie w ms_v sc_v stval_v sepc_v g tlbvec E Φ HN
              Hexec Hnlpad Hok Hvec Hchk0 HupdN Hpbmt0 Hcw HSXL Hval Hcanon
              Hvpn_def Hpaal HnotRVC Hdec).
  Qed.

  Lemma ustep_sret_illegal
      (va : mword 64) (vpn : mword 27) (ie : uwalk_info) (w : mword 32)
      (ms_v sc_v stval_v sepc_v : mword 64)
      (g : gmap regidx (mword 64)) (tlbvec : vec (option TLB_Entry) (2 ^ 6))
      E (Φ : mval -> iProp Σ) :
    upriv_illegal_arm (SRET tt) va vpn ie w ms_v sc_v stval_v sepc_v g tlbvec E Φ ->
    hw_config -∗ minstret_inv -∗ hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ User -∗ mstatus ↦ᵣ ms_v -∗ scause ↦ᵣ sc_v -∗ stval ↦ᵣ stval_v -∗
    sepc ↦ᵣ sepc_v -∗ tlb ↦ᵣ tlbvec -∗ pc_is va -∗ gpr_file g -∗
    upt_inv root slots spec -∗ user_code -∗ user_data -∗ user_cfg -∗
    ▷ (user_trap_frame -∗ WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intro Harm.
    iApply (upriv_illegal_run (SRET tt) va vpn ie w ms_v sc_v stval_v sepc_v g tlbvec E Φ
              Harm eq_refl (fun s Hs => exec_execute_SRET_illegal_U s Hs)).
  Qed.

  Lemma ustep_mret_illegal
      (va : mword 64) (vpn : mword 27) (ie : uwalk_info) (w : mword 32)
      (ms_v sc_v stval_v sepc_v : mword 64)
      (g : gmap regidx (mword 64)) (tlbvec : vec (option TLB_Entry) (2 ^ 6))
      E (Φ : mval -> iProp Σ) :
    upriv_illegal_arm (MRET tt) va vpn ie w ms_v sc_v stval_v sepc_v g tlbvec E Φ ->
    hw_config -∗ minstret_inv -∗ hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ User -∗ mstatus ↦ᵣ ms_v -∗ scause ↦ᵣ sc_v -∗ stval ↦ᵣ stval_v -∗
    sepc ↦ᵣ sepc_v -∗ tlb ↦ᵣ tlbvec -∗ pc_is va -∗ gpr_file g -∗
    upt_inv root slots spec -∗ user_code -∗ user_data -∗ user_cfg -∗
    ▷ (user_trap_frame -∗ WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intro Harm.
    iApply (upriv_illegal_run (MRET tt) va vpn ie w ms_v sc_v stval_v sepc_v g tlbvec E Φ
              Harm eq_refl (fun s Hs => exec_execute_MRET_illegal_U s Hs)).
  Qed.

  Lemma ustep_wfi_illegal
      (va : mword 64) (vpn : mword 27) (ie : uwalk_info) (w : mword 32)
      (ms_v sc_v stval_v sepc_v : mword 64)
      (g : gmap regidx (mword 64)) (tlbvec : vec (option TLB_Entry) (2 ^ 6))
      E (Φ : mval -> iProp Σ) :
    upriv_illegal_arm (WFI tt) va vpn ie w ms_v sc_v stval_v sepc_v g tlbvec E Φ ->
    hw_config -∗ minstret_inv -∗ hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ User -∗ mstatus ↦ᵣ ms_v -∗ scause ↦ᵣ sc_v -∗ stval ↦ᵣ stval_v -∗
    sepc ↦ᵣ sepc_v -∗ tlb ↦ᵣ tlbvec -∗ pc_is va -∗ gpr_file g -∗
    upt_inv root slots spec -∗ user_code -∗ user_data -∗ user_cfg -∗
    ▷ (user_trap_frame -∗ WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intro Harm.
    iApply (upriv_illegal_run (WFI tt) va vpn ie w ms_v sc_v stval_v sepc_v g tlbvec E Φ
              Harm eq_refl (fun s Hs => exec_execute_WFI_illegal_U s Hs)).
  Qed.

  Lemma ustep_sfence_w_inval_illegal
      (va : mword 64) (vpn : mword 27) (ie : uwalk_info) (w : mword 32)
      (ms_v sc_v stval_v sepc_v : mword 64)
      (g : gmap regidx (mword 64)) (tlbvec : vec (option TLB_Entry) (2 ^ 6))
      E (Φ : mval -> iProp Σ) :
    upriv_illegal_arm (SFENCE_W_INVAL tt) va vpn ie w ms_v sc_v stval_v sepc_v g tlbvec E Φ ->
    hw_config -∗ minstret_inv -∗ hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ User -∗ mstatus ↦ᵣ ms_v -∗ scause ↦ᵣ sc_v -∗ stval ↦ᵣ stval_v -∗
    sepc ↦ᵣ sepc_v -∗ tlb ↦ᵣ tlbvec -∗ pc_is va -∗ gpr_file g -∗
    upt_inv root slots spec -∗ user_code -∗ user_data -∗ user_cfg -∗
    ▷ (user_trap_frame -∗ WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intro Harm.
    iApply (upriv_illegal_run (SFENCE_W_INVAL tt) va vpn ie w ms_v sc_v stval_v sepc_v g tlbvec E Φ
              Harm eq_refl (fun s Hs => exec_execute_SFENCE_W_INVAL_illegal_U s Hs)).
  Qed.

  Lemma ustep_sfence_inval_ir_illegal
      (va : mword 64) (vpn : mword 27) (ie : uwalk_info) (w : mword 32)
      (ms_v sc_v stval_v sepc_v : mword 64)
      (g : gmap regidx (mword 64)) (tlbvec : vec (option TLB_Entry) (2 ^ 6))
      E (Φ : mval -> iProp Σ) :
    upriv_illegal_arm (SFENCE_INVAL_IR tt) va vpn ie w ms_v sc_v stval_v sepc_v g tlbvec E Φ ->
    hw_config -∗ minstret_inv -∗ hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ User -∗ mstatus ↦ᵣ ms_v -∗ scause ↦ᵣ sc_v -∗ stval ↦ᵣ stval_v -∗
    sepc ↦ᵣ sepc_v -∗ tlb ↦ᵣ tlbvec -∗ pc_is va -∗ gpr_file g -∗
    upt_inv root slots spec -∗ user_code -∗ user_data -∗ user_cfg -∗
    ▷ (user_trap_frame -∗ WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intro Harm.
    iApply (upriv_illegal_run (SFENCE_INVAL_IR tt) va vpn ie w ms_v sc_v stval_v sepc_v g tlbvec E Φ
              Harm eq_refl (fun s Hs => exec_execute_SFENCE_INVAL_IR_illegal_U s Hs)).
  Qed.

  Lemma ustep_sfence_vma_illegal (rs1 rs2 : mword 5)
      (va : mword 64) (vpn : mword 27) (ie : uwalk_info) (w : mword 32)
      (ms_v sc_v stval_v sepc_v : mword 64)
      (g : gmap regidx (mword 64)) (tlbvec : vec (option TLB_Entry) (2 ^ 6))
      E (Φ : mval -> iProp Σ) :
    upriv_illegal_arm (SFENCE_VMA (Regidx rs1, Regidx rs2)) va vpn ie w ms_v sc_v stval_v sepc_v g tlbvec E Φ ->
    hw_config -∗ minstret_inv -∗ hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ User -∗ mstatus ↦ᵣ ms_v -∗ scause ↦ᵣ sc_v -∗ stval ↦ᵣ stval_v -∗
    sepc ↦ᵣ sepc_v -∗ tlb ↦ᵣ tlbvec -∗ pc_is va -∗ gpr_file g -∗
    upt_inv root slots spec -∗ user_code -∗ user_data -∗ user_cfg -∗
    ▷ (user_trap_frame -∗ WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intro Harm.
    iApply (upriv_illegal_run (SFENCE_VMA (Regidx rs1, Regidx rs2))
              va vpn ie w ms_v sc_v stval_v sepc_v g tlbvec E Φ
              Harm eq_refl (fun s Hs => exec_execute_SFENCE_VMA_illegal_U rs1 rs2 s Hs)).
  Qed.

  (* SINVAL.VMA: unlike the direct ops, its execute yields ExecuteAs(SFENCE_VMA)
     rather than Illegal, so it rides ustep_illegal_run_st with the
     F_Base+ExecuteAs run producer (re-dispatch to SFENCE_VMA -> Illegal)
     instead of the direct base progress. *)
  Lemma ustep_sinval_vma_illegal (rs1 rs2 : mword 5)
      (va : mword 64) (vpn : mword 27) (ie : uwalk_info) (w : mword 32)
      (ms_v sc_v stval_v sepc_v : mword 64)
      (g : gmap regidx (mword 64)) (tlbvec : vec (option TLB_Entry) (2 ^ 6))
      E (Φ : mval -> iProp Σ) :
    upriv_illegal_arm (SINVAL_VMA (Regidx rs1, Regidx rs2)) va vpn ie w ms_v sc_v stval_v sepc_v g tlbvec E Φ ->
    hw_config -∗ minstret_inv -∗ hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ User -∗ mstatus ↦ᵣ ms_v -∗ scause ↦ᵣ sc_v -∗ stval ↦ᵣ stval_v -∗
    sepc ↦ᵣ sepc_v -∗ tlb ↦ᵣ tlbvec -∗ pc_is va -∗ gpr_file g -∗
    upt_inv root slots spec -∗ user_code -∗ user_data -∗ user_cfg -∗
    ▷ (user_trap_frame -∗ WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intros (HN & Hok & Hvec & Hchk0 & HupdN & Hpbmt0 & Hcw & HSXL & Hval &
            Hcanon & Hvpn_def & Hpaal & HnotRVC & Hdec).
    assert (Hrun : forall σ0 : mstate,
       register_lookup cur_privilege σ0.(sregs) = User ->
       exec (dispatchInterrupt User) σ0 = Some (None, σ0) ->
       exec (fetch tt) σ0 = Some (F_Base w, σ0) ->
       exec (ext_decode w) σ0 = Some (SINVAL_VMA (Regidx rs1, Regidx rs2), σ0) ->
       eq_vec (register_lookup elp σ0.(sregs))
              (landing_pad_bits_backwards LP_EXPECTED) = false ->
       register_lookup PC σ0.(sregs) = va ->
       register_lookup menvcfg σ0.(sregs) = MENVCFG_S ->
       register_lookup senvcfg σ0.(sregs) = (mword_of_int 0 : mword 64) ->
       exec (currentlyEnabled Ext_S) σ0 = Some (true, σ0) ->
       exec (run_hart_active 0) σ0
         = Some (Step_Execute (Illegal_Instruction tt, zero_extend' 32 w),
                 set_reg σ0 nextPC (add_vec_int va 4))).
    { intros σ0 Hcp Hdsp Hft Hdc Hlp Hpc _ _ _.
      apply (exec_hart_active_progress_base_ExecuteAs_gen User σ0 σ0
               (set_reg σ0 nextPC (add_vec_int va 4)) w
               (SINVAL_VMA (Regidx rs1, Regidx rs2)) (SFENCE_VMA (Regidx rs1, Regidx rs2))
               va (Illegal_Instruction tt) Hcp Hdsp Hft Hdc Hlp eq_refl Hpc).
      - exact (exec_execute_SINVAL_VMA_ExecuteAs (Regidx rs1) (Regidx rs2)
                 (set_reg σ0 nextPC (add_vec_int va 4))).
      - apply exec_execute_SFENCE_VMA_illegal_U. lk. exact Hcp. }
    iApply (ustep_illegal_run_st (SINVAL_VMA (Regidx rs1, Regidx rs2))
              va vpn ie w ms_v sc_v stval_v sepc_v g tlbvec E Φ
              HN Hrun Hok Hvec Hchk0 HupdN Hpbmt0 Hcw HSXL Hval Hcanon
              Hvpn_def Hpaal HnotRVC Hdec).
  Qed.

  (* ZICBOM (CBO_CLEAN/FLUSH/INVAL): execute is directly Illegal in U under
     the xv6 config (menvcfg/senvcfg enable bits pinned off), so it rides the
     direct base progress producer.  The config facts are threaded through the
     three extra producer hyps (menvcfg = MENVCFG_S, senvcfg = 0, Ext_S on). *)
  Lemma ustep_zicbom_illegal (op : cbop_zicbom) (rs1 : regidx)
      (va : mword 64) (vpn : mword 27) (ie : uwalk_info) (w : mword 32)
      (ms_v sc_v stval_v sepc_v : mword 64)
      (g : gmap regidx (mword 64)) (tlbvec : vec (option TLB_Entry) (2 ^ 6))
      E (Φ : mval -> iProp Σ) :
    upriv_illegal_arm (ZICBOM (op, rs1)) va vpn ie w ms_v sc_v stval_v sepc_v g tlbvec E Φ ->
    hw_config -∗ minstret_inv -∗ hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ User -∗ mstatus ↦ᵣ ms_v -∗ scause ↦ᵣ sc_v -∗ stval ↦ᵣ stval_v -∗
    sepc ↦ᵣ sepc_v -∗ tlb ↦ᵣ tlbvec -∗ pc_is va -∗ gpr_file g -∗
    upt_inv root slots spec -∗ user_code -∗ user_data -∗ user_cfg -∗
    ▷ (user_trap_frame -∗ WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intros (HN & Hok & Hvec & Hchk0 & HupdN & Hpbmt0 & Hcw & HSXL & Hval &
            Hcanon & Hvpn_def & Hpaal & HnotRVC & Hdec).
    assert (Hrun : forall σ0 : mstate,
       register_lookup cur_privilege σ0.(sregs) = User ->
       exec (dispatchInterrupt User) σ0 = Some (None, σ0) ->
       exec (fetch tt) σ0 = Some (F_Base w, σ0) ->
       exec (ext_decode w) σ0 = Some (ZICBOM (op, rs1), σ0) ->
       eq_vec (register_lookup elp σ0.(sregs))
              (landing_pad_bits_backwards LP_EXPECTED) = false ->
       register_lookup PC σ0.(sregs) = va ->
       register_lookup menvcfg σ0.(sregs) = MENVCFG_S ->
       register_lookup senvcfg σ0.(sregs) = (mword_of_int 0 : mword 64) ->
       exec (currentlyEnabled Ext_S) σ0 = Some (true, σ0) ->
       exec (run_hart_active 0) σ0
         = Some (Step_Execute (Illegal_Instruction tt, zero_extend' 32 w),
                 set_reg σ0 nextPC (add_vec_int va 4))).
    { intros σ0 Hcp Hdsp Hft Hdc Hlp Hpc Hmenv0 Hsenv0 HES0.
      apply (exec_hart_active_progress_base_gen User σ0 σ0
               (set_reg σ0 nextPC (add_vec_int va 4)) w
               (ZICBOM (op, rs1)) va (Illegal_Instruction tt)
               Hcp Hdsp Hft Hdc Hlp eq_refl Hpc).
      - apply exec_execute_ZICBOM_illegal.
        + lk. exact Hcp.
        + lk. exact Hmenv0.
        + lk. exact Hsenv0.
        + apply exec_currentlyEnabled_S_set_nextPC. exact HES0.
      - exact I. }
    iApply (ustep_illegal_run_st (ZICBOM (op, rs1))
              va vpn ie w ms_v sc_v stval_v sepc_v g tlbvec E Φ
              HN Hrun Hok Hvec Hchk0 HupdN Hpbmt0 Hcw HSXL Hval Hcanon
              Hvpn_def Hpaal HnotRVC Hdec).
  Qed.

  (* ZICBOZ (CBO.ZERO): illegal in U on menvcfg.CBZE = 0 (short-circuits before
     any memory access).  Only the menvcfg config hyp is needed. *)
  Lemma ustep_zicboz_illegal (rs1 : regidx)
      (va : mword 64) (vpn : mword 27) (ie : uwalk_info) (w : mword 32)
      (ms_v sc_v stval_v sepc_v : mword 64)
      (g : gmap regidx (mword 64)) (tlbvec : vec (option TLB_Entry) (2 ^ 6))
      E (Φ : mval -> iProp Σ) :
    upriv_illegal_arm (ZICBOZ rs1) va vpn ie w ms_v sc_v stval_v sepc_v g tlbvec E Φ ->
    hw_config -∗ minstret_inv -∗ hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ User -∗ mstatus ↦ᵣ ms_v -∗ scause ↦ᵣ sc_v -∗ stval ↦ᵣ stval_v -∗
    sepc ↦ᵣ sepc_v -∗ tlb ↦ᵣ tlbvec -∗ pc_is va -∗ gpr_file g -∗
    upt_inv root slots spec -∗ user_code -∗ user_data -∗ user_cfg -∗
    ▷ (user_trap_frame -∗ WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intros (HN & Hok & Hvec & Hchk0 & HupdN & Hpbmt0 & Hcw & HSXL & Hval &
            Hcanon & Hvpn_def & Hpaal & HnotRVC & Hdec).
    assert (Hrun : forall σ0 : mstate,
       register_lookup cur_privilege σ0.(sregs) = User ->
       exec (dispatchInterrupt User) σ0 = Some (None, σ0) ->
       exec (fetch tt) σ0 = Some (F_Base w, σ0) ->
       exec (ext_decode w) σ0 = Some (ZICBOZ rs1, σ0) ->
       eq_vec (register_lookup elp σ0.(sregs))
              (landing_pad_bits_backwards LP_EXPECTED) = false ->
       register_lookup PC σ0.(sregs) = va ->
       register_lookup menvcfg σ0.(sregs) = MENVCFG_S ->
       register_lookup senvcfg σ0.(sregs) = (mword_of_int 0 : mword 64) ->
       exec (currentlyEnabled Ext_S) σ0 = Some (true, σ0) ->
       exec (run_hart_active 0) σ0
         = Some (Step_Execute (Illegal_Instruction tt, zero_extend' 32 w),
                 set_reg σ0 nextPC (add_vec_int va 4))).
    { intros σ0 Hcp Hdsp Hft Hdc Hlp Hpc Hmenv0 _ _.
      apply (exec_hart_active_progress_base_gen User σ0 σ0
               (set_reg σ0 nextPC (add_vec_int va 4)) w
               (ZICBOZ rs1) va (Illegal_Instruction tt)
               Hcp Hdsp Hft Hdc Hlp eq_refl Hpc).
      - apply exec_execute_ZICBOZ_illegal.
        + lk. exact Hcp.
        + lk. exact Hmenv0.
      - exact I. }
    iApply (ustep_illegal_run_st (ZICBOZ rs1)
              va vpn ie w ms_v sc_v stval_v sepc_v g tlbvec E Φ
              HN Hrun Hok Hvec Hchk0 HupdN Hpbmt0 Hcw HSXL Hval Hcanon
              Hvpn_def Hpaal HnotRVC Hdec).
  Qed.

  (* SSAMOSWAP (Zicfiss shadow-stack AMO): illegal in U on senvcfg.SSE = 0
     with Ext_S on.  Needs all three config hyps. *)
  Lemma ustep_ssamoswap_illegal (aq rl : bool) (rs2 rs1 : regidx)
      (width : Z) (rd : regidx)
      (va : mword 64) (vpn : mword 27) (ie : uwalk_info) (w : mword 32)
      (ms_v sc_v stval_v sepc_v : mword 64)
      (g : gmap regidx (mword 64)) (tlbvec : vec (option TLB_Entry) (2 ^ 6))
      E (Φ : mval -> iProp Σ) :
    upriv_illegal_arm (SSAMOSWAP (aq, rl, rs2, rs1, width, rd))
      va vpn ie w ms_v sc_v stval_v sepc_v g tlbvec E Φ ->
    hw_config -∗ minstret_inv -∗ hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ User -∗ mstatus ↦ᵣ ms_v -∗ scause ↦ᵣ sc_v -∗ stval ↦ᵣ stval_v -∗
    sepc ↦ᵣ sepc_v -∗ tlb ↦ᵣ tlbvec -∗ pc_is va -∗ gpr_file g -∗
    upt_inv root slots spec -∗ user_code -∗ user_data -∗ user_cfg -∗
    ▷ (user_trap_frame -∗ WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intros (HN & Hok & Hvec & Hchk0 & HupdN & Hpbmt0 & Hcw & HSXL & Hval &
            Hcanon & Hvpn_def & Hpaal & HnotRVC & Hdec).
    assert (Hrun : forall σ0 : mstate,
       register_lookup cur_privilege σ0.(sregs) = User ->
       exec (dispatchInterrupt User) σ0 = Some (None, σ0) ->
       exec (fetch tt) σ0 = Some (F_Base w, σ0) ->
       exec (ext_decode w) σ0 = Some (SSAMOSWAP (aq, rl, rs2, rs1, width, rd), σ0) ->
       eq_vec (register_lookup elp σ0.(sregs))
              (landing_pad_bits_backwards LP_EXPECTED) = false ->
       register_lookup PC σ0.(sregs) = va ->
       register_lookup menvcfg σ0.(sregs) = MENVCFG_S ->
       register_lookup senvcfg σ0.(sregs) = (mword_of_int 0 : mword 64) ->
       exec (currentlyEnabled Ext_S) σ0 = Some (true, σ0) ->
       exec (run_hart_active 0) σ0
         = Some (Step_Execute (Illegal_Instruction tt, zero_extend' 32 w),
                 set_reg σ0 nextPC (add_vec_int va 4))).
    { intros σ0 Hcp Hdsp Hft Hdc Hlp Hpc Hmenv0 Hsenv0 HES0.
      apply (exec_hart_active_progress_base_gen User σ0 σ0
               (set_reg σ0 nextPC (add_vec_int va 4)) w
               (SSAMOSWAP (aq, rl, rs2, rs1, width, rd)) va (Illegal_Instruction tt)
               Hcp Hdsp Hft Hdc Hlp eq_refl Hpc).
      - apply exec_execute_SSAMOSWAP_illegal.
        + lk. exact Hcp.
        + lk. exact Hmenv0.
        + lk. exact Hsenv0.
        + apply exec_currentlyEnabled_S_set_nextPC. exact HES0.
      - exact I. }
    iApply (ustep_illegal_run_st (SSAMOSWAP (aq, rl, rs2, rs1, width, rd))
              va vpn ie w ms_v sc_v stval_v sepc_v g tlbvec E Φ
              HN Hrun Hok Hvec Hchk0 HupdN Hpbmt0 Hcw HSXL Hval Hcanon
              Hvpn_def Hpaal HnotRVC Hdec).
  Qed.

End WpUserPriv.
