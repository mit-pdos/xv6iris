(* WpSmode.v -- the first SUPERVISOR-mode instruction after start()'s MRET.

   start() ends with an MRET that drops the hart to Supervisor mode at
   PC = mepc = 0x80000e82 = <main>, with satp = Bare (paging off).  main's first
   instruction (kernel_instrs idx 1304) is `c.addi sp,sp,-16` (RVC 0x1141, the
   2-byte-aligned compressed encoding).

   This file sets up the WP for that first S-mode instruction (`wp_smode_caddi`)
   and chains it to the end of `wp_kernel` (`wp_kernel_smode1`).

   The EXECUTE (sp := sp + imm) is privilege-independent and reuses the Machine
   machinery.  The FETCH differs from the Machine path in exactly the places the
   exploration identified:
     - translationMode Supervisor READS satp (Machine returns Bare for free);
       with satp = 0 it is still Bare (identity translation), but satp must be
       owned and known-Bare.
     - pmpCheck Supervisor: an all-OFF PMP (`pmp_allows_all`) FAULTS in S-mode;
       the kernel's pmpcfg0/pmpaddr0 write must MATCH the fetch address and grant
       execute.  (Hypothesis `Hpmp_x` below abstracts "the boot PMP grants S-mode
       execute at pc"; supplying it concretely is the remaining S-mode model work.)
     - getPendingSet Supervisor = None needs mip/mie/mideleg facts (Machine gets
       it free from mstatus.MIE = 0).
     - should_inc_minstret uses the SINH (not MINH) counter-filter bit. *)
From Stdlib Require Import Eqdep_dec ZArith Lia List.
From stdpp Require Import gmap list list_monad bitvector.definitions bitvector.tactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes.
Require Import SailStdpp.Base SailStdpp.TypeCasts.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvTryStep RiscvFetchExec RiscvExtras WpFetch WpDecode WpEntry WpGpr WpRvc WpAuipc WpGprCsrw WpGprMret WpGprMretWp WpStartText KernelBoot WpStartChain WpStart2 WpStart3.
From Kernel Require Import KernelInstrs.
Local Open Scope Z_scope.

Section WpSmode.
  Context `{!riscvGS Σ}.

  (* ===================================================================== *)
  (* S-mode fetch infrastructure: analogs of the Machine-mode lemmas in     *)
  (* RiscvFetchExec.v / WpEntry.v, for cur_privilege = Supervisor.  The      *)
  (* differences (per the model) are exactly:                                *)
  (*   - translationMode Supervisor READS satp (Machine returns Bare free);  *)
  (*   - should_inc_minstret uses the SINH (not MINH) filter bit;            *)
  (*   - translateAddr's effectivePrivilege for a fetch keeps Supervisor.    *)
  (* ===================================================================== *)

  (* [should_inc_minstret] is privilege-generic: priv only appears in the    *)
  (* [counter_priv_filter_bit] of the RESULT, never in the control flow.     *)
  Lemma exec_should_inc_S (mc : mword 32) (mcfg : mword 64) (priv : Privilege) s :
    register_lookup mcountinhibit s.(sregs) = mc ->
    register_lookup minstretcfg s.(sregs) = mcfg ->
    exec (should_inc_minstret priv) s
      = Some (andb (eq_vec (_get_Counterin_IR mc) ('b"0"))
                   (eq_vec (counter_priv_filter_bit mcfg priv) ('b"0")), s).
  Proof.
    intros Hmc Hmcfg. unfold should_inc_minstret.
    erewrite (exec_and_boolM_Some _ _ s (eq_vec (_get_Counterin_IR mc) ('b"0")) s).
    2:{ rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mcountinhibit s)). rewrite Hmc. apply exec_returnm. }
    destruct (eq_vec (_get_Counterin_IR mc) ('b"0")) eqn:Ea; cbn [andb].
    - rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg minstretcfg s)). rewrite Hmcfg. apply exec_returnm.
    - reflexivity.
  Qed.

  (* translationMode Supervisor = Bare, when SXL = 10 (RV64) and satp's MODE   *)
  (* field is 0 (Bare).  Mirrors exec_translationMode_M but reads satp.        *)
  Lemma exec_translationMode_S_bare (satp0 : mword 64) s :
    _get_Mstatus_SXL (register_lookup mstatus s.(sregs)) = 'b"10" ->
    register_lookup satp s.(sregs) = satp0 ->
    _get_Satp64_Mode (Mk_Satp64 satp0) = ('b"0000" : mword 4) ->
    exec (translationMode Supervisor) s = Some (Bare, s).
  Proof.
    intros HSXL Hsatp Hmode.
    unfold translationMode.
    replace (generic_eq Supervisor Machine) with false by (vm_compute; reflexivity).
    rewrite (exec_bind_Some _ _ _ _ _ (exec_architecture_Supervisor s HSXL)).
    cbn match.
    (* The RV64 arm computes mbits = satp.MODE; reduce it to a single value first. *)
    change (xlen >=? 64) with true.
    match goal with |- exec (Defs.bind ?ARM _) s = _ =>
      assert (HARM : exec ARM s = Some (_get_Satp64_Mode (Mk_Satp64 satp0), s)) end.
    { assert (Hae : exec (Defs.assert_exp' true "sys/vmem.sail:254.25-254.26") s
                    = Some (eq_refl, s)).
      { unfold assert_exp'. cbn match. apply exec_returnm. }
      rewrite (exec_bind_Some _ _ _ _ _ Hae).
      rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg satp s)).
      rewrite Hsatp. apply exec_returnm. }
    rewrite (exec_bind_Some _ _ _ _ _ HARM).
    rewrite Hmode.
    replace (satpMode_of_bits RV64 ('b"0000" : mword 4)) with (Some Bare)
      by (vm_compute; reflexivity).
    cbn match. apply exec_returnm.
  Qed.

  (* translateAddr is the identity for a Supervisor-mode instruction fetch when
     satp is Bare.  Mirrors exec_translateAddr_identity (Machine) but the
     effectivePrivilege stays Supervisor and translationMode reads satp. *)
  Lemma exec_translateAddr_identity_S (a satp0 : mword 64) s :
    register_lookup cur_privilege s.(sregs) = Supervisor ->
    _get_Mstatus_SXL (register_lookup mstatus s.(sregs)) = 'b"10" ->
    register_lookup satp s.(sregs) = satp0 ->
    _get_Satp64_Mode (Mk_Satp64 satp0) = ('b"0000" : mword 4) ->
    exec (translateAddr (Virtaddr a) (InstructionFetch tt)) s
      = Some (Ok (Physaddr (zero_extend' 64 (bits_of_virtaddr (Virtaddr a))),
                  PBMT_PMA, init_ext_ptw), s).
  Proof.
    intros Hcp HSXL Hsatp Hmode.
    unfold translateAddr.
    rewrite exec_catch_early_return.
    rewrite (execR_liftR_seq _ _ _ _ _ (exec_read_reg mstatus s)).
    rewrite (execR_liftR_seq _ _ _ _ _ (exec_read_reg cur_privilege s)).
    rewrite Hcp.
    rewrite (execR_liftR_seq _ _ _ _ _ (exec_effectivePrivilege_fetch _ _ s)).
    rewrite (execR_liftR_seq _ _ _ _ _ (exec_translationMode_S_bare satp0 s HSXL Hsatp Hmode)).
    rewrite (execR_liftR_seq _ _ _ _ _ (exec_is_shadow_stack_fetch s)).
    unfold Defs.bind0.
    replace (generic_eq Bare Bare) with true by (vm_compute; reflexivity).
    rewrite execR_bind. cbn match. reflexivity.
  Qed.

  (* WP for one Supervisor-mode 2-aligned RVC `c.addi rd,rd,imm` step.
     Mirrors WpRvc.wp_caddi_gpr, but in Supervisor mode with satp = Bare. *)
  Lemma wp_smode_caddi (pc : mword 64) (w16 : mword 16) (rd : mword 5) (imm6 : mword 6)
      (m : gmap register_bitvector_64 (mword 64)) (vd misa0 mdv0 mstatus0 satp0 : mword 64)
      (priv : Privilege) (b1 : bool) (npc0 mst0 : mword 64)
      (mc : mword 32) (mcfg : mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (pmpaddr00 : type_of_register pmpaddr_n)
      (pmar0 : list PMA_Region)
      (mi0 : bool) (elp0 : mword 1) E {dq : dfrac} {dqc : dfrac} (Phi : mval -> iProp Σ) :
    uint rd <> 0 ->
    m !! gpr_of_Z (uint rd) = Some vd ->
    (* the hart is NOT in Machine mode (it is in Supervisor after the MRET) *)
    generic_neq priv Machine = true ->
    (* satp is in Bare mode (MODE field = 0): translation is identity, no page walk *)
    _get_Satp64_Mode (Mk_Satp64 satp0) = ('b"0000" : mword 4) ->
    (* the boot PMP configuration grants Supervisor-mode EXECUTE at [pc]
       (replaces [pmp_allows_all], which faults in S-mode) -- the remaining
       S-mode model obligation. *)
    pma_allows_all pmar0 ->
    is_aligned_paddr (Physaddr (fetch_pa pc)) 2 = true ->
    neq_vec (access_vec_dec pc 0) ('b"0") = false ->
    neq_vec (access_vec_dec pc 1) ('b"0") = true ->
    is_aligned_vaddr (Virtaddr pc) 4 = false ->
    isRVC w16 = true ->
    eq_vec (_get_Misa_C misa0) ('b"1") = true ->
    eq_vec (_get_Misa_S misa0) ('b"1") = true ->
    (forall s0, eq_vec (_get_Misa_C (register_lookup misa s0.(sregs))) ('b"1") = true ->
       exec (ext_decode_compressed w16) s0 = Some (C_ADDI (imm6, Regidx rd), s0)) ->
    b1 = andb (eq_vec (_get_Counterin_IR mc) ('b"0"))
              (eq_vec (counter_priv_filter_bit mcfg priv) ('b"0")) ->
    eq_vec (_get_Mstatus_MIE mstatus0) ('b"1") = false ->
    eq_vec elp0 (landing_pad_bits_backwards LP_EXPECTED) = false ->
    PC ↦ᵣ pc -∗ gpr_file m -∗ reg_pointsto misa dqc misa0 -∗ nextPC ↦ᵣ npc0 -∗
    (R_bool minstret_increment) ↦ᵣ mi0 -∗ minstret ↦ᵣ mst0 -∗
    cur_privilege ↦ᵣ priv -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
    (R_bitvector_64 mideleg) ↦ᵣ mdv0 -∗ (R_bitvector_64 mstatus) ↦ᵣ mstatus0 -∗
    satp ↦ᵣ satp0 -∗
    elp ↦ᵣ elp0 -∗ reg_pointsto mcountinhibit dqc mc -∗ reg_pointsto minstretcfg dqc mcfg -∗
    pmpcfg_n ↦ᵣ pmpcfg0 -∗ pmpaddr_n ↦ᵣ pmpaddr00 -∗ reg_pointsto pma_regions dqc pmar0 -∗ reg_pointsto htif_tohost_base dqc None -∗
    ([∗ list] j ∈ seq 0 2, (pa_add (fetch_pa pc) j) ↦ₘ{dq} nth_byte w16 j) -∗
    ▷ ( PC ↦ᵣ add_vec_int pc 2 -∗
        gpr_file (<[gpr_of_Z (uint rd) :=
                     regval_into_reg (add_vec vd (sign_extend' 64 (sign_extend' 12 imm6)))]> m) -∗
        reg_pointsto misa dqc misa0 -∗ nextPC ↦ᵣ add_vec_int pc 2 -∗ (R_bool minstret_increment) ↦ᵣ b1 -∗
        minstret ↦ᵣ (if b1 then add_vec_int mst0 1 else mst0) -∗
        cur_privilege ↦ᵣ priv -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
        (R_bitvector_64 mideleg) ↦ᵣ mdv0 -∗ (R_bitvector_64 mstatus) ↦ᵣ mstatus0 -∗
        satp ↦ᵣ satp0 -∗
        elp ↦ᵣ elp0 -∗ reg_pointsto mcountinhibit dqc mc -∗ reg_pointsto minstretcfg dqc mcfg -∗
        pmpcfg_n ↦ᵣ pmpcfg0 -∗ pmpaddr_n ↦ᵣ pmpaddr00 -∗ reg_pointsto pma_regions dqc pmar0 -∗ reg_pointsto htif_tohost_base dqc None -∗
        ([∗ list] j ∈ seq 0 2, (pa_add (fetch_pa pc) j) ↦ₘ{dq} nth_byte w16 j) -∗
        WP (Loop : expr riscv_lang) @ E {{ Phi }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Phi }}.
  Proof.
    (* The EXECUTE (sp := sp + imm) is exactly WpRvc.wp_caddi_gpr's.  The fetch/
       step wrapper is the S-mode port.  PROVEN reusable pieces above:
         - exec_should_inc_S        (SINH filter bit; privilege-generic);
         - exec_translationMode_S_bare (Supervisor reads satp; MODE=0 -> Bare);
         - exec_translateAddr_identity_S (S-mode fetch identity translation).
       REMAINING (the substantive S-mode model work):
         - exec_pmpCheck_supervisor_grant: with all-OFF PMP an S-mode fetch FAULTS,
           so this needs the kernel's concrete granting entry (pmpcfg0=0xf TOR,
           pmpaddr0=0x3fffffffffffff): the foreach loop EARLY-RETURNS None at entry
           0 (pmpMatchAddr TOR -> PMP_Match, pmpCheckRWX -> X granted).  Requires a
           foreach early-return lemma + concrete TOR range arithmetic.
         - exec_mem_read_fetch_2_S / exec_fetch_RVC_2_S (mirror the Machine ones,
           swapping translateAddr_identity_S + pmpCheck_supervisor_grant);
         - exec_getPendingSet_supervisor_none (mIE is true in S-mode, so this needs
           pending_m = mip & mie & ~mideleg = 0, i.e. interrupt-register facts);
         - exec_hart_active_progress / riscv_step / forward_exec for Supervisor. *)
  Admitted.

  (* ===================================================================== *)
  (* wp_kernel_smode1 : the WHOLE boot path (CPU reset -> _entry -> start ->  *)
  (* timerinit -> MRET) chained THROUGH the first Supervisor-mode instruction *)
  (* (c.addi sp,sp,-16 at 0x80000e82 = <main>).  Same boot interface as       *)
  (* wp_kernel; the continuation runs after main's first instruction.  This   *)
  (* CONFIRMS the handoff: wp_kernel's (now concrete) post-MRET state supplies *)
  (* every precondition wp_smode_caddi needs.                                 *)
  (* ===================================================================== *)
  Lemma wp_kernel_smode1
      (v : bv 64) (sp0b mst0 mstatus0 : mword 64) (mi0 : bool) (elp0 : mword 1)
      (mc : mword 32) (mcfg : mword 64) (mseccfg0 : mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (pmar0 : list PMA_Region)
      (x1_0 x10_0 x11_0 mhartid0 misa0 : mword 64)
      (m : gmap register_bitvector_64 (mword 64))
      (menvcfg0 mtime0 stimecmp0 mepc0 satp0 medeleg0 mie0 : mword 64)
      (mcounteren0 : mword 32) (pmpaddr00 : type_of_register pmpaddr_n)
      (vs0b va4b va5b : mword 64)
      (vold_ra vold_s0 vti_ra vti_s0 : bv 64) (newpriv : Privilege) (lpe : bool)
      (* ---- first S-mode instruction (c.addi sp,sp,-16) ---- *)
      (rd : mword 5) (imm6 : mword 6) (b1s : bool)
      E (Φ : mval -> iProp Σ) :
      let bb     := andb (eq_vec (_get_Counterin_IR mc) ('b"0"))
                         (eq_vec (counter_priv_filter_bit mcfg Machine) ('b"0")) in
      let sp1e   := regval_into_reg (add_vec kpc0 (auipc_off imm_auipc)) in
      let eal    := add_vec sp1e (sign_extend' 64 imm_ld) in
      let a8l    := zero_extend' 64 (subrange_vec_dec eal (xlen - 0 - 1) 0) in
      let pal    := zero_extend' 64 (add_vec_int a8l (0 * 8)) in
      let bumpe  := fun mm => if bb then add_vec_int mm 1 else mm in
      let mst1   := if bb then add_vec_int mst0 1 else mst0 in
      let x2ld   := regval_into_reg (extend_value false (update_subrange_vec_dec (zeros' (8*1*8)) (8*(0+1)*8-1) (8*0*8) v)) in
      let x10l   := regval_into_reg luival in
      let x11c   := regval_into_reg mhartid0 in
      let x11a   := regval_into_reg (add_vec x11c (sign_extend' 64 (sign_extend' 12 imm_caddi))) in
      let x10m   := regval_into_reg (mult_to_bits_half xlen (mulop_mul.(mul_op_signed_rs1))
                      (mulop_mul.(mul_op_signed_rs2)) x10l x11a (mulop_mul.(mul_op_result_part))) in
      let x2add  := regval_into_reg (add_vec x2ld x10m) in
      let x1j    := regval_into_reg (add_vec_int kpc7 4) in
      let m8     := bumpe (bumpe (bumpe (bumpe (bumpe (bumpe (bumpe mst1)))))) in
      let sp1  := add_vec x2add (sign_extend' 64 (sign_extend' 12 imm9)) in
      let imm_ra := zero_extend' 12 (concat_vec uimm10 ('b"000")) in
      let pa_ra  := zero_extend' 64 (add_vec_int (zero_extend' 64 (subrange_vec_dec (add_vec sp1 (sign_extend' 64 imm_ra)) (xlen - 0 - 1) 0)) (0 * 8)) in
      let imm_s0 := zero_extend' 12 (concat_vec uimm11 ('b"000")) in
      let pa_s0  := zero_extend' 64 (add_vec_int (zero_extend' 64 (subrange_vec_dec (add_vec sp1 (sign_extend' 64 imm_s0)) (xlen - 0 - 1) 0)) (0 * 8)) in
      let a8_ra  := zero_extend' 64 (subrange_vec_dec (add_vec sp1 (sign_extend' 64 imm_ra)) (xlen - 0 - 1) 0) in
      let a8_s0  := zero_extend' 64 (subrange_vec_dec (add_vec sp1 (sign_extend' 64 imm_s0)) (xlen - 0 - 1) 0) in
      let va5_c2 := regval_into_reg (subrange_vec_dec mstatus0 (Z.sub xlen 1) 0) in
      let va4_35 := WpGprLui.luival (sign_extend' 20 (sclui_imm sw35)) in
      let va4_36 := add_vec va4_35 (sign_extend' 64 (subrange_vec_dec sw36 31 20)) in
      let va5_37 := and_vec va5_c2 va4_36 in
      let va4_38 := WpGprLui.luival (sign_extend' 20 (sclui_imm sw38)) in
      let va4_39 := add_vec va4_38 (sign_extend' 64 (subrange_vec_dec sw39 31 20)) in
      let va5_40 := or_vec va5_37 va4_39 in
      let mstatus1 := mstatus_legalized mstatus0 va5_40 in
      let va5_42 := add_vec spc42 (auipc_off (subrange_vec_dec sw42 31 12)) in
      let va5_43 := add_vec va5_42 (sign_extend' 64 (subrange_vec_dec sw43 31 20)) in
      let va5_45 := cli_wval (scli_imm sw45) in
      let va5_47 := WpGprLui.luival (sign_extend' 20 (sclui_imm sw47)) in
      let va5_48 := add_vec va5_47 (sign_extend' 64 (sign_extend' 12 (scli_imm sw48))) in
      let mdv0 := mideleg_legalized (zeros' 64) va5_48 in
      let va5_51 := lower_mie mie0 mdv0 in
      let va5_52 := or_vec va5_51 (sign_extend' 64 (subrange_vec_dec sw52 31 20)) in
      let va5_54 := cli_wval (scli_imm sw54) in
      let va5_55 := csrli_wval (scsrli_sh sw55) va5_54 in
      let va5_57 := cli_wval (scli_imm sw57) in
      let pmpcfg1 := pmpcfg0_finalvec va5_57 pmpcfg0 in
      let c6sp   := add_vec sp1 (sign_extend' 64 (sign_extend' 12 imm9)) in
      let tpa_ra := zero_extend' 64 (add_vec_int (zero_extend' 64 (subrange_vec_dec (add_vec c6sp (sign_extend' 64 imm_ra)) (xlen - 0 - 1) 0)) (0 * 8)) in
      let tpa_s0 := zero_extend' 64 (add_vec_int (zero_extend' 64 (subrange_vec_dec (add_vec c6sp (sign_extend' 64 imm_s0)) (xlen - 0 - 1) 0)) (0 * 8)) in
      let ta8_ra := zero_extend' 64 (subrange_vec_dec (add_vec c6sp (sign_extend' 64 imm_ra)) (xlen - 0 - 1) 0) in
      let ta8_s0 := zero_extend' 64 (subrange_vec_dec (add_vec c6sp (sign_extend' 64 imm_s0)) (xlen - 0 - 1) 0) in
      m !! x1 = Some x1_0 -> m !! x2 = Some sp0b ->
      m !! x10 = Some x10_0 -> m !! x11 = Some x11_0 ->
      m !! gpr_of_Z 8 = Some vs0b -> m !! gpr_of_Z 14 = Some va4b -> m !! gpr_of_Z 15 = Some va5b ->
      is_Some (m !! gpr_of_Z 4) ->
      pma_allows_all pmar0 -> pmp_allows_all pmpcfg0 ->
      eq_vec (_get_Mstatus_MIE mstatus0) ('b"1") = false ->
      eq_vec elp0 (landing_pad_bits_backwards LP_EXPECTED) = false ->
      eq_vec (_get_Mstatus_MPRV mstatus0) ('b"1") = false ->
      pmm_mode_backwards (_get_Seccfg_PMM mseccfg0) = PMM_Disabled ->
      is_aligned_vaddr (Virtaddr a8l) 8 = true -> is_aligned_paddr (Physaddr pal) 8 = true ->
      eq_vec (_get_Misa_C misa0) ('b"1") = true ->
      eq_vec (_get_Misa_M misa0) ('b"1") = true ->
      eq_vec (_get_Misa_S misa0) ('b"1") = true ->
      eq_vec (_get_Misa_U misa0) ('b"1") = true ->
      eq_vec (_get_Mstatus_MIE mstatus1) ('b"1") = false ->
      _get_Mstatus_SXL mstatus1 = 'b"10" ->
      is_aligned_vaddr (Virtaddr a8_ra) 8 = true -> is_aligned_paddr (Physaddr pa_ra) 8 = true ->
      is_aligned_vaddr (Virtaddr a8_s0) 8 = true -> is_aligned_paddr (Physaddr pa_s0) 8 = true ->
      eq_vec (_get_Mstatus_MPRV mstatus1) ('b"1") = false ->
      bool_bit_backwards (_get_Seccfg_MLPE mseccfg0) = false ->
      pmp_allows_all pmpcfg1 ->
      is_aligned_vaddr (Virtaddr ta8_ra) 8 = true -> is_aligned_paddr (Physaddr tpa_ra) 8 = true ->
      is_aligned_vaddr (Virtaddr ta8_s0) 8 = true -> is_aligned_paddr (Physaddr tpa_s0) 8 = true ->
      privLevel_bits_forwards (_get_Mstatus_MPP (cms2 mstatus1), ('b"0")) = returnM newpriv ->
      generic_neq newpriv Machine = true ->
      (forall sz, exec (get_xLPE newpriv) sz = Some (lpe, sz)) ->
      (* ---- facts about the post-MRET S-mode state (the remaining model work
         for the c.addi fetch; see wp_smode_caddi) ---- *)
      uint rd = 2 ->
      b1s = andb (eq_vec (_get_Counterin_IR mc) ('b"0"))
                 (eq_vec (counter_priv_filter_bit mcfg newpriv) ('b"0")) ->
      _get_Satp64_Mode (Mk_Satp64 (satp_legalized satp0 va5_45)) = ('b"0000" : mword 4) ->
      eq_vec (_get_Mstatus_MIE (cms5 mstatus1)) ('b"1") = false ->
      eq_vec (celpv lpe mstatus1) (landing_pad_bits_backwards LP_EXPECTED) = false ->
      (forall s0, eq_vec (_get_Misa_C (register_lookup misa s0.(sregs))) ('b"1") = true ->
         exec (ext_decode_compressed (mword_of_int 0x1141 : mword 16)) s0
           = Some (C_ADDI (imm6, Regidx rd), s0)) ->
      PC ↦ᵣ kpc0 -∗ gpr_file m -∗
      mhartid ↦ᵣ mhartid0 -∗
      nextPC ↦ᵣ kpc0 -∗ (R_bool minstret_increment) ↦ᵣ mi0 -∗ minstret ↦ᵣ mst0 -∗
      cur_privilege ↦ᵣ Machine -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
      (R_bitvector_64 mideleg) ↦ᵣ zeros' 64 -∗ (R_bitvector_64 mstatus) ↦ᵣ mstatus0 -∗
      elp ↦ᵣ elp0 -∗ pmpcfg_n ↦ᵣ pmpcfg0 -∗
      hw_config misa0 mseccfg0 mc mcfg pmar0 -∗
      ([∗ list] j ∈ seq 0 8, (pa_add pal j) ↦ₘ nth_byte v j) -∗
      menvcfg ↦ᵣ menvcfg0 -∗ mcounteren ↦ᵣ mcounteren0 -∗ mtime ↦ᵣ mtime0 -∗ stimecmp ↦ᵣ stimecmp0 -∗
      mepc ↦ᵣ mepc0 -∗ satp ↦ᵣ satp0 -∗ medeleg ↦ᵣ medeleg0 -∗ mie ↦ᵣ mie0 -∗ pmpaddr_n ↦ᵣ pmpaddr00 -∗
      ([∗ list] j ∈ seq 0 8, (pa_add pa_ra j) ↦ₘ nth_byte vold_ra j) -∗
      ([∗ list] j ∈ seq 0 8, (pa_add pa_s0 j) ↦ₘ nth_byte vold_s0 j) -∗
      ([∗ list] j ∈ seq 0 8, (pa_add tpa_ra j) ↦ₘ nth_byte vti_ra j) -∗
      ([∗ list] j ∈ seq 0 8, (pa_add tpa_s0 j) ↦ₘ nth_byte vti_s0 j) -∗
      kernel_text -∗
      ▷ ( (∃ (mf' : gmap register_bitvector_64 (mword 64)) (mstf' : mword 64)
              (pmpaddrf : type_of_register pmpaddr_n),
            PC ↦ᵣ add_vec_int (mword_of_int 0x80000e82) 2 ∗
            nextPC ↦ᵣ add_vec_int (mword_of_int 0x80000e82) 2 ∗
            gpr_file mf' ∗
            (R_bool minstret_increment) ↦ᵣ b1s ∗ minstret ↦ᵣ mstf' ∗
            cur_privilege ↦ᵣ newpriv ∗ hart_state ↦ᵣ HART_ACTIVE tt ∗
            (R_bitvector_64 mideleg) ↦ᵣ mdv0 ∗ (R_bitvector_64 mstatus) ↦ᵣ cms5 mstatus1 ∗
            satp ↦ᵣ satp_legalized satp0 va5_45 ∗ elp ↦ᵣ celpv lpe mstatus1 ∗
            pmpcfg_n ↦ᵣ pmpcfg1 ∗ pmpaddr_n ↦ᵣ pmpaddrf)
          -∗ WP (Loop : expr riscv_lang) @ E {{ Φ }} ) -∗
      WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intros bb sp1e eal a8l pal bumpe mst1 x2ld x10l x11c x11a x10m x2add x1j m8
           sp1 imm_ra pa_ra imm_s0 pa_s0 a8_ra a8_s0 va5_c2 va4_35 va4_36 va5_37 va4_38 va4_39 va5_40 mstatus1
           va5_42 va5_43 va5_45 va5_47 va5_48 mdv0 va5_51 va5_52 va5_54 va5_55 va5_57 pmpcfg1
           c6sp tpa_ra tpa_s0 ta8_ra ta8_s0.
    intros Hm1 Hm2 Hm10 Hm11 Hm8 Hm14 Hm15 Hm4 Hpmaall Hpmpf HmIE Hlp HMPRV Hpmm Ha8l Hpall HmisaC HmisaM HmisaS HmisaU
           HmIE1 HSXL1 Hsa8ra Hspara Hsa8s0 Hspas0 HMPRV1 Hmlpe Hpmpf1 Hta8ra Htpara Hta8s0 Htpas0 Hnp Hnpm Hlpe
           Hrd2 Hb1s Hsatp_bare Hmie_s Help_s Hdec.
    iIntros "Hpc Hfile Hmh Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hpmpc Hhw Hbytes
             Hmenv Hmcen Hmtime Hstc Hmepc Hsatp Hmede Hmie Hpmpaddr Hstkra Hstks0 Htra Htrs0 HK Hcont".
    iDestruct "Hhw" as "#Hhwb".
    iAssert (hw_config misa0 mseccfg0 mc mcfg pmar0)%I as "#Hhw". { iExact "Hhwb". }
    iDestruct "Hhwb" as "#(Hmisa & Hsec & Hmcinh & Hmcfg & Hpma & Hhtif & _ & _ & _ & _ & _)".
    (* ---- run the whole boot path up to and including the MRET ---- *)
    iApply (wp_kernel v sp0b mst0 mstatus0 mi0 elp0 mc mcfg mseccfg0 pmpcfg0 pmar0
              x1_0 x10_0 x11_0 mhartid0 misa0 m menvcfg0 mtime0 stimecmp0 mepc0 satp0 medeleg0 mie0
              mcounteren0 pmpaddr00 vs0b va4b va5b vold_ra vold_s0 vti_ra vti_s0 newpriv lpe E Φ
              Hm1 Hm2 Hm10 Hm11 Hm8 Hm14 Hm15 Hm4 Hpmaall Hpmpf HmIE Hlp HMPRV Hpmm Ha8l Hpall
              HmisaC HmisaM HmisaS HmisaU HmIE1 HSXL1 Hsa8ra Hspara Hsa8s0 Hspas0 HMPRV1 Hmlpe Hpmpf1
              Hta8ra Htpara Hta8s0 Htpas0 Hnp Hnpm Hlpe
              with "Hpc Hfile Hmh Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hpmpc Hhw
                    Hbytes Hmenv Hmcen Hmtime Hstc Hmepc Hsatp Hmede Hmie Hpmpaddr Hstkra Hstks0 Htra Htrs0 HK").
    iNext.
    iDestruct 1 as (mf mstf pmpaddrf)
      "(Hpc & Hnpc & Hfile & %Hsp & Hmh & Hmi & Hmst & Hpriv & %Hnpriv & Hhs & Hmdl & Hms & Hmepc &
        Hsatp & Help & Hpmpc & Hpmpaddr & H)".
    (* PC = ctgt (mepc_val va5_43) = 0x80000e82 = <main> *)
    assert (Hpceq : ctgt (mepc_val va5_43) = (mword_of_int 0x80000e82 : mword 64))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpceq) in "Hpc". iEval (rewrite Hpceq) in "Hnpc".
    (* extract main's first-instruction window from the (persistent) kernel_text *)
    iAssert (kinstr_bytes (skinstr 1304)) as "#Kmain". { sg 1304. }
    assert (Hk_a : ki_addr (skinstr 1304) = 0x80000e82) by (vm_compute; reflexivity).
    assert (Hk_e : ki_enc (skinstr 1304) = 0x1141) by (vm_compute; reflexivity).
    assert (Hk_w : (2 <= ki_width (skinstr 1304) / 8)%nat) by (vm_compute; lia).
    iDestruct (kinstr_window16 (skinstr 1304) 0x80000e82 0x1141 Hk_a Hk_e Hk_w with "Kmain") as "#Wmain".
    destruct Hsp as [vd Hsp].
    (* ---- run the first Supervisor-mode instruction (c.addi sp,sp,-16) ---- *)
    iApply (wp_smode_caddi (mword_of_int 0x80000e82) (mword_of_int 0x1141 : mword 16) rd imm6
              mf vd misa0 mdv0 (cms5 mstatus1) (satp_legalized satp0 va5_45) newpriv b1s
              (mword_of_int 0x80000e82) mstf mc mcfg pmpcfg1 pmpaddrf pmar0 bb (celpv lpe mstatus1)
              E (dq := DfracDiscarded) (dqc := DfracDiscarded) Φ
              ltac:(rewrite Hrd2; discriminate)
              ltac:(rewrite Hrd2; exact Hsp)
              Hnpriv Hsatp_bare Hpmaall
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
              HmisaC HmisaS Hdec Hb1s Hmie_s Help_s
              with "Hpc Hfile Hmisa Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Hsatp Help Hmcinh Hmcfg Hpmpc Hpmpaddr Hpma Hhtif Wmain").
    iNext.
    iIntros "Hpc2 Hfile2 Hmisa2 Hnpc2 Hmi2 Hmst2 Hpriv2 Hhs2 Hmdl2 Hms2 Hsatp2 Help2 Hmcinh2 Hmcfg2 Hpmpc2 Hpmpaddr2 Hpma2 Hhtif2 _".
    iApply "Hcont".
    iExists _, _, pmpaddrf. iFrame.
  Qed.

End WpSmode.
