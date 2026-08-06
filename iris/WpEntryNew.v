(* WpEntryNew.v -- the xv6 kernel [_entry] boot sequence (8 instructions at
   0x80000000) up to and including the [jal] into [start()], proved as ONE WP
   theorem [wp_entry] by composing ONLY the new-style [wp_*_gpr] WP lemmas.

   The eight instructions (ground truth from the ELF dump):
     0x80000000 AUIPC   sp := pc + (imm_auipc<<12)          [4-aligned, F_Base]
     0x80000004 LOAD    sp := mem[sp + sext(imm_ld)]        [4-aligned, F_Base]
     0x80000008 C.LUI   a0 := 0x1000                        [RVC]
     0x8000000a CSRRS   a1 := mhartid                       [2-aligned, F_Base]
     0x8000000e C.ADDI  a1 := a1 + 1                        [RVC]
     0x80000010 MUL     a0 := a0 * a1                       [4-aligned, F_Base]
     0x80000014 C.ADD   sp := sp + a0                       [RVC]
     0x80000016 JAL     ra := pc+4; PC := start (0x80000058) [2-aligned, F_Base]

   All decoded-field / word Definitions (imm_auipc, i_auipc, imm_ld, i_ld,
   imm_clui, rd_clui, csr_csrr, i_rd_csrr, imm_caddi, rsd_caddi, i_mul_*,
   rsd_cadd, rs2_cadd, imm_jal, i_jal, mulop_mul) are REUSED from WpDecode.v /
  .v -- not redefined here.

   The chain applies, in order:
     wp_auipc_gpr → wp_ld_gpr → wp_clui_gpr → wp_csrr_mhartid_gpr
       → wp_caddi_gpr → wp_mul_gpr → wp_cadd_gpr → wp_jal_gpr
   threading pc_is / gpr_file / mmode_config / pmpcfg_n through each
   continuation.  The two 2-aligned full instructions (csrr@0xa, jal@0x16)
   now go through the SAME [instr]/[wp_instr]-based WPs as the 4-aligned
   ones: [instr]/[instr_bytes] dispatch on alignment (InstrBytes.v), so
   [wp_csrr_mhartid_gpr] / [wp_jal_gpr] work at any 2-aligned PC. *)
From Stdlib Require Import ZArith.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language.
Require Import SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import SailStdpp.Base.
Require Import RiscvLang RegFile RiscvPtsto RiscvFetchExec WpDecode WpGpr.
Require Import WpAuipc WpMmodeMul WpMmodeJal.
Require Import RiscvExtras.
Require Import WpMmodeLeafBase.
Require Import WpMmodeLoad.
Require Import WpGprCsrrA.
Require Import WpMmodeUtype.
Require Import WpMmodeItype.
Require Import WpMmodeRtype.
Require Import InstrBytes KernelText.
From iris.base_logic.lib Require Import invariants.
From Kernel Require KernelInstrs.
From Kernel Require KernelSyms.
Require Import CodeEntry.
Require Import CodeEntryAux.
Local Open Scope Z_scope.

(* Moved here from WpDecode.v via the late KernelBoot.v (this file is now their
   only user): the one-shot decodes of _entry's two 32-bit prefix instructions. *)

(* discharge [wp_instr]'s per-byte static premise at a concrete boot pc:
   M-mode fetch is untranslated, so the identity/static window is guard-permitted. *)
Ltac boot_static :=
  apply KptPt.instr_window_static; intros jj Hjj; unfold addr_is_text;
  destruct jj as [|[|[|[|]]]]; try lia;
  (split; [vm_compute; discriminate | vm_compute; reflexivity]).

Section WpEntryNew.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.


  (* The load effective address: sp (just set by AUIPC) + sext(imm_ld). *)
  Definition entry_ld_ea : mword 64 := add_vec entry_sp1 (sign_extend' 64 imm_ld).

  (* ---- pure address / register arithmetic, all by vm_compute ---- *)
  Lemma pc_e0_e1 : add_vec_int pc_e0 4 = pc_e1.
  Proof. vm_compute. reflexivity. Qed.
  Lemma pc_e1_e2 : add_vec_int pc_e1 4 = pc_e2.
  Proof. vm_compute. reflexivity. Qed.
  Lemma pc_e2_e3 : add_vec_int pc_e2 2 = pc_e3.
  Proof. vm_compute. reflexivity. Qed.
  Lemma pc_e3_e4 : add_vec_int pc_e3 4 = pc_e4.
  Proof. vm_compute. reflexivity. Qed.
  Lemma pc_e4_e5 : add_vec_int pc_e4 2 = pc_e5.
  Proof. vm_compute. reflexivity. Qed.
  Lemma pc_e5_e6 : add_vec_int pc_e5 4 = pc_e6.
  Proof. vm_compute. reflexivity. Qed.
  Lemma pc_e6_e7 : add_vec_int pc_e6 2 = pc_e7.
  Proof. vm_compute. reflexivity. Qed.
  Lemma pc_e7_start : add_vec pc_e7 (sign_extend' 64 imm_jal) = pc_start.
  Proof. vm_compute. reflexivity. Qed.
  Lemma jal_aligned :
    is_aligned_paddr (Physaddr (add_vec pc_e7 (sign_extend' 64 imm_jal))) 4 = true.
  Proof. vm_compute. reflexivity. Qed.

  (* i_ld and i_auipc are the same architectural register (x2/sp). *)
  Lemma reg_ld_auipc : (Regidx i_ld : regidx) = Regidx i_auipc.
  Proof. vm_compute. reflexivity. Qed.

  (* [kernel_text], [kernel_window_pc], [pa_add_mword] and the [mk_base] /
     [mk_rvc] constructors come from the lightweight [KernelText] base. *)

  (* ---- the eight [_entry] instructions, each recovered from the image.
     Every constructor is [kernel_text -∗ instr ...]. *)






  (* MUL's decoder wants misa.M; [close_dec] computes it from the [misa =
     MISA_C] hypothesis [instr] already supplies, so no [hw_config] is
     needed here. *)



  (* The final gpr_file after the eight writes, in terms of the abstract initial
     map [m], the loaded stack pointer [v_stack0], and the abstract [mhartid_in].
     Each nested insert is exactly the continuation map handed back by the
     corresponding WP.  (a1's C.ADDI and a0's MUL and sp's C.ADD read their
     inputs off the threaded map, so their written values are left as symbolic
     [!!!] reads over the running map -- exactly what the WPs produce.) *)
  Definition m_auipc (m : regfile) : regfile :=
    <[Regidx i_auipc := regval_into_reg entry_sp1]> m.
  Definition m_ld (m : regfile) (v_stack0 : bv 64)
      : regfile :=
    <[Regidx i_ld := regval_into_reg v_stack0]> (m_auipc m).
  Definition m_clui (m : regfile) (v_stack0 : bv 64)
      : regfile :=
    <[Regidx (regidx_bits rd_clui) :=
        regval_into_reg (luival (sign_extend' 20 imm_clui))]> (m_ld m v_stack0).
  Definition m_csrr (m : regfile) (v_stack0 : bv 64)
      (mhartid_in : mword 64) : regfile :=
    <[Regidx i_rd_csrr := regval_into_reg mhartid_in]> (m_clui m v_stack0).
  Definition m_caddi (m : regfile) (v_stack0 : bv 64)
      (mhartid_in : mword 64) : regfile :=
    <[Regidx (regidx_bits rsd_caddi) :=
        regval_into_reg
          (add_vec (m_csrr m v_stack0 mhartid_in !!! Regidx (regidx_bits rsd_caddi))
             (sign_extend' 64 imm_caddi))]> (m_csrr m v_stack0 mhartid_in).
  Definition m_mul (m : regfile) (v_stack0 : bv 64)
      (mhartid_in : mword 64) : regfile :=
    <[Regidx i_mul_rd :=
        regval_into_reg
          (mult_to_bits_half xlen (mulop_mul.(mul_op_signed_rs1))
             (mulop_mul.(mul_op_signed_rs2))
             (m_caddi m v_stack0 mhartid_in !!! Regidx i_mul_rs1)
             (m_caddi m v_stack0 mhartid_in !!! Regidx i_mul_rs2)
             (mulop_mul.(mul_op_result_part)))]> (m_caddi m v_stack0 mhartid_in).
  Definition m_cadd (m : regfile) (v_stack0 : bv 64)
      (mhartid_in : mword 64) : regfile :=
    <[Regidx (regidx_bits rsd_cadd) :=
        regval_into_reg
          (add_vec (m_mul m v_stack0 mhartid_in !!! Regidx (regidx_bits rsd_cadd))
             (m_mul m v_stack0 mhartid_in !!! Regidx (regidx_bits rs2_cadd)))]>
      (m_mul m v_stack0 mhartid_in).
  Definition m_jal (m : regfile) (v_stack0 : bv 64)
      (mhartid_in : mword 64) : regfile :=
    <[Regidx i_jal := regval_into_reg (add_vec_int pc_e7 4)]>
      (m_cadd m v_stack0 mhartid_in).

  (* ================================================================= *)
  (*  THE THEOREM: the whole [_entry] boot chain, one Qed.             *)
  (* ================================================================= *)
  Lemma wp_entry (Φ : mval -> iProp Σ)
      (m : regfile) (v_stack0 : bv 64) (mhartid_in : mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) {dq : dfrac} :
    (* [pmp_all_off] (not just unlocked): the chain contains an 8-byte load
       (`ld sp, ..`), whose PMP check needs the all-OFF form -- see the note
       on [pmp_all_off] in RiscvFetchExec.v.  It holds of the boot-time
       all-zero pmpcfg by vm_compute. *)
    pmp_all_off pmpcfg0 ->
    mmode_config (DfracOwn 1) -∗
    pmpcfg_n ↦ᵣ pmpcfg0 -∗
    pc_is pc_e0 -∗
    gpr_file m -∗
    mhartid ↦ᵣ mhartid_in -∗
    (* the stack0 pointer word sitting at the load effective address *)
    entry_ld_ea ↦ₚ₈{ dq } v_stack0 -∗
    (* the kernel text image: the eight decoded [instr] facts are derived from
       it inside the proof via the [entry_instr_*] constructors ([kernel_text]
       is persistent, so one copy feeds all eight) *)
    kernel_text -∗
    ( mmode_config (DfracOwn 1) -∗
      pmpcfg_n ↦ᵣ pmpcfg0 -∗
      pc_is pc_start -∗
      gpr_file (m_jal m v_stack0 mhartid_in) -∗
      mhartid ↦ᵣ mhartid_in -∗
      entry_ld_ea ↦ₚ₈{ dq } v_stack0 -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    iIntros (Hpmp)
      "Hmm Hpmpc Hpc Hfile Hmh Hbytes #Htext Hcont".
    pose proof (pmp_all_off_allows_all _ Hpmp) as HpmpU.
    (* derive the eight [instr] facts off the (persistent) text image *)
    iPoseProof (entry_instr_auipc with "Htext") as "Hi0".
    iPoseProof (entry_instr_ld    with "Htext") as "Hi1".
    iPoseProof (entry_instr_clui  with "Htext") as "Hi2".
    iPoseProof (entry_instr_csrr  with "Htext") as "Hi3".
    iPoseProof (entry_instr_caddi with "Htext") as "Hi4".
    iPoseProof (entry_instr_mul   with "Htext") as "Hi5".
    iPoseProof (entry_instr_cadd  with "Htext") as "Hi6".
    iPoseProof (entry_instr_jal   with "Htext") as "Hi7".
    (* register-nonzero side conditions (all targets are sp/a0/a1/ra <> x0) *)
    assert (Hrd0 : uint i_auipc <> 0) by (vm_compute; discriminate).
    assert (Hrd1 : uint i_ld <> 0) by (vm_compute; discriminate).
    assert (Hrd2 : uint (regidx_bits rd_clui) <> 0) by (vm_compute; discriminate).
    assert (Hrd3 : uint i_rd_csrr <> 0) by (vm_compute; discriminate).
    assert (Hrd4 : uint (regidx_bits rsd_caddi) <> 0) by (vm_compute; discriminate).
    assert (Hrd5 : uint i_mul_rd <> 0) by (vm_compute; discriminate).
    assert (Hrd6 : uint (regidx_bits rsd_cadd) <> 0) by (vm_compute; discriminate).
    assert (Hrd7 : uint i_jal <> 0) by (vm_compute; discriminate).

    (* ---- 1. AUIPC @ pc_e0: sp := entry_sp1 ---- *)
    iApply (wp_auipc_gpr Φ pc_e0 i_auipc imm_auipc m pmpcfg0 1%Qp HpmpU ltac:(boot_static) Hrd0
              with "Hmm Hpmpc Hpc Hfile Hi0").
    iEval (rewrite pc_e0_e1).
    iIntros "Hmm Hpmpc Hpc Hfile".
    (* fold the AUIPC continuation map into [m_auipc m] *)
    iEval (change (<[Regidx i_auipc := regval_into_reg (add_vec pc_e0 (auipc_off imm_auipc))]> m)
             with (m_auipc m)) in "Hfile".

    (* ---- 2. LOAD @ pc_e1: sp := mem[sp + sext(imm_ld)] = v_stack0 ---- *)
    (* the load reads rs1 = i_ld = i_auipc = sp, whose value in [m_auipc m] is
       entry_sp1, so the effective address is entry_ld_ea. *)
    assert (Hea : add_vec (m_auipc m !!! Regidx i_ld) (sign_extend' 64 imm_ld)
                  = entry_ld_ea).
    { unfold entry_ld_ea, entry_sp1, m_auipc.
      rewrite reg_ld_auipc.
      rewrite upd_eq. reflexivity. }
    iApply (wp_ld_gpr Φ pc_e1 false i_ld i_ld imm_ld (m_auipc m) v_stack0 pmpcfg0 1%Qp
              (dq := dq) Hpmp ltac:(boot_static) Hrd1 with "Hmm Hpmpc Hpc Hfile Hi1 [Hbytes]").
    { rewrite Hea. iExact "Hbytes". }
    iEval (rewrite pc_e1_e2).
    iIntros "Hmm Hpmpc Hpc Hfile Hbytes".
    iEval (rewrite Hea) in "Hbytes".
    iEval (change (<[Regidx i_ld := regval_into_reg v_stack0]> (m_auipc m))
             with (m_ld m v_stack0)) in "Hfile".

    (* ---- 3. C.LUI @ pc_e2: a0 := 0x1000 ---- *)
    iApply (wp_lui_gpr Φ pc_e2 true (regidx_bits rd_clui) (sign_extend' 20 imm_clui)
              (m_ld m v_stack0) pmpcfg0 1%Qp HpmpU ltac:(boot_static) Hrd2
              with "Hmm Hpmpc Hpc Hfile Hi2").
    iEval (change (if true then 2%Z else 4%Z) with 2%Z).
    iEval (rewrite pc_e2_e3).
    iIntros "Hmm Hpmpc Hpc Hfile".
    iEval (change (<[Regidx (regidx_bits rd_clui) :=
                      regval_into_reg (luival (sign_extend' 20 imm_clui))]> (m_ld m v_stack0))
             with (m_clui m v_stack0)) in "Hfile".

    (* ---- 4. CSRRS @ pc_e3 (2-aligned): a1 := mhartid ---- *)
    iApply (wp_csrr_mhartid_gpr Φ pc_e3 i_rd_csrr mhartid_in
              (m_clui m v_stack0) pmpcfg0 1%Qp HpmpU ltac:(boot_static) Hrd3
              with "Hmm Hpmpc Hpc Hfile Hmh Hi3").
    iEval (rewrite pc_e3_e4).
    iIntros "Hmm Hpmpc Hpc Hfile Hmh".
    iEval (change (<[Regidx i_rd_csrr := regval_into_reg mhartid_in]> (m_clui m v_stack0))
             with (m_csrr m v_stack0 mhartid_in)) in "Hfile".

    (* ---- 5. C.ADDI @ pc_e4: a1 := a1 + 1 ---- *)
    iApply (wp_addi_gpr Φ pc_e4 true (regidx_bits rsd_caddi) (regidx_bits rsd_caddi)
              (sign_extend' 12 imm_caddi)
              (m_csrr m v_stack0 mhartid_in) pmpcfg0 1%Qp HpmpU ltac:(boot_static) Hrd4
              with "Hmm Hpmpc Hpc Hfile Hi4").
    iEval (change (if true then 2%Z else 4%Z) with 2%Z).
    iEval (rewrite pc_e4_e5).
    iIntros "Hmm Hpmpc Hpc Hfile".
    iEval (rewrite sext6_12_64) in "Hfile".
    iEval (change (<[Regidx (regidx_bits rsd_caddi) :=
             regval_into_reg
               (add_vec (m_csrr m v_stack0 mhartid_in !!! Regidx (regidx_bits rsd_caddi))
                  (sign_extend' 64 imm_caddi))]> (m_csrr m v_stack0 mhartid_in))
             with (m_caddi m v_stack0 mhartid_in)) in "Hfile".

    (* ---- 6. MUL @ pc_e5: a0 := a0 * a1 ---- *)
    iApply (wp_mul_gpr Φ pc_e5 i_mul_rs2 i_mul_rs1 i_mul_rd
              (m_caddi m v_stack0 mhartid_in) pmpcfg0 HpmpU ltac:(boot_static) Hrd5
              with "Hmm Hpmpc Hpc Hfile Hi5").
    iEval (rewrite pc_e5_e6).
    iIntros "Hmm Hpmpc Hpc Hfile".
    iEval (change (<[Regidx i_mul_rd :=
             regval_into_reg
               (mult_to_bits_half xlen (mulop_mul.(mul_op_signed_rs1))
                  (mulop_mul.(mul_op_signed_rs2))
                  (m_caddi m v_stack0 mhartid_in !!! Regidx i_mul_rs1)
                  (m_caddi m v_stack0 mhartid_in !!! Regidx i_mul_rs2)
                  (mulop_mul.(mul_op_result_part)))]> (m_caddi m v_stack0 mhartid_in))
             with (m_mul m v_stack0 mhartid_in)) in "Hfile".

    (* ---- 7. C.ADD @ pc_e6: sp := sp + a0 ---- *)
    iApply (wp_add_gpr Φ pc_e6 true (regidx_bits rs2_cadd) (regidx_bits rsd_cadd)
              (regidx_bits rsd_cadd)
              (m_mul m v_stack0 mhartid_in) pmpcfg0 1%Qp HpmpU ltac:(boot_static) Hrd6
              with "Hmm Hpmpc Hpc Hfile Hi6").
    iEval (change (if true then 2%Z else 4%Z) with 2%Z).
    iEval (rewrite pc_e6_e7).
    iIntros "Hmm Hpmpc Hpc Hfile".
    iEval (change (<[Regidx (regidx_bits rsd_cadd) :=
             regval_into_reg
               (add_vec (m_mul m v_stack0 mhartid_in !!! Regidx (regidx_bits rsd_cadd))
                  (m_mul m v_stack0 mhartid_in !!! Regidx (regidx_bits rs2_cadd)))]>
             (m_mul m v_stack0 mhartid_in))
             with (m_cadd m v_stack0 mhartid_in)) in "Hfile".

    (* ---- 8. JAL @ pc_e7 (2-aligned): ra := pc+4; PC := start ---- *)
    iApply (wp_jal_gpr Φ pc_e7 i_jal imm_jal
              (m_cadd m v_stack0 mhartid_in) pmpcfg0 1%Qp HpmpU ltac:(boot_static) Hrd7 jal_aligned
              with "Hmm Hpmpc Hpc Hfile Hi7").
    iEval (rewrite pc_e7_start).
    iIntros "Hmm Hpmpc Hpc Hfile".
    iEval (change (<[Regidx i_jal := regval_into_reg (add_vec_int pc_e7 4)]>
             (m_cadd m v_stack0 mhartid_in))
             with (m_jal m v_stack0 mhartid_in)) in "Hfile".

    (* hand everything to the caller's continuation *)
    iApply ("Hcont" with "Hmm Hpmpc Hpc Hfile Hmh Hbytes").
  Qed.

End WpEntryNew.
