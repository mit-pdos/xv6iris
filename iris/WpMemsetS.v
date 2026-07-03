(* WpMemsetS.v -- executing [memset]'s entry in S-mode.

   [memset(void *dst, int c, uint n)] (kernel/string.c) begins, per the proof's
   [KernelInstrs] byte map, at [KernelSyms.memset = 0x80000ccc]:

     80000ccc:  1141    addi  sp,sp,-16     <- this instruction (frame alloc)
     80000cce:  e406    sd    ra,8(sp)
     80000cd0:  e022    sd    s0,0(sp)
     80000cd2:  0800    addi  s0,sp,16
     80000cd4:  ca19    beqz  a2,...        (loop-skip when n = 0)
     ...

   The entry instruction is the compressed [c.addi sp,sp,-16] (halfword 0x1141,
   funct3 = 000 -- an ordinary C.ADDI to x2, NOT c.addi16sp).  It is register-
   only (it writes just [sp]; no memory access), so it needs no data-page Sv39
   geometry -- only the FETCH side conditions of the S-mode step engine.  We
   run it on [wp_rvc_gpr_write_s] (the generic S-mode RVC gpr-write engine, the
   same one [wp_caddi16sp_gpr_s] is built on), specialising the ExecuteAs base
   to the [ITYPE ADDI] expansion.

   THE THEOREM ([wp_memset_s]): from [memset]'s entry PC in S-mode -- with the
   standard kernel Sv39 fetch setup (identity superpage TLB hit at slot 5, PMP
   TOR entry 0 granting S-mode fetch over the code page) -- [memset] executes
   its first instruction, allocating its 16-byte stack frame ([sp := sp - 16])
   and advancing to [memset+2], with every ambient S-mode cell handed back to
   the continuation unchanged. *)
From Stdlib Require Import Eqdep_dec ZArith Lia List.
From stdpp Require Import gmap list list_monad bitvector.definitions bitvector.tactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap invariants.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import RiscvModelBytes.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvExtras RiscvTryStep RiscvFetchExec.
Require Import MinstretInv InstrBytes.
Require Import WpAdd WpFetch WpLoad WpDecode WpLeafCommon WpEntry WpEntryNew.
Require Import WpGpr WpGprAddi WpGprRvc WpGprShift WpGprJalr.
Require Import SmodeCore WpSmodeGpr.
From Kernel Require KernelInstrs.
From Kernel Require KernelSyms.
Local Open Scope Z_scope.

Section WpMemsetS.
  Context `{!riscvGS Σ}.

  Definition pc_memset : mword 64 := mword_of_int KernelSyms.memset.
  (* the entry halfword [c.addi sp,sp,-16], and the 4-byte fetch window it sits
     in (its own 0x1141 in the low half, the next halfword 0xe406 in the high). *)
  Definition h_memset0 : mword 16 := mword_of_int 0x1141.
  Definition w_memset0 : mword 32 := mword_of_int 0xe4061141.
  (* C.ADDI's 6-bit signed immediate (== -16) and destination register (== sp),
     extracted exactly as the model's decoder does (mirror of [imm_caddi] /
     [rsd_caddi] in WpEntry). *)
  Definition imm_memset0 : mword 6 :=
    concat_vec (subrange_vec_dec h_memset0 12 12) (subrange_vec_dec h_memset0 6 2).
  Definition rsd_memset0 : regidx :=
    Regidx (autocast (T := mword)
              (subrange_vec_dec (subrange_vec_dec h_memset0 11 7)
                 (Z.sub regidx_bit_width 1) 0)).

  (* The destination is sp, and the immediate sign-extends to -16. *)
  Lemma rsd_memset0_sp : rsd_memset0 = Regidx csp_rs1.
  Proof. reflexivity. Qed.

  Lemma imm_memset0_val :
    sign_extend' 64 (sign_extend' 12 imm_memset0) = (mword_of_int (-16) : mword 64).
  Proof. apply bv_eq. vm_compute; reflexivity. Qed.

  (* ---- decode: 0x1141 decodes to [C_ADDI (imm_memset0, rsd_memset0)] ---- *)
  Lemma decode_memset_addi s :
    eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
    exec (ext_decode_compressed h_memset0) s = Some (C_ADDI (imm_memset0, rsd_memset0), s).
  Proof.
    intro HmisaC. unfold imm_memset0, rsd_memset0.
    assert (Hrsd : exec (encdec_reg_backwards (subrange_vec_dec h_memset0 11 7)) s
                = Some (Regidx (autocast (T := mword)
                          (subrange_vec_dec (subrange_vec_dec h_memset0 11 7)
                             (Z.sub regidx_bit_width 1) 0)), s)).
    { unfold encdec_reg_backwards.
      match goal with |- context[if ?g then returnM (Regidx _) else _] =>
        replace g with true by (vm_compute; reflexivity) end. cbn match. apply exec_returnM. }
    unfold ext_decode_compressed, encdec_compressed_backwards. cbv beta. cbn zeta.
    skip_pure_clause.
    repeat (dstep s HmisaC).
    match goal with |- context[if ?g then _ else returnM None] =>
      replace g with true by (vm_compute; reflexivity) end.
    cbn match. rewrite exec_bind.
    rewrite (exec_bind_Some _ _ _ _ _ Hrsd). cbn beta.
    rewrite (exec_bind_Some _ _ _ _ _
              (_ : exec (Defs.and_boolM (returnM _) (currentlyEnabled Ext_Zca)) s = Some (true, s))).
    2:{ apply exec_andM_true; [ apply exec_returnM_true; vm_compute; reflexivity |].
        apply exec_currentlyEnabled_Zca; exact HmisaC. }
    cbn beta iota. rewrite exec_returnM. cbn beta iota. rewrite exec_returnM. reflexivity.
  Qed.

  (* ---- the [instr] fact at [memset]'s entry (4-aligned RVC) ---- *)
  Lemma memset_instr0 :
    kernel_text -∗ instr pc_memset true (C_ADDI (imm_memset0, Regidx csp_rs1)).
  Proof.
    assert (Hlpad : is_lpad_instruction (C_ADDI (imm_memset0, Regidx csp_rs1)) = false)
      by (vm_compute; reflexivity).
    assert (H2al : is_aligned_vaddr (Virtaddr pc_memset) 2 = true) by (vm_compute; reflexivity).
    assert (H4al : is_aligned_vaddr (Virtaddr pc_memset) 4 = true) by (vm_compute; reflexivity).
    assert (Hrvc : isRVC h_memset0 = true) by (vm_compute; reflexivity).
    assert (Hsub : subrange_vec_dec w_memset0 15 0 = h_memset0)
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Hbytes : forall j, (j < 4)%nat ->
        KernelInstrs.kernel_bytes !! (KernelSyms.memset + Z.of_nat j)%Z = Some (nth_byte w_memset0 j)).
    { intros j Hj;
        do 4 (destruct j as [|j]; [vm_compute; f_equal; apply bv_eq; reflexivity|]); lia. }
    iIntros "#Ht". rewrite /instr.
    iSplitR; [iPureIntro; exact Hlpad|].
    iExists (F_RVC h_memset0).
    iSplitR; [iPureIntro; reflexivity|].
    iSplitL "".
    - iApply (instr_bytes_rvc4 pc_memset h_memset0 w_memset0 H2al H4al Hrvc Hsub).
      iApply (kernel_window_pc KernelSyms.memset w_memset0 4 pc_memset eq_refl Hbytes with "Ht").
    - iIntros (σ ns κs nt) "_". iPureIntro. intros _ HmisaC.
      rewrite <- rsd_memset0_sp. exact (decode_memset_addi σ HmisaC).
  Qed.

  (* =================================================================== *)
  (*  Register-only S-mode leaf WPs that memset needs beyond c.addi /     *)
  (*  c.sdsp / c.ldsp.  Each wraps [wp_rvc_gpr_write_s] with the existing  *)
  (*  ExecuteAs expansion + base [_gpr] value lemma, exactly as            *)
  (*  [wp_caddi16sp_gpr_s] does.  All are register-only (no data page).    *)
  (* =================================================================== *)

  (* ---- c.addi4spn rd', sp, nzimm  (rd' := sp + nzimm) ---- *)
  Lemma wp_caddi4spn_gpr_s (root_ppn : mword 44) E (Φ : mval -> iProp Σ)
      (pc : mword 64) (rdc : cregidx) (nzimm : mword 8) (rd : mword 5)
      (m : gmap regidx (mword 64)) (satp0 : mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (pmpaddr00 : type_of_register pmpaddr_n)
      (tlbvec : vec (option TLB_Entry) (2 ^ 6)) (q : Qp) {dqt : dfrac} :
    ↑minstretN ⊆ E ->
    creg2reg_idx rdc = Regidx rd ->
    uint rd <> 0 ->
    vec_access_dec tlbvec 5 = Some (pw_tlb_entry root_ppn (mword_of_int 0)) ->
    kv_fetch_geom pc ->
    pmp_tor0_sfetch_all pmpcfg0 pmpaddr00 pc ->
    smode_config (DfracOwn q) satp0 -∗
    pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
    pmpaddr_n ↦ᵣ{DfracOwn q} pmpaddr00 -∗
    tlb ↦ᵣ{ dqt } tlbvec -∗
    pc_is pc -∗
    gpr_file m -∗
    instr pc true (C_ADDI4SPN (rdc, nzimm)) -∗
    ( smode_config (DfracOwn q) satp0 -∗
      pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
      pmpaddr_n ↦ᵣ{DfracOwn q} pmpaddr00 -∗
      tlb ↦ᵣ{ dqt } tlbvec -∗
      pc_is (add_vec_int pc 2) -∗
      gpr_file (<[Regidx rd := regval_into_reg
        (add_vec (m !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm nzimm)))]> m) -∗
      WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    iIntros (HN Hrdc Hrd Hvec Hgeom Hpmp) "Hsm Hpmpc Hpmpa Htlb Hpc Hfile Hinstr Hcont".
    unshelve iApply (wp_rvc_gpr_write_s root_ppn E Φ pc rd csp_rs1 csp_rs1
              (C_ADDI4SPN (rdc, nzimm))
              (ITYPE (caddi4spn_imm nzimm, sp, Regidx rd, ADDI))
              (add_vec (m !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm nzimm)))
              m satp0 pmpcfg0 pmpaddr00 tlbvec q HN Hvec Hgeom Hpmp Hrd _ _
              with "Hsm Hpmpc Hpmpa Htlb Hpc Hfile Hinstr Hcont").
    - intro s. rewrite <- Hrdc. exact (exec_execute_C_ADDI4SPN rdc nzimm s).
    - intros s_pc Hnpc Hva _.
      change sp with (Regidx csp_rs1).
      rewrite (exec_execute_ITYPE_ADDI_gpr csp_rs1 rd (caddi4spn_imm nzimm) s_pc).
      replace (Z.eqb (uint rd) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrd).
      unfold gpr_addi_val. rewrite Hva. reflexivity.
  Qed.

  (* ---- c.mv rd, rs2  (rd := rs2, via RTYPE ADD rd, x0, rs2) ---- *)
  Lemma wp_cmv_gpr_s (root_ppn : mword 44) E (Φ : mval -> iProp Σ)
      (pc : mword 64) (rd rs2 : mword 5)
      (m : gmap regidx (mword 64)) (satp0 : mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (pmpaddr00 : type_of_register pmpaddr_n)
      (tlbvec : vec (option TLB_Entry) (2 ^ 6)) (q : Qp) {dqt : dfrac} :
    ↑minstretN ⊆ E ->
    uint rd <> 0 ->
    vec_access_dec tlbvec 5 = Some (pw_tlb_entry root_ppn (mword_of_int 0)) ->
    kv_fetch_geom pc ->
    pmp_tor0_sfetch_all pmpcfg0 pmpaddr00 pc ->
    smode_config (DfracOwn q) satp0 -∗
    pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
    pmpaddr_n ↦ᵣ{DfracOwn q} pmpaddr00 -∗
    tlb ↦ᵣ{ dqt } tlbvec -∗
    pc_is pc -∗
    gpr_file m -∗
    instr pc true (C_MV (Regidx rd, Regidx rs2)) -∗
    ( smode_config (DfracOwn q) satp0 -∗
      pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
      pmpaddr_n ↦ᵣ{DfracOwn q} pmpaddr00 -∗
      tlb ↦ᵣ{ dqt } tlbvec -∗
      pc_is (add_vec_int pc 2) -∗
      gpr_file (<[Regidx rd := regval_into_reg
        (add_vec zero_reg (m !!! Regidx rs2))]> m) -∗
      WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    iIntros (HN Hrd Hvec Hgeom Hpmp) "Hsm Hpmpc Hpmpa Htlb Hpc Hfile Hinstr Hcont".
    unshelve iApply (wp_rvc_gpr_write_s root_ppn E Φ pc rd rs2 rs2
              (C_MV (Regidx rd, Regidx rs2))
              (RTYPE (Regidx rs2, zreg, Regidx rd, ADD))
              (add_vec zero_reg (m !!! Regidx rs2))
              m satp0 pmpcfg0 pmpaddr00 tlbvec q HN Hvec Hgeom Hpmp Hrd _ _
              with "Hsm Hpmpc Hpmpa Htlb Hpc Hfile Hinstr Hcont").
    - intro s. exact (exec_execute_C_MV (Regidx rd) (Regidx rs2) s).
    - intros s_pc Hnpc Hva _.
      change zreg with (Regidx (zero_extend' 5 ('b"00") : mword 5)).
      change (execute (RTYPE (Regidx rs2, Regidx (zero_extend' 5 ('b"00") : mword 5), Regidx rd, ADD)))
        with (execute_RTYPE (Regidx rs2) (Regidx (zero_extend' 5 ('b"00") : mword 5)) (Regidx rd) ADD).
      rewrite (exec_execute_RTYPE_ADD_gpr rs2 (zero_extend' 5 ('b"00") : mword 5) rd s_pc).
      replace (Z.eqb (uint rd) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrd).
      unfold gpr_rd_val.
      replace (Z.eqb (uint (zero_extend' 5 ('b"00") : mword 5)) 0) with true by (vm_compute; reflexivity).
      rewrite Hva. reflexivity.
  Qed.

  (* ---- c.slli rsd, shamt  (rsd := rsd << shamt) ---- *)
  Lemma wp_cslli_gpr_s (root_ppn : mword 44) E (Φ : mval -> iProp Σ)
      (pc : mword 64) (rsd : regidx) (rd : mword 5) (shamt : mword 6)
      (m : gmap regidx (mword 64)) (satp0 : mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (pmpaddr00 : type_of_register pmpaddr_n)
      (tlbvec : vec (option TLB_Entry) (2 ^ 6)) (q : Qp) {dqt : dfrac} :
    ↑minstretN ⊆ E ->
    rsd = Regidx rd ->
    uint rd <> 0 ->
    vec_access_dec tlbvec 5 = Some (pw_tlb_entry root_ppn (mword_of_int 0)) ->
    kv_fetch_geom pc ->
    pmp_tor0_sfetch_all pmpcfg0 pmpaddr00 pc ->
    smode_config (DfracOwn q) satp0 -∗
    pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
    pmpaddr_n ↦ᵣ{DfracOwn q} pmpaddr00 -∗
    tlb ↦ᵣ{ dqt } tlbvec -∗
    pc_is pc -∗
    gpr_file m -∗
    instr pc true (C_SLLI (shamt, rsd)) -∗
    ( smode_config (DfracOwn q) satp0 -∗
      pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
      pmpaddr_n ↦ᵣ{DfracOwn q} pmpaddr00 -∗
      tlb ↦ᵣ{ dqt } tlbvec -∗
      pc_is (add_vec_int pc 2) -∗
      gpr_file (<[Regidx rd := regval_into_reg
        (shift_bits_left (m !!! Regidx rd) (subrange_vec_dec shamt (Z.sub log2_xlen 1) 0))]> m) -∗
      WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    iIntros (HN Hrsd Hrd Hvec Hgeom Hpmp) "Hsm Hpmpc Hpmpa Htlb Hpc Hfile Hinstr Hcont".
    unshelve iApply (wp_rvc_gpr_write_s root_ppn E Φ pc rd rd rd
              (C_SLLI (shamt, rsd))
              (SHIFTIOP (shamt, Regidx rd, Regidx rd, SLLI))
              (shift_bits_left (m !!! Regidx rd) (subrange_vec_dec shamt (Z.sub log2_xlen 1) 0))
              m satp0 pmpcfg0 pmpaddr00 tlbvec q HN Hvec Hgeom Hpmp Hrd _ _
              with "Hsm Hpmpc Hpmpa Htlb Hpc Hfile Hinstr Hcont").
    - intro s. rewrite Hrsd. exact (exec_execute_C_SLLI shamt (Regidx rd) s).
    - intros s_pc Hnpc Hva _.
      rewrite (exec_execute_SHIFTIOP_SLLI_gpr rd rd shamt s_pc).
      replace (Z.eqb (uint rd) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrd).
      unfold gpr_slli_val, gpr_src. rewrite Hva. reflexivity.
  Qed.

  (* ---- c.srli rd', shamt  (rd' := rd' >>u shamt) ---- *)
  Lemma wp_csrli_gpr_s (root_ppn : mword 44) E (Φ : mval -> iProp Σ)
      (pc : mword 64) (crsd : cregidx) (rd : mword 5) (shamt : mword 6)
      (m : gmap regidx (mword 64)) (satp0 : mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (pmpaddr00 : type_of_register pmpaddr_n)
      (tlbvec : vec (option TLB_Entry) (2 ^ 6)) (q : Qp) {dqt : dfrac} :
    ↑minstretN ⊆ E ->
    creg2reg_idx crsd = Regidx rd ->
    uint rd <> 0 ->
    vec_access_dec tlbvec 5 = Some (pw_tlb_entry root_ppn (mword_of_int 0)) ->
    kv_fetch_geom pc ->
    pmp_tor0_sfetch_all pmpcfg0 pmpaddr00 pc ->
    smode_config (DfracOwn q) satp0 -∗
    pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
    pmpaddr_n ↦ᵣ{DfracOwn q} pmpaddr00 -∗
    tlb ↦ᵣ{ dqt } tlbvec -∗
    pc_is pc -∗
    gpr_file m -∗
    instr pc true (C_SRLI (shamt, crsd)) -∗
    ( smode_config (DfracOwn q) satp0 -∗
      pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
      pmpaddr_n ↦ᵣ{DfracOwn q} pmpaddr00 -∗
      tlb ↦ᵣ{ dqt } tlbvec -∗
      pc_is (add_vec_int pc 2) -∗
      gpr_file (<[Regidx rd := regval_into_reg
        (shift_bits_right (m !!! Regidx rd) (subrange_vec_dec shamt (Z.sub log2_xlen 1) 0))]> m) -∗
      WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    iIntros (HN Hcrsd Hrd Hvec Hgeom Hpmp) "Hsm Hpmpc Hpmpa Htlb Hpc Hfile Hinstr Hcont".
    unshelve iApply (wp_rvc_gpr_write_s root_ppn E Φ pc rd rd rd
              (C_SRLI (shamt, crsd))
              (SHIFTIOP (shamt, Regidx rd, Regidx rd, SRLI))
              (shift_bits_right (m !!! Regidx rd) (subrange_vec_dec shamt (Z.sub log2_xlen 1) 0))
              m satp0 pmpcfg0 pmpaddr00 tlbvec q HN Hvec Hgeom Hpmp Hrd _ _
              with "Hsm Hpmpc Hpmpa Htlb Hpc Hfile Hinstr Hcont").
    - intro s. rewrite <- Hcrsd. exact (exec_execute_C_SRLI shamt crsd s).
    - intros s_pc Hnpc Hva _.
      rewrite (exec_execute_SHIFTIOP_SRLI_gpr rd rd shamt s_pc).
      replace (Z.eqb (uint rd) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrd).
      unfold gpr_srli_val, gpr_src. rewrite Hva. reflexivity.
  Qed.

  (* =================================================================== *)
  (*  Branch execute-reductions (BTYPE), from scratch against the model's  *)
  (*  [execute_BTYPE]: read rs1/rs2, compare, and either fall through      *)
  (*  (RETIRE_SUCCESS, state unchanged) or jump to PC + sext(imm).         *)
  (* =================================================================== *)

  (* register value as [rX_bits] reads it (x0 -> zero_reg). *)
  Definition rvv (r : mword 5) (s : mstate) : mword 64 :=
    if Z.eqb (uint r) 0 then zero_reg
    else register_lookup (R_bitvector_64 (gpr_of_Z (uint r))) s.(sregs).

  (* the comparison prefix of [execute_BTYPE] for BNE / BEQ evaluates to the
     boolean [taken], leaving the state unchanged. *)
  Lemma exec_BTYPE_cmp_BNE (rs2 rs1 : mword 5) s :
    exec (Defs.bind (rX_bits (Regidx rs1))
            (fun w2 => Defs.bind (rX_bits (Regidx rs2))
               (fun w3 => returnM (neq_vec w2 w3)))) s
      = Some (neq_vec (rvv rs1 s) (rvv rs2 s), s).
  Proof.
    unfold rvv.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_rX_bits_gpr rs1 s)).
    rewrite (exec_bind_Some _ _ _ _ _ (exec_rX_bits_gpr rs2 s)).
    apply exec_returnM.
  Qed.

  Lemma exec_BTYPE_cmp_BEQ (rs2 rs1 : mword 5) s :
    exec (Defs.bind (rX_bits (Regidx rs1))
            (fun w2 => Defs.bind (rX_bits (Regidx rs2))
               (fun w3 => returnM (eq_vec w2 w3)))) s
      = Some (eq_vec (rvv rs1 s) (rvv rs2 s), s).
  Proof.
    unfold rvv.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_rX_bits_gpr rs1 s)).
    rewrite (exec_bind_Some _ _ _ _ _ (exec_rX_bits_gpr rs2 s)).
    apply exec_returnM.
  Qed.

  Lemma exec_execute_BTYPE_BNE_fall (imm : mword 13) (rs2 rs1 : mword 5) s :
    neq_vec (rvv rs1 s) (rvv rs2 s) = false ->
    exec (execute (BTYPE (imm, Regidx rs2, Regidx rs1, BNE))) s
      = Some (RETIRE_SUCCESS, s).
  Proof.
    intro Hfall.
    unfold execute. cbn match. unfold execute_BTYPE.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_BTYPE_cmp_BNE rs2 rs1 s)).
    rewrite Hfall. apply exec_returnM.
  Qed.

  Lemma exec_execute_BTYPE_BEQ_fall (imm : mword 13) (rs2 rs1 : mword 5) s :
    eq_vec (rvv rs1 s) (rvv rs2 s) = false ->
    exec (execute (BTYPE (imm, Regidx rs2, Regidx rs1, BEQ))) s
      = Some (RETIRE_SUCCESS, s).
  Proof.
    intro Hfall.
    unfold execute. cbn match. unfold execute_BTYPE.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_BTYPE_cmp_BEQ rs2 rs1 s)).
    rewrite Hfall. apply exec_returnM.
  Qed.

  Lemma exec_execute_BTYPE_BNE_taken (imm : mword 13) (rs2 rs1 : mword 5) s :
    neq_vec (rvv rs1 s) (rvv rs2 s) = true ->
    eq_vec (access_vec_dec (add_vec (register_lookup PC s.(sregs)) (sign_extend' 64 imm)) 0) ('b"0") = true ->
    bit_to_bool (access_vec_dec (add_vec (register_lookup PC s.(sregs)) (sign_extend' 64 imm)) 1) = false ->
    exec (execute (BTYPE (imm, Regidx rs2, Regidx rs1, BNE))) s
      = Some (RETIRE_SUCCESS,
              set_reg s nextPC (add_vec (register_lookup PC s.(sregs)) (sign_extend' 64 imm))).
  Proof.
    intros Htaken Halign Hbit1.
    unfold execute. cbn match. unfold execute_BTYPE.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_BTYPE_cmp_BNE rs2 rs1 s)).
    rewrite Htaken.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg PC s)).
    exact (exec_jump_to _ s Halign Hbit1).
  Qed.

  Lemma exec_execute_C_BEQZ (imm : mword 8) (rs : cregidx) s :
    exec (execute (C_BEQZ (imm, rs))) s
      = Some (ExecuteAs (BTYPE (sign_extend' 13 (concat_vec imm ('b"0")), zreg, creg2reg_idx rs, BEQ)), s).
  Proof. unfold execute. cbn match. unfold execute_C_BEQZ. apply exec_returnM. Qed.

  (* ---- bne rs1,rs2  NOT taken (rs1 == rs2): fall through to pc+4 ---- *)
  Lemma wp_bne_fall_s (root_ppn : mword 44) E (Φ : mval -> iProp Σ)
      (pc : mword 64) (imm : mword 13) (rs2 rs1 : mword 5)
      (m : gmap regidx (mword 64)) (satp0 : mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (pmpaddr00 : type_of_register pmpaddr_n)
      (tlbvec : vec (option TLB_Entry) (2 ^ 6)) (q : Qp) {dqt : dfrac} :
    ↑minstretN ⊆ E ->
    vec_access_dec tlbvec 5 = Some (pw_tlb_entry root_ppn (mword_of_int 0)) ->
    kv_fetch_geom pc ->
    kv_fetch_geom (add_vec_int pc 2) ->
    pmp_tor0_sfetch_all pmpcfg0 pmpaddr00 pc ->
    uint rs1 <> 0 -> uint rs2 <> 0 ->
    neq_vec (m !!! Regidx rs1) (m !!! Regidx rs2) = false ->
    smode_config (DfracOwn q) satp0 -∗
    pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
    pmpaddr_n ↦ᵣ{DfracOwn q} pmpaddr00 -∗
    tlb ↦ᵣ{ dqt } tlbvec -∗
    pc_is pc -∗
    gpr_file m -∗
    instr pc false (BTYPE (imm, Regidx rs2, Regidx rs1, BNE)) -∗
    ( smode_config (DfracOwn q) satp0 -∗
      pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
      pmpaddr_n ↦ᵣ{DfracOwn q} pmpaddr00 -∗
      tlb ↦ᵣ{ dqt } tlbvec -∗
      pc_is (add_vec_int pc 4) -∗
      gpr_file m -∗
      WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    iIntros (HN Hvec Hgeom HgeomB Hpmp Hrs1 Hrs2 Hcmp)
      "Hsm Hpmpc Hpmpa Htlb [Hpc Hnpc] [%Hdom Hfmap] Hinstr Hcont".
    iApply (wp_instr_s root_ppn E Φ pc false (BTYPE (imm, Regidx rs2, Regidx rs1, BNE))
              satp0 pmpcfg0 pmpaddr00 tlbvec HN Hvec Hgeom (fun _ => HgeomB) Hpmp
              with "Hsm Hpmpc Hpmpa Htlb Hpc Hinstr").
    iIntros (σ ns κs nt Hpceq) "Hsi".
    iDestruct "Hsi" as "[Hreg Hmem]".
    assert (Hma : m !! Regidx rs1 = Some (m !!! Regidx rs1))
      by (apply lookup_lookup_total_dom; apply Hdom).
    assert (Hmb : m !! Regidx rs2 = Some (m !!! Regidx rs2))
      by (apply lookup_lookup_total_dom; apply Hdom).
    iMod (reg_update _ nextPC _ (add_vec_int pc 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s_pc := set_reg σ nextPC (add_vec_int pc 4)).
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hma with "Hfmap") as "[Hrac Hfba]".
    iDestruct (gpr_pt_value rs1 (m !!! Regidx rs1) s_pc with "Hreg Hrac") as %Lva.
    iDestruct ("Hfba" with "Hrac") as "Hfmap".
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hmb with "Hfmap") as "[Hrbc Hfbb]".
    iDestruct (gpr_pt_value rs2 (m !!! Regidx rs2) s_pc with "Hreg Hrbc") as %Lvb.
    iDestruct ("Hfbb" with "Hrbc") as "Hfmap".
    iModIntro. iExists s_pc.
    iSplitR.
    { iPureIntro. rewrite Hpceq. fold s_pc.
      apply exec_execute_BTYPE_BNE_fall. unfold rvv. rewrite Lva Lvb. exact Hcmp. }
    iSplitL "Hreg Hmem". { unfold s_pc, set_reg; cbn [sregs mem]. iFrame "Hreg Hmem". }
    iIntros "Hsm' Hpmpc' Hpmpa' Htlb' Hpc'".
    assert (Lnpc : register_lookup nextPC s_pc.(sregs) = add_vec_int pc 4)
      by (unfold s_pc; rewrite register_lookup_set; reflexivity).
    iEval (rewrite Lnpc) in "Hpc'".
    iApply ("Hcont" with "Hsm' Hpmpc' Hpmpa' Htlb' [$Hpc' $Hnpc] [Hfmap]").
    iSplitR; [iPureIntro; exact Hdom | iExact "Hfmap"].
  Qed.

  (* ---- bne rs1,rs2  TAKEN (rs1 <> rs2): jump to pc + sext(imm) ---- *)
  Lemma wp_bne_taken_s (root_ppn : mword 44) E (Φ : mval -> iProp Σ)
      (pc : mword 64) (imm : mword 13) (rs2 rs1 : mword 5)
      (m : gmap regidx (mword 64)) (satp0 : mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (pmpaddr00 : type_of_register pmpaddr_n)
      (tlbvec : vec (option TLB_Entry) (2 ^ 6)) (q : Qp) {dqt : dfrac} :
    ↑minstretN ⊆ E ->
    vec_access_dec tlbvec 5 = Some (pw_tlb_entry root_ppn (mword_of_int 0)) ->
    kv_fetch_geom pc ->
    kv_fetch_geom (add_vec_int pc 2) ->
    pmp_tor0_sfetch_all pmpcfg0 pmpaddr00 pc ->
    uint rs1 <> 0 -> uint rs2 <> 0 ->
    neq_vec (m !!! Regidx rs1) (m !!! Regidx rs2) = true ->
    eq_vec (access_vec_dec (add_vec pc (sign_extend' 64 imm)) 0) ('b"0") = true ->
    bit_to_bool (access_vec_dec (add_vec pc (sign_extend' 64 imm)) 1) = false ->
    smode_config (DfracOwn q) satp0 -∗
    pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
    pmpaddr_n ↦ᵣ{DfracOwn q} pmpaddr00 -∗
    tlb ↦ᵣ{ dqt } tlbvec -∗
    pc_is pc -∗
    gpr_file m -∗
    instr pc false (BTYPE (imm, Regidx rs2, Regidx rs1, BNE)) -∗
    ( smode_config (DfracOwn q) satp0 -∗
      pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
      pmpaddr_n ↦ᵣ{DfracOwn q} pmpaddr00 -∗
      tlb ↦ᵣ{ dqt } tlbvec -∗
      pc_is (add_vec pc (sign_extend' 64 imm)) -∗
      gpr_file m -∗
      WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    iIntros (HN Hvec Hgeom HgeomB Hpmp Hrs1 Hrs2 Hcmp Hal0 Hal1)
      "Hsm Hpmpc Hpmpa Htlb [Hpc Hnpc] [%Hdom Hfmap] Hinstr Hcont".
    iApply (wp_instr_s root_ppn E Φ pc false (BTYPE (imm, Regidx rs2, Regidx rs1, BNE))
              satp0 pmpcfg0 pmpaddr00 tlbvec HN Hvec Hgeom (fun _ => HgeomB) Hpmp
              with "Hsm Hpmpc Hpmpa Htlb Hpc Hinstr").
    iIntros (σ ns κs nt Hpceq) "Hsi".
    iDestruct "Hsi" as "[Hreg Hmem]".
    assert (Hma : m !! Regidx rs1 = Some (m !!! Regidx rs1))
      by (apply lookup_lookup_total_dom; apply Hdom).
    assert (Hmb : m !! Regidx rs2 = Some (m !!! Regidx rs2))
      by (apply lookup_lookup_total_dom; apply Hdom).
    iMod (reg_update _ nextPC _ (add_vec_int pc 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s_pc := set_reg σ nextPC (add_vec_int pc 4)).
    assert (Hpcv : register_lookup PC s_pc.(sregs) = pc).
    { unfold s_pc, set_reg; cbn [sregs].
      rewrite irrelevant_register_set; [ exact Hpceq | vm_compute; reflexivity ]. }
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hma with "Hfmap") as "[Hrac Hfba]".
    iDestruct (gpr_pt_value rs1 (m !!! Regidx rs1) s_pc with "Hreg Hrac") as %Lva.
    iDestruct ("Hfba" with "Hrac") as "Hfmap".
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hmb with "Hfmap") as "[Hrbc Hfbb]".
    iDestruct (gpr_pt_value rs2 (m !!! Regidx rs2) s_pc with "Hreg Hrbc") as %Lvb.
    iDestruct ("Hfbb" with "Hrbc") as "Hfmap".
    iMod (reg_update _ nextPC _ (add_vec pc (sign_extend' 64 imm)) with "Hreg Hnpc") as "[Hreg Hnpc]".
    iModIntro.
    iExists (set_reg s_pc nextPC (add_vec pc (sign_extend' 64 imm))).
    iSplitR.
    { iPureIntro. rewrite Hpceq. fold s_pc.
      assert (Htk : neq_vec (rvv rs1 s_pc) (rvv rs2 s_pc) = true)
        by (unfold rvv; rewrite Lva Lvb; exact Hcmp).
      epose proof (exec_execute_BTYPE_BNE_taken imm rs2 rs1 s_pc Htk) as Hred.
      rewrite Hpcv in Hred. exact (Hred Hal0 Hal1). }
    iSplitL "Hreg Hmem". { unfold s_pc, set_reg; cbn [sregs mem]. iFrame "Hreg Hmem". }
    iIntros "Hsm' Hpmpc' Hpmpa' Htlb' Hpc'".
    assert (Lnpc : register_lookup nextPC
             (set_reg s_pc nextPC (add_vec pc (sign_extend' 64 imm))).(sregs)
             = add_vec pc (sign_extend' 64 imm))
      by (unfold set_reg; cbn [sregs]; rewrite register_lookup_set; reflexivity).
    iEval (rewrite Lnpc) in "Hpc'".
    iApply ("Hcont" with "Hsm' Hpmpc' Hpmpa' Htlb' [$Hpc' $Hnpc] [Hfmap]").
    iSplitR; [iPureIntro; exact Hdom | iExact "Hfmap"].
  Qed.

  (* ---- beqz rs (c.beqz) NOT taken (rs <> 0): fall through to pc+2 ---- *)
  Lemma wp_cbeqz_fall_s (root_ppn : mword 44) E (Φ : mval -> iProp Σ)
      (pc : mword 64) (imm8 : mword 8) (rs : cregidx) (rd1 : mword 5)
      (m : gmap regidx (mword 64)) (satp0 : mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (pmpaddr00 : type_of_register pmpaddr_n)
      (tlbvec : vec (option TLB_Entry) (2 ^ 6)) (q : Qp) {dqt : dfrac} :
    ↑minstretN ⊆ E ->
    creg2reg_idx rs = Regidx rd1 ->
    uint rd1 <> 0 ->
    eq_vec (m !!! Regidx rd1) zero_reg = false ->
    vec_access_dec tlbvec 5 = Some (pw_tlb_entry root_ppn (mword_of_int 0)) ->
    kv_fetch_geom pc ->
    pmp_tor0_sfetch_all pmpcfg0 pmpaddr00 pc ->
    smode_config (DfracOwn q) satp0 -∗
    pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
    pmpaddr_n ↦ᵣ{DfracOwn q} pmpaddr00 -∗
    tlb ↦ᵣ{ dqt } tlbvec -∗
    pc_is pc -∗
    gpr_file m -∗
    instr pc true (C_BEQZ (imm8, rs)) -∗
    ( smode_config (DfracOwn q) satp0 -∗
      pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
      pmpaddr_n ↦ᵣ{DfracOwn q} pmpaddr00 -∗
      tlb ↦ᵣ{ dqt } tlbvec -∗
      pc_is (add_vec_int pc 2) -∗
      gpr_file m -∗
      WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    iIntros (HN Hrs Hrd1 Hcmp Hvec Hgeom Hpmp)
      "Hsm Hpmpc Hpmpa Htlb [Hpc Hnpc] [%Hdom Hfmap] Hinstr Hcont".
    iApply (wp_instr_s root_ppn E Φ pc true (C_BEQZ (imm8, rs))
              satp0 pmpcfg0 pmpaddr00 tlbvec HN Hvec Hgeom ltac:(discriminate) Hpmp
              with "Hsm Hpmpc Hpmpa Htlb Hpc Hinstr").
    iIntros (σ ns κs nt Hpceq) "Hsi".
    iDestruct "Hsi" as "[Hreg Hmem]".
    assert (Hma : m !! Regidx rd1 = Some (m !!! Regidx rd1))
      by (apply lookup_lookup_total_dom; apply Hdom).
    iMod (reg_update _ nextPC _ (add_vec_int pc 2) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s_pc := set_reg σ nextPC (add_vec_int pc 2)).
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hma with "Hfmap") as "[Hrac Hfba]".
    iDestruct (gpr_pt_value rd1 (m !!! Regidx rd1) s_pc with "Hreg Hrac") as %Lva.
    iDestruct ("Hfba" with "Hrac") as "Hfmap".
    iModIntro. iExists s_pc.
    iSplitR.
    { iExists (BTYPE (sign_extend' 13 (concat_vec imm8 ('b"0")), zreg, creg2reg_idx rs, BEQ)).
      iSplitR.
      { iPureIntro. rewrite Hpceq. fold s_pc. apply exec_execute_C_BEQZ. }
      iPureIntro. rewrite Hpceq. fold s_pc. rewrite Hrs.
      change zreg with (Regidx (zero_extend' 5 ('b"00") : mword 5)).
      apply exec_execute_BTYPE_BEQ_fall. unfold rvv.
      rewrite Lva.
      replace (Z.eqb (uint (zero_extend' 5 ('b"00") : mword 5)) 0) with true
        by (vm_compute; reflexivity).
      cbn match. exact Hcmp. }
    iSplitL "Hreg Hmem". { unfold s_pc, set_reg; cbn [sregs mem]. iFrame "Hreg Hmem". }
    iIntros "Hsm' Hpmpc' Hpmpa' Htlb' Hpc'".
    assert (Lnpc : register_lookup nextPC s_pc.(sregs) = add_vec_int pc 2)
      by (unfold s_pc; rewrite register_lookup_set; reflexivity).
    iEval (rewrite Lnpc) in "Hpc'".
    iApply ("Hcont" with "Hsm' Hpmpc' Hpmpa' Htlb' [$Hpc' $Hnpc] [Hfmap]").
    iSplitR; [iPureIntro; exact Hdom | iExact "Hfmap"].
  Qed.

  (* =================================================================== *)
  (*  Base (4-byte) register-write S-mode engine -- the [is_rvc = false]   *)
  (*  analogue of [wp_rvc_gpr_write_s]: any base instruction [i] that       *)
  (*  writes ONE gpr [rd := wval].  Used for memset's [add a4,a2,a0].       *)
  (*  Extra premise: the SECOND fetch half also has fetch geometry.         *)
  (* =================================================================== *)
  Lemma wp_base_gpr_write_s (root_ppn : mword 44) E (Φ : mval -> iProp Σ)
      (pc : mword 64) (rd rsa rsb : mword 5) (i : instruction) (wval : mword 64)
      (m : gmap regidx (mword 64)) (satp0 : mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (pmpaddr00 : type_of_register pmpaddr_n)
      (tlbvec : vec (option TLB_Entry) (2 ^ 6)) (q : Qp) {dqt : dfrac} :
    ↑minstretN ⊆ E ->
    vec_access_dec tlbvec 5 = Some (pw_tlb_entry root_ppn (mword_of_int 0)) ->
    kv_fetch_geom pc ->
    kv_fetch_geom (add_vec_int pc 2) ->
    pmp_tor0_sfetch_all pmpcfg0 pmpaddr00 pc ->
    uint rd <> 0 ->
    (forall s_pc : mstate,
       register_lookup nextPC s_pc.(sregs) = add_vec_int pc 4 ->
       (if Z.eqb (uint rsa) 0 then zero_reg
        else register_lookup (R_bitvector_64 (gpr_of_Z (uint rsa))) s_pc.(sregs)) = m !!! Regidx rsa ->
       (if Z.eqb (uint rsb) 0 then zero_reg
        else register_lookup (R_bitvector_64 (gpr_of_Z (uint rsb))) s_pc.(sregs)) = m !!! Regidx rsb ->
       exec (execute i) s_pc
       = Some (RETIRE_SUCCESS,
               set_reg s_pc (R_bitvector_64 (gpr_of_Z (uint rd))) (regval_into_reg wval))) ->
    smode_config (DfracOwn q) satp0 -∗
    pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
    pmpaddr_n ↦ᵣ{DfracOwn q} pmpaddr00 -∗
    tlb ↦ᵣ{ dqt } tlbvec -∗
    pc_is pc -∗
    gpr_file m -∗
    instr pc false i -∗
    ( smode_config (DfracOwn q) satp0 -∗
      pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
      pmpaddr_n ↦ᵣ{DfracOwn q} pmpaddr00 -∗
      tlb ↦ᵣ{ dqt } tlbvec -∗
      pc_is (add_vec_int pc 4) -∗
      gpr_file (<[Regidx rd := regval_into_reg wval]> m) -∗
      WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    iIntros (HN Hvec Hgeom HgeomB Hpmp Hrd Hbexec)
      "Hsm Hpmpc Hpmpa Htlb [Hpc Hnpc] [%Hdom Hfmap] Hinstr Hcont".
    iApply (wp_instr_s root_ppn E Φ pc false i satp0 pmpcfg0 pmpaddr00 tlbvec HN Hvec Hgeom
              (fun _ => HgeomB) Hpmp with "Hsm Hpmpc Hpmpa Htlb Hpc Hinstr").
    iIntros (σ ns κs nt Hpceq) "Hsi".
    iDestruct "Hsi" as "[Hreg Hmem]".
    assert (Hma : m !! Regidx rsa = Some (m !!! Regidx rsa))
      by (apply lookup_lookup_total_dom; apply Hdom).
    assert (Hmb : m !! Regidx rsb = Some (m !!! Regidx rsb))
      by (apply lookup_lookup_total_dom; apply Hdom).
    assert (Hmd : m !! Regidx rd = Some (m !!! Regidx rd))
      by (apply lookup_lookup_total_dom; apply Hdom).
    iMod (reg_update _ nextPC _ (add_vec_int pc 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s_pc := set_reg σ nextPC (add_vec_int pc 4)).
    assert (Lnpc0 : register_lookup nextPC s_pc.(sregs) = add_vec_int pc 4)
      by (unfold s_pc; rewrite register_lookup_set; reflexivity).
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hma with "Hfmap") as "[Hrac Hfba]".
    iDestruct (gpr_pt_value rsa (m !!! Regidx rsa) s_pc with "Hreg Hrac") as %Lva0.
    iDestruct ("Hfba" with "Hrac") as "Hfmap".
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hmb with "Hfmap") as "[Hrbc Hfbb]".
    iDestruct (gpr_pt_value rsb (m !!! Regidx rsb) s_pc with "Hreg Hrbc") as %Lvb0.
    iDestruct ("Hfbb" with "Hrbc") as "Hfmap".
    iDestruct (big_sepM_insert_acc _ _ _ _ Hmd with "Hfmap") as "[Hrdc Hfins]".
    rewrite (gpr_pt_nz rd _ Hrd).
    iMod (reg_update _ (R_bitvector_64 (gpr_of_Z (uint rd))) _ (regval_into_reg wval)
            with "Hreg Hrdc") as "[Hreg Hrdc]".
    iDestruct ("Hfins" $! (regval_into_reg wval) with "[Hrdc]") as "Hfmap".
    { rewrite (gpr_pt_nz rd _ Hrd). iExact "Hrdc". }
    iModIntro.
    iExists (set_reg s_pc (R_bitvector_64 (gpr_of_Z (uint rd))) (regval_into_reg wval)).
    iSplitR.
    { iPureIntro. rewrite Hpceq. fold s_pc. exact (Hbexec s_pc Lnpc0 Lva0 Lvb0). }
    iSplitL "Hreg Hmem".
    { unfold s_pc, set_reg; cbn [sregs mem]. iFrame "Hreg Hmem". }
    iIntros "Hsm' Hpmpc' Hpmpa' Htlb' Hpc'".
    assert (Lnpc : register_lookup nextPC
             (set_reg s_pc (R_bitvector_64 (gpr_of_Z (uint rd))) (regval_into_reg wval)).(sregs)
             = add_vec_int pc 4).
    { tmig. exact Lnpc0. }
    iEval (rewrite Lnpc) in "Hpc'".
    iApply ("Hcont" with "Hsm' Hpmpc' Hpmpa' Htlb' [$Hpc' $Hnpc] [Hfmap]").
    iSplitR.
    { iPureIntro. intro r. rewrite dom_insert_L. apply elem_of_union_r. apply Hdom. }
    iExact "Hfmap".
  Qed.

  (* =================================================================== *)
  (*  THE THEOREM: [memset]'s entry step in S-mode allocates its frame.  *)
  (* =================================================================== *)
  Lemma wp_memset_s (root_ppn : mword 44) E (Φ : mval -> iProp Σ)
      (m : gmap regidx (mword 64)) (satp0 : mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (pmpaddr00 : type_of_register pmpaddr_n)
      (tlbvec : vec (option TLB_Entry) (2 ^ 6)) (q : Qp) {dqt : dfrac} :
    ↑minstretN ⊆ E ->
    vec_access_dec tlbvec 5 = Some (pw_tlb_entry root_ppn (mword_of_int 0)) ->
    kv_fetch_geom pc_memset ->
    pmp_tor0_sfetch_all pmpcfg0 pmpaddr00 pc_memset ->
    smode_config (DfracOwn q) satp0 -∗
    pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
    pmpaddr_n ↦ᵣ{DfracOwn q} pmpaddr00 -∗
    tlb ↦ᵣ{ dqt } tlbvec -∗
    pc_is pc_memset -∗
    gpr_file m -∗
    kernel_text -∗
    ( smode_config (DfracOwn q) satp0 -∗
      pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
      pmpaddr_n ↦ᵣ{DfracOwn q} pmpaddr00 -∗
      tlb ↦ᵣ{ dqt } tlbvec -∗
      pc_is (add_vec_int pc_memset 2) -∗
      (* the stack frame is allocated: sp := sp - 16 *)
      gpr_file (<[Regidx csp_rs1 :=
                    regval_into_reg (add_vec (m !!! Regidx csp_rs1)
                                       (mword_of_int (-16) : mword 64))]> m) -∗
      WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    iIntros (HN Hvec Hgeom Hpmp) "Hsm Hpmpc Hpmpa Htlb Hpc Hfile Htext Hcont".
    iPoseProof (memset_instr0 with "Htext") as "Hinstr".
    assert (Hsp : uint csp_rs1 <> 0) by (vm_compute; discriminate).
    unshelve iApply (wp_rvc_gpr_write_s root_ppn E Φ pc_memset csp_rs1 csp_rs1 csp_rs1
              (C_ADDI (imm_memset0, Regidx csp_rs1))
              (ITYPE (sign_extend' 12 imm_memset0, Regidx csp_rs1, Regidx csp_rs1, ADDI))
              (add_vec (m !!! Regidx csp_rs1) (mword_of_int (-16) : mword 64))
              m satp0 pmpcfg0 pmpaddr00 tlbvec q HN Hvec Hgeom Hpmp Hsp
              (fun s => exec_execute_C_ADDI imm_memset0 (Regidx csp_rs1) s) _
              with "Hsm Hpmpc Hpmpa Htlb Hpc Hfile Hinstr Hcont").
    intros s_pc Hnpc Hva _.
    rewrite (exec_execute_ITYPE_ADDI_gpr csp_rs1 csp_rs1 (sign_extend' 12 imm_memset0) s_pc).
    replace (Z.eqb (uint csp_rs1) 0) with false by (symmetry; apply Z.eqb_neq; exact Hsp).
    unfold gpr_addi_val. rewrite Hva. rewrite imm_memset0_val. reflexivity.
  Qed.

End WpMemsetS.
