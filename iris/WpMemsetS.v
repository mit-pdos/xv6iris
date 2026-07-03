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
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvExtras RiscvTryStep RiscvFetchExec.
Require Import MinstretInv InstrBytes.
Require Import WpAdd WpFetch WpLoad WpDecode WpLeafCommon WpEntry WpEntryNew.
Require Import WpGpr WpGprAddi WpGprRvc.
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
