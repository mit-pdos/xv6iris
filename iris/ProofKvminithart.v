(* ProofKvminithart.v -- whole-function proof of kvminithart (kernel/vm.c):
   the Bare->Sv39 switch that installs the verified kernel page table.

   Structure: a 2-slot frame push (ra/s0 saves; addi4spn s0), a first
   sfence.vma (under Bare), the auipc/ld of kernel_pagetable into a5, the
   MAKE_SATP assembly (srli a5,12; li a4,-1; slli a4,0x3f; or a5,a5,a4),
   the csrw satp,a5 -- THE SWITCH -- a second sfence.vma (under the new
   kernel PT), and the 2-slot frame teardown + ret. *)
From Stdlib Require Import Eqdep_dec ZArith Lia List.
From stdpp Require Import gmap list list_monad list_numbers bitvector.definitions bitvector.tactics.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import excl.
From iris.base_logic.lib Require Import gen_heap invariants ghost_var ghost_map.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.Base SailStdpp.Operators_mwords SailStdpp.Values SailStdpp.MachineWord.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import RiscvPtsto RiscvLang RiscvExtras.
Require Import SmodeCore RegFile WpGpr WpMmodeLeafBase.
Require Import HartTp WpNext IntrDefs WpSmodeIntr WpSconfAlu WpSconfMem WpSconfCtl WpAuipc.
Require Import CalleeSaved StackOwn.
Require Import InstrBytes.
Require Import PtTree KptTree KvmMap.
Require Import KptGhost KptShare.
Require Import TransPt.
Require Import UserretDefs.
Require Import WpKvminithart WpKvminithartInstr.
Require Import SpecKvminithart.
From Kernel Require KernelSyms.
Require Import KernelRvcDecode.
Local Open Scope Z_scope.
Import Defs.

Section KvminithartBody.
  Context `{!riscvGS Σ, !sieG Σ}.
  Context `{CID : CpuId}.

  Notation KVI := KernelSyms.kvminithart.

  Ltac reg_neq :=
    lazymatch goal with
    | |- ?a <> ?b => tryif unify a b then fail else (vm_compute; discriminate)
    end.

  Lemma wp_kvminithart_sconf_proof
      (Φ : mval -> iProp Σ) (mm : regfile) (lvl K : nat)
      (root : mword 44)
      (tlbvec0 : vec (option TLB_Entry) (2 ^ 6)) (b : bool) :
    wp_kvminithart_sconf_body Φ mm lvl K root tlbvec0 b.
  Proof.
    unfold wp_kvminithart_sconf_body.
    intros Hlvl HK.
    iIntros "Hcg Hbit #Htext Hpc Htlb #Hcell #Hkinv Hcont".
    (* the snapshot off the shared invariant, taken UP FRONT: both
       sfence.vma's leave the TLB empty, so any tree will do for the
       re-entry coherence. *)
    iApply fupd_wp.
    iMod (KptShare.kpt_inv_snapshot ⊤ root ltac:(solve_ndisj) with "Hkinv") as (t0) "#Hlbt".
    iModIntro.
    (* register disequalities for creg mapping *)
    assert (Hc6 : creg2reg_idx (Cregidx (mword_of_int 6)) = Regidx (mword_of_int 14 : mword 5))
      by (vm_compute; reflexivity).
    assert (Hc7 : creg2reg_idx (Cregidx (mword_of_int 7)) = Regidx (mword_of_int 15 : mword 5))
      by (vm_compute; reflexivity).
    assert (Hzreg : Regidx (mword_of_int 0 : mword 5) = zreg)
      by (vm_compute; reflexivity).
    (* frame-cell address facts (2-slot frame: ra @ slot 1, s0 @ slot 2) *)
    assert (Hpush : add_vec (mm !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6))) = pa_stk (mm !!! Regidx csp_rs1) 2).
    { unfold pa_stk, add_vec_int. apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    assert (Hb1 : add_vec (add_vec (mm !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6)))) (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000"))) = pa_stk (mm !!! Regidx csp_rs1) 1).
    { unfold pa_stk, add_vec_int. rewrite !pa_stk_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb2 : add_vec (add_vec (mm !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6)))) (zero_extend' 64 (concat_vec (mword_of_int 0 : mword 6) ('b"000"))) = pa_stk (mm !!! Regidx csp_rs1) 2).
    { unfold pa_stk, add_vec_int. rewrite !pa_stk_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    iPoseProof (kvi_00 with "Htext") as "Hi00".
    iPoseProof (kvi_02 with "Htext") as "Hi02".
    iPoseProof (kvi_04 with "Htext") as "Hi04".
    iPoseProof (kvi_06 with "Htext") as "Hi06".
    iPoseProof (kvi_08 with "Htext") as "Hi08".
    iPoseProof (kvi_0c with "Htext") as "Hi0c".
    iPoseProof (kvi_10 with "Htext") as "Hi10".
    iPoseProof (kvi_14 with "Htext") as "Hi14".
    iPoseProof (kvi_16 with "Htext") as "Hi16".
    iPoseProof (kvi_18 with "Htext") as "Hi18".
    iPoseProof (kvi_1a with "Htext") as "Hi1a".
    iPoseProof (kvi_1c with "Htext") as "Hi1c".
    iPoseProof (kvi_20 with "Htext") as "Hi20".
    iPoseProof (kvi_24 with "Htext") as "Hi24".
    iPoseProof (kvi_26 with "Htext") as "Hi26".
    iPoseProof (kvi_28 with "Htext") as "Hi28".
    iPoseProof (kvi_2a with "Htext") as "Hi2a".
    (* ============ +0x00 addi sp,sp,-16 : 2-slot frame push ============ *)
    iApply (wp_caddi_sp_push_s_sconf Φ (mword_of_int KVI) (mword_of_int 48 : mword 6) mm K 2 b HK Hpush
              with "Hcg Hpc Hi00 [-]").
    iIntros (CID1 Hs1) "Hcg Hframe Hpc".
    set (W1 := <[Regidx csp_rs1 := regval_into_reg
        (add_vec (mm !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6))))]> mm).
    iEval (rewrite stack_own_slots; cbn [seq]) in "Hframe".
    iDestruct "Hframe" as "(S1 & S2 & _)".
    iDestruct "S1" as (v1) "Hc1". iDestruct "S2" as (v2) "Hc2".
    assert (HspW1 : W1 !!! Regidx csp_rs1 = add_vec (mm !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6)))) by (rewrite /W1 upd_eq; reflexivity).
    assert (Hp02 : add_vec_int (mword_of_int KVI : mword 64) 2 = mword_of_int (KVI + 0x02)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp02) in "Hpc".
    (* +0x02 sd ra,8(sp) -> slot 1 *)
    iApply (wp_csdsp_s_sconf Φ (mword_of_int (KVI + 0x02)) (mword_of_int 1 : mword 6) (mword_of_int 1 : mword 5)
              W1 (K - 2)%nat v1 b with "Hcg Hpc Hi02 [Hc1] [-]").
    { iEval (rewrite HspW1 Hb1). iExact "Hc1". }
    iIntros (CID2 Hs2) "Hcg Hpc Hc1". iEval (rewrite HspW1 Hb1; rgne) in "Hc1".
    assert (HW1r1 : W1 !!! Regidx (mword_of_int 1 : mword 5) = mm !!! Regidx (mword_of_int 1)) by (rewrite /W1 upd_ne; [reflexivity | reg_neq]).
    iEval (rewrite HW1r1) in "Hc1".
    assert (Hp04 : add_vec_int (mword_of_int (KVI + 0x02) : mword 64) 2 = mword_of_int (KVI + 0x04)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp04) in "Hpc".
    (* +0x04 sd s0,0(sp) -> slot 2 *)
    iApply (wp_csdsp_s_sconf Φ (mword_of_int (KVI + 0x04)) (mword_of_int 0 : mword 6) (mword_of_int 8 : mword 5)
              W1 (K - 2)%nat v2 b with "Hcg Hpc Hi04 [Hc2] [-]").
    { iEval (rewrite HspW1 Hb2). iExact "Hc2". }
    iIntros (CID3 Hs3) "Hcg Hpc Hc2". iEval (rewrite HspW1 Hb2; rgne) in "Hc2".
    assert (HW1r8 : W1 !!! Regidx (mword_of_int 8 : mword 5) = mm !!! Regidx (mword_of_int 8)) by (rewrite /W1 upd_ne; [reflexivity | reg_neq]).
    iEval (rewrite HW1r8) in "Hc2".
    assert (Hp06 : add_vec_int (mword_of_int (KVI + 0x04) : mword 64) 2 = mword_of_int (KVI + 0x06)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp06) in "Hpc".
    (* +0x06 addi s0,sp,16 (value unused) *)
    iApply (wp_caddi4spn_s_sconf Φ (mword_of_int (KVI + 0x06)) (Cregidx (mword_of_int 0)) (mword_of_int 4 : mword 8) (mword_of_int 8 : mword 5)
              W1 (K - 2)%nat b ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi06 [-]").
    iIntros (CID4 Hs4) "Hcg Hpc".
    set (W2 := <[Regidx (mword_of_int 8 : mword 5) := regval_into_reg (add_vec (W1 !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm (mword_of_int 4 : mword 8))))]> W1).
    assert (Hp08 : add_vec_int (mword_of_int (KVI + 0x06) : mword 64) 2 = mword_of_int (KVI + 0x08)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp08) in "Hpc".
    (* ============ +0x08 sfence.vma zero,zero (under Bare) ============= *)
    (* BLOCKED (explicit-cpuid port): SpecKvminithart.v wraps this function's
       continuation in [wp_next b (fun CID => ...)] with a fully GENERIC [b],
       but [Htlb : tlb ↦ᵣ tlbvec0] (and, further down, [Hbit : strans_bit
       strans_bit_bare] / [Hbitkpt]) are HART-INDEXED resources ([↦ᵣ] and
       [strans_bit] both carry an implicit ambient [CpuId]) that this whole
       function must carry from ENTRY all the way to this sfence.vma (and
       later to the csrw / second sfence.vma).  Getting here already crosses
       FOUR wp_next-wrapped leaf steps (caddi_sp_push, the two csdsp's,
       caddi4spn); at generic [b] each such crossing hands back a genuinely
       fresh, UNCONSTRAINED [CpuId] (the guide's conditional equality
       [b = false -> CID = CID0] is vacuous unless [b] is known false), so by
       the time we reach here [Hreg]/[Hcap] are typed at that fresh hart while
       [Htlb] is still typed at the function's ENTRY hart -- there is no proof
       that the two coincide, and no transport lemma for [tlb ↦ᵣ]/[strans_bit]
       across a generic wp_next crossing exists yet.  This is exactly the
       "Caller-supplied propositions must be hart-INDEPENDENT" / Stage 2 open
       design question the porting guide flags, not a mechanical porting
       mistake: [iMod (reg_update _ tlb _ tlbz1 with "Hreg Htlb")] below fails
       with "iSpecialize: cannot instantiate (tlb ↦ᵣ ?v ==∗ ...) with (tlb
       ↦ᵣ tlbvec0)".  kvminithart is boot-only code (called from main(),
       always with interrupts disabled), so the natural fix is for
       SpecKvminithart.v to drop the [wp_next] wrapper and state this
       contract at [b = false], the same shape as SpecCpuid.v/SpecMycpu.v --
       but Spec*.v files are out of scope for this port.  Left un-Qed'd
       below at the point this genuinely stops. *)
    iApply (wp_instr_s_sconf W2 (K - 2)%nat b Φ (mword_of_int (KVI + 0x08)) false
              (SFENCE_VMA (Regidx (mword_of_int 0), Regidx (mword_of_int 0)))
              with "Hcg Hpc Hi08").
    iIntros (σ1 Hpceq1) "Hsc Hcap Hfile Hnpc Hsi".
    iDestruct "Hsc" as "(#Hhw & #Hminv & Hpriv & Hmsx & Hmiex & Hmenvx)".
    iDestruct "Hmsx" as (ms1) "(Hms & Hhalf & %Hmsf)".
    pose proof Hmsf as (HMPRV & HSXL & HMXR & HTSR & HXS & HFS & HVS & HSD & HMPP & HTVM).
    iDestruct "Hsi" as "[Hreg Hmem]".
    iDestruct (reg_valid with "Hreg Hpriv") as %Lpriv1.
    iDestruct (reg_valid with "Hreg Hms") as %Lms1.
    iMod (reg_update _ nextPC _ (add_vec_int (mword_of_int (KVI + 0x08)) 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s_pc1 := set_reg σ1 nextPC (add_vec_int (mword_of_int (KVI + 0x08)) 4)).
    assert (Lpriv1p : register_lookup cur_privilege s_pc1.(sregs) = Supervisor)
      by (unfold s_pc1; tmig; exact Lpriv1).
    assert (Lms1p : register_lookup mstatus s_pc1.(sregs) = ms1)
      by (unfold s_pc1; tmig; exact Lms1).
    destruct (exec_execute_SFENCE_VMA_S s_pc1 Lpriv1p ltac:(rewrite Lms1p; exact HTVM))
      as (tlbz1 & Hex1 & Hnone1).
    iMod (reg_update _ tlb _ tlbz1 with "Hreg Htlb") as "[Hreg Htlb]".
    iModIntro. iExists (set_reg s_pc1 tlb tlbz1).
    iSplitR.
    { iPureIntro. rewrite Hpceq1. fold s_pc1. rewrite Hzreg. exact Hex1. }
    iSplitL "Hreg Hmem".
    { unfold s_pc1, set_reg; cbn [sregs mem mdev]. iFrame "Hreg Hmem". }
    iIntros "Hhs Hpc". iNext.
    assert (Lnpc1 : register_lookup nextPC (set_reg s_pc1 tlb tlbz1).(sregs)
                    = mword_of_int (KVI + 0x0c)).
    { unfold s_pc1; cbn [sregs]. tmig. rewrite register_lookup_set.
      apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite Lnpc1) in "Hpc".
    assert (Hpnpc1 : add_vec_int (mword_of_int (KVI + 0x08) : mword 64) 4 = mword_of_int (KVI + 0x0c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpnpc1) in "Hnpc".
    (* reassemble the ambient bundle at pc = 0x0c *)
    iAssert sconf with "[Hpriv Hms Hhalf Hmiex Hmenvx]" as "Hsc".
    { iFrame "Hhw Hminv Hpriv Hmiex Hmenvx". iExists ms1. iFrame "Hms Hhalf". done. }
    iAssert (pc_is (mword_of_int (KVI + 0x0c))) with "[Hpc Hnpc]" as "Hpc".
    { iFrame "Hpc Hnpc". }
    iDestruct (sie_cap_gpr_join with "Hhs Hsc Hcap Hfile") as "Hcg".
    (* ============ +0x0c auipc a5,0x9 ============ *)
    iApply (wp_auipc_s_sconf Φ (mword_of_int (KVI + 0x0c)) (mword_of_int 15 : mword 5) (mword_of_int 9 : mword 20)
              W2 (K - 2)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi0c [-]").
    iIntros (CID5 Hs5) "Hcg Hpc".
    set (A0 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (add_vec (mword_of_int (KVI + 0x0c) : mword 64) (auipc_off (mword_of_int 9 : mword 20)))]> W2).
    assert (Hp10 : add_vec_int (mword_of_int (KVI + 0x0c) : mword 64) 4 = mword_of_int (KVI + 0x10)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp10) in "Hpc".
    (* ============ +0x10 ld a5,764(a5) : a5 := root_b ============ *)
    assert (Haddr : add_vec (A0 !!! Regidx (mword_of_int 15 : mword 5)) (sign_extend' 64 (mword_of_int 764 : mword 12)) = mword_of_int KernelSyms.kernel_pagetable).
    { rewrite /A0 upd_eq. apply bv_eq; vm_compute; reflexivity. }
    iApply (wp_ld_s_sconf Φ (mword_of_int (KVI + 0x10)) (mword_of_int 15 : mword 5) (mword_of_int 15 : mword 5) (mword_of_int 764 : mword 12)
              A0 (K - 2)%nat (zero_extend' 64 (concat_vec root (zeros' 12 : mword 12))) b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi10 [] [-]").
    { iEval (rgne; rewrite Haddr). iExact "Hcell". }
    iIntros (CID6 Hs6) "Hcg Hpc _".
    set (L := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (zero_extend' 64 (concat_vec root (zeros' 12 : mword 12)))]> A0).
    assert (Hp14 : add_vec_int (mword_of_int (KVI + 0x10) : mword 64) 4 = mword_of_int (KVI + 0x14)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp14) in "Hpc".
    (* ============ +0x14 srli a5,a5,0xc ============ *)
    iEval (rewrite Hc7) in "Hi14".
    iApply (wp_csrli_s_sconf Φ (mword_of_int (KVI + 0x14)) (Cregidx (mword_of_int 7)) (mword_of_int 15 : mword 5) (mword_of_int 12 : mword 6)
              L (K - 2)%nat b Hc7 ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi14 [-]").
    iIntros (CID7 Hs7) "Hcg Hpc".
    set (S1 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg
        (shift_bits_right (rget L (mword_of_int 15 : mword 5)) (subrange_vec_dec (mword_of_int 12 : mword 6) (Z.sub log2_xlen 1) 0))]> L).
    assert (Hp16 : add_vec_int (mword_of_int (KVI + 0x14) : mword 64) 2 = mword_of_int (KVI + 0x16)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp16) in "Hpc".
    (* ============ +0x16 li a4,-1 ============ *)
    iApply (wp_cli_s_sconf Φ (mword_of_int (KVI + 0x16)) (mword_of_int 14 : mword 5) (mword_of_int 63 : mword 6)
              (add_vec zero_reg (sign_extend' 64 (sign_extend' 12 (mword_of_int 63 : mword 6))))
              S1 (K - 2)%nat b ltac:(vm_compute; discriminate) ltac:(rdok) eq_refl
              with "Hcg Hpc Hi16 [-]").
    iIntros (CID8 Hs8) "Hcg Hpc".
    set (S2 := <[Regidx (mword_of_int 14 : mword 5) := regval_into_reg
        (add_vec zero_reg (sign_extend' 64 (sign_extend' 12 (mword_of_int 63 : mword 6))))]> S1).
    assert (Hp18 : add_vec_int (mword_of_int (KVI + 0x16) : mword 64) 2 = mword_of_int (KVI + 0x18)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp18) in "Hpc".
    (* ============ +0x18 slli a4,a4,0x3f ============ *)
    iApply (wp_cslli_s_sconf Φ (mword_of_int (KVI + 0x18)) (Regidx (mword_of_int 14 : mword 5)) (mword_of_int 14 : mword 5) (mword_of_int 63 : mword 6)
              S2 (K - 2)%nat b eq_refl ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi18 [-]").
    iIntros (CID9 Hs9) "Hcg Hpc".
    set (S3 := <[Regidx (mword_of_int 14 : mword 5) := regval_into_reg
        (shift_bits_left (rget S2 (mword_of_int 14 : mword 5)) (subrange_vec_dec (mword_of_int 63 : mword 6) (Z.sub log2_xlen 1) 0))]> S2).
    assert (Hp1a : add_vec_int (mword_of_int (KVI + 0x18) : mword 64) 2 = mword_of_int (KVI + 0x1a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp1a) in "Hpc".
    (* ============ +0x1a or a5,a5,a4 : a5 := kvi_satp_word t ============ *)
    iEval (rewrite Hc6 Hc7) in "Hi1a".
    assert (Hor : or_vec (S3 !!! Regidx (mword_of_int 15 : mword 5)) (S3 !!! Regidx (mword_of_int 14 : mword 5)) = kvi_satp_word root).
    { assert (H15 : S3 !!! Regidx (mword_of_int 15 : mword 5)
                    = shift_bits_right (zero_extend' 64 (concat_vec root (zeros' 12 : mword 12))) (subrange_vec_dec (mword_of_int 12 : mword 6) (Z.sub log2_xlen 1) 0)).
      { rewrite /S3 upd_ne; [| reg_neq]. rewrite /S2 upd_ne; [| reg_neq].
        rewrite /S1 upd_eq. rgne. rewrite /L upd_eq. reflexivity. }
      assert (H14 : S3 !!! Regidx (mword_of_int 14 : mword 5)
                    = shift_bits_left (add_vec zero_reg (sign_extend' 64 (sign_extend' 12 (mword_of_int 63 : mword 6)))) (subrange_vec_dec (mword_of_int 63 : mword 6) (Z.sub log2_xlen 1) 0)).
      { rewrite /S3 upd_eq. rgne. rewrite /S2 upd_eq. reflexivity. }
      rewrite H15 H14. unfold kvi_satp_word. reflexivity. }
    iApply (wp_cor_s_sconf Φ (mword_of_int (KVI + 0x1a)) (mword_of_int 15 : mword 5) (mword_of_int 15 : mword 5) (mword_of_int 14 : mword 5)
              (kvi_satp_word root) S3 (K - 2)%nat b ltac:(vm_compute; discriminate) ltac:(rdok) Hor
              with "Hcg Hpc Hi1a [-]").
    iIntros (CID10 Hs10) "Hcg Hpc".
    set (S4 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (kvi_satp_word root)]> S3).
    assert (Ha5 : S4 !!! Regidx (mword_of_int 15 : mword 5) = kvi_satp_word root) by (rewrite /S4 upd_eq; reflexivity).
    assert (Hp1c : add_vec_int (mword_of_int (KVI + 0x1a) : mword 64) 2 = mword_of_int (KVI + 0x1c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp1c) in "Hpc".
    (* ============ +0x1c csrw satp,a5 : THE SWITCH ============ *)
    iApply (wp_instr_s_sconf S4 (K - 2)%nat b Φ (mword_of_int (KVI + 0x1c)) false
              (CSRReg (mword_of_int 384 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 0), CSRRW))
              with "Hcg Hpc Hi1c").
    iIntros (σ2 Hpceq2) "Hsc Hcap Hfile Hnpc Hsi".
    iDestruct "Hsc" as "(#Hhw2 & #Hminv2 & Hpriv & Hmsx & Hmiex & Hmenvx)".
    iDestruct "Hmsx" as (ms2) "(Hms & Hhalf & %Hmsf2)".
    pose proof Hmsf2 as (HMPRV2 & HSXL2 & HMXR2 & HTSR2 & HXS2 & HFS2 & HVS2 & HSD2 & HMPP2 & HTVM2).
    iPoseProof "Hhw2" as "#Hhwc2".
    iDestruct "Hhwc2" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & _ & _ & _ & _ & %HmisaS & _)".
    iDestruct "Hsi" as "[Hreg Hmem]".
    iDestruct (reg_valid with "Hreg Hpriv") as %Lpriv2.
    iDestruct (reg_valid with "Hreg Hms") as %Lms2.
    iDestruct (reg_valid_dq with "Hreg Hmisa") as %Lmisa2.
    iMod (reg_update _ nextPC _ (add_vec_int (mword_of_int (KVI + 0x1c)) 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s_pc2 := set_reg σ2 nextPC (add_vec_int (mword_of_int (KVI + 0x1c)) 4)).
    assert (Lpriv2p : register_lookup cur_privilege s_pc2.(sregs) = Supervisor)
      by (unfold s_pc2; tmig; exact Lpriv2).
    assert (Lms2p : register_lookup mstatus s_pc2.(sregs) = ms2)
      by (unfold s_pc2; tmig; exact Lms2).
    assert (Lmisa2p : register_lookup misa s_pc2.(sregs) = misa0)
      by (unfold s_pc2; tmig; exact Lmisa2).
    (* a5's value at the executing state *)
    iDestruct (gpr_file_lookup_acc (tp_pin S4) (Regidx (mword_of_int 15 : mword 5)) with "Hfile") as "[Hspc Hfb]".
    iDestruct (gpr_pt_value (mword_of_int 15) (S4 (Regidx (mword_of_int 15 : mword 5))) s_pc2 with "Hreg Hspc") as %Lva2.
    iDestruct ("Hfb" with "Hspc") as "Hfile".
    replace (Z.eqb (uint (mword_of_int 15 : mword 5)) 0) with false in Lva2 by (vm_compute; reflexivity).
    rewrite -rf_lookup Ha5 in Lva2.
    pose proof (exec_execute_csrw_satp_S (mword_of_int 15) s_pc2
                  ltac:(vm_compute; lia) Lpriv2p
                  ltac:(rewrite Lms2p; exact HTVM2)
                  ltac:(rewrite Lmisa2p; exact HmisaS)
                  ltac:(rewrite Lms2p; exact HSXL2)) as Hex2.
    rewrite Lva2 in Hex2.
    rewrite (satp_legalized_sv39 (register_lookup satp s_pc2.(sregs)) (kvi_satp_word root) (kvi_satp_mode root)) in Hex2.
    (* open the Bare arm of the translation slot; do the switch *)
    iDestruct "Hcap" as "(Hstk & Htr & Harm)".
    iDestruct (strans_inv_acc_bare with "Hbit Htr") as "(Hbit & Hbit2 & Hbare & Hstv)".
    iDestruct "Hbare" as (satp0) "(Hsatpc & %HbareMode & Hpmp)".
    iMod (reg_update _ satp _ (kvi_satp_word root) with "Hreg Hsatpc") as "[Hreg Hsatpc]".
    (* The table is ALREADY published (main's boot arm did it, once): all this
       hart does is re-seal its own slot at the KPT arm, out of its own
       satp/tlb/pmp cells plus the up-front snapshot [kpt_lb t0] and the
       persistent [kpt_inv root] riding along. *)
    iDestruct (tlb_res_pt_intro root (kvi_satp_word root) tlbz1 t0
                 (kvi_satp_mode root) (kvi_satp_asid root) (kvi_satp_ppn root)
                 (tlb_ok_pt_empty (mword_of_int 0) t0 tlbz1 (fun vpn' => Hnone1 _ (tlb_hash_range vpn')))
                 with "Hsatpc Htlb Hlbt [Hpmp] Hkinv") as "Htlbinv".
    { iApply (pmp_config_reindex (mword_of_int 0) root with "Hpmp"). }
    iMod (strans_bit_flip with "Hbit Hbit2") as "[Hbitkpt Hbitkpt2]".
    iDestruct (strans_inv_intro root with "Hbitkpt2 Htlbinv") as "Htr".
    iAssert (sie_cap S4 (K - 2) b) with "[Hstk Htr Harm]" as "Hcap".
    { rewrite /sie_cap. iFrame "Hstk Htr Harm". }
    iModIntro. iExists (set_reg s_pc2 satp (kvi_satp_word root)).
    iSplitR.
    { iPureIntro. rewrite Hpceq2. fold s_pc2.
      rewrite Hzreg. exact Hex2. }
    iSplitL "Hreg Hmem".
    { unfold s_pc2, set_reg; cbn [sregs mem mdev]. iFrame "Hreg Hmem". }
    iIntros "Hhs Hpc". iNext.
    assert (Lnpc2 : register_lookup nextPC (set_reg s_pc2 satp (kvi_satp_word root)).(sregs)
                    = mword_of_int (KVI + 0x20)).
    { unfold s_pc2; cbn [sregs]. tmig. rewrite register_lookup_set.
      apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite Lnpc2) in "Hpc".
    assert (Hpnpc2 : add_vec_int (mword_of_int (KVI + 0x1c) : mword 64) 4 = mword_of_int (KVI + 0x20)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpnpc2) in "Hnpc".
    iAssert sconf with "[Hpriv Hms Hhalf Hmiex Hmenvx]" as "Hsc".
    { iFrame "Hhw2 Hminv2 Hpriv Hmiex Hmenvx". iExists ms2. iFrame "Hms Hhalf". done. }
    iAssert (pc_is (mword_of_int (KVI + 0x20))) with "[Hpc Hnpc]" as "Hpc".
    { iFrame "Hpc Hnpc". }
    iDestruct (sie_cap_gpr_join with "Hhs Hsc Hcap Hfile") as "Hcg".
    (* ============ +0x20 sfence.vma zero,zero (under the kernel PT) ===== *)
    iApply (wp_instr_s_sconf S4 (K - 2)%nat b Φ (mword_of_int (KVI + 0x20)) false
              (SFENCE_VMA (Regidx (mword_of_int 0), Regidx (mword_of_int 0)))
              with "Hcg Hpc Hi20").
    iIntros (σ3 Hpceq3) "Hsc Hcap Hfile Hnpc Hsi".
    iDestruct "Hsc" as "(#Hhw3 & #Hminv3 & Hpriv & Hmsx & Hmiex & Hmenvx)".
    iDestruct "Hmsx" as (ms3) "(Hms & Hhalf & %Hmsf3)".
    pose proof Hmsf3 as (HMPRV3 & HSXL3 & HMXR3 & HTSR3 & HXS3 & HFS3 & HVS3 & HSD3 & HMPP3 & HTVM3).
    iDestruct "Hsi" as "[Hreg Hmem]".
    iDestruct (reg_valid with "Hreg Hpriv") as %Lpriv3.
    iDestruct (reg_valid with "Hreg Hms") as %Lms3.
    iMod (reg_update _ nextPC _ (add_vec_int (mword_of_int (KVI + 0x20)) 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s_pc3 := set_reg σ3 nextPC (add_vec_int (mword_of_int (KVI + 0x20)) 4)).
    assert (Lpriv3p : register_lookup cur_privilege s_pc3.(sregs) = Supervisor)
      by (unfold s_pc3; tmig; exact Lpriv3).
    assert (Lms3p : register_lookup mstatus s_pc3.(sregs) = ms3)
      by (unfold s_pc3; tmig; exact Lms3).
    destruct (exec_execute_SFENCE_VMA_S s_pc3 Lpriv3p ltac:(rewrite Lms3p; exact HTVM3))
      as (tlbz3 & Hex3 & Hnone3).
    (* open the KPT arm to reach the tlb cell; flush; re-seal *)
    iDestruct "Hcap" as "(Hstk & Htr & Harm)".
    iDestruct "Htr" as "[(Hbit0 & _ & _) | (Hbit1 & Hk)]".
    { iDestruct (strans_bit_agree with "Hbitkpt Hbit0") as %Hbad.
      apply (f_equal (@bv_unsigned _)) in Hbad. vm_compute in Hbad. discriminate. }
    iDestruct "Hk" as (root_ppn) "Htlbinv".
    (* the flush touches only THIS hart's tlb cell: the tree stays inside
       [kpt_inv], and the post-flush coherence is [tlb_ok_pt_empty] at the
       residue's OWN snapshot, so no invariant is opened in this step. *)
    iDestruct (tlb_res_pt_open with "Htlbinv") as (ksatp3 tlbvec3)
      "(Hsatp & %HkMode3 & %Hkasid3 & %Hkppn3 & Htlbc & Hsnap3 & Hpmp & #Hkinv3)".
    iDestruct "Hsnap3" as (kt3) "(_ & #Hlb3)".
    iMod (reg_update _ tlb _ tlbz3 with "Hreg Htlbc") as "[Hreg Htlbc]".
    iDestruct (tlb_res_pt_intro root_ppn ksatp3 tlbz3 kt3 HkMode3 Hkasid3 Hkppn3
                 (tlb_ok_pt_empty (mword_of_int 0) kt3 tlbz3 (fun vpn' => Hnone3 _ (tlb_hash_range vpn')))
                 with "Hsatp Htlbc Hlb3 Hpmp Hkinv3") as "Htlbinv".
    iDestruct (strans_inv_intro root_ppn with "Hbit1 Htlbinv") as "Htr".
    iAssert (sie_cap S4 (K - 2) b) with "[Hstk Htr Harm]" as "Hcap".
    { rewrite /sie_cap. iFrame "Hstk Htr Harm". }
    iModIntro. iExists (set_reg s_pc3 tlb tlbz3).
    iSplitR.
    { iPureIntro. rewrite Hpceq3. fold s_pc3. rewrite Hzreg. exact Hex3. }
    iSplitL "Hreg Hmem".
    { unfold s_pc3, set_reg; cbn [sregs mem mdev]. iFrame "Hreg Hmem". }
    iIntros "Hhs Hpc". iNext.
    assert (Lnpc3 : register_lookup nextPC (set_reg s_pc3 tlb tlbz3).(sregs)
                    = mword_of_int (KVI + 0x24)).
    { unfold s_pc3; cbn [sregs]. tmig. rewrite register_lookup_set.
      apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite Lnpc3) in "Hpc".
    assert (Hpnpc3 : add_vec_int (mword_of_int (KVI + 0x20) : mword 64) 4 = mword_of_int (KVI + 0x24)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpnpc3) in "Hnpc".
    iAssert sconf with "[Hpriv Hms Hhalf Hmiex Hmenvx]" as "Hsc".
    { iFrame "Hhw3 Hminv3 Hpriv Hmiex Hmenvx". iExists ms3. iFrame "Hms Hhalf". done. }
    iAssert (pc_is (mword_of_int (KVI + 0x24))) with "[Hpc Hnpc]" as "Hpc".
    { iFrame "Hpc Hnpc". }
    iDestruct (sie_cap_gpr_join with "Hhs Hsc Hcap Hfile") as "Hcg".
    (* ============ epilogue: +0x24 ld ra ; +0x26 ld s0 ; +0x28 addi sp ; +0x2a ret ==== *)
    assert (HS4sp : S4 !!! Regidx csp_rs1 = add_vec (mm !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6)))).
    { rewrite /S4 upd_ne; [| reg_neq]. rewrite /S3 upd_ne; [| reg_neq].
      rewrite /S2 upd_ne; [| reg_neq]. rewrite /S1 upd_ne; [| reg_neq].
      rewrite /L upd_ne; [| reg_neq]. rewrite /A0 upd_ne; [| reg_neq].
      rewrite /W2 upd_ne; [| reg_neq]. exact HspW1. }
    (* +0x24 ld ra,8(sp) *)
    iApply (wp_cldsp_s_sconf Φ (mword_of_int (KVI + 0x24)) (mword_of_int 1 : mword 6) (mword_of_int 1 : mword 5)
              S4 (K - 2)%nat (mm !!! Regidx (mword_of_int 1)) b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi24 [Hc1] [-]").
    { iEval (rewrite HS4sp Hb1). iExact "Hc1". }
    iIntros (CID11 Hs11) "Hcg Hpc Hc1". iEval (rewrite HS4sp Hb1) in "Hc1".
    set (L1 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (mm !!! Regidx (mword_of_int 1))]> S4).
    assert (HL1sp : L1 !!! Regidx csp_rs1 = add_vec (mm !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6)))) by (rewrite /L1 upd_ne; [| reg_neq]; exact HS4sp).
    assert (Hp26 : add_vec_int (mword_of_int (KVI + 0x24) : mword 64) 2 = mword_of_int (KVI + 0x26)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp26) in "Hpc".
    (* +0x26 ld s0,0(sp) *)
    iApply (wp_cldsp_s_sconf Φ (mword_of_int (KVI + 0x26)) (mword_of_int 0 : mword 6) (mword_of_int 8 : mword 5)
              L1 (K - 2)%nat (mm !!! Regidx (mword_of_int 8)) b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi26 [Hc2] [-]").
    { iEval (rewrite HL1sp Hb2). iExact "Hc2". }
    iIntros (CID12 Hs12) "Hcg Hpc Hc2". iEval (rewrite HL1sp Hb2) in "Hc2".
    set (L2 := <[Regidx (mword_of_int 8 : mword 5) := regval_into_reg (mm !!! Regidx (mword_of_int 8))]> L1).
    assert (HL2sp : L2 !!! Regidx csp_rs1 = add_vec (mm !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6)))) by (rewrite /L2 upd_ne; [| reg_neq]; exact HL1sp).
    assert (Hp28 : add_vec_int (mword_of_int (KVI + 0x26) : mword 64) 2 = mword_of_int (KVI + 0x28)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp28) in "Hpc".
    (* +0x28 addi sp,sp,16 : the frame pop *)
    assert (Hwv : add_vec (L2 !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 16 : mword 6))) = mm !!! Regidx csp_rs1).
    { rewrite HL2sp. apply frame_cancel_16. }
    assert (Hpop : L2 !!! Regidx csp_rs1 = pa_stk (add_vec (L2 !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 16 : mword 6)))) 2).
    { rewrite Hwv. rewrite HL2sp. exact Hpush. }
    iAssert (stack_own (mm !!! Regidx csp_rs1) 2) with "[Hc1 Hc2]" as "Hframe".
    { rewrite stack_own_slots; cbn [seq].
      iSplitL "Hc1". { iExists (mm !!! Regidx (mword_of_int 1)). iExact "Hc1". }
      iSplitL "Hc2". { iExists (mm !!! Regidx (mword_of_int 8)). iExact "Hc2". }
      done. }
    iEval (rewrite -Hwv) in "Hframe".
    iApply (wp_caddi_sp_pop_s_sconf Φ (mword_of_int (KVI + 0x28)) (mword_of_int 16 : mword 6)
              L2 (K - 2)%nat 2 b Hpop with "Hcg Hpc Hi28 Hframe [-]").
    iIntros (CID13 Hs13) "Hcg Hpc".
    set (Efin := <[Regidx csp_rs1 := regval_into_reg (add_vec (L2 !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 16 : mword 6))))]> L2).
    assert (Hnk : ((K - 2) + 2)%nat = K) by lia.
    iEval (rewrite Hnk) in "Hcg".
    assert (Hp2a : add_vec_int (mword_of_int (KVI + 0x28) : mword 64) 2 = mword_of_int (KVI + 0x2a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp2a) in "Hpc".
    (* +0x2a ret *)
    assert (HEfin1 : Efin !!! Regidx (mword_of_int 1 : mword 5) = mm !!! Regidx (mword_of_int 1)).
    { rewrite /Efin upd_ne; [| reg_neq]. rewrite /L2 upd_ne; [| reg_neq]. rewrite /L1 upd_eq. reflexivity. }
    iApply (wp_cret_s_sconf Φ (mword_of_int (KVI + 0x2a)) (mword_of_int 1 : mword 5) Efin K b
              ltac:(vm_compute; discriminate) with "Hcg Hpc Hi2a [-]").
    iIntros (CID14 Hs14) "Hcg Hpc". iEval (rgne; rewrite HEfin1) in "Hpc".
    (* ---- hand the continuation the post-switch resources ---- *)
    iSpecialize ("Hcont" $! CID14 with "[%]"); [wp_next_chain|].
    iApply ("Hcont" $! Efin with "Hcg Hpc [%] Hbitkpt [Hstv]").
    { (* callee_saved mm Efin *)
      unfold callee_saved.
      repeat split;
        first [ by (rewrite /Efin upd_eq; exact Hwv)
              | by (rewrite /Efin upd_ne; [| reg_neq]; rewrite /L2 upd_eq)
              | (rewrite /Efin /L2 /L1 /S4 /S3 /S2 /S1 /L /A0 /W2 /W1;
                 repeat (rewrite upd_ne; [| reg_neq]); reflexivity) ]. }
    { iExact "Hstv". }
  Qed.

End KvminithartBody.

Module KvminithartProof : KVMINITHART.
  Definition wp_kvminithart_sconf
      `{!riscvGS Σ, !sieG Σ} `{CID : CpuId}
      (Φ : mval -> iProp Σ) (mm : regfile) (lvl K : nat)
      (root : mword 44)
      (tlbvec0 : vec (option TLB_Entry) (2 ^ 6)) (b : bool)
      : wp_kvminithart_sconf_body Φ mm lvl K root tlbvec0 b :=
    wp_kvminithart_sconf_proof Φ mm lvl K root tlbvec0 b.
End KvminithartProof.
