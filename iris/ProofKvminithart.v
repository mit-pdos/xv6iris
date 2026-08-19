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
Require Import RiscvPtsto RiscvLang.
Require Import SmodeCore RegFile WpGpr WpMmodeLeafBase.
Require Import HartTp WpNext IntrDefs WpSmodeIntr WpSconfAlu WpSconfMem WpSconfCtl.
(* the two converted leaves this function's three raw blocks became *)
Require Import WpSconfCsr WpSconfSfence.
Require Import RiscvExtras.
Require Import CalleeSaved StackOwn.
Require Import InstrBytes.
Require Import PtTree.
Require Import KptShare.
Require Import TransPt.
Require Import UserretDefs.
Require Import WpKvminithart CodeKvminithart.
Require Import SpecKvminithart.
From Kernel Require KernelSyms.
Require Import KernelRvcDecode.
Local Open Scope Z_scope.
Import Defs.

Section KvminithartBody.
  Context `{!riscvGS Σ, !sieG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.


  Ltac reg_neq :=
    lazymatch goal with
    | |- ?a <> ?b => tryif unify a b then fail else (vm_compute; discriminate)
    end.

  Lemma wp_kvminithart_sconf_proof (mm : regfile) (lvl K : nat)
      (root : mword 44)
      (tlbvec0 : vec (option TLB_Entry) (2 ^ 6)) (pcur : mword 64) :
    wp_kvminithart_sconf_body mm lvl K root tlbvec0 pcur.
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
    (* frame-cell address facts (2-slot frame: ra @ slot 1, s0 @ slot 2) *)
    assert (Hpush : add_vec (mm !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6))) = pa_stk (mm !!! Regidx csp_rs1) 2).
    { unfold pa_stk, add_vec_int. apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    assert (Hb1 : add_vec (add_vec (mm !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6)))) (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000"))) = pa_stk (mm !!! Regidx csp_rs1) 1).
    { unfold pa_stk, add_vec_int. rewrite !pa_stk_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb2 : add_vec (add_vec (mm !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6)))) (zero_extend' 64 (concat_vec (mword_of_int 0 : mword 6) ('b"000"))) = pa_stk (mm !!! Regidx csp_rs1) 2).
    { unfold pa_stk, add_vec_int. rewrite !pa_stk_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    iPoseProof (kvi_00 with "Htext") as "Hi00".
    (* ============ +0x00 addi sp,sp,-16 : 2-slot frame push ============ *)
    iApply (wp_caddi_sp_push_s_sconf (mword_of_int KernelSyms.kvminithart) (mword_of_int 48 : mword 6) mm K 2 false HK Hpush
              with "Hcg Hpc Hi00").
              iClear "Hi00".
    iApply wp_next_off_intro.
    iIntros "Hcg Hframe Hpc".
    set (W1 := <[Regidx csp_rs1 := regval_into_reg
        (add_vec (mm !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6))))]> mm).
    iEval (rewrite (stack_own_slots (KTR := KT0)); cbn [seq]) in "Hframe".
    iDestruct "Hframe" as "(S1 & S2 & _)".
    iDestruct "S1" as (v1) "Hc1". iDestruct "S2" as (v2) "Hc2".
    assert (HspW1 : W1 !!! Regidx csp_rs1 = add_vec (mm !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6)))) by (rewrite /W1 upd_eq; reflexivity).
    assert (Hp02 : add_vec_int (mword_of_int KernelSyms.kvminithart : mword 64) 2 = mword_of_int (KernelSyms.kvminithart + 0x02)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp02) in "Hpc".
    iPoseProof (kvi_02 with "Htext") as "Hi02".
    (* +0x02 sd ra,8(sp) -> slot 1 *)
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.kvminithart + 0x02)) (mword_of_int 1 : mword 6) (mword_of_int 1 : mword 5)
              W1 (K - 2)%nat v1 false with "Hcg Hpc Hi02 [Hc1]").
              iClear "Hi02".
    { iEval (rewrite HspW1 Hb1). iExact "Hc1". }
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc Hc1". iEval (rewrite HspW1 Hb1; rgne) in "Hc1".
    assert (HW1r1 : W1 !!! Regidx (mword_of_int 1 : mword 5) = mm !!! Regidx (mword_of_int 1)) by (rewrite /W1 upd_ne; [reflexivity | reg_neq]).
    iEval (rewrite HW1r1) in "Hc1".
    assert (Hp04 : add_vec_int (mword_of_int (KernelSyms.kvminithart + 0x02) : mword 64) 2 = mword_of_int (KernelSyms.kvminithart + 0x04)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp04) in "Hpc".
    iPoseProof (kvi_04 with "Htext") as "Hi04".
    (* +0x04 sd s0,0(sp) -> slot 2 *)
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.kvminithart + 0x04)) (mword_of_int 0 : mword 6) (mword_of_int 8 : mword 5)
              W1 (K - 2)%nat v2 false with "Hcg Hpc Hi04 [Hc2]").
              iClear "Hi04".
    { iEval (rewrite HspW1 Hb2). iExact "Hc2". }
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc Hc2". iEval (rewrite HspW1 Hb2; rgne) in "Hc2".
    assert (HW1r8 : W1 !!! Regidx (mword_of_int 8 : mword 5) = mm !!! Regidx (mword_of_int 8)) by (rewrite /W1 upd_ne; [reflexivity | reg_neq]).
    iEval (rewrite HW1r8) in "Hc2".
    assert (Hp06 : add_vec_int (mword_of_int (KernelSyms.kvminithart + 0x04) : mword 64) 2 = mword_of_int (KernelSyms.kvminithart + 0x06)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp06) in "Hpc".
    iPoseProof (kvi_06 with "Htext") as "Hi06".
    (* +0x06 addi s0,sp,16 (value unused) *)
    iApply (wp_caddi4spn_s_sconf (mword_of_int (KernelSyms.kvminithart + 0x06)) (Cregidx (mword_of_int 0)) (mword_of_int 4 : mword 8) (mword_of_int 8 : mword 5)
              W1 (K - 2)%nat false ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi06").
              iClear "Hi06".
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    set (W2 := <[Regidx (mword_of_int 8 : mword 5) := regval_into_reg (add_vec (W1 !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm (mword_of_int 4 : mword 8))))]> W1).
    assert (Hp08 : add_vec_int (mword_of_int (KernelSyms.kvminithart + 0x06) : mword 64) 2 = mword_of_int (KernelSyms.kvminithart + 0x08)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp08) in "Hpc".
    iPoseProof (kvi_08 with "Htext") as "Hi08".
    (* ============ +0x08 sfence.vma zero,zero (under Bare) =============
       THE FLUSHED CELL STAYS IN THE FUNCTION'S OWN HAND from here to
       +0x1c.  That is what the leaf's CELL interface is for
       (WpSconfSfence.v's closing note): the six instructions in between run
       on [Hcg] alone, [Htlb] sits beside the bundle owned by nobody else,
       and the switch consumes it with [Hnone1] still attached.  Re-sealing
       it into the translation slot would discard exactly that fact. *)
    iApply (wp_sfence_vma_s_sconf KT0 pcur
              (mword_of_int (KernelSyms.kvminithart + 0x08))
              W2 (K - 2)%nat tlbvec0 with "Hcg Htlb Hpc Hi08").
    iApply wp_next_off_intro.
    iIntros "Hcg Htlbz Hpc".
    iDestruct "Htlbz" as (tlbz1) "(%Hnone1 & Htlb)".
    assert (Hpnpc1 : add_vec_int (mword_of_int (KernelSyms.kvminithart + 0x08) : mword 64) 4 = mword_of_int (KernelSyms.kvminithart + 0x0c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpnpc1) in "Hpc".
    iPoseProof (kvi_0c with "Htext") as "Hi0c".
    (* ============ +0x0c auipc a5,0x9 ============ *)
    iApply (wp_auipc_s_sconf (mword_of_int (KernelSyms.kvminithart + 0x0c)) (mword_of_int 15 : mword 5) (mword_of_int 9 : mword 20)
              W2 (K - 2)%nat false ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi0c").
              iClear "Hi0c".
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    set (A0 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (add_vec (mword_of_int (KernelSyms.kvminithart + 0x0c) : mword 64) (auipc_off (mword_of_int 9 : mword 20)))]> W2).
    assert (Hp10 : add_vec_int (mword_of_int (KernelSyms.kvminithart + 0x0c) : mword 64) 4 = mword_of_int (KernelSyms.kvminithart + 0x10)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp10) in "Hpc".
    (* ============ +0x10 ld a5,764(a5) : a5 := root_b ============ *)
    assert (Haddr : add_vec (A0 !!! Regidx (mword_of_int 15 : mword 5)) (sign_extend' 64 (mword_of_int 968 : mword 12)) = mword_of_int KernelSyms.kernel_pagetable).
    { rewrite /A0 upd_eq. apply bv_eq; vm_compute; reflexivity. }
    iPoseProof (kvi_10 with "Htext") as "Hi10".
    iApply (wp_ld_s_sconf (kt := KT0) (ktd := KT0) (mword_of_int (KernelSyms.kvminithart + 0x10)) (mword_of_int 15 : mword 5) (mword_of_int 15 : mword 5) (mword_of_int 968 : mword 12)
              A0 (K - 2)%nat (zero_extend' 64 (concat_vec root (zeros' 12 : mword 12))) false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi10 []").
              iClear "Hi10".
    { iEval (rgne; rewrite Haddr). iExact "Hcell". }
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc _".
    set (L := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (zero_extend' 64 (concat_vec root (zeros' 12 : mword 12)))]> A0).
    assert (Hp14 : add_vec_int (mword_of_int (KernelSyms.kvminithart + 0x10) : mword 64) 4 = mword_of_int (KernelSyms.kvminithart + 0x14)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp14) in "Hpc".
    iPoseProof (kvi_14 with "Htext") as "Hi14".
    (* ============ +0x14 srli a5,a5,0xc ============ *)
    iEval (rewrite Hc7) in "Hi14".
    iApply (wp_csrli_s_sconf (mword_of_int (KernelSyms.kvminithart + 0x14)) (Cregidx (mword_of_int 7)) (mword_of_int 15 : mword 5) (mword_of_int 12 : mword 6)
              L (K - 2)%nat false Hc7 ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi14").
              iClear "Hi14".
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    set (S1 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg
        (shift_bits_right (rget L (mword_of_int 15 : mword 5)) (subrange_vec_dec (mword_of_int 12 : mword 6) (Z.sub log2_xlen 1) 0))]> L).
    assert (Hp16 : add_vec_int (mword_of_int (KernelSyms.kvminithart + 0x14) : mword 64) 2 = mword_of_int (KernelSyms.kvminithart + 0x16)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp16) in "Hpc".
    iPoseProof (kvi_16 with "Htext") as "Hi16".
    (* ============ +0x16 li a4,-1 ============ *)
    iApply (wp_cli_s_sconf (mword_of_int (KernelSyms.kvminithart + 0x16)) (mword_of_int 14 : mword 5) (mword_of_int 63 : mword 6)
              (add_vec zero_reg (sign_extend' 64 (sign_extend' 12 (mword_of_int 63 : mword 6))))
              S1 (K - 2)%nat false ltac:(vm_compute; discriminate) ltac:(rdok) eq_refl
              with "Hcg Hpc Hi16").
              iClear "Hi16".
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    set (S2 := <[Regidx (mword_of_int 14 : mword 5) := regval_into_reg
        (add_vec zero_reg (sign_extend' 64 (sign_extend' 12 (mword_of_int 63 : mword 6))))]> S1).
    assert (Hp18 : add_vec_int (mword_of_int (KernelSyms.kvminithart + 0x16) : mword 64) 2 = mword_of_int (KernelSyms.kvminithart + 0x18)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp18) in "Hpc".
    iPoseProof (kvi_18 with "Htext") as "Hi18".
    (* ============ +0x18 slli a4,a4,0x3f ============ *)
    iApply (wp_cslli_s_sconf (mword_of_int (KernelSyms.kvminithart + 0x18)) (Regidx (mword_of_int 14 : mword 5)) (mword_of_int 14 : mword 5) (mword_of_int 63 : mword 6)
              S2 (K - 2)%nat false eq_refl ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi18").
              iClear "Hi18".
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    set (S3 := <[Regidx (mword_of_int 14 : mword 5) := regval_into_reg
        (shift_bits_left (rget S2 (mword_of_int 14 : mword 5)) (subrange_vec_dec (mword_of_int 63 : mword 6) (Z.sub log2_xlen 1) 0))]> S2).
    assert (Hp1a : add_vec_int (mword_of_int (KernelSyms.kvminithart + 0x18) : mword 64) 2 = mword_of_int (KernelSyms.kvminithart + 0x1a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp1a) in "Hpc".
    iPoseProof (kvi_1a with "Htext") as "Hi1a".
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
    iApply (wp_cor_s_sconf (mword_of_int (KernelSyms.kvminithart + 0x1a)) (mword_of_int 15 : mword 5) (mword_of_int 15 : mword 5) (mword_of_int 14 : mword 5)
              (kvi_satp_word root) S3 (K - 2)%nat false ltac:(vm_compute; discriminate) ltac:(rdok) Hor
              with "Hcg Hpc Hi1a").
              iClear "Hi1a".
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    set (S4 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (kvi_satp_word root)]> S3).
    assert (Ha5 : S4 !!! Regidx (mword_of_int 15 : mword 5) = kvi_satp_word root) by (rewrite /S4 upd_eq; reflexivity).
    assert (Hp1c : add_vec_int (mword_of_int (KernelSyms.kvminithart + 0x1a) : mword 64) 2 = mword_of_int (KernelSyms.kvminithart + 0x1c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp1c) in "Hpc".
    iPoseProof (kvi_1c with "Htext") as "Hi1c".
    (* ============ +0x1c csrw satp,a5 : THE SWITCH ============
       The leaf owns the instruction; THE SLOT MOVE IS THIS FUNCTION'S, and
       it is the pre-move block's own script -- the leaf hands the Bare
       arm's cells over with satp already rewritten, and takes back a slot
       re-sealed at the kernel-table arm. *)
    assert (Hrs15 : uint (mword_of_int 15 : mword 5) <> 0) by (vm_compute; lia).
    assert (Ha5r : rget S4 (mword_of_int 15 : mword 5) = kvi_satp_word root)
      by (rgne; exact Ha5).
    iApply (wp_csrw_satp_s_sconf (mword_of_int (KernelSyms.kvminithart + 0x1c))
              (mword_of_int 15 : mword 5) S4 (K - 2)%nat (kvi_satp_word root)
              (kpt_on cpu_id ∗ (∃ v : mword 64, stvec ↦ᵣ v))%I
              Hrs15 Ha5r
              with "Hcg Hbit [Htlb] Hpc Hi1c").
    { (* The table is ALREADY published (main's boot arm did it, once): all
         this hart does is re-seal its own slot at the KPT arm, out of its
         own satp/tlb/pmp cells plus the up-front snapshot [kpt_lb t0] and
         the persistent [kpt_inv root] riding along.  [tlbz1] / [Hnone1] are
         the +0x08 flush, still in hand and never re-sealed. *)
      iIntros (satp0) "Hsatpc Hpmp Hstv Hbit Hbit2".
      iEval (rewrite (satp_legalized_sv39 satp0 (kvi_satp_word root)
                        (kvi_satp_mode root))) in "Hsatpc".
      iDestruct (tlb_res_pt_intro root (kvi_satp_word root) tlbz1 t0
                   (kvi_satp_mode root) (kvi_satp_asid root) (kvi_satp_ppn root)
                   (tlb_ok_pt_empty (mword_of_int 0) t0 tlbz1 (fun vpn' => Hnone1 _ (tlb_hash_range vpn')))
                   with "Hsatpc Htlb Hlbt [Hpmp] Hkinv") as "Htlbinv".
      { iApply (pmp_config_reindex (mword_of_int 0) root with "Hpmp"). }
      iMod (strans_flip with "Hbit Hbit2") as "[Hbitkpt2 #Hbitkpt]".
      iDestruct (strans_inv_intro root with "Hbitkpt2 Htlbinv") as "Htr".
      iModIntro. iFrame "Htr Hbitkpt Hstv". }
    iApply wp_next_off_intro.
    iIntros "Hcg [#Hbitkpt Hstv] Hpc".
    assert (Hpnpc2 : add_vec_int (mword_of_int (KernelSyms.kvminithart + 0x1c) : mword 64) 4 = mword_of_int (KernelSyms.kvminithart + 0x20)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpnpc2) in "Hpc".
    iPoseProof (kvi_20 with "Htext") as "Hi20".
    (* ============ +0x20 sfence.vma zero,zero (under the kernel PT) =====
       THE OTHER SFENCE LEAF.  By here the cell is back inside the
       translation slot, at the arm the switch just installed, and nothing
       downstream reads this flush -- so the KPT-arm variant borrows the
       cell out of [tlb_res_pt], re-seals it at the flushed vector, and the
       receipt the switch produced is the whole price. *)
    iApply (wp_sfence_vma_kpt_s_sconf KT0 pcur
              (mword_of_int (KernelSyms.kvminithart + 0x20))
              S4 (K - 2)%nat with "Hcg Hbitkpt Hpc Hi20").
    iApply wp_next_off_intro.
    iIntros "Hcg _ Hpc".
    assert (Hpnpc3 : add_vec_int (mword_of_int (KernelSyms.kvminithart + 0x20) : mword 64) 4 = mword_of_int (KernelSyms.kvminithart + 0x24)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpnpc3) in "Hpc".
    (* ============ epilogue: +0x24 ld ra ; +0x26 ld s0 ; +0x28 addi sp ; +0x2a ret ==== *)
    assert (HS4sp : S4 !!! Regidx csp_rs1 = add_vec (mm !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6)))).
    { rewrite /S4 upd_ne; [| reg_neq]. rewrite /S3 upd_ne; [| reg_neq].
      rewrite /S2 upd_ne; [| reg_neq]. rewrite /S1 upd_ne; [| reg_neq].
      rewrite /L upd_ne; [| reg_neq]. rewrite /A0 upd_ne; [| reg_neq].
      rewrite /W2 upd_ne; [| reg_neq]. exact HspW1. }
    iPoseProof (kvi_24 with "Htext") as "Hi24".
    (* +0x24 ld ra,8(sp) *)
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.kvminithart + 0x24)) (mword_of_int 1 : mword 6) (mword_of_int 1 : mword 5)
              S4 (K - 2)%nat (mm !!! Regidx (mword_of_int 1)) false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi24 [Hc1]").
              iClear "Hi24".
    { iEval (rewrite HS4sp Hb1). iExact "Hc1". }
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc Hc1". iEval (rewrite HS4sp Hb1) in "Hc1".
    set (L1 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (mm !!! Regidx (mword_of_int 1))]> S4).
    assert (HL1sp : L1 !!! Regidx csp_rs1 = add_vec (mm !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6)))) by (rewrite /L1 upd_ne; [| reg_neq]; exact HS4sp).
    assert (Hp26 : add_vec_int (mword_of_int (KernelSyms.kvminithart + 0x24) : mword 64) 2 = mword_of_int (KernelSyms.kvminithart + 0x26)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp26) in "Hpc".
    iPoseProof (kvi_26 with "Htext") as "Hi26".
    (* +0x26 ld s0,0(sp) *)
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.kvminithart + 0x26)) (mword_of_int 0 : mword 6) (mword_of_int 8 : mword 5)
              L1 (K - 2)%nat (mm !!! Regidx (mword_of_int 8)) false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi26 [Hc2]").
              iClear "Hi26".
    { iEval (rewrite HL1sp Hb2). iExact "Hc2". }
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc Hc2". iEval (rewrite HL1sp Hb2) in "Hc2".
    set (L2 := <[Regidx (mword_of_int 8 : mword 5) := regval_into_reg (mm !!! Regidx (mword_of_int 8))]> L1).
    assert (HL2sp : L2 !!! Regidx csp_rs1 = add_vec (mm !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6)))) by (rewrite /L2 upd_ne; [| reg_neq]; exact HL1sp).
    assert (Hp28 : add_vec_int (mword_of_int (KernelSyms.kvminithart + 0x26) : mword 64) 2 = mword_of_int (KernelSyms.kvminithart + 0x28)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp28) in "Hpc".
    (* +0x28 addi sp,sp,16 : the frame pop *)
    assert (Hwv : add_vec (L2 !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 16 : mword 6))) = mm !!! Regidx csp_rs1).
    { rewrite HL2sp. apply frame_cancel_16. }
    assert (Hpop : L2 !!! Regidx csp_rs1 = pa_stk (add_vec (L2 !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 16 : mword 6)))) 2).
    { rewrite Hwv. rewrite HL2sp. exact Hpush. }
    iAssert (stack_own (KTR := KT0) (mm !!! Regidx csp_rs1) 2) with "[Hc1 Hc2]" as "Hframe".
    { rewrite (stack_own_slots (KTR := KT0)); cbn [seq].
      iSplitL "Hc1". { iExists (mm !!! Regidx (mword_of_int 1)). iExact "Hc1". }
      iSplitL "Hc2". { iExists (mm !!! Regidx (mword_of_int 8)). iExact "Hc2". }
      done. }
    iEval (rewrite -Hwv) in "Hframe".
    iPoseProof (kvi_28 with "Htext") as "Hi28".
    iApply (wp_caddi_sp_pop_s_sconf (mword_of_int (KernelSyms.kvminithart + 0x28)) (mword_of_int 16 : mword 6)
              L2 (K - 2)%nat 2 false Hpop with "Hcg Hpc Hi28 Hframe").
              iClear "Hi28".
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    set (Efin := <[Regidx csp_rs1 := regval_into_reg (add_vec (L2 !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 16 : mword 6))))]> L2).
    assert (Hnk : ((K - 2) + 2)%nat = K) by lia.
    iEval (rewrite Hnk) in "Hcg".
    assert (Hp2a : add_vec_int (mword_of_int (KernelSyms.kvminithart + 0x28) : mword 64) 2 = mword_of_int (KernelSyms.kvminithart + 0x2a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp2a) in "Hpc".
    (* +0x2a ret *)
    assert (HEfin1 : Efin !!! Regidx (mword_of_int 1 : mword 5) = mm !!! Regidx (mword_of_int 1)).
    { rewrite /Efin upd_ne; [| reg_neq]. rewrite /L2 upd_ne; [| reg_neq]. rewrite /L1 upd_eq. reflexivity. }
    iPoseProof (kvi_2a with "Htext") as "Hi2a".
    iApply (wp_cret_s_sconf (mword_of_int (KernelSyms.kvminithart + 0x2a)) (mword_of_int 1 : mword 5) Efin K false
              ltac:(vm_compute; discriminate) with "Hcg Hpc Hi2a").
              iClear "Hi2a".
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc". iEval (rgne; rewrite HEfin1) in "Hpc".
    (* ---- hand the continuation the post-switch resources ---- *)
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
      `{!riscvGS Σ, !sieG Σ} `{GEN : GenId} `{CID : CpuId}
      (mm : regfile) (lvl K : nat)
      (root : mword 44)
      (tlbvec0 : vec (option TLB_Entry) (2 ^ 6)) (pcur : mword 64)
      : wp_kvminithart_sconf_body mm lvl K root tlbvec0 pcur :=
    wp_kvminithart_sconf_proof mm lvl K root tlbvec0 pcur.
End KvminithartProof.
