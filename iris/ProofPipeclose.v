(* ProofPipeclose.v -- pipeclose over the SIE-agnostic v2 bundle.

   The function that finally frees a pipe.  Its shape in the logic:

   - acquire takes the lock against the caller's REFERENCE (ACQUIRE_GEN at
     [Tc := pipe_ref γp w 1], accessor [PipeInv.is_pipe_openable]);
   - the flag store spends that end: [pipe_endstate_shut] sends the reference
     home and hands back the persistent RECEIPT [pipe_shut γp w];
   - the flag reads at +0x24 / +0x2a decide.  If the OTHER end is still open
     the pipe lives and release merely closes the invariant again (RELEASE_GEN
     with [lock_finisher_close] -- NOT [RELEASE], which wants an [is_lock] the
     pipe does not have).  If it is shut, [pipe_endstate_closed] hands over ITS
     receipt too and RELEASE_CANCEL destroys the invariant at the word clear,
     cashing [PipeInv.pipe_res_dead]; out come the lock's own two words and
     every other byte of the object, which [pipe_bytes_page_own] makes a page
     again for kfree.

   Two joins, both [iAssert]ed continuations, because the binary has two: the
   flag tests at +0x24 are shared by the writable and readable arms, and the
   epilogue at +0x36 by the freeing and non-freeing ones.  The +0x24 join is
   built BEFORE the branch on [writable], or its whole tail would be
   duplicated across the two arms of [destruct w].                          *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
From iris.algebra Require Import frac.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExtras.
Require Import RegFile.
Require Import InstrBytes WpMmodeLeafBase.
Require Import SmodeCore.
Require Import StackOwn CalleeSaved KernelText.
Require Import VcGen WpSconfAlu WpSconfMem WpSconfCtl WpSconfBtype WpSconfLock.
Require Import WpLock WpMycpu ProcGeom CpuOwn KernelRvcDecode.
Require Import IntrDefs.
Require Import FdSlots SchedCtx.
Require Import KallocInv PageFields PipeInv.
Require Import SpecPanic.
Require Import SpecAcquire SpecRelease SpecWakeup SpecKfree.
Require Import WpPipecloseDecode.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SpecPipeclose.
Import Defs.

Local Ltac peel n := do n (rewrite upd_ne; [| vm_compute; discriminate]).
Local Ltac nz := vm_compute; discriminate.

Local Lemma pcv_addv_zero_l (x : mword 64) : add_vec zero_reg x = x.
Proof.
  assert (add_vec_unsigned : forall a b : mword 64,
            bv_unsigned (add_vec a b) = bv_wrap 64 (bv_unsigned a + bv_unsigned b)).
  { intros a b. unfold add_vec, Operators_mwords.word_binop, Operators_mwords.with_word',
      SailStdpp.Values.with_word, to_word, get_word, MachineWord.MachineWord.add.
    rewrite bv_add_unsigned. reflexivity. }
  apply bv_eq. rewrite add_vec_unsigned.
  change (bv_unsigned (zero_reg : mword 64)) with 0%Z. rewrite Z.add_0_l.
  apply bv_wrap_small. apply bv_unsigned_in_range.
Qed.

Module PipecloseProof (Acquire : ACQUIRE_GEN) (Wakeup : WAKEUP)
                      (Release : RELEASE_GEN) (ReleaseCancel : RELEASE_CANCEL)
                      (Kfree : KFREE) : PIPECLOSE.

Section ProofPipeclose.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !pipeG Σ, !kallocG Σ}.
  Context `{CID : CpuId}.

  Lemma wp_pipeclose_sconf (γ : gname) (Φ : mval -> iProp Σ) (γs : list gname)
      (γl : gname) (γp : pipe_names) (w : bool)
      (γkl : gname) (γk : gname * gname) (klk kfl : mword 64) (on : option nat)
      (m : regfile) (n : nat) (eb : bool) (pme : mword 64) (C : iProp Σ) (av : nat)
    : wp_pipeclose_sconf_body γ Φ γs γl γp w γkl γk klk kfl on m n eb pme C av.
  Proof.
    cbv beta delta [wp_pipeclose_sconf_body].
    intros pcE pi ret_tgt Hw Htp Hav Hpos Hklk Hkfl.
    pose (sp0 := (m !!! Regidx csp_rs1 : mword 64)).
    assert (Hcpune : eq_vec (zero_reg : mword 64) (mycpu_ret cid_word) = false)
      by (apply mycpu_ret_nonzero; apply tp_ok_cid).
    iIntros "Hcg Hown #Htext Hpc #Hpipe Href #Hkmem Havail #Hpinv #Hpanic Hcont".
    iAssert (⌜length γs = NPROC⌝)%I as %Hlen.
    { iDestruct "Hpinv" as "[%Hl _]". iPureIntro. exact Hl. }
    iDestruct (is_pipe_valid with "Hpipe") as %Hpv.
    iPoseProof (is_pipe_openable with "Hpipe") as "#Hopen".
    iPoseProof (pci_00 with "Htext") as "Hi00".
    iPoseProof (pci_02 with "Htext") as "Hi02".
    iPoseProof (pci_04 with "Htext") as "Hi04".
    iPoseProof (pci_06 with "Htext") as "Hi06".
    iPoseProof (pci_08 with "Htext") as "Hi08".
    iPoseProof (pci_0a with "Htext") as "Hi0a".
    iPoseProof (pci_0c with "Htext") as "Hi0c".
    iPoseProof (pci_0e with "Htext") as "Hi0e".
    (* ---- 0x00: c.addi sp,-32 -- the frame trade (k := 4) ---- *)
    set (spr := add_vec sp0 (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6)))).
    set (A0 := <[Regidx csp_rs1 := regval_into_reg
        (add_vec (m !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))))]> m).
    assert (HcspA0 : A0 !!! Regidx csp_rs1 = spr) by (rewrite /A0 upd_eq; reflexivity).
    assert (Hspr4 : pa_stk sp0 4 = spr).
    { rewrite /spr. unfold pa_stk, add_vec_int. apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    assert (Hspm : m !!! Regidx csp_rs1 = sp0) by reflexivity.
    assert (Hpush : add_vec (m !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))) = pa_stk (m !!! Regidx csp_rs1) 4).
    { unfold pa_stk, add_vec_int. apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    iApply (wp_caddi_sp_push_s_sconf γ Φ pcE (mword_of_int 32 : mword 6) m av 4 ltac:(lia) Hpush
              with "Hcg Hpc Hi00 [-]").
    iIntros "Hcg Hframe Hpc".
    iEval (rewrite Hspm) in "Hframe".
    change (<[Regidx csp_rs1 := regval_into_reg
        (add_vec (m !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))))]> m) with A0.
    assert (Hpc02 : add_vec_int (pcE : mword 64) 2 = mword_of_int (PC + 0x02)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc02) in "Hpc".
    iEval (rewrite stack_own_slots; cbn [seq]) in "Hframe".
    iDestruct "Hframe" as "(S1c & S2c & S3c & S4c & _)".
    iDestruct "S1c" as (vr24) "Hr24".
    iDestruct "S2c" as (vr16) "Hr16".
    iDestruct "S3c" as (vr8) "Hr8".
    iDestruct "S4c" as (vr0) "Hr0".
    assert (Hb1 : pa_stk sp0 1 = add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000")))).
    { rewrite /spr. unfold sp0, pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb2 : pa_stk sp0 2 = add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000")))).
    { rewrite /spr. unfold sp0, pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb3 : pa_stk sp0 3 = add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000")))).
    { rewrite /spr. unfold sp0, pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb4 : pa_stk sp0 4 = add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 0 : mword 6) ('b"000")))).
    { rewrite /spr. unfold sp0, pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    (* ---- 0x02..0x08: c.sdsp ra/s0/s1/s2 ---- *)
    iApply (wp_csdsp_s_sconf γ Φ (mword_of_int (PC + 0x02)) (mword_of_int 3 : mword 6) (mword_of_int 1 : mword 5)
              A0 (av - 4)%nat vr24 with "Hcg Hpc Hi02 [Hr24] [-]").
    { iEval (rewrite HcspA0 -Hb1). iExact "Hr24". }
    iIntros "Hcg Hpc Hr24".
    assert (Hpc04 : add_vec_int (mword_of_int (PC + 0x02) : mword 64) 2 = mword_of_int (PC + 0x04)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc04) in "Hpc".
    iApply (wp_csdsp_s_sconf γ Φ (mword_of_int (PC + 0x04)) (mword_of_int 2 : mword 6) (mword_of_int 8 : mword 5)
              A0 (av - 4)%nat vr16 with "Hcg Hpc Hi04 [Hr16] [-]").
    { iEval (rewrite HcspA0 -Hb2). iExact "Hr16". }
    iIntros "Hcg Hpc Hr16".
    assert (Hpc06 : add_vec_int (mword_of_int (PC + 0x04) : mword 64) 2 = mword_of_int (PC + 0x06)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc06) in "Hpc".
    iApply (wp_csdsp_s_sconf γ Φ (mword_of_int (PC + 0x06)) (mword_of_int 1 : mword 6) (mword_of_int 9 : mword 5)
              A0 (av - 4)%nat vr8 with "Hcg Hpc Hi06 [Hr8] [-]").
    { iEval (rewrite HcspA0 -Hb3). iExact "Hr8". }
    iIntros "Hcg Hpc Hr8".
    assert (Hpc08 : add_vec_int (mword_of_int (PC + 0x06) : mword 64) 2 = mword_of_int (PC + 0x08)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc08) in "Hpc".
    iApply (wp_csdsp_s_sconf γ Φ (mword_of_int (PC + 0x08)) (mword_of_int 0 : mword 6) (mword_of_int 18 : mword 5)
              A0 (av - 4)%nat vr0 with "Hcg Hpc Hi08 [Hr0] [-]").
    { iEval (rewrite HcspA0 -Hb4). iExact "Hr0". }
    iIntros "Hcg Hpc Hr0".
    assert (Hpc0a : add_vec_int (mword_of_int (PC + 0x08) : mword 64) 2 = mword_of_int (PC + 0x0a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc0a) in "Hpc".
    (* ---- 0x0a: c.addi4spn s0,sp,32 ---- *)
    iApply (wp_caddi4spn_s_sconf γ Φ (mword_of_int (PC + 0x0a)) (Cregidx (mword_of_int 0)) (mword_of_int 8 : mword 8) (mword_of_int 8 : mword 5)
              A0 (av - 4)%nat ltac:(vm_compute; reflexivity) ltac:(nz) ltac:(nz)
              with "Hcg Hpc Hi0a [-]").
    iIntros "Hcg Hpc".
    set (A1 := <[Regidx (mword_of_int 8 : mword 5) := regval_into_reg
        (add_vec (A0 !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm (mword_of_int 8 : mword 8))))]> A0).
    change (<[Regidx (mword_of_int 8 : mword 5) := regval_into_reg
        (add_vec (A0 !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm (mword_of_int 8 : mword 8))))]> A0) with A1.
    assert (Hpc0c : add_vec_int (mword_of_int (PC + 0x0a) : mword 64) 2 = mword_of_int (PC + 0x0c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc0c) in "Hpc".
    (* ---- 0x0c: c.mv s1,a0 ---- *)
    iApply (wp_cmv_s_sconf γ Φ (mword_of_int (PC + 0x0c)) (mword_of_int 9 : mword 5) (mword_of_int 10 : mword 5)
              A1 (av - 4)%nat ltac:(nz) ltac:(nz) with "Hcg Hpc Hi0c [-]").
    iIntros "Hcg Hpc".
    set (A2 := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg
        (add_vec zero_reg (A1 !!! Regidx (mword_of_int 10 : mword 5)))]> A1).
    change (<[Regidx (mword_of_int 9 : mword 5) := regval_into_reg
        (add_vec zero_reg (A1 !!! Regidx (mword_of_int 10 : mword 5)))]> A1) with A2.
    assert (Hpc0e : add_vec_int (mword_of_int (PC + 0x0c) : mword 64) 2 = mword_of_int (PC + 0x0e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc0e) in "Hpc".
    (* ---- 0x0e: c.mv s2,a1 ---- *)
    iApply (wp_cmv_s_sconf γ Φ (mword_of_int (PC + 0x0e)) (mword_of_int 18 : mword 5) (mword_of_int 11 : mword 5)
              A2 (av - 4)%nat ltac:(nz) ltac:(nz) with "Hcg Hpc Hi0e [-]").
    iIntros "Hcg Hpc".
    set (A3 := <[Regidx (mword_of_int 18 : mword 5) := regval_into_reg
        (add_vec zero_reg (A2 !!! Regidx (mword_of_int 11 : mword 5)))]> A2).
    change (<[Regidx (mword_of_int 18 : mword 5) := regval_into_reg
        (add_vec zero_reg (A2 !!! Regidx (mword_of_int 11 : mword 5)))]> A2) with A3.
    assert (Hpc10 : add_vec_int (mword_of_int (PC + 0x0e) : mword 64) 2 = mword_of_int (PC + 0x10)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc10) in "Hpc".
    (* ---- 0x10: jal ra,acquire ---- *)
    iPoseProof (pci_10 with "Htext") as "Hi10".
    iApply (wp_jal_s_sconf γ Φ (mword_of_int (PC + 0x10)) (mword_of_int 1 : mword 5) (mword_of_int 2082744 : mword 21)
              A3 (av - 4)%nat ltac:(nz) ltac:(nz) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi10 [-]").
    iIntros "Hcg Hpc".
    set (A4 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (PC + 0x10) : mword 64) 4)]> A3).
    change (<[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (PC + 0x10) : mword 64) 4)]> A3) with A4.
    assert (Hpcaq : add_vec (mword_of_int (PC + 0x10) : mword 64) (sign_extend' 64 (mword_of_int 2082744 : mword 21))
                    = mword_of_int KernelSyms.acquire) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpcaq) in "Hpc".
    assert (Ha0A4 : A4 !!! Regidx (mword_of_int 10 : mword 5) = pi) by (rewrite /A4 /A3 /A2 /A1 /A0; do 5 (rewrite upd_ne; [| nz]); reflexivity).
    assert (HtpA4 : A4 !!! Regidx (mword_of_int 4 : mword 5) = cid_word) by (rewrite /A4 /A3 /A2 /A1 /A0; do 5 (rewrite upd_ne; [| nz]); exact Htp).
    assert (HcspA4 : A4 !!! Regidx csp_rs1 = spr).
    { rewrite /A4 /A3 /A2 /A1; do 4 (rewrite upd_ne; [| nz]); exact HcspA0. }
    assert (Hs1A4 : A4 !!! Regidx (mword_of_int 9 : mword 5) = pi).
    { rewrite /A4 /A3; do 2 (rewrite upd_ne; [| nz]).
      rewrite /A2 upd_eq. unfold regval_into_reg.
      rewrite /A1 /A0; do 2 (rewrite upd_ne; [| nz]). apply pcv_addv_zero_l. }
    assert (Hs2A4 : A4 !!! Regidx (mword_of_int 18 : mword 5) = m !!! Regidx (mword_of_int 11 : mword 5)).
    { rewrite /A4; do 1 (rewrite upd_ne; [| nz]).
      rewrite /A3 upd_eq. unfold regval_into_reg.
      rewrite /A2 /A1 /A0; do 3 (rewrite upd_ne; [| nz]). apply pcv_addv_zero_l. }
    assert (HraA4 : A4 !!! Regidx (mword_of_int 1 : mword 5) = add_vec_int (mword_of_int (PC + 0x10) : mword 64) 4)
      by (rewrite /A4; apply upd_eq).
    assert (HraA0 : A0 !!! Regidx (mword_of_int 1 : mword 5) = m !!! Regidx (mword_of_int 1 : mword 5))
      by (rewrite /A0 upd_ne; [reflexivity | nz]).
    assert (Hs0A0 : A0 !!! Regidx (mword_of_int 8 : mword 5) = m !!! Regidx (mword_of_int 8 : mword 5))
      by (rewrite /A0 upd_ne; [reflexivity | nz]).
    assert (Hs1A0 : A0 !!! Regidx (mword_of_int 9 : mword 5) = m !!! Regidx (mword_of_int 9 : mword 5))
      by (rewrite /A0 upd_ne; [reflexivity | nz]).
    assert (Hs2A0 : A0 !!! Regidx (mword_of_int 18 : mword 5) = m !!! Regidx (mword_of_int 18 : mword 5))
      by (rewrite /A0 upd_ne; [reflexivity | nz]).
    iEval (rewrite HcspA0 HraA0) in "Hr24".
    iEval (rewrite HcspA0 Hs0A0) in "Hr16".
    iEval (rewrite HcspA0 Hs1A0) in "Hr8".
    iEval (rewrite HcspA0 Hs2A0) in "Hr0".
    (* ================================================================= *)
    (* JOIN 2 -- the epilogue at +0x36.                                   *)
    (* ================================================================= *)
    iAssert (∀ (M : regfile),
               ⌜ callee_saved A4 M ⌝ -∗
               sie_cap_gpr γ M (av - 4)%nat -∗
               pc_is (mword_of_int (PC + 0x36) : mword 64) -∗
               cpu_own γ n eb pme C -∗
               (kalloc_avail γk on ∨ kalloc_avail γk (avail_inc on)) -∗
               WP (Loop : expr riscv_lang) {{ Φ }})%I
      with "[Hcont Hr24 Hr16 Hr8 Hr0]" as "EPI".
    { iIntros (M) "%Hcs Hcg Hpc Hown Hav".
      assert (HcspM : M !!! Regidx csp_rs1 = spr).
      { rewrite (callee_saved_lookup Hcs csp_rs1 ltac:(vm_compute; reflexivity)). exact HcspA4. }
      iPoseProof (pci_36 with "Htext") as "Hi36".
      iApply (wp_cldsp_s_sconf γ Φ (mword_of_int (PC + 0x36)) (mword_of_int 3 : mword 6) (mword_of_int 1 : mword 5)
                M (av - 4)%nat (m !!! Regidx (mword_of_int 1 : mword 5))
                ltac:(nz) ltac:(nz) with "Hcg Hpc Hi36 [Hr24] [-]").
      { iEval (rewrite HcspM). iExact "Hr24". }
      iIntros "Hcg Hpc Hr24".
      set (E1 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 1 : mword 5))]> M).
      change (<[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 1 : mword 5))]> M) with E1.
      assert (Hpc38 : add_vec_int (mword_of_int (PC + 0x36) : mword 64) 2 = mword_of_int (PC + 0x38)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpc38) in "Hpc".
      assert (HcspE1 : E1 !!! Regidx csp_rs1 = spr) by (rewrite /E1 upd_ne; [exact HcspM | nz]).
      iPoseProof (pci_38 with "Htext") as "Hi38".
      iApply (wp_cldsp_s_sconf γ Φ (mword_of_int (PC + 0x38)) (mword_of_int 2 : mword 6) (mword_of_int 8 : mword 5)
                E1 (av - 4)%nat (m !!! Regidx (mword_of_int 8 : mword 5))
                ltac:(nz) ltac:(nz) with "Hcg Hpc Hi38 [Hr16] [-]").
      { iEval (rewrite HcspE1). iExact "Hr16". }
      iIntros "Hcg Hpc Hr16".
      set (E2 := <[Regidx (mword_of_int 8 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 8 : mword 5))]> E1).
      change (<[Regidx (mword_of_int 8 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 8 : mword 5))]> E1) with E2.
      assert (Hpc3a : add_vec_int (mword_of_int (PC + 0x38) : mword 64) 2 = mword_of_int (PC + 0x3a)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpc3a) in "Hpc".
      assert (HcspE2 : E2 !!! Regidx csp_rs1 = spr) by (rewrite /E2 upd_ne; [exact HcspE1 | nz]).
      iPoseProof (pci_3a with "Htext") as "Hi3a".
      iApply (wp_cldsp_s_sconf γ Φ (mword_of_int (PC + 0x3a)) (mword_of_int 1 : mword 6) (mword_of_int 9 : mword 5)
                E2 (av - 4)%nat (m !!! Regidx (mword_of_int 9 : mword 5))
                ltac:(nz) ltac:(nz) with "Hcg Hpc Hi3a [Hr8] [-]").
      { iEval (rewrite HcspE2). iExact "Hr8". }
      iIntros "Hcg Hpc Hr8".
      set (E3 := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 9 : mword 5))]> E2).
      change (<[Regidx (mword_of_int 9 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 9 : mword 5))]> E2) with E3.
      assert (Hpc3c : add_vec_int (mword_of_int (PC + 0x3a) : mword 64) 2 = mword_of_int (PC + 0x3c)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpc3c) in "Hpc".
      assert (HcspE3 : E3 !!! Regidx csp_rs1 = spr) by (rewrite /E3 upd_ne; [exact HcspE2 | nz]).
      iPoseProof (pci_3c with "Htext") as "Hi3c".
      iApply (wp_cldsp_s_sconf γ Φ (mword_of_int (PC + 0x3c)) (mword_of_int 0 : mword 6) (mword_of_int 18 : mword 5)
                E3 (av - 4)%nat (m !!! Regidx (mword_of_int 18 : mword 5))
                ltac:(nz) ltac:(nz) with "Hcg Hpc Hi3c [Hr0] [-]").
      { iEval (rewrite HcspE3). iExact "Hr0". }
      iIntros "Hcg Hpc Hr0".
      set (E4 := <[Regidx (mword_of_int 18 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 18 : mword 5))]> E3).
      change (<[Regidx (mword_of_int 18 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 18 : mword 5))]> E3) with E4.
      assert (Hpc3e : add_vec_int (mword_of_int (PC + 0x3c) : mword 64) 2 = mword_of_int (PC + 0x3e)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpc3e) in "Hpc".
      assert (HcspE4 : E4 !!! Regidx csp_rs1 = spr) by (rewrite /E4 upd_ne; [exact HcspE3 | nz]).
      assert (Hsp0up : add_vec spr (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))) = sp0).
      { rewrite /spr /sp0 po_addv_assoc.
        assert (HAB : add_vec (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6)))
                              (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))) = mword_of_int 0)
          by (apply bv_eq; vm_compute; reflexivity).
        rewrite HAB. apply avi0. }
      assert (Hwv : add_vec (E4 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))) = sp0)
        by (rewrite HcspE4; exact Hsp0up).
      assert (Hpop : E4 !!! Regidx csp_rs1
                     = pa_stk (add_vec (E4 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6)))) 4).
      { rewrite Hwv HcspE4. symmetry. exact Hspr4. }
      iPoseProof (pci_3e with "Htext") as "Hi3e".
      iAssert (stack_own sp0 4) with "[Hr24 Hr16 Hr8 Hr0]" as "Hframe4".
      { rewrite stack_own_slots. cbn [seq].
        iSplitL "Hr24". { iExists _. iEval (rewrite Hb1 -HcspM). iExact "Hr24". }
        iSplitL "Hr16". { iExists _. iEval (rewrite Hb2 -HcspE1). iExact "Hr16". }
        iSplitL "Hr8".  { iExists _. iEval (rewrite Hb3 -HcspE2). iExact "Hr8". }
        iSplitL "Hr0".  { iExists _. iEval (rewrite Hb4 -HcspE3). iExact "Hr0". }
        done. }
      iEval (rewrite -Hwv) in "Hframe4".
      iApply (wp_caddi16sp_pop_s_sconf γ Φ (mword_of_int (PC + 0x3e)) (mword_of_int 2 : mword 6) E4 (av - 4)%nat 4 Hpop
                with "Hcg Hpc Hi3e Hframe4 [-]").
      iIntros "Hcg Hpc".
      assert (Hnk : ((av - 4) + 4)%nat = av) by lia.
      iEval (rewrite Hnk) in "Hcg".
      set (E5 := <[Regidx csp_rs1 := regval_into_reg
          (add_vec (E4 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))))]> E4).
      change (<[Regidx csp_rs1 := regval_into_reg
          (add_vec (E4 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))))]> E4) with E5.
      assert (Hpc40 : add_vec_int (mword_of_int (PC + 0x3e) : mword 64) 2 = mword_of_int (PC + 0x40)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpc40) in "Hpc".
      assert (HE5ra : E5 !!! Regidx (mword_of_int 1 : mword 5) = m !!! Regidx (mword_of_int 1 : mword 5)).
      { rewrite /E5 /E4 /E3 /E2; do 4 (rewrite upd_ne; [| nz]).
        rewrite /E1 upd_eq. unfold regval_into_reg. reflexivity. }
      iPoseProof (pci_40 with "Htext") as "Hi40".
      iApply (wp_cret_s_sconf γ Φ (mword_of_int (PC + 0x40)) (mword_of_int 1 : mword 5) E5 av
                ltac:(nz) with "Hcg Hpc Hi40 [-]").
      iIntros "Hcg Hpc".
      assert (Hra_final : ret_pc (E5 !!! Regidx (mword_of_int 1 : mword 5)) = ret_tgt)
        by (rewrite HE5ra; reflexivity).
      iEval (rewrite Hra_final) in "Hpc".
      iApply ("Hcont" $! E5 with "Hcg Hown Hpc [%] Hav").
      (* [repeat split] discharges s0/s1/s2 by conversion -- the epilogue
         reloaded them from the frame, so those equalities are definitional.
         What is left is sp (the frame trade), tp and s3..s11 (threaded
         through acquire, wakeup and release by their own callee_saved). *)
      unfold callee_saved. repeat split.
      + rewrite /E5 upd_eq. unfold regval_into_reg. rewrite HcspE4 Hsp0up. reflexivity.
      + do 5 (rewrite upd_ne; [| nz]).
        rewrite (callee_saved_lookup Hcs (mword_of_int 4) ltac:(vm_compute; reflexivity)).
        rewrite HtpA4. symmetry. exact Htp.
      + do 5 (rewrite upd_ne; [| nz]).
        rewrite (callee_saved_lookup Hcs (mword_of_int 19) ltac:(vm_compute; reflexivity)).
        rewrite /A4 /A3 /A2 /A1 /A0; do 5 (rewrite upd_ne; [| nz]); reflexivity.
      + do 5 (rewrite upd_ne; [| nz]).
        rewrite (callee_saved_lookup Hcs (mword_of_int 20) ltac:(vm_compute; reflexivity)).
        rewrite /A4 /A3 /A2 /A1 /A0; do 5 (rewrite upd_ne; [| nz]); reflexivity.
      + do 5 (rewrite upd_ne; [| nz]).
        rewrite (callee_saved_lookup Hcs (mword_of_int 21) ltac:(vm_compute; reflexivity)).
        rewrite /A4 /A3 /A2 /A1 /A0; do 5 (rewrite upd_ne; [| nz]); reflexivity.
      + do 5 (rewrite upd_ne; [| nz]).
        rewrite (callee_saved_lookup Hcs (mword_of_int 22) ltac:(vm_compute; reflexivity)).
        rewrite /A4 /A3 /A2 /A1 /A0; do 5 (rewrite upd_ne; [| nz]); reflexivity.
      + do 5 (rewrite upd_ne; [| nz]).
        rewrite (callee_saved_lookup Hcs (mword_of_int 23) ltac:(vm_compute; reflexivity)).
        rewrite /A4 /A3 /A2 /A1 /A0; do 5 (rewrite upd_ne; [| nz]); reflexivity.
      + do 5 (rewrite upd_ne; [| nz]).
        rewrite (callee_saved_lookup Hcs (mword_of_int 24) ltac:(vm_compute; reflexivity)).
        rewrite /A4 /A3 /A2 /A1 /A0; do 5 (rewrite upd_ne; [| nz]); reflexivity.
      + do 5 (rewrite upd_ne; [| nz]).
        rewrite (callee_saved_lookup Hcs (mword_of_int 25) ltac:(vm_compute; reflexivity)).
        rewrite /A4 /A3 /A2 /A1 /A0; do 5 (rewrite upd_ne; [| nz]); reflexivity.
      + do 5 (rewrite upd_ne; [| nz]).
        rewrite (callee_saved_lookup Hcs (mword_of_int 26) ltac:(vm_compute; reflexivity)).
        rewrite /A4 /A3 /A2 /A1 /A0; do 5 (rewrite upd_ne; [| nz]); reflexivity.
      + do 5 (rewrite upd_ne; [| nz]).
        rewrite (callee_saved_lookup Hcs (mword_of_int 27) ltac:(vm_compute; reflexivity)).
        rewrite /A4 /A3 /A2 /A1 /A0; do 5 (rewrite upd_ne; [| nz]); reflexivity. }
    (* ================================================================= *)
    (* acquire -- against the caller's REFERENCE                          *)
    (* ================================================================= *)
    iApply (Acquire.wp_acquire_gen_sconf γ Φ γl (pipe_res γp pi)
              (pipe_ref γp w 1) (pipe_dead γl γp) A4 n eb pme C (av - 4)%nat
              HtpA4 ltac:(lia) ltac:(lia)
              ltac:(iApply pipe_ref_dead) ltac:(iApply locked_pre_dead)
              with "Hcg Hown Htext Hpc [] Href Hpanic [-]").
    { iEval (rewrite Ha0A4). iExact "Hopen". }
    iIntros (ms M0) "%Hms Href Hcg Hpc %HcsM0 Hlocked Hres Hown Hpay".
    iEval (rewrite HraA4) in "Hpc".
    assert (Hpc14 : ret_pc (add_vec_int (mword_of_int (PC + 0x10) : mword 64) 4)
                    = (mword_of_int (PC + 0x14) : mword 64)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc14) in "Hpc".
    (* ================================================================= *)
    (* JOIN 1 -- the flag tests at +0x24, shared by both arms.            *)
    (* ================================================================= *)
    iAssert (∀ (M : regfile),
               ⌜ callee_saved A4 M ⌝ -∗
               sie_cap_gpr γ M (av - 4)%nat -∗
               pc_is (mword_of_int (PC + 0x24) : mword 64) -∗
               cpu_own γ (S n) eb pme C -∗
               trap_csrs_pay n eb -∗
               locked γl cpu_id -∗
               pipe_res γp pi -∗
               WP (Loop : expr riscv_lang) {{ Φ }})%I
      with "[EPI Havail]" as "JOIN".
    { iIntros (M) "%Hcs Hcg Hpc Hown Hpay Hlocked Hres".
      assert (Hs1M : M !!! Regidx (mword_of_int 9 : mword 5) = pi).
      { rewrite (callee_saved_lookup Hcs (mword_of_int 9) ltac:(vm_compute; reflexivity)). exact Hs1A4. }
      assert (HtpM : M !!! Regidx (mword_of_int 4 : mword 5) = cid_word).
      { rewrite (callee_saved_lookup Hcs (mword_of_int 4) ltac:(vm_compute; reflexivity)). exact HtpA4. }
      (* -- The two tails, offered as a CONJUNCTION: exactly one is taken, so
            they must SHARE the epilogue and the page count rather than split
            them.  Left: the plain release at +0x30, reached from both flag
            tests.  Right: the page count back, plus the epilogue for the
            freeing path (which spends it on kfree and gets a bigger one). -- *)
      iAssert ((∀ (M' : regfile),
                 ⌜ callee_saved A4 M' ⌝ -∗
                 sie_cap_gpr γ M' (av - 4)%nat -∗
                 pc_is (mword_of_int (PC + 0x30) : mword 64) -∗
                 cpu_own γ (S n) eb pme C -∗
                 trap_csrs_pay n eb -∗
                 locked γl cpu_id -∗
                 pipe_res γp pi -∗
                 WP (Loop : expr riscv_lang) {{ Φ }})
               ∧ (kalloc_avail γk on ∗
                  (∀ (M' : regfile),
                     ⌜ callee_saved A4 M' ⌝ -∗
                     sie_cap_gpr γ M' (av - 4)%nat -∗
                     pc_is (mword_of_int (PC + 0x36) : mword 64) -∗
                     cpu_own γ n eb pme C -∗
                     kalloc_avail γk (avail_inc on) -∗
                     WP (Loop : expr riscv_lang) {{ Φ }})))%I
        with "[EPI Havail]" as "TAILS".
      { iSplit.
        2:{ iFrame "Havail". iIntros (M') "%Hcs' Hcg Hpc Hown Hav".
            iApply ("EPI" $! M' with "[%] Hcg Hpc Hown [Hav]"); [exact Hcs' | by iRight]. }
        iIntros (M') "%Hcs' Hcg Hpc Hown Hpay Hlocked Hres".
        assert (Hs1M' : M' !!! Regidx (mword_of_int 9 : mword 5) = pi).
        { rewrite (callee_saved_lookup Hcs' (mword_of_int 9) ltac:(vm_compute; reflexivity)). exact Hs1A4. }
        assert (HtpM' : M' !!! Regidx (mword_of_int 4 : mword 5) = cid_word).
        { rewrite (callee_saved_lookup Hcs' (mword_of_int 4) ltac:(vm_compute; reflexivity)). exact HtpA4. }
        iPoseProof (pci_30 with "Htext") as "Hi30".
        iApply (wp_cmv_s_sconf γ Φ (mword_of_int (PC + 0x30)) (mword_of_int 10 : mword 5) (mword_of_int 9 : mword 5)
                  M' (av - 4)%nat ltac:(nz) ltac:(nz) with "Hcg Hpc Hi30 [-]").
        iIntros "Hcg Hpc".
        set (V1 := <[Regidx (mword_of_int 10 : mword 5) := regval_into_reg
            (add_vec zero_reg (M' !!! Regidx (mword_of_int 9 : mword 5)))]> M').
        change (<[Regidx (mword_of_int 10 : mword 5) := regval_into_reg
            (add_vec zero_reg (M' !!! Regidx (mword_of_int 9 : mword 5)))]> M') with V1.
        assert (Hpc32 : add_vec_int (mword_of_int (PC + 0x30) : mword 64) 2 = mword_of_int (PC + 0x32)) by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hpc32) in "Hpc".
        iPoseProof (pci_32 with "Htext") as "Hi32".
        iApply (wp_jal_s_sconf γ Φ (mword_of_int (PC + 0x32)) (mword_of_int 1 : mword 5) (mword_of_int 2082846 : mword 21)
                  V1 (av - 4)%nat ltac:(nz) ltac:(nz) ltac:(vm_compute; reflexivity)
                  with "Hcg Hpc Hi32 [-]").
        iIntros "Hcg Hpc".
        set (V2 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (PC + 0x32) : mword 64) 4)]> V1).
        change (<[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (PC + 0x32) : mword 64) 4)]> V1) with V2.
        assert (Hpcrl : add_vec (mword_of_int (PC + 0x32) : mword 64) (sign_extend' 64 (mword_of_int 2082846 : mword 21))
                        = mword_of_int KernelSyms.release) by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hpcrl) in "Hpc".
        assert (Ha0V2 : V2 !!! Regidx (mword_of_int 10 : mword 5) = pi).
        { rewrite /V2 upd_ne; [| nz]. rewrite /V1 upd_eq. unfold regval_into_reg.
          rewrite Hs1M'. apply pcv_addv_zero_l. }
        assert (HtpV2 : V2 !!! Regidx (mword_of_int 4 : mword 5) = cid_word).
        { rewrite /V2 /V1; do 2 (rewrite upd_ne; [| nz]). exact HtpM'. }
        assert (HlkaV2 : add_vec (V2 !!! Regidx (mword_of_int 10 : mword 5)) (sign_extend' 64 (mword_of_int 0 : mword 12)) = pi).
        { rewrite Ha0V2.
          replace (sign_extend' 64 (mword_of_int 0 : mword 12)) with (mword_of_int 0 : mword 64)
            by (apply bv_eq; vm_compute; reflexivity).
          apply kv_addv_zero. }
        iApply (Release.wp_release_gen_sconf γ Φ γl pi (pipe_res γp pi) (pipe_dead γl γp) emp%I
                  V2 n eb pme C (av - 4)%nat
                  HlkaV2 HtpV2 ltac:(lia)
                  ltac:(iApply locked_dead) ltac:(iApply locked_pre_dead)
                  with "Hcg Htext Hpc Hopen Hlocked Hres [] Hown Hpay [-]").
        { iApply lock_finisher_close. }
        iIntros (mr) "_ Hcg Hpc %Hcsr Hown".
        assert (HraV2 : V2 !!! Regidx (mword_of_int 1 : mword 5) = add_vec_int (mword_of_int (PC + 0x32) : mword 64) 4)
          by (rewrite /V2; apply upd_eq).
        iEval (rewrite HraV2) in "Hpc".
        assert (Hpc36 : ret_pc (add_vec_int (mword_of_int (PC + 0x32) : mword 64) 4)
                        = (mword_of_int (PC + 0x36) : mword 64)) by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hpc36) in "Hpc".
        iApply ("EPI" $! mr with "[%] Hcg Hpc Hown [Havail]"); [| by iLeft].
        apply (callee_saved_trans A4 V2 mr); [| exact Hcsr].
        rewrite /V2 /V1.
        apply callee_saved_insert_r; [vm_compute; reflexivity|].
        apply callee_saved_insert_r; [vm_compute; reflexivity|]. exact Hcs'. }
      iAssert (True)%I as "_"; [done|].
      (* -- 0x24: lw a5,544(s1) : a5 := pi->readopen -- *)
      iDestruct "Hres" as (nr nw ro wo vname bs) "(Hnm & Hnr & Hnw & Hro & Hwo & Hst0 & Hst1 & %Hbslen & Hdat & Hslack)".
      assert (Hroaddr : add_vec (M !!! Regidx (mword_of_int 9 : mword 5)) (sign_extend' 64 (mword_of_int 544 : mword 12)) = a_popen pi false)
        by (rewrite Hs1M; reflexivity).
      assert (Hwoaddr : add_vec (M !!! Regidx (mword_of_int 9 : mword 5)) (sign_extend' 64 (mword_of_int 548 : mword 12)) = a_popen pi true)
        by (rewrite Hs1M; reflexivity).
      iPoseProof (pci_24 with "Htext") as "Hi24".
      iApply (wp_lw_s_sconf γ Φ (mword_of_int (PC + 0x24)) (mword_of_int 15 : mword 5) (mword_of_int 9 : mword 5)
                (mword_of_int 544 : mword 12) M (av - 4)%nat ro ltac:(nz) ltac:(nz)
                with "Hcg Hpc Hi24 [Hro] [-]").
      { iEval (rewrite Hroaddr). iExact "Hro". }
      iIntros "Hcg Hpc Hro".
      iEval (rewrite Hroaddr) in "Hro".
      set (J1 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (sign_extend' 64 ro)]> M).
      change (<[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (sign_extend' 64 ro)]> M) with J1.
      assert (Hpc28 : add_vec_int (mword_of_int (PC + 0x24) : mword 64) 4 = mword_of_int (PC + 0x28)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpc28) in "Hpc".
      assert (HcsJ1 : callee_saved A4 J1)
        by (rewrite /J1; apply callee_saved_insert_r; [vm_compute; reflexivity | exact Hcs]).
      assert (Ha5J1 : J1 !!! Regidx (mword_of_int 15 : mword 5) = sign_extend' 64 ro)
        by (rewrite /J1; apply upd_eq).
      iPoseProof (pci_28 with "Htext") as "Hi28".
      destruct (neq_vec (sign_extend' 64 ro) (zero_reg : mword 64)) eqn:Hroop.
      { (* ===== the read end is still OPEN: c.bnez taken, plain release ===== *)
        iApply (wp_cbnez_taken_s_sconf γ Φ (mword_of_int (PC + 0x28)) (mword_of_int 4 : mword 8) (Cregidx (mword_of_int 7)) (mword_of_int 15 : mword 5)
                  J1 (av - 4)%nat ltac:(vm_compute; reflexivity) ltac:(nz)
                  ltac:(rewrite Ha5J1; exact Hroop) ltac:(vm_compute; reflexivity)
                  with "Hcg Hpc Hi28 [-]").
        iNext. iIntros "Hcg Hpc".
        assert (Hpc30 : add_vec (mword_of_int (PC + 0x28) : mword 64)
                          (sign_extend' 64 (sign_extend' 13 (concat_vec (mword_of_int 4 : mword 8) ('b"0"))))
                        = mword_of_int (PC + 0x30)) by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hpc30) in "Hpc".
        iDestruct "TAILS" as "[REL _]".
        iApply ("REL" $! J1 with "[%] Hcg Hpc Hown Hpay Hlocked [-]"); [exact HcsJ1|].
        iExists nr, nw, ro, wo, vname, bs. iFrame. done. }
      (* ===== the read end is SHUT: fall to 0x2a and test the write end ===== *)
      assert (Hroc : ~ pflag_open ro).
      { unfold pflag_open. rewrite Hroop. intro Hc. discriminate. }
      iApply (wp_cbnez_fall_s_sconf γ Φ (mword_of_int (PC + 0x28)) (mword_of_int 4 : mword 8) (Cregidx (mword_of_int 7)) (mword_of_int 15 : mword 5)
                J1 (av - 4)%nat ltac:(vm_compute; reflexivity) ltac:(nz)
                ltac:(rewrite Ha5J1; exact Hroop) with "Hcg Hpc Hi28 [-]").
      iIntros "Hcg Hpc".
      assert (Hpc2a : add_vec_int (mword_of_int (PC + 0x28) : mword 64) 2 = mword_of_int (PC + 0x2a)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpc2a) in "Hpc".
      assert (Hs1J1 : J1 !!! Regidx (mword_of_int 9 : mword 5) = pi)
        by (rewrite /J1 upd_ne; [exact Hs1M | nz]).
      assert (Hwoaddr1 : add_vec (J1 !!! Regidx (mword_of_int 9 : mword 5)) (sign_extend' 64 (mword_of_int 548 : mword 12)) = a_popen pi true)
        by (rewrite Hs1J1; reflexivity).
      iPoseProof (pci_2a with "Htext") as "Hi2a".
      iApply (wp_lw_s_sconf γ Φ (mword_of_int (PC + 0x2a)) (mword_of_int 15 : mword 5) (mword_of_int 9 : mword 5)
                (mword_of_int 548 : mword 12) J1 (av - 4)%nat wo ltac:(nz) ltac:(nz)
                with "Hcg Hpc Hi2a [Hwo] [-]").
      { iEval (rewrite Hwoaddr1). iExact "Hwo". }
      iIntros "Hcg Hpc Hwo".
      iEval (rewrite Hwoaddr1) in "Hwo".
      iEval (rewrite upd_upd) in "Hcg".
      set (J2 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (sign_extend' 64 wo)]> M).
      change (<[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (sign_extend' 64 wo)]> M) with J2.
      assert (Hpc2e : add_vec_int (mword_of_int (PC + 0x2a) : mword 64) 4 = mword_of_int (PC + 0x2e)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpc2e) in "Hpc".
      assert (HcsJ2 : callee_saved A4 J2)
        by (rewrite /J2; apply callee_saved_insert_r; [vm_compute; reflexivity | exact Hcs]).
      assert (Ha5J2 : J2 !!! Regidx (mword_of_int 15 : mword 5) = sign_extend' 64 wo)
        by (rewrite /J2; apply upd_eq).
      assert (Hs1J2 : J2 !!! Regidx (mword_of_int 9 : mword 5) = pi)
        by (rewrite /J2 upd_ne; [exact Hs1M | nz]).
      assert (HtpJ2 : J2 !!! Regidx (mword_of_int 4 : mword 5) = cid_word)
        by (rewrite /J2 upd_ne; [exact HtpM | nz]).
      iPoseProof (pci_2e with "Htext") as "Hi2e".
      destruct (eq_vec (sign_extend' 64 wo) (zero_reg : mword 64)) eqn:Hwoeq.
      2:{ (* the write end is still open: fall through to the plain release *)
        iApply (wp_cbeqz_fall_s_sconf γ Φ (mword_of_int (PC + 0x2e)) (mword_of_int 17 : mword 8) (Cregidx (mword_of_int 7)) (mword_of_int 15 : mword 5)
                  J2 (av - 4)%nat ltac:(vm_compute; reflexivity) ltac:(nz)
                  ltac:(rewrite Ha5J2; exact Hwoeq) with "Hcg Hpc Hi2e [-]").
        iIntros "Hcg Hpc".
        assert (Hpc30' : add_vec_int (mword_of_int (PC + 0x2e) : mword 64) 2 = mword_of_int (PC + 0x30)) by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hpc30') in "Hpc".
        iDestruct "TAILS" as "[REL _]".
        iApply ("REL" $! J2 with "[%] Hcg Hpc Hown Hpay Hlocked [-]"); [exact HcsJ2|].
        iExists nr, nw, ro, wo, vname, bs. iFrame. done. }
      (* ===== BOTH ends shut: free the page ===== *)
      assert (Hwoc : ~ pflag_open wo).
      { unfold pflag_open, neq_vec. rewrite Hwoeq. intro Hc. discriminate. }
      iDestruct "TAILS" as "[_ [Havail EPIF]]".
      iDestruct (pipe_endstate_closed γp false ro Hroc with "Hst0") as "[Hst0 #Hs0]".
      iDestruct (pipe_endstate_closed γp true wo Hwoc with "Hst1") as "[Hst1 #Hs1]".
      iApply (wp_cbeqz_taken_s_sconf γ Φ (mword_of_int (PC + 0x2e)) (mword_of_int 17 : mword 8) (Cregidx (mword_of_int 7)) (mword_of_int 15 : mword 5)
                J2 (av - 4)%nat ltac:(vm_compute; reflexivity) ltac:(nz)
                ltac:(rewrite Ha5J2; exact Hwoeq) ltac:(vm_compute; reflexivity)
                with "Hcg Hpc Hi2e [-]").
      iNext. iIntros "Hcg Hpc".
      assert (Hpc50 : add_vec (mword_of_int (PC + 0x2e) : mword 64)
                        (sign_extend' 64 (sign_extend' 13 (concat_vec (mword_of_int 17 : mword 8) ('b"0"))))
                      = mword_of_int (PC + 0x50)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpc50) in "Hpc".
      (* 0x50: c.mv a0,s1 *)
      iPoseProof (pci_50 with "Htext") as "Hi50".
      iApply (wp_cmv_s_sconf γ Φ (mword_of_int (PC + 0x50)) (mword_of_int 10 : mword 5) (mword_of_int 9 : mword 5)
                J2 (av - 4)%nat ltac:(nz) ltac:(nz) with "Hcg Hpc Hi50 [-]").
      iIntros "Hcg Hpc".
      set (K1 := <[Regidx (mword_of_int 10 : mword 5) := regval_into_reg
          (add_vec zero_reg (J2 !!! Regidx (mword_of_int 9 : mword 5)))]> J2).
      change (<[Regidx (mword_of_int 10 : mword 5) := regval_into_reg
          (add_vec zero_reg (J2 !!! Regidx (mword_of_int 9 : mword 5)))]> J2) with K1.
      assert (Hpc52 : add_vec_int (mword_of_int (PC + 0x50) : mword 64) 2 = mword_of_int (PC + 0x52)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpc52) in "Hpc".
      (* 0x52: jal release *)
      iPoseProof (pci_52 with "Htext") as "Hi52".
      iApply (wp_jal_s_sconf γ Φ (mword_of_int (PC + 0x52)) (mword_of_int 1 : mword 5) (mword_of_int 2082814 : mword 21)
                K1 (av - 4)%nat ltac:(nz) ltac:(nz) ltac:(vm_compute; reflexivity)
                with "Hcg Hpc Hi52 [-]").
      iIntros "Hcg Hpc".
      set (K2 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (PC + 0x52) : mword 64) 4)]> K1).
      change (<[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (PC + 0x52) : mword 64) 4)]> K1) with K2.
      assert (Hpcrl2 : add_vec (mword_of_int (PC + 0x52) : mword 64) (sign_extend' 64 (mword_of_int 2082814 : mword 21))
                       = mword_of_int KernelSyms.release) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpcrl2) in "Hpc".
      assert (Ha0K2 : K2 !!! Regidx (mword_of_int 10 : mword 5) = pi).
      { rewrite /K2 upd_ne; [| nz]. rewrite /K1 upd_eq. unfold regval_into_reg.
        rewrite Hs1J2. apply pcv_addv_zero_l. }
      assert (HtpK2 : K2 !!! Regidx (mword_of_int 4 : mword 5) = cid_word).
      { rewrite /K2 /K1; do 2 (rewrite upd_ne; [| nz]). exact HtpJ2. }
      assert (HlkaK2 : add_vec (K2 !!! Regidx (mword_of_int 10 : mword 5)) (sign_extend' 64 (mword_of_int 0 : mword 12)) = pi).
      { rewrite Ha0K2.
        replace (sign_extend' 64 (mword_of_int 0 : mword 12)) with (mword_of_int 0 : mword 64)
          by (apply bv_eq; vm_compute; reflexivity).
        apply kv_addv_zero. }
      iApply (ReleaseCancel.wp_release_cancel_sconf γ Φ γl pi (pipe_res γp pi)
                (pipe_dead γl γp) (pipe_bytes pi) K2 n eb pme C (av - 4)%nat
                HlkaK2 HtpK2 ltac:(lia)
                ltac:(iApply locked_dead) ltac:(iApply locked_pre_dead)
                with "Hcg Htext Hpc Hopen Hlocked [Hnm Hnr Hnw Hro Hwo Hst0 Hst1 Hdat Hslack] [] Hown Hpay [-]").
      { iExists nr, nw, ro, wo, vname, bs. iFrame. done. }
      { iIntros "Hfrag Hres". iModIntro.
        iApply (pipe_res_dead with "Hs0 Hs1 Hfrag Hres"). }
      iIntros (mr) "Hword Hcpu Hbytes Hcg Hpc %Hcsr Hown".
      assert (HraK2 : K2 !!! Regidx (mword_of_int 1 : mword 5) = add_vec_int (mword_of_int (PC + 0x52) : mword 64) 4)
        by (rewrite /K2; apply upd_eq).
      iEval (rewrite HraK2) in "Hpc".
      assert (Hpc56 : ret_pc (add_vec_int (mword_of_int (PC + 0x52) : mword 64) 4)
                      = (mword_of_int (PC + 0x56) : mword 64)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpc56) in "Hpc".
      assert (HcsA4K2 : callee_saved A4 K2).
      { rewrite /K2 /K1.
        apply callee_saved_insert_r; [vm_compute; reflexivity|].
        apply callee_saved_insert_r; [vm_compute; reflexivity|]. exact HcsJ2. }
      assert (HcsA4mr : callee_saved A4 mr) by (apply (callee_saved_trans A4 K2 mr HcsA4K2 Hcsr)).
      assert (Hs1mr : mr !!! Regidx (mword_of_int 9 : mword 5) = pi).
      { rewrite (callee_saved_lookup HcsA4mr (mword_of_int 9) ltac:(vm_compute; reflexivity)). exact Hs1A4. }
      assert (Htpmr : mr !!! Regidx (mword_of_int 4 : mword 5) = cid_word).
      { rewrite (callee_saved_lookup HcsA4mr (mword_of_int 4) ltac:(vm_compute; reflexivity)). exact HtpA4. }
      (* 0x56: c.mv a0,s1 *)
      iPoseProof (pci_56 with "Htext") as "Hi56".
      iApply (wp_cmv_s_sconf γ Φ (mword_of_int (PC + 0x56)) (mword_of_int 10 : mword 5) (mword_of_int 9 : mword 5)
                mr (av - 4)%nat ltac:(nz) ltac:(nz) with "Hcg Hpc Hi56 [-]").
      iIntros "Hcg Hpc".
      set (K3 := <[Regidx (mword_of_int 10 : mword 5) := regval_into_reg
          (add_vec zero_reg (mr !!! Regidx (mword_of_int 9 : mword 5)))]> mr).
      change (<[Regidx (mword_of_int 10 : mword 5) := regval_into_reg
          (add_vec zero_reg (mr !!! Regidx (mword_of_int 9 : mword 5)))]> mr) with K3.
      assert (Hpc58 : add_vec_int (mword_of_int (PC + 0x56) : mword 64) 2 = mword_of_int (PC + 0x58)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpc58) in "Hpc".
      (* 0x58: jal kfree *)
      iPoseProof (pci_58 with "Htext") as "Hi58".
      iApply (wp_jal_s_sconf γ Φ (mword_of_int (PC + 0x58)) (mword_of_int 1 : mword 5) (mword_of_int 2082222 : mword 21)
                K3 (av - 4)%nat ltac:(nz) ltac:(nz) ltac:(vm_compute; reflexivity)
                with "Hcg Hpc Hi58 [-]").
      iIntros "Hcg Hpc".
      set (K4 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (PC + 0x58) : mword 64) 4)]> K3).
      change (<[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (PC + 0x58) : mword 64) 4)]> K3) with K4.
      assert (Hpckf : add_vec (mword_of_int (PC + 0x58) : mword 64) (sign_extend' 64 (mword_of_int 2082222 : mword 21))
                      = mword_of_int KernelSyms.kfree) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpckf) in "Hpc".
      assert (Ha0K4 : K4 !!! Regidx (mword_of_int 10 : mword 5) = pi).
      { rewrite /K4 upd_ne; [| nz]. rewrite /K3 upd_eq. unfold regval_into_reg.
        rewrite Hs1mr. apply pcv_addv_zero_l. }
      assert (HtpK4 : K4 !!! Regidx (mword_of_int 4 : mword 5) = cid_word).
      { rewrite /K4 /K3; do 2 (rewrite upd_ne; [| nz]). exact Htpmr. }
      iApply (Kfree.wp_kfree_sconf γ Φ γkl γk klk kfl K4 on n eb pme C (av - 4)%nat
                ltac:(lia) HtpK4 Hklk Hkfl ltac:(lia)
                with "Hcg Hown Htext Hpc Hkmem [Hword Hcpu Hbytes] Havail Hpanic [-]").
      { rewrite /kfree_pre. iEval (rewrite Ha0K4). iSplitR; [done|].
        iApply (pipe_bytes_page_own with "Hword Hcpu Hbytes"). }
      iIntros (mk) "Hcg Hown Hpc %Hcsk Havail".
      assert (HraK4 : K4 !!! Regidx (mword_of_int 1 : mword 5) = add_vec_int (mword_of_int (PC + 0x58) : mword 64) 4)
        by (rewrite /K4; apply upd_eq).
      iEval (rewrite HraK4) in "Hpc".
      assert (Hpc5c : ret_pc (add_vec_int (mword_of_int (PC + 0x58) : mword 64) 4)
                      = (mword_of_int (PC + 0x5c) : mword 64)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpc5c) in "Hpc".
      (* 0x5c: c.j -> the epilogue *)
      iPoseProof (pci_5c with "Htext") as "Hi5c".
      iApply (wp_cj_s_sconf γ Φ (mword_of_int (PC + 0x5c))
                (sign_extend' 21 (concat_vec (mword_of_int 2029 : mword 11) ('b"0")))
                mk (av - 4)%nat ltac:(vm_compute; reflexivity) with "Hcg Hpc Hi5c [-]").
      iNext. iIntros "Hcg Hpc".
      assert (Hpcj36 : add_vec (mword_of_int (PC + 0x5c) : mword 64)
                         (sign_extend' 64 (sign_extend' 21 (concat_vec (mword_of_int 2029 : mword 11) ('b"0"))))
                       = mword_of_int (PC + 0x36)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpcj36) in "Hpc".
      iApply ("EPIF" $! mk with "[%] Hcg Hpc Hown Havail").
      apply (callee_saved_trans A4 K4 mk); [| exact Hcsk].
      rewrite /K4 /K3.
      apply callee_saved_insert_r; [vm_compute; reflexivity|].
      apply callee_saved_insert_r; [vm_compute; reflexivity|]. exact HcsA4mr. }
    (* ================================================================= *)
    (* 0x14: beq s2,zero -- the [writable] branch.                        *)
    (* ================================================================= *)
    assert (Hs1M0 : M0 !!! Regidx (mword_of_int 9 : mword 5) = pi).
    { rewrite (callee_saved_lookup HcsM0 (mword_of_int 9) ltac:(vm_compute; reflexivity)). exact Hs1A4. }
    assert (HtpM0 : M0 !!! Regidx (mword_of_int 4 : mword 5) = cid_word).
    { rewrite (callee_saved_lookup HcsM0 (mword_of_int 4) ltac:(vm_compute; reflexivity)). exact HtpA4. }
    assert (Hs2M0 : M0 !!! Regidx (mword_of_int 18 : mword 5) = m !!! Regidx (mword_of_int 11 : mword 5)).
    { rewrite (callee_saved_lookup HcsM0 (mword_of_int 18) ltac:(vm_compute; reflexivity)). exact Hs2A4. }
    iPoseProof (pci_14 with "Htext") as "Hi14".
    iDestruct "Hres" as (nr nw ro wo vname bs) "(Hnm & Hnr & Hnw & Hro & Hwo & Hst0 & Hst1 & %Hbslen & Hdat & Hslack)".
    destruct w.
    - (* ===== writable: the branch falls through, the WRITE end closes ===== *)
      assert (Hbz : eq_vec (M0 !!! Regidx (mword_of_int 18 : mword 5)) (zero_reg : mword 64) = false)
        by (rewrite Hs2M0; exact Hw).
      iApply (wp_beqz_x0_fall_s_sconf γ Φ (mword_of_int (PC + 0x14)) (mword_of_int 46 : mword 13)
                (mword_of_int 18 : mword 5) M0 (av - 4)%nat ltac:(nz) Hbz
                with "Hcg Hpc Hi14 [-]").
      iIntros "Hcg Hpc".
      assert (Hpc18 : add_vec_int (mword_of_int (PC + 0x14) : mword 64) 4 = mword_of_int (PC + 0x18)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpc18) in "Hpc".
      iMod (pipe_endstate_shut γp true wo with "Hst1 Href") as "[Hst1 _]".
      assert (Hwoaddr : add_vec (M0 !!! Regidx (mword_of_int 9 : mword 5)) (sign_extend' 64 (mword_of_int 548 : mword 12)) = a_popen pi true)
        by (rewrite Hs1M0; reflexivity).
      iPoseProof (pci_18 with "Htext") as "Hi18".
      iApply (wp_sw_zero_s_sconf γ Φ (mword_of_int (PC + 0x18)) (mword_of_int 9 : mword 5)
                (mword_of_int 548 : mword 12) M0 (av - 4)%nat wo with "Hcg Hpc Hi18 [Hwo] [-]").
      { iEval (rewrite Hwoaddr). iExact "Hwo". }
      iIntros "Hcg Hpc Hwo".
      iEval (rewrite Hwoaddr) in "Hwo".
      assert (Hpc1c : add_vec_int (mword_of_int (PC + 0x18) : mword 64) 4 = mword_of_int (PC + 0x1c)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpc1c) in "Hpc".
      iPoseProof (pci_1c with "Htext") as "Hi1c".
      iApply (wp_addi4_s_sconf γ Φ (mword_of_int (PC + 0x1c)) (mword_of_int 10 : mword 5) (mword_of_int 9 : mword 5)
                (mword_of_int 536 : mword 12) M0 (av - 4)%nat ltac:(nz) ltac:(nz)
                with "Hcg Hpc Hi1c [-]").
      iIntros "Hcg Hpc".
      set (W1 := <[Regidx (mword_of_int 10 : mword 5) := regval_into_reg
          (add_vec (M0 !!! Regidx (mword_of_int 9 : mword 5)) (sign_extend' 64 (mword_of_int 536 : mword 12)))]> M0).
      change (<[Regidx (mword_of_int 10 : mword 5) := regval_into_reg
          (add_vec (M0 !!! Regidx (mword_of_int 9 : mword 5)) (sign_extend' 64 (mword_of_int 536 : mword 12)))]> M0) with W1.
      assert (Hpc20 : add_vec_int (mword_of_int (PC + 0x1c) : mword 64) 4 = mword_of_int (PC + 0x20)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpc20) in "Hpc".
      iPoseProof (pci_20 with "Htext") as "Hi20".
      iApply (wp_jal_s_sconf γ Φ (mword_of_int (PC + 0x20)) (mword_of_int 1 : mword 5) (mword_of_int 2087666 : mword 21)
                W1 (av - 4)%nat ltac:(nz) ltac:(nz) ltac:(vm_compute; reflexivity)
                with "Hcg Hpc Hi20 [-]").
      iIntros "Hcg Hpc".
      set (W2 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (PC + 0x20) : mword 64) 4)]> W1).
      change (<[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (PC + 0x20) : mword 64) 4)]> W1) with W2.
      assert (Hpcwk : add_vec (mword_of_int (PC + 0x20) : mword 64) (sign_extend' 64 (mword_of_int 2087666 : mword 21))
                      = mword_of_int KernelSyms.wakeup) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpcwk) in "Hpc".
      assert (HtpW2 : W2 !!! Regidx (mword_of_int 4 : mword 5) = cid_word).
      { rewrite /W2 /W1; do 2 (rewrite upd_ne; [| nz]). exact HtpM0. }
      iApply (Wakeup.wp_wakeup_sconf γ Φ W2 γs (mycpu_ret cid_word) pme (S n) (av - 4)%nat eb C
                ltac:(lia) ltac:(intro r; apply rf_to_gmap_dom) Hlen HtpW2
                ltac:(rewrite HtpW2; reflexivity) ltac:(rewrite HtpW2; exact Hcpune) ltac:(lia)
                with "Hcg Hown Htext Hpc Hpanic Hpinv [-]").
      iIntros (Mw) "[%Hwcs %Hwdom] Hcg Hown Htext2 Hpc".
      assert (HraW2 : W2 !!! Regidx (mword_of_int 1 : mword 5) = add_vec_int (mword_of_int (PC + 0x20) : mword 64) 4)
        by (rewrite /W2; apply upd_eq).
      iEval (rewrite HraW2) in "Hpc".
      assert (Hpc24 : ret_pc (add_vec_int (mword_of_int (PC + 0x20) : mword 64) 4)
                      = (mword_of_int (PC + 0x24) : mword 64)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpc24) in "Hpc".
      iApply ("JOIN" $! Mw with "[%] Hcg Hpc Hown Hpay Hlocked [-]").
      { apply (callee_saved_trans A4 W2 Mw); [| exact Hwcs].
        rewrite /W2 /W1.
        apply callee_saved_insert_r; [vm_compute; reflexivity|].
        apply callee_saved_insert_r; [vm_compute; reflexivity|]. exact HcsM0. }
      iExists nr, nw, ro, (mword_of_int 0 : mword 32), vname, bs. iFrame. done.
    - (* ===== not writable: the branch is TAKEN, the READ end closes ===== *)
      assert (Hbz : eq_vec (M0 !!! Regidx (mword_of_int 18 : mword 5)) (zero_reg : mword 64) = true)
        by (rewrite Hs2M0; exact Hw).
      iApply (wp_beqz_x0_taken_s_sconf γ Φ (mword_of_int (PC + 0x14)) (mword_of_int 46 : mword 13)
                (mword_of_int 18 : mword 5) M0 (av - 4)%nat ltac:(nz) Hbz ltac:(vm_compute; reflexivity)
                with "Hcg Hpc Hi14 [-]").
      iNext. iIntros "Hcg Hpc".
      assert (Hpc42 : add_vec (mword_of_int (PC + 0x14) : mword 64) (sign_extend' 64 (mword_of_int 46 : mword 13))
                      = mword_of_int (PC + 0x42)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpc42) in "Hpc".
      iMod (pipe_endstate_shut γp false ro with "Hst0 Href") as "[Hst0 _]".
      assert (Hroaddr : add_vec (M0 !!! Regidx (mword_of_int 9 : mword 5)) (sign_extend' 64 (mword_of_int 544 : mword 12)) = a_popen pi false)
        by (rewrite Hs1M0; reflexivity).
      iPoseProof (pci_42 with "Htext") as "Hi42".
      iApply (wp_sw_zero_s_sconf γ Φ (mword_of_int (PC + 0x42)) (mword_of_int 9 : mword 5)
                (mword_of_int 544 : mword 12) M0 (av - 4)%nat ro with "Hcg Hpc Hi42 [Hro] [-]").
      { iEval (rewrite Hroaddr). iExact "Hro". }
      iIntros "Hcg Hpc Hro".
      iEval (rewrite Hroaddr) in "Hro".
      assert (Hpc46 : add_vec_int (mword_of_int (PC + 0x42) : mword 64) 4 = mword_of_int (PC + 0x46)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpc46) in "Hpc".
      iPoseProof (pci_46 with "Htext") as "Hi46".
      iApply (wp_addi4_s_sconf γ Φ (mword_of_int (PC + 0x46)) (mword_of_int 10 : mword 5) (mword_of_int 9 : mword 5)
                (mword_of_int 540 : mword 12) M0 (av - 4)%nat ltac:(nz) ltac:(nz)
                with "Hcg Hpc Hi46 [-]").
      iIntros "Hcg Hpc".
      set (W1 := <[Regidx (mword_of_int 10 : mword 5) := regval_into_reg
          (add_vec (M0 !!! Regidx (mword_of_int 9 : mword 5)) (sign_extend' 64 (mword_of_int 540 : mword 12)))]> M0).
      change (<[Regidx (mword_of_int 10 : mword 5) := regval_into_reg
          (add_vec (M0 !!! Regidx (mword_of_int 9 : mword 5)) (sign_extend' 64 (mword_of_int 540 : mword 12)))]> M0) with W1.
      assert (Hpc4a : add_vec_int (mword_of_int (PC + 0x46) : mword 64) 4 = mword_of_int (PC + 0x4a)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpc4a) in "Hpc".
      iPoseProof (pci_4a with "Htext") as "Hi4a".
      iApply (wp_jal_s_sconf γ Φ (mword_of_int (PC + 0x4a)) (mword_of_int 1 : mword 5) (mword_of_int 2087624 : mword 21)
                W1 (av - 4)%nat ltac:(nz) ltac:(nz) ltac:(vm_compute; reflexivity)
                with "Hcg Hpc Hi4a [-]").
      iIntros "Hcg Hpc".
      set (W2 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (PC + 0x4a) : mword 64) 4)]> W1).
      change (<[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (PC + 0x4a) : mword 64) 4)]> W1) with W2.
      assert (Hpcwk : add_vec (mword_of_int (PC + 0x4a) : mword 64) (sign_extend' 64 (mword_of_int 2087624 : mword 21))
                      = mword_of_int KernelSyms.wakeup) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpcwk) in "Hpc".
      assert (HtpW2 : W2 !!! Regidx (mword_of_int 4 : mword 5) = cid_word).
      { rewrite /W2 /W1; do 2 (rewrite upd_ne; [| nz]). exact HtpM0. }
      iApply (Wakeup.wp_wakeup_sconf γ Φ W2 γs (mycpu_ret cid_word) pme (S n) (av - 4)%nat eb C
                ltac:(lia) ltac:(intro r; apply rf_to_gmap_dom) Hlen HtpW2
                ltac:(rewrite HtpW2; reflexivity) ltac:(rewrite HtpW2; exact Hcpune) ltac:(lia)
                with "Hcg Hown Htext Hpc Hpanic Hpinv [-]").
      iIntros (Mw) "[%Hwcs %Hwdom] Hcg Hown Htext2 Hpc".
      assert (HraW2 : W2 !!! Regidx (mword_of_int 1 : mword 5) = add_vec_int (mword_of_int (PC + 0x4a) : mword 64) 4)
        by (rewrite /W2; apply upd_eq).
      iEval (rewrite HraW2) in "Hpc".
      assert (Hpc4e : ret_pc (add_vec_int (mword_of_int (PC + 0x4a) : mword 64) 4)
                      = (mword_of_int (PC + 0x4e) : mword 64)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpc4e) in "Hpc".
      (* 0x4e: c.j -> the flag tests *)
      iPoseProof (pci_4e with "Htext") as "Hi4e".
      iApply (wp_cj_s_sconf γ Φ (mword_of_int (PC + 0x4e))
                (sign_extend' 21 (concat_vec (mword_of_int 2027 : mword 11) ('b"0")))
                Mw (av - 4)%nat ltac:(vm_compute; reflexivity) with "Hcg Hpc Hi4e [-]").
      iNext. iIntros "Hcg Hpc".
      assert (Hpcj24 : add_vec (mword_of_int (PC + 0x4e) : mword 64)
                         (sign_extend' 64 (sign_extend' 21 (concat_vec (mword_of_int 2027 : mword 11) ('b"0"))))
                       = mword_of_int (PC + 0x24)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpcj24) in "Hpc".
      iApply ("JOIN" $! Mw with "[%] Hcg Hpc Hown Hpay Hlocked [-]").
      { apply (callee_saved_trans A4 W2 Mw); [| exact Hwcs].
        rewrite /W2 /W1.
        apply callee_saved_insert_r; [vm_compute; reflexivity|].
        apply callee_saved_insert_r; [vm_compute; reflexivity|]. exact HcsM0. }
      iExists nr, nw, (mword_of_int 0 : mword 32), wo, vname, bs. iFrame. done.
  Qed.
End ProofPipeclose.
End PipecloseProof.
