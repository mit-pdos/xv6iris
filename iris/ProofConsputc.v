(* ProofConsputc.v -- the whole-function WP for xv6's consputc() over the
   SIE-agnostic sconf world.

     void consputc(int c) {
       if (c == BACKSPACE) {
         uartputc_sync('\b'); uartputc_sync(' '); uartputc_sync('\b');
       } else {
         uartputc_sync(c);
       }
     }

   Seventeen instructions: the standard 16-byte / 2-slot frame, one BEQ, and
   either one or three calls to uartputc_sync.  The two arms REJOIN at the
   epilogue (the backspace arm's [c.j] lands on the ordinary arm's [ld ra]), so
   the epilogue is proved ONCE, as [wp_consputc_epi], against an arbitrary map
   [mc] constrained only by what the join actually guarantees:

     - [mc] has the pushed sp, and
     - [mc] agrees with the entry map on every callee-saved register other than
       sp and s0 (the two the epilogue itself restores).

   Both arms establish those two facts from the callee's [callee_saved] hop, and
   the epilogue turns them back into the caller-visible [callee_saved m mf].
   Splitting it out this way is what keeps the byte-list bookkeeping (one byte
   on one arm, three on the other) out of the frame reasoning entirely: the
   epilogue never mentions the UART. *)
From Stdlib Require Import ZArith Bool Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_var gen_heap invariants.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import RiscvLang RiscvPtsto.
Require Import RegFile InstrBytes WpMmodeLeafBase.
Require Import SmodeCore.
Require Import StackOwn CalleeSaved KernelText.
Require Import KernelRvcDecode.
Require Import WpSconfAlu WpSconfMem WpSconfCtl WpSconfBtype WpSmodeIntr.
Require Import DiskPtsto WpUart.
Require Import IntrDefs HartTp WpNext.
Require Import CodeConsputc.
Require Import SpecUartPutc SpecConsputc.
From Kernel Require KernelInstrs.
From Kernel Require KernelSyms.
Local Open Scope Z_scope.
Import Defs.

(* clean-context (mword-free) nat bounds, so [lia] never sees a bv. *)
Lemma cp_cap_bounds (K : nat) : (6 <= K)%nat -> (2 <= K)%nat /\ (4 <= K - 2)%nat.
Proof. lia. Qed.

Lemma cp_nk (K : nat) : (2 <= K)%nat -> ((K - 2) + 2)%nat = K.
Proof. lia. Qed.

Module ConsputcProof (UartPutc : UARTPUTC) : CONSPUTC.

Section ProofConsputc.
  Context `{!riscvGS Σ, !sieG Σ}.
  Context `{!uartGhostG Σ, !diskGhostG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.


  Ltac reg_neq :=
    lazymatch goal with
    | |- ?a <> ?b => tryif unify a b then fail else (vm_compute; discriminate)
    end.

  Local Notation ra_idx := (mword_of_int 1 : mword 5).
  Local Notation s0_idx := (mword_of_int 8 : mword 5).
  Local Notation a0_idx := (mword_of_int 10 : mword 5).
  Local Notation a5_idx := (mword_of_int 15 : mword 5).

  (* =================================================================== *)
  (*  THE SHARED EPILOGUE (0x14 .. 0x1a), entered from both arms.         *)
  (* =================================================================== *)

  (* [CID] is its OWN binder here (shadowing the section's fixed [Context
     CID]): this "post-resume half" gets applied at whichever hart the two
     arms above actually migrated to (CID1..CIDn from their own leaf/callee
     steps), not necessarily the section's original entry hart -- the same
     rule as ProofConsoleinit.v's [wp_initlock]/[wp_uartinit] Hypotheses and
     durable-notes' "post-resume half needs CID as a binder". *)
  Lemma wp_consputc_epi `{CID0 : CpuId} (Φ : mval -> iProp Σ)
      (m mc : regfile) (K : nat) (b : bool) (p : mword 64) :
    (2 <= K)%nat ->
    mc !!! Regidx csp_rs1
      = add_vec (m !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6))) ->
    (forall c : mword 5, is_cs_idx c = true -> c <> csp_rs1 -> c <> s0_idx ->
       mc !!! Regidx c = m !!! Regidx c) ->
    sie_cap_gpr mc (K - 2)%nat b p -∗
    kernel_text -∗
    pc_is (mword_of_int (KernelSyms.consputc + 0x14) : mword 64) -∗
    pa_stk (m !!! Regidx csp_rs1) 1 ↦₈ (m !!! Regidx ra_idx) -∗
    pa_stk (m !!! Regidx csp_rs1) 2 ↦₈ (m !!! Regidx s0_idx) -∗
    wp_next b p (fun (CID : CpuId) =>
      ∀ mf,
      sie_cap_gpr mf K b p -∗
      pc_is (ret_pc (m !!! Regidx ra_idx)) -∗
      ⌜ callee_saved m mf /\ mf !!! Regidx ra_idx = m !!! Regidx ra_idx ⌝ -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    intros HK Hsp Hagree.
    iIntros "Hcg #Htext Hpc Hc1 Hc2 Hcont".
    iPoseProof (cpi_14 with "Htext") as "Hi14".
    iPoseProof (cpi_16 with "Htext") as "Hi16".
    iPoseProof (cpi_18 with "Htext") as "Hi18".
    iPoseProof (cpi_1a with "Htext") as "Hi1a".
    assert (Hpush : add_vec (m !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6))) = pa_stk (m !!! Regidx csp_rs1) 2).
    { unfold pa_stk, add_vec_int. apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    assert (Hb1 : add_vec (add_vec (m !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6)))) (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000"))) = pa_stk (m !!! Regidx csp_rs1) 1).
    { unfold pa_stk, add_vec_int. rewrite !pa_stk_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb2 : add_vec (add_vec (m !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6)))) (zero_extend' 64 (concat_vec (mword_of_int 0 : mword 6) ('b"000"))) = pa_stk (m !!! Regidx csp_rs1) 2).
    { unfold pa_stk, add_vec_int. rewrite !pa_stk_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    (* +0x14 ld ra,8(sp) *)
    iApply (wp_cldsp_s_sconf Φ (mword_of_int (KernelSyms.consputc + 0x14)) (mword_of_int 1 : mword 6) ra_idx
              mc (K - 2)%nat (m !!! Regidx ra_idx) b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi14 [Hc1] [-]").
    { iEval (rewrite Hsp Hb1). iExact "Hc1". }
    iIntros (CID1 Hs1) "Hcg Hpc Hc1". iEval (rewrite Hsp Hb1) in "Hc1".
    set (E1 := <[Regidx ra_idx := regval_into_reg (m !!! Regidx ra_idx)]> mc).
    assert (HE1sp : E1 !!! Regidx csp_rs1 = add_vec (m !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6))))
      by (rewrite /E1 upd_ne; [exact Hsp | reg_neq]).
    assert (Hp16 : add_vec_int (mword_of_int (KernelSyms.consputc + 0x14) : mword 64) 2 = mword_of_int (KernelSyms.consputc + 0x16)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp16) in "Hpc".
    (* +0x16 ld s0,0(sp) *)
    iApply (wp_cldsp_s_sconf Φ (mword_of_int (KernelSyms.consputc + 0x16)) (mword_of_int 0 : mword 6) s0_idx
              E1 (K - 2)%nat (m !!! Regidx s0_idx) b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi16 [Hc2] [-]").
    { iEval (rewrite HE1sp Hb2). iExact "Hc2". }
    iIntros (CID2 Hs2) "Hcg Hpc Hc2". iEval (rewrite HE1sp Hb2) in "Hc2".
    set (E2 := <[Regidx s0_idx := regval_into_reg (m !!! Regidx s0_idx)]> E1).
    assert (HE2sp : E2 !!! Regidx csp_rs1 = add_vec (m !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6))))
      by (rewrite /E2 upd_ne; [exact HE1sp | reg_neq]).
    assert (Hp18 : add_vec_int (mword_of_int (KernelSyms.consputc + 0x16) : mword 64) 2 = mword_of_int (KernelSyms.consputc + 0x18)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp18) in "Hpc".
    (* +0x18 addi sp,sp,16 : the frame pop *)
    assert (Hwv : add_vec (E2 !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 16 : mword 6))) = m !!! Regidx csp_rs1).
    { rewrite HE2sp. apply frame_cancel_16. }
    assert (Hpop : E2 !!! Regidx csp_rs1 = pa_stk (add_vec (E2 !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 16 : mword 6)))) 2).
    { rewrite Hwv. rewrite HE2sp. exact Hpush. }
    iAssert (stack_own (m !!! Regidx csp_rs1) 2) with "[Hc1 Hc2]" as "Hframe".
    { rewrite stack_own_slots; cbn [seq].
      iSplitL "Hc1". { iExists (m !!! Regidx ra_idx). iExact "Hc1". }
      iSplitL "Hc2". { iExists (m !!! Regidx s0_idx). iExact "Hc2". }
      done. }
    iEval (rewrite -Hwv) in "Hframe".
    iApply (wp_caddi_sp_pop_s_sconf Φ (mword_of_int (KernelSyms.consputc + 0x18)) (mword_of_int 16 : mword 6)
              E2 (K - 2)%nat 2 b Hpop with "Hcg Hpc Hi18 Hframe [-]").
    iIntros (CID3 Hs3) "Hcg Hpc".
    set (E3 := <[Regidx csp_rs1 := regval_into_reg (add_vec (E2 !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 16 : mword 6))))]> E2).
    iEval (rewrite (cp_nk K HK)) in "Hcg".
    assert (Hp1a : add_vec_int (mword_of_int (KernelSyms.consputc + 0x18) : mword 64) 2 = mword_of_int (KernelSyms.consputc + 0x1a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp1a) in "Hpc".
    (* +0x1a ret *)
    assert (HE3ra : E3 !!! Regidx ra_idx = m !!! Regidx ra_idx).
    { rewrite /E3 upd_ne; [| reg_neq]. rewrite /E2 upd_ne; [| reg_neq]. rewrite /E1 upd_eq. reflexivity. }
    assert (Hrt : forall (CID' : CpuId), ret_pc (rget (CID := CID') E3 ra_idx) = ret_pc (m !!! Regidx ra_idx))
      by (intros CID'; rgne; rewrite HE3ra; reflexivity).
    iApply (wp_cret_s_sconf Φ (mword_of_int (KernelSyms.consputc + 0x1a)) ra_idx E3 K b
              ltac:(vm_compute; discriminate) with "Hcg Hpc Hi1a [-]").
    iIntros (CID4 Hs4) "Hcg Hpc". iEval (rewrite Hrt) in "Hpc".
    iSpecialize ("Hcont" $! CID4 with "[%]"); [wp_next_chain|].
    iApply ("Hcont" $! E3 with "Hcg Hpc [%]").
    split; [| exact HE3ra ].
    assert (Hthread : forall c : mword 5, is_cs_idx c = true ->
              c <> csp_rs1 -> c <> s0_idx -> E3 !!! Regidx c = m !!! Regidx c).
    { intros c Hc Nsp N8.
      pose proof (is_cs_idx_true_neq ra_idx c ltac:(vm_compute; reflexivity) Hc) as N1.
      rewrite /E3 upd_ne; [| congruence].
      rewrite /E2 upd_ne; [| congruence].
      rewrite /E1 upd_ne; [| congruence].
      exact (Hagree c Hc Nsp N8). }
    unfold callee_saved.
    split. { rewrite /E3 upd_eq. exact Hwv. }
    split. { rewrite /E3 upd_ne; [| reg_neq]. rewrite /E2 upd_eq; reflexivity. }
    repeat split; apply Hthread; vm_compute; first [reflexivity | discriminate].
  Qed.

  (* =================================================================== *)
  (*  THE WHOLE FUNCTION.                                                 *)
  (* =================================================================== *)

  (* [CID] is its OWN binder (not the section's fixed [Context CID]): by the
     time this proof reaches a [wp_uartputc] call it may have migrated hart
     (generic [b]), so the callee's contract must be instantiable at
     whichever hart that turns out to be -- same reasoning as
     ProofConsoleinit.v's [wp_initlock]/[wp_uartinit]. *)
  Hypothesis wp_uartputc :
    forall `{CID : CpuId} (γd : uart_names) (γv : disk_names) (Φ : mval -> iProp Σ) (m0 : regfile) (K : nat)
      (l : list (bv 8)) (pv pkv : mword 32) (dqm dqm2 : dfrac) (b : bool) (p : mword 64),
      wp_uartputc_sconf_body γd γv Φ m0 K l pv pkv dqm dqm2 b p.

  Lemma wp_consputc_sconf_gen (γd : uart_names) (γv : disk_names) (Φ : mval -> iProp Σ)
      (m : regfile) (K : nat) (l : list (bv 8)) (pv pkv : mword 32) (dqm dqm2 : dfrac) (b : bool) (p : mword 64)
    : wp_consputc_sconf_body γd γv Φ m K l pv pkv dqm dqm2 b p.
  Proof.
    cbv beta delta [wp_consputc_sconf_body].
    intros ra_i pcE ra0 ret_tgt HK Hpv Hpkv.
    pose proof (cp_cap_bounds K HK) as (Hc2 & HK4).
    iIntros "Hcg #Htext Hpc Hpanicking Hpanicked #Hdev Htx #Hdlab Hcont".
    iPoseProof (cpi_00 with "Htext") as "Hi00".
    iPoseProof (cpi_02 with "Htext") as "Hi02".
    iPoseProof (cpi_04 with "Htext") as "Hi04".
    iPoseProof (cpi_06 with "Htext") as "Hi06".
    iPoseProof (cpi_08 with "Htext") as "Hi08".
    iPoseProof (cpi_0c with "Htext") as "Hi0c".
    iPoseProof (cpi_10 with "Htext") as "Hi10".
    iPoseProof (cpi_1c with "Htext") as "Hi1c".
    iPoseProof (cpi_1e with "Htext") as "Hi1e".
    iPoseProof (cpi_22 with "Htext") as "Hi22".
    iPoseProof (cpi_26 with "Htext") as "Hi26".
    iPoseProof (cpi_2a with "Htext") as "Hi2a".
    iPoseProof (cpi_2c with "Htext") as "Hi2c".
    iPoseProof (cpi_30 with "Htext") as "Hi30".
    (* frame-cell address facts (2-slot frame: ra @ slot 1, s0 @ slot 2) *)
    assert (Hpush : add_vec (m !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6))) = pa_stk (m !!! Regidx csp_rs1) 2).
    { unfold pa_stk, add_vec_int. apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    assert (Hb1 : add_vec (add_vec (m !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6)))) (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000"))) = pa_stk (m !!! Regidx csp_rs1) 1).
    { unfold pa_stk, add_vec_int. rewrite !pa_stk_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb2 : add_vec (add_vec (m !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6)))) (zero_extend' 64 (concat_vec (mword_of_int 0 : mword 6) ('b"000"))) = pa_stk (m !!! Regidx csp_rs1) 2).
    { unfold pa_stk, add_vec_int. rewrite !pa_stk_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    (* ===== PROLOGUE (0x00..0x06) ===== *)
    iApply (wp_caddi_sp_push_s_sconf Φ (mword_of_int KernelSyms.consputc) (mword_of_int 48 : mword 6) m K 2 b Hc2 Hpush
              with "Hcg Hpc Hi00 [-]").
    iIntros (CID1 Hs1) "Hcg Hframe Hpc".
    set (W1 := <[Regidx csp_rs1 := regval_into_reg
        (add_vec (m !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6))))]> m).
    iEval (rewrite stack_own_slots; cbn [seq]) in "Hframe".
    iDestruct "Hframe" as "(S1 & S2 & _)".
    iDestruct "S1" as (v1) "Hc1". iDestruct "S2" as (v2) "Hc2".
    assert (HspW1 : W1 !!! Regidx csp_rs1 = add_vec (m !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6)))) by (rewrite /W1 upd_eq; reflexivity).
    assert (Hp02 : add_vec_int (mword_of_int KernelSyms.consputc : mword 64) 2 = mword_of_int (KernelSyms.consputc + 0x02)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp02) in "Hpc".
    (* +0x02 sd ra,8(sp) -> slot 1 *)
    iApply (wp_csdsp_s_sconf Φ (mword_of_int (KernelSyms.consputc + 0x02)) (mword_of_int 1 : mword 6) ra_idx
              W1 (K - 2)%nat v1 b with "Hcg Hpc Hi02 [Hc1] [-]").
    { iEval (rewrite HspW1 Hb1). iExact "Hc1". }
    iIntros (CID2 Hs2) "Hcg Hpc Hc1".
    assert (HW1r1 : forall (CID' : CpuId), rget (CID := CID') W1 ra_idx = m !!! Regidx ra_idx)
      by (intros CID'; rgne; rewrite /W1 upd_ne; [reflexivity | reg_neq]).
    iEval (rewrite HspW1 Hb1 HW1r1) in "Hc1".
    assert (Hp04 : add_vec_int (mword_of_int (KernelSyms.consputc + 0x02) : mword 64) 2 = mword_of_int (KernelSyms.consputc + 0x04)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp04) in "Hpc".
    (* +0x04 sd s0,0(sp) -> slot 2 *)
    iApply (wp_csdsp_s_sconf Φ (mword_of_int (KernelSyms.consputc + 0x04)) (mword_of_int 0 : mword 6) s0_idx
              W1 (K - 2)%nat v2 b with "Hcg Hpc Hi04 [Hc2] [-]").
    { iEval (rewrite HspW1 Hb2). iExact "Hc2". }
    iIntros (CID3 Hs3) "Hcg Hpc Hc2".
    assert (HW1r8 : forall (CID' : CpuId), rget (CID := CID') W1 s0_idx = m !!! Regidx s0_idx)
      by (intros CID'; rgne; rewrite /W1 upd_ne; [reflexivity | reg_neq]).
    iEval (rewrite HspW1 Hb2 HW1r8) in "Hc2".
    assert (Hp06 : add_vec_int (mword_of_int (KernelSyms.consputc + 0x04) : mword 64) 2 = mword_of_int (KernelSyms.consputc + 0x06)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp06) in "Hpc".
    (* +0x06 addi s0,sp,16 (value unused; s0 reloaded at the epilogue) *)
    iApply (wp_caddi4spn_s_sconf Φ (mword_of_int (KernelSyms.consputc + 0x06)) (Cregidx (mword_of_int 0)) (mword_of_int 4 : mword 8) s0_idx
              W1 (K - 2)%nat b ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi06 [-]").
    iIntros (CID4 Hs4) "Hcg Hpc".
    set (W2 := <[Regidx s0_idx := regval_into_reg (add_vec (W1 !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm (mword_of_int 4 : mword 8))))]> W1).
    assert (Hp08 : add_vec_int (mword_of_int (KernelSyms.consputc + 0x06) : mword 64) 2 = mword_of_int (KernelSyms.consputc + 0x08)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp08) in "Hpc".
    (* ===== if (c == BACKSPACE) (0x08..0x0c) ===== *)
    (* +0x08 li a5,256 *)
    iApply (wp_li4_s_sconf Φ (mword_of_int (KernelSyms.consputc + 0x08)) a5_idx (mword_of_int 256 : mword 12)
              (mword_of_int 256 : mword 64) W2 (K - 2)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc Hi08 [-]").
    iIntros (CID5 Hs5) "Hcg Hpc".
    set (W3 := <[Regidx a5_idx := regval_into_reg (mword_of_int 256 : mword 64)]> W2).
    assert (Hp0c : add_vec_int (mword_of_int (KernelSyms.consputc + 0x08) : mword 64) 4 = mword_of_int (KernelSyms.consputc + 0x0c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp0c) in "Hpc".
    (* the register facts the whole rest of the proof runs on *)
    assert (HW3sp : W3 !!! Regidx csp_rs1 = add_vec (m !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6)))).
    { rewrite /W3 upd_ne; [| reg_neq]. rewrite /W2 upd_ne; [| reg_neq]. exact HspW1. }
    (* [W3] agrees with the entry map on every callee-saved register except
       sp and s0 -- the invariant the arms carry to the epilogue. *)
    assert (HW3cs : forall c : mword 5, is_cs_idx c = true -> c <> csp_rs1 -> c <> s0_idx ->
              W3 !!! Regidx c = m !!! Regidx c).
    { intros c Hc Nsp N8.
      pose proof (is_cs_idx_true_neq a5_idx c ltac:(vm_compute; reflexivity) Hc) as Na5.
      rewrite /W3 upd_ne; [| congruence].
      rewrite /W2 upd_ne; [| congruence].
      rewrite /W1 upd_ne; [reflexivity | congruence]. }
    (* +0x0c beq a0,a5 -- the BACKSPACE test, both arms taken below.  The
       leaf's own comparison premise is [rget]-spelled ([a0_idx]/[a5_idx] are
       ITS variable [rs1]/[rs2] params), so destruct at that shape directly
       rather than bridging a raw fact afterward. *)
    destruct (eq_vec (rget W3 a0_idx) (rget W3 a5_idx)) eqn:Hbs.
    - (* ============ BACKSPACE arm: '\b', ' ', '\b' ============ *)
      iApply (wp_beq_taken_s_sconf Φ (mword_of_int (KernelSyms.consputc + 0x0c)) (mword_of_int 16 : mword 13) a5_idx a0_idx
                W3 (K - 2)%nat b ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) Hbs
                ltac:(vm_compute; reflexivity)
                with "Hcg Hpc Hi0c [-]").
      iNext. iIntros (CIDta Hsta) "Hcg Hpc".
      assert (Htgt1c : add_vec (mword_of_int (KernelSyms.consputc + 0x0c) : mword 64) (sign_extend' 64 (mword_of_int 16 : mword 13)) = mword_of_int (KernelSyms.consputc + 0x1c)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Htgt1c) in "Hpc".
      (* +0x1c c.li a0,8 *)
      iApply (wp_cli_s_sconf Φ (mword_of_int (KernelSyms.consputc + 0x1c)) a0_idx (mword_of_int 8 : mword 6)
                (mword_of_int 8 : mword 64) W3 (K - 2)%nat b
                ltac:(vm_compute; discriminate) ltac:(rdok)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                with "Hcg Hpc Hi1c [-]").
      iIntros (CID6 Hs6) "Hcg Hpc".
      set (T1 := <[Regidx a0_idx := regval_into_reg (mword_of_int 8 : mword 64)]> W3).
      assert (Hp1e : add_vec_int (mword_of_int (KernelSyms.consputc + 0x1c) : mword 64) 2 = mword_of_int (KernelSyms.consputc + 0x1e)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hp1e) in "Hpc".
      (* +0x1e jal uartputc_sync *)
      iApply (wp_jal_s_sconf Φ (mword_of_int (KernelSyms.consputc + 0x1e)) ra_idx (mword_of_int 1750 : mword 21)
                T1 (K - 2)%nat b ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(vm_compute; reflexivity)
                with "Hcg Hpc Hi1e [-]").
      iIntros (CID7 Hs7) "Hcg Hpc".
      set (T2 := <[Regidx ra_idx := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.consputc + 0x1e) : mword 64) 4)]> T1).
      assert (Htgtu1 : add_vec (mword_of_int (KernelSyms.consputc + 0x1e) : mword 64) (sign_extend' 64 (mword_of_int 1750 : mword 21)) = mword_of_int KernelSyms.uartputc_sync) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Htgtu1) in "Hpc".
      iApply (wp_uartputc γd γv Φ T2 (K - 2)%nat l pv pkv dqm dqm2 b p HK4 Hpv Hpkv
                with "Hcg Htext Hpc Hpanicking Hpanicked Hdev Htx Hdlab [-]").
      iIntros (CID8 Hs8 mf1) "Hcg Hpc %Hcs1 Hpanicking Hpanicked Htx #Hsent1".
      destruct Hcs1 as [Hcs1 Hra1].
      assert (Hret1 : ret_pc (T2 !!! Regidx ra_idx) = mword_of_int (KernelSyms.consputc + 0x22)).
      { rewrite /T2 upd_eq. unfold ret_pc. apply bv_eq; vm_compute; reflexivity. }
      iEval (rewrite Hret1) in "Hpc".
      (* +0x22 li a0,32 *)
      iApply (wp_li4_s_sconf Φ (mword_of_int (KernelSyms.consputc + 0x22)) a0_idx (mword_of_int 32 : mword 12)
                (mword_of_int 32 : mword 64) mf1 (K - 2)%nat b
                ltac:(vm_compute; discriminate) ltac:(rdok)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                with "Hcg Hpc Hi22 [-]").
      iIntros (CID9 Hs9) "Hcg Hpc".
      set (T3 := <[Regidx a0_idx := regval_into_reg (mword_of_int 32 : mword 64)]> mf1).
      assert (Hp26 : add_vec_int (mword_of_int (KernelSyms.consputc + 0x22) : mword 64) 4 = mword_of_int (KernelSyms.consputc + 0x26)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hp26) in "Hpc".
      (* +0x26 jal uartputc_sync *)
      iApply (wp_jal_s_sconf Φ (mword_of_int (KernelSyms.consputc + 0x26)) ra_idx (mword_of_int 1742 : mword 21)
                T3 (K - 2)%nat b ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(vm_compute; reflexivity)
                with "Hcg Hpc Hi26 [-]").
      iIntros (CID10 Hs10) "Hcg Hpc".
      set (T4 := <[Regidx ra_idx := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.consputc + 0x26) : mword 64) 4)]> T3).
      assert (Htgtu2 : add_vec (mword_of_int (KernelSyms.consputc + 0x26) : mword 64) (sign_extend' 64 (mword_of_int 1742 : mword 21)) = mword_of_int KernelSyms.uartputc_sync) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Htgtu2) in "Hpc".
      iApply (wp_uartputc γd γv Φ T4 (K - 2)%nat _ pv pkv dqm dqm2 b p HK4 Hpv Hpkv
                with "Hcg Htext Hpc Hpanicking Hpanicked Hdev Htx Hdlab [-]").
      iIntros (CID11 Hs11 mf2) "Hcg Hpc %Hcs2 Hpanicking Hpanicked Htx #Hsent2".
      destruct Hcs2 as [Hcs2 Hra2].
      assert (Hret2 : ret_pc (T4 !!! Regidx ra_idx) = mword_of_int (KernelSyms.consputc + 0x2a)).
      { rewrite /T4 upd_eq. unfold ret_pc. apply bv_eq; vm_compute; reflexivity. }
      iEval (rewrite Hret2) in "Hpc".
      (* +0x2a c.li a0,8 *)
      iApply (wp_cli_s_sconf Φ (mword_of_int (KernelSyms.consputc + 0x2a)) a0_idx (mword_of_int 8 : mword 6)
                (mword_of_int 8 : mword 64) mf2 (K - 2)%nat b
                ltac:(vm_compute; discriminate) ltac:(rdok)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                with "Hcg Hpc Hi2a [-]").
      iIntros (CID12 Hs12) "Hcg Hpc".
      set (T5 := <[Regidx a0_idx := regval_into_reg (mword_of_int 8 : mword 64)]> mf2).
      assert (Hp2c : add_vec_int (mword_of_int (KernelSyms.consputc + 0x2a) : mword 64) 2 = mword_of_int (KernelSyms.consputc + 0x2c)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hp2c) in "Hpc".
      (* +0x2c jal uartputc_sync *)
      iApply (wp_jal_s_sconf Φ (mword_of_int (KernelSyms.consputc + 0x2c)) ra_idx (mword_of_int 1736 : mword 21)
                T5 (K - 2)%nat b ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(vm_compute; reflexivity)
                with "Hcg Hpc Hi2c [-]").
      iIntros (CID13 Hs13) "Hcg Hpc".
      set (T6 := <[Regidx ra_idx := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.consputc + 0x2c) : mword 64) 4)]> T5).
      assert (Htgtu3 : add_vec (mword_of_int (KernelSyms.consputc + 0x2c) : mword 64) (sign_extend' 64 (mword_of_int 1736 : mword 21)) = mword_of_int KernelSyms.uartputc_sync) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Htgtu3) in "Hpc".
      iApply (wp_uartputc γd γv Φ T6 (K - 2)%nat _ pv pkv dqm dqm2 b p HK4 Hpv Hpkv
                with "Hcg Htext Hpc Hpanicking Hpanicked Hdev Htx Hdlab [-]").
      iIntros (CID14 Hs14 mf3) "Hcg Hpc %Hcs3 Hpanicking Hpanicked Htx #Hsent3".
      destruct Hcs3 as [Hcs3 Hra3].
      assert (Hret3 : ret_pc (T6 !!! Regidx ra_idx) = mword_of_int (KernelSyms.consputc + 0x30)).
      { rewrite /T6 upd_eq. unfold ret_pc. apply bv_eq; vm_compute; reflexivity. }
      iEval (rewrite Hret3) in "Hpc".
      (* +0x30 j -> the shared epilogue *)
      iApply (wp_cj_s_sconf Φ (mword_of_int (KernelSyms.consputc + 0x30)) (sign_extend' 21 (concat_vec (mword_of_int 2034 : mword 11) ('b"0")))
                mf3 (K - 2)%nat b ltac:(vm_compute; reflexivity)
                with "Hcg Hpc Hi30 [-]").
      iIntros (CID15 Hs15). iNext. iIntros "Hcg Hpc".
      assert (Htgtj : add_vec (mword_of_int (KernelSyms.consputc + 0x30) : mword 64) (sign_extend' 64 (sign_extend' 21 (concat_vec (mword_of_int 2034 : mword 11) ('b"0")))) = mword_of_int (KernelSyms.consputc + 0x14)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Htgtj) in "Hpc".
      (* the three calls' callee-saved hops, composed back to the map at the
         BEQ: the three (c.li a0 / jal ra) pairs touch only caller-saved
         registers, so every callee-saved index survives the whole arm. *)
      assert (Hthread0 : forall c : mword 5, is_cs_idx c = true ->
                mf3 !!! Regidx c = W3 !!! Regidx c).
      { intros c Hc.
        pose proof (is_cs_idx_true_neq ra_idx c ltac:(vm_compute; reflexivity) Hc) as N1.
        pose proof (is_cs_idx_true_neq a0_idx c ltac:(vm_compute; reflexivity) Hc) as Na0.
        rewrite (callee_saved_lookup Hcs3 c Hc).
        rewrite /T6 upd_ne; [| congruence].
        rewrite /T5 upd_ne; [| congruence].
        rewrite (callee_saved_lookup Hcs2 c Hc).
        rewrite /T4 upd_ne; [| congruence].
        rewrite /T3 upd_ne; [| congruence].
        rewrite (callee_saved_lookup Hcs1 c Hc).
        rewrite /T2 upd_ne; [| congruence].
        rewrite /T1 upd_ne; [reflexivity | congruence]. }
      assert (Hthread : forall c : mword 5, is_cs_idx c = true -> c <> csp_rs1 -> c <> s0_idx ->
                mf3 !!! Regidx c = m !!! Regidx c).
      { intros c Hc Nsp N8. rewrite (Hthread0 c Hc). exact (HW3cs c Hc Nsp N8). }
      assert (Hmf3sp : mf3 !!! Regidx csp_rs1 = add_vec (m !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6)))).
      { rewrite (Hthread0 csp_rs1 ltac:(vm_compute; reflexivity)). exact HW3sp. }
      (* the three bytes accumulated as [((l ++ b1) ++ b2) ++ b3]; the spec's
         post is [l ++ bs], so reassociate once and read [bs] off. *)
      iEval (rewrite -!app_assoc) in "Htx".
      iEval (rewrite -!app_assoc) in "Hsent3".
      iApply (wp_consputc_epi Φ m mf3 K b p Hc2 Hmf3sp Hthread
                with "Hcg Htext Hpc Hc1 Hc2 [-]").
      iIntros (CID16 Hs16 mfin) "Hcg Hpc %Hfin".
      iSpecialize ("Hcont" $! CID16 with "[%]"); [wp_next_chain|].
      iApply ("Hcont" $! mfin with "Hcg Hpc [%] Hpanicking Hpanicked [Htx] [Hsent3]").
      { exact Hfin. }
      { iExact "Htx". }
      { iExact "Hsent3". }
    - (* ============ ordinary arm: uartputc_sync(c) ============ *)
      iApply (wp_beq_fall_s_sconf Φ (mword_of_int (KernelSyms.consputc + 0x0c)) (mword_of_int 16 : mword 13) a5_idx a0_idx
                W3 (K - 2)%nat b ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) Hbs
                with "Hcg Hpc Hi0c [-]").
      iIntros (CID6' Hs6') "Hcg Hpc".
      assert (Hp10 : add_vec_int (mword_of_int (KernelSyms.consputc + 0x0c) : mword 64) 4 = mword_of_int (KernelSyms.consputc + 0x10)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hp10) in "Hpc".
      (* +0x10 jal uartputc_sync *)
      iApply (wp_jal_s_sconf Φ (mword_of_int (KernelSyms.consputc + 0x10)) ra_idx (mword_of_int 1764 : mword 21)
                W3 (K - 2)%nat b ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(vm_compute; reflexivity)
                with "Hcg Hpc Hi10 [-]").
      iIntros (CID7' Hs7') "Hcg Hpc".
      set (F1 := <[Regidx ra_idx := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.consputc + 0x10) : mword 64) 4)]> W3).
      assert (Htgtu : add_vec (mword_of_int (KernelSyms.consputc + 0x10) : mword 64) (sign_extend' 64 (mword_of_int 1764 : mword 21)) = mword_of_int KernelSyms.uartputc_sync) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Htgtu) in "Hpc".
      iApply (wp_uartputc γd γv Φ F1 (K - 2)%nat l pv pkv dqm dqm2 b p HK4 Hpv Hpkv
                with "Hcg Htext Hpc Hpanicking Hpanicked Hdev Htx Hdlab [-]").
      iIntros (CID8' Hs8' mf) "Hcg Hpc %Hcsf Hpanicking Hpanicked Htx #Hsent".
      destruct Hcsf as [Hcsf Hraf].
      assert (Hretf : ret_pc (F1 !!! Regidx ra_idx) = mword_of_int (KernelSyms.consputc + 0x14)).
      { rewrite /F1 upd_eq. unfold ret_pc. apply bv_eq; vm_compute; reflexivity. }
      iEval (rewrite Hretf) in "Hpc".
      assert (Hthread0 : forall c : mword 5, is_cs_idx c = true ->
                mf !!! Regidx c = W3 !!! Regidx c).
      { intros c Hc.
        pose proof (is_cs_idx_true_neq ra_idx c ltac:(vm_compute; reflexivity) Hc) as N1.
        rewrite (callee_saved_lookup Hcsf c Hc).
        rewrite /F1 upd_ne; [reflexivity | congruence]. }
      assert (Hthread : forall c : mword 5, is_cs_idx c = true -> c <> csp_rs1 -> c <> s0_idx ->
                mf !!! Regidx c = m !!! Regidx c).
      { intros c Hc Nsp N8. rewrite (Hthread0 c Hc). exact (HW3cs c Hc Nsp N8). }
      assert (Hmfsp : mf !!! Regidx csp_rs1 = add_vec (m !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6)))).
      { rewrite (Hthread0 csp_rs1 ltac:(vm_compute; reflexivity)). exact HW3sp. }
      iApply (wp_consputc_epi Φ m mf K b p Hc2 Hmfsp Hthread
                with "Hcg Htext Hpc Hc1 Hc2 [-]").
      iIntros (CID9' Hs9' mfin) "Hcg Hpc %Hfin".
      iSpecialize ("Hcont" $! CID9' with "[%]"); [wp_next_chain|].
      iApply ("Hcont" $! mfin with "Hcg Hpc [%] Hpanicking Hpanicked [Htx] [Hsent]").
      { exact Hfin. }
      { iExact "Htx". }
      { iExact "Hsent". }
  Qed.

End ProofConsputc.

(* ===================================================================== *)
(* THE SEALED FUNCTOR: instantiate the callee's WP hypothesis with its     *)
(* proven spec, discharging the CONSPUTC Module Type.                      *)
(* ===================================================================== *)
  Definition wp_consputc_sconf `{!riscvGS Σ, !sieG Σ} `{!uartGhostG Σ, !diskGhostG Σ} `{GEN : GenId} `{CID : CpuId}
      (γd : uart_names) (γv : disk_names) (Φ : mval -> iProp Σ) (m0 : regfile) (K : nat)
      (l : list (bv 8)) (pv pkv : mword 32) {dqm dqm2 : dfrac} (b : bool) (p : mword 64)
      : wp_consputc_sconf_body γd γv Φ m0 K l pv pkv dqm dqm2 b p :=
    (* eta-expand to keep [UartPutc.wp_uartputc_sconf]'s own [CID] genuinely
       polymorphic per application (see ProofConsoleinit.v's identical fix
       for [wp_initlock]/[wp_uartinit]) rather than letting it be eagerly
       specialized to THIS definition's [CID]. *)
    wp_consputc_sconf_gen
      (fun `(CID' : CpuId) γd' γv' Φ' m' K' l' pv' pkv' dqm' dqm2' b' p' =>
         UartPutc.wp_uartputc_sconf (CID:=CID') γd' γv' Φ' m' K' l' pv' pkv' (dqm:=dqm') (dqm2:=dqm2') b' p')
      γd γv Φ m0 K l pv pkv dqm dqm2 b p.

End ConsputcProof.
