(* ProofPrintk.v -- the whole-function WP for xv6's printk(), in progress.

     int printk(char *fmt, ...);

   264 instructions, a 24-slot frame, fifteen dispatch arms, two inlined loops
   (printptr's hex walk for %p and the string walk for %s) and two rejoining
   restore blocks.  Built bottom-up; this file currently holds the frame
   abstraction and the epilogue, which every path ends in.

   THE FRAME ([pk_frame]).  printk's 24 slots are, from the entry sp:

     1..7   the varargs -- a1..a7 spilled at 56(s0)..8(s0), s0 = sp0-64
     8      unused (0(s0))
     9      ra          10  s0          11  s1 (lazy)   12  s2
     13..18 s3..s8 (lazy)               19  s9 (saved INSIDE the %p arm only)
     20  s10 (lazy)     21  s11 (lazy)  22  unused
     23     ap, the va_list cursor, at -120(s0)
     24     unused

   Only ra/s0/s2 are restored by the epilogue itself; the rest of the frame is
   carried as "some word per slot", which is all the pop needs.  Keeping that
   split in ONE definition is what stops every lemma in the file from taking
   twenty-four points-to arguments.

   THE EPILOGUE is the panic path's: the [beqz] at 0x268 falls through (the
   spec's [panicking <> 0]), so the release of pr.lock at 0x28a is dead, and
   printk returns 0. *)
From Stdlib Require Import ZArith Bool Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_var gen_heap invariants.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvFetchExec RiscvExtras RiscvModelBytes.
Require Import RegFile InstrBytes WpMmodeLeafBase.
Require Import SmodeCore.
Require Import StackOwn CalleeSaved KernelText KernelDataInv.
Require Import KernelRvcDecode WpAuipc.
Require Import WpSconfAlu WpSconfMem WpSconfCtl WpSconfBtype WpSmodeIntr.
Require Import WpUart.
Require Import IntrDefs.
Require Import WpPrintkDecode.
Require Import SpecPrintk.
From Kernel Require KernelInstrs KernelData.
From Kernel Require KernelSyms.
Local Open Scope Z_scope.
Import Defs.

(* clean-context (mword-free) nat bounds *)
Lemma pk_cap_bounds (K : nat) : (38 <= K)%nat -> (24 <= K)%nat /\ (14 <= K - 24)%nat.
Proof. lia. Qed.

Lemma pk_nk (K : nat) : (24 <= K)%nat -> ((K - 24) + 24)%nat = K.
Proof. lia. Qed.

Section ProofPrintk.
  Context `{!riscvGS Σ, !sieG Σ}.
  Context `{!uartGhostG Σ}.
  Context `{CID : CpuId}.

  Notation PK := KernelSyms.printk.

  Ltac reg_neq :=
    lazymatch goal with
    | |- ?a <> ?b => tryif unify a b then fail else (vm_compute; discriminate)
    end.

  Local Notation ra_idx := (mword_of_int 1 : mword 5).
  Local Notation s0_idx := (mword_of_int 8 : mword 5).
  Local Notation a0_idx := (mword_of_int 10 : mword 5).
  Local Notation a5_idx := (mword_of_int 15 : mword 5).
  Local Notation s2_idx := (mword_of_int 18 : mword 5).

  (* the frame slots the epilogue does NOT restore *)
  Definition pk_slots (sp0 : mword 64) : iProp Σ :=
    ([∗ list] k ∈ [1;2;3;4;5;6;7;8;11;13;14;15;16;17;18;19;20;21;22;23;24]%nat,
       ∃ w : mword 64, (pa_stk sp0 k) ↦₈ w)%I.

  Definition pk_frame (sp0 ra0 s00 s20 : mword 64) : iProp Σ :=
    ((pa_stk sp0 9) ↦₈ ra0 ∗ (pa_stk sp0 10) ↦₈ s00 ∗ (pa_stk sp0 12) ↦₈ s20 ∗
     pk_slots sp0)%I.

  (* the whole frame, as the pop wants it *)
  Lemma pk_frame_stack_own (sp0 ra0 s00 s20 : mword 64) :
    pk_frame sp0 ra0 s00 s20 ⊢ stack_own sp0 24.
  Proof.
    rewrite /pk_frame /pk_slots stack_own_slots.
    iIntros "(H9 & H10 & H12 & Hr)".
    cbn [seq]. cbn [big_opL].
    iDestruct "Hr" as "(K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K11 & K13 & K14 &
                        K15 & K16 & K17 & K18 & K19 & K20 & K21 & K22 & K23 & K24 & _)".
    iFrame "K1 K2 K3 K4 K5 K6 K7 K8".
    iSplitL "H9". { iExists ra0. iExact "H9". }
    iSplitL "H10". { iExists s00. iExact "H10". }
    iFrame "K11".
    iSplitL "H12". { iExists s20. iExact "H12". }
    iFrame "K13 K14 K15 K16 K17 K18 K19 K20 K21 K22 K23 K24".
  Qed.

  (* ================================================================== *)
  (*  THE EPILOGUE (0x260 .. 0x274), the end of every path.              *)
  (* ================================================================== *)

  Lemma wp_printk_epi (γ : gname) (Φ : mval -> iProp Σ)
      (m mc : regfile) (K : nat) (pv pkv : mword 32) (dqm dqm2 : dfrac) (R : iProp Σ) :
    let sp0 := m !!! Regidx csp_rs1 in
    let spd := add_vec sp0 (sign_extend' 64 (caddi16sp_imm (mword_of_int 52 : mword 6))) in
    (24 <= K)%nat ->
    eq_vec (sign_extend' 64 pv) zero_reg = false ->
    mc !!! Regidx csp_rs1 = spd ->
    (forall c : mword 5, is_cs_idx c = true -> c <> csp_rs1 -> c <> s0_idx -> c <> s2_idx ->
       mc !!! Regidx c = m !!! Regidx c) ->
    sie_cap_gpr γ mc (K - 24)%nat -∗
    kernel_text -∗
    pc_is (mword_of_int (PK + 0x260) : mword 64) -∗
    pk_frame sp0 (m !!! Regidx ra_idx) (m !!! Regidx s0_idx) (m !!! Regidx s2_idx) -∗
    (mword_of_int KernelSyms.panicking : mword 64) ↦₄{ dqm } pv -∗
    R -∗
    ( ∀ mf,
      sie_cap_gpr γ mf K -∗
      pc_is (ret_pc (m !!! Regidx ra_idx)) -∗
      ⌜ callee_saved m mf /\ mf !!! Regidx ra_idx = m !!! Regidx ra_idx
        /\ mf !!! Regidx a0_idx = zero_reg ⌝ -∗
      (mword_of_int KernelSyms.panicking : mword 64) ↦₄{ dqm } pv -∗
      R -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    intros sp0 spd HK Hpv Hsp Hagree.
    iIntros "Hcg #Htext Hpc Hfr Hpanicking HR Hcont".
    iPoseProof (pki_260 with "Htext") as "Hi260".
    iPoseProof (pki_264 with "Htext") as "Hi264".
    iPoseProof (pki_268 with "Htext") as "Hi268".
    iPoseProof (pki_26a with "Htext") as "Hi26a".
    iPoseProof (pki_26c with "Htext") as "Hi26c".
    iPoseProof (pki_26e with "Htext") as "Hi26e".
    iPoseProof (pki_270 with "Htext") as "Hi270".
    iPoseProof (pki_272 with "Htext") as "Hi272".
    iPoseProof (pki_274 with "Htext") as "Hi274".
    iDestruct "Hfr" as "(H9 & H10 & H12 & Hrest)".
    assert (Hpush : spd = pa_stk sp0 24).
    { unfold spd, pa_stk, add_vec_int. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb9 : add_vec spd (zero_extend' 64 (concat_vec (mword_of_int 15 : mword 6) ('b"000"))) = pa_stk sp0 9).
    { rewrite Hpush. unfold pa_stk, add_vec_int. rewrite pa_stk_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb10 : add_vec spd (zero_extend' 64 (concat_vec (mword_of_int 14 : mword 6) ('b"000"))) = pa_stk sp0 10).
    { rewrite Hpush. unfold pa_stk, add_vec_int. rewrite pa_stk_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb12 : add_vec spd (zero_extend' 64 (concat_vec (mword_of_int 12 : mword 6) ('b"000"))) = pa_stk sp0 12).
    { rewrite Hpush. unfold pa_stk, add_vec_int. rewrite pa_stk_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    (* +0x260/0x264 auipc/lw a5 : the [panicking] flag *)
    iApply (wp_auipc_s_sconf γ Φ (mword_of_int (PK + 0x260)) a5_idx (mword_of_int 10 : mword 20)
              mc (K - 24)%nat ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi260 [-]").
    iIntros "Hcg Hpc".
    set (E1 := <[Regidx a5_idx := regval_into_reg (add_vec (mword_of_int (PK + 0x260) : mword 64) (auipc_off (mword_of_int 10 : mword 20)))]> mc).
    assert (Hpanaddr : add_vec (E1 !!! Regidx a5_idx) (sign_extend' 64 (mword_of_int 2760 : mword 12))
                       = (mword_of_int KernelSyms.panicking : mword 64)).
    { rewrite /E1 upd_eq. unfold regval_into_reg. apply bv_eq; vm_compute; reflexivity. }
    assert (Hp264 : add_vec_int (mword_of_int (PK + 0x260) : mword 64) 4 = mword_of_int (PK + 0x264)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp264) in "Hpc".
    iEval (rewrite -Hpanaddr) in "Hpanicking".
    iApply (wp_lw_s_sconf γ Φ (mword_of_int (PK + 0x264)) a5_idx a5_idx (mword_of_int 2760 : mword 12)
              E1 (K - 24)%nat pv ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi264 Hpanicking [-]").
    iIntros "Hcg Hpc Hpanicking". iEval (rewrite Hpanaddr) in "Hpanicking".
    set (E2 := <[Regidx a5_idx := regval_into_reg (sign_extend' 64 pv)]> E1).
    assert (Hp268 : add_vec_int (mword_of_int (PK + 0x264) : mword 64) 4 = mword_of_int (PK + 0x268)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp268) in "Hpc".
    (* +0x268 beqz a5 : NOT taken -- this is the panic path, so no release *)
    iApply (wp_cbeqz_fall_s_sconf γ Φ (mword_of_int (PK + 0x268)) (mword_of_int 17 : mword 8)
              (Cregidx (mword_of_int 7)) a5_idx E2 (K - 24)%nat
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
              ltac:(rewrite /E2 upd_eq; exact Hpv)
              with "Hcg Hpc Hi268 [-]").
    iIntros "Hcg Hpc".
    assert (Hp26a : add_vec_int (mword_of_int (PK + 0x268) : mword 64) 2 = mword_of_int (PK + 0x26a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp26a) in "Hpc".
    (* +0x26a c.li a0,0 : the return value *)
    iApply (wp_cli_s_sconf γ Φ (mword_of_int (PK + 0x26a)) a0_idx (mword_of_int 0 : mword 6)
              (zero_reg : mword 64) E2 (K - 24)%nat
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc Hi26a [-]").
    iIntros "Hcg Hpc".
    set (E3 := <[Regidx a0_idx := regval_into_reg (zero_reg : mword 64)]> E2).
    assert (HE3sp : E3 !!! Regidx csp_rs1 = spd).
    { rewrite /E3 upd_ne; [| reg_neq]. rewrite /E2 upd_ne; [| reg_neq].
      rewrite /E1 upd_ne; [exact Hsp | reg_neq]. }
    assert (Hp26c : add_vec_int (mword_of_int (PK + 0x26a) : mword 64) 2 = mword_of_int (PK + 0x26c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp26c) in "Hpc".
    (* +0x26c/0x26e/0x270 restore ra / s0 / s2 *)
    iApply (wp_cldsp_s_sconf γ Φ (mword_of_int (PK + 0x26c)) (mword_of_int 15 : mword 6) ra_idx
              E3 (K - 24)%nat (m !!! Regidx ra_idx)
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi26c [H9] [-]").
    { iEval (rewrite HE3sp Hb9). iExact "H9". }
    iIntros "Hcg Hpc H9". iEval (rewrite HE3sp Hb9) in "H9".
    set (E4 := <[Regidx ra_idx := regval_into_reg (m !!! Regidx ra_idx)]> E3).
    assert (HE4sp : E4 !!! Regidx csp_rs1 = spd) by (rewrite /E4 upd_ne; [exact HE3sp | reg_neq]).
    assert (Hp26e : add_vec_int (mword_of_int (PK + 0x26c) : mword 64) 2 = mword_of_int (PK + 0x26e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp26e) in "Hpc".
    iApply (wp_cldsp_s_sconf γ Φ (mword_of_int (PK + 0x26e)) (mword_of_int 14 : mword 6) s0_idx
              E4 (K - 24)%nat (m !!! Regidx s0_idx)
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi26e [H10] [-]").
    { iEval (rewrite HE4sp Hb10). iExact "H10". }
    iIntros "Hcg Hpc H10". iEval (rewrite HE4sp Hb10) in "H10".
    set (E5 := <[Regidx s0_idx := regval_into_reg (m !!! Regidx s0_idx)]> E4).
    assert (HE5sp : E5 !!! Regidx csp_rs1 = spd) by (rewrite /E5 upd_ne; [exact HE4sp | reg_neq]).
    assert (Hp270 : add_vec_int (mword_of_int (PK + 0x26e) : mword 64) 2 = mword_of_int (PK + 0x270)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp270) in "Hpc".
    iApply (wp_cldsp_s_sconf γ Φ (mword_of_int (PK + 0x270)) (mword_of_int 12 : mword 6) s2_idx
              E5 (K - 24)%nat (m !!! Regidx s2_idx)
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi270 [H12] [-]").
    { iEval (rewrite HE5sp Hb12). iExact "H12". }
    iIntros "Hcg Hpc H12". iEval (rewrite HE5sp Hb12) in "H12".
    set (E6 := <[Regidx s2_idx := regval_into_reg (m !!! Regidx s2_idx)]> E5).
    assert (HE6sp : E6 !!! Regidx csp_rs1 = spd) by (rewrite /E6 upd_ne; [exact HE5sp | reg_neq]).
    assert (Hp272 : add_vec_int (mword_of_int (PK + 0x270) : mword 64) 2 = mword_of_int (PK + 0x272)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp272) in "Hpc".
    (* +0x272 addi sp,sp,192 : the frame pop *)
    assert (Hwv : add_vec (E6 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 12 : mword 6))) = sp0).
    { rewrite HE6sp. unfold spd. apply frame_cancel_192. }
    assert (Hpop : E6 !!! Regidx csp_rs1 = pa_stk (add_vec (E6 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 12 : mword 6)))) 24).
    { rewrite Hwv HE6sp. exact Hpush. }
    iAssert (stack_own sp0 24) with "[H9 H10 H12 Hrest]" as "Hframe".
    { iApply pk_frame_stack_own. rewrite /pk_frame. iFrame "H9 H10 H12 Hrest". }
    iEval (rewrite -Hwv) in "Hframe".
    iApply (wp_caddi16sp_pop_s_sconf γ Φ (mword_of_int (PK + 0x272)) (mword_of_int 12 : mword 6)
              E6 (K - 24)%nat 24 Hpop with "Hcg Hpc Hi272 Hframe [-]").
    iIntros "Hcg Hpc".
    set (E7 := <[Regidx csp_rs1 := regval_into_reg (add_vec (E6 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 12 : mword 6))))]> E6).
    iEval (rewrite (pk_nk K HK)) in "Hcg".
    assert (Hp274 : add_vec_int (mword_of_int (PK + 0x272) : mword 64) 2 = mword_of_int (PK + 0x274)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp274) in "Hpc".
    (* +0x274 ret *)
    assert (HE7ra : E7 !!! Regidx ra_idx = m !!! Regidx ra_idx).
    { rewrite /E7 upd_ne; [| reg_neq]. rewrite /E6 upd_ne; [| reg_neq].
      rewrite /E5 upd_ne; [| reg_neq]. rewrite /E4 upd_eq. reflexivity. }
    assert (Hrt : ret_pc (E7 !!! Regidx ra_idx) = ret_pc (m !!! Regidx ra_idx)) by (rewrite HE7ra; reflexivity).
    iApply (wp_cret_s_sconf γ Φ (mword_of_int (PK + 0x274)) ra_idx E7 K
              ltac:(vm_compute; discriminate) with "Hcg Hpc Hi274 [-]").
    iIntros "Hcg Hpc". iEval (rewrite Hrt) in "Hpc".
    iApply ("Hcont" $! E7 with "Hcg Hpc [%] Hpanicking HR").
    split; [| split; [exact HE7ra | ] ].
    - assert (Hthread : forall c : mword 5, is_cs_idx c = true ->
                c <> csp_rs1 -> c <> s0_idx -> c <> s2_idx -> E7 !!! Regidx c = m !!! Regidx c).
      { intros c Hc Nsp N8 N18.
        pose proof (is_cs_idx_true_neq ra_idx c ltac:(vm_compute; reflexivity) Hc) as N1.
        pose proof (is_cs_idx_true_neq a0_idx c ltac:(vm_compute; reflexivity) Hc) as N10.
        pose proof (is_cs_idx_true_neq a5_idx c ltac:(vm_compute; reflexivity) Hc) as N15.
        rewrite /E7 upd_ne; [| congruence]. rewrite /E6 upd_ne; [| congruence].
        rewrite /E5 upd_ne; [| congruence]. rewrite /E4 upd_ne; [| congruence].
        rewrite /E3 upd_ne; [| congruence]. rewrite /E2 upd_ne; [| congruence].
        rewrite /E1 upd_ne; [| congruence]. exact (Hagree c Hc Nsp N8 N18). }
      unfold callee_saved.
      split. { rewrite /E7 upd_eq. exact Hwv. }
      split. { apply Hthread; vm_compute; first [reflexivity | discriminate]. }
      split. { rewrite /E7 upd_ne; [| reg_neq]. rewrite /E6 upd_ne; [| reg_neq].
               rewrite /E5 upd_eq; reflexivity. }
      split. { apply Hthread; vm_compute; first [reflexivity | discriminate]. }
      split. { rewrite /E7 upd_ne; [| reg_neq]. rewrite /E6 upd_eq; reflexivity. }
      repeat split; apply Hthread; vm_compute; first [reflexivity | discriminate].
    - rewrite /E7 upd_ne; [| reg_neq]. rewrite /E6 upd_ne; [| reg_neq].
      rewrite /E5 upd_ne; [| reg_neq]. rewrite /E4 upd_ne; [| reg_neq].
      rewrite /E3 upd_eq. reflexivity.
  Qed.

End ProofPrintk.
