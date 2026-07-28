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
Require Import PrintintArith.
Require Import WpPrintkDecode.
Require Import PrintkFmt SpecConsputc SpecPrintint SpecPrintk.
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

  (* raw [mword 5] disequality: [discriminate] cannot see it (a [bv] is a
     RECORD, so two distinct values share a constructor) -- go through
     [bv_unsigned].  [reg_neq] below is for the [Regidx _ <> Regidx _] form. *)
  Ltac mw_neq :=
    let He := fresh in intro He;
    apply (f_equal bv_unsigned) in He; vm_compute in He; discriminate.

  Ltac reg_neq :=
    lazymatch goal with
    | |- ?a <> ?b => tryif unify a b then fail else (vm_compute; discriminate)
    end.

  Local Notation ra_idx := (mword_of_int 1 : mword 5).
  Local Notation s0_idx := (mword_of_int 8 : mword 5).
  Local Notation a0_idx := (mword_of_int 10 : mword 5).
  Local Notation a1_idx := (mword_of_int 11 : mword 5).
  Local Notation a5_idx := (mword_of_int 15 : mword 5).
  Local Notation s2_idx := (mword_of_int 18 : mword 5).

  (* the eleven callee-saved registers the epilogue does NOT restore: it
     reloads sp, s0 and s2 only, so every other callee-saved register must
     already agree with the entry map.  Spelled out rather than quantified over
     [is_cs_idx], because an [is_cs_idx]-enumeration tactic has to case-split
     fourteen ways inside a large iris context. *)
  Definition pk_cs_kept (m mc : regfile) : Prop :=
    mc !!! Regidx (mword_of_int 4 : mword 5)  = m !!! Regidx (mword_of_int 4 : mword 5)  /\
    mc !!! Regidx (mword_of_int 9 : mword 5)  = m !!! Regidx (mword_of_int 9 : mword 5)  /\
    mc !!! Regidx (mword_of_int 19 : mword 5) = m !!! Regidx (mword_of_int 19 : mword 5) /\
    mc !!! Regidx (mword_of_int 20 : mword 5) = m !!! Regidx (mword_of_int 20 : mword 5) /\
    mc !!! Regidx (mword_of_int 21 : mword 5) = m !!! Regidx (mword_of_int 21 : mword 5) /\
    mc !!! Regidx (mword_of_int 22 : mword 5) = m !!! Regidx (mword_of_int 22 : mword 5) /\
    mc !!! Regidx (mword_of_int 23 : mword 5) = m !!! Regidx (mword_of_int 23 : mword 5) /\
    mc !!! Regidx (mword_of_int 24 : mword 5) = m !!! Regidx (mword_of_int 24 : mword 5) /\
    mc !!! Regidx (mword_of_int 25 : mword 5) = m !!! Regidx (mword_of_int 25 : mword 5) /\
    mc !!! Regidx (mword_of_int 26 : mword 5) = m !!! Regidx (mword_of_int 26 : mword 5) /\
    mc !!! Regidx (mword_of_int 27 : mword 5) = m !!! Regidx (mword_of_int 27 : mword 5).

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
  (*  THE PROLOGUE (0x00 .. 0x1a): the 24-slot push, the three eager     *)
  (*  saves, s0/s2, and the seven vararg spills.                         *)
  (*                                                                     *)
  (*  It ends at 0x1e with the frame in the shape the rest of the        *)
  (*  function reads it: slots 9/10/12 hold ra/s0/s2, slots 7..1 hold    *)
  (*  a1..a7 (the va_list, in ABI order, HIGHEST slot first), and every  *)
  (*  other slot is still untouched.                                     *)
  (* ================================================================== *)

  (* the seven spilled varargs: slot 7 down to slot 1 IS a1 .. a7.  Spelled
     out rather than indexed, so no [7 - j] / [11 + j] arithmetic has to be
     reduced at every use. *)
  Definition pk_va (sp0 : mword 64) (m : regfile) : iProp Σ :=
    ((pa_stk sp0 7) ↦₈ (m !!! Regidx (mword_of_int 11 : mword 5)) ∗
     (pa_stk sp0 6) ↦₈ (m !!! Regidx (mword_of_int 12 : mword 5)) ∗
     (pa_stk sp0 5) ↦₈ (m !!! Regidx (mword_of_int 13 : mword 5)) ∗
     (pa_stk sp0 4) ↦₈ (m !!! Regidx (mword_of_int 14 : mword 5)) ∗
     (pa_stk sp0 3) ↦₈ (m !!! Regidx (mword_of_int 15 : mword 5)) ∗
     (pa_stk sp0 2) ↦₈ (m !!! Regidx (mword_of_int 16 : mword 5)) ∗
     (pa_stk sp0 1) ↦₈ (m !!! Regidx (mword_of_int 17 : mword 5)))%I.

  Lemma wp_printk_prologue (γ : gname) (Φ : mval -> iProp Σ)
      (m : regfile) (K : nat) :
    let sp0 := m !!! Regidx csp_rs1 in
    let spd := add_vec sp0 (sign_extend' 64 (caddi16sp_imm (mword_of_int 52 : mword 6))) in
    (24 <= K)%nat ->
    sie_cap_gpr γ m K -∗
    kernel_text -∗
    pc_is (mword_of_int PK : mword 64) -∗
    ( ∀ mp : regfile,
      ⌜ mp !!! Regidx csp_rs1 = spd
        /\ mp !!! Regidx s0_idx = add_vec sp0 (sign_extend' 64 (mword_of_int (-64) : mword 12))
        /\ mp !!! Regidx s2_idx = m !!! Regidx a0_idx
        /\ (forall c : mword 5, c <> csp_rs1 -> c <> s0_idx -> c <> s2_idx ->
              mp !!! Regidx c = m !!! Regidx c) ⌝ -∗
      sie_cap_gpr γ mp (K - 24)%nat -∗
      pc_is (mword_of_int (PK + 0x1e) : mword 64) -∗
      (pa_stk sp0 9) ↦₈ (m !!! Regidx ra_idx) -∗
      (pa_stk sp0 10) ↦₈ (m !!! Regidx s0_idx) -∗
      (pa_stk sp0 12) ↦₈ (m !!! Regidx s2_idx) -∗
      pk_va sp0 m -∗
      ([∗ list] k ∈ [8;11;13;14;15;16;17;18;19;20;21;22;23;24]%nat,
         ∃ w : mword 64, (pa_stk sp0 k) ↦₈ w) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    intros sp0 spd HK.
    iIntros "Hcg #Htext Hpc Hcont".
    iPoseProof (pki_00 with "Htext") as "Hi00".
    iPoseProof (pki_02 with "Htext") as "Hi02".
    iPoseProof (pki_04 with "Htext") as "Hi04".
    iPoseProof (pki_06 with "Htext") as "Hi06".
    iPoseProof (pki_08 with "Htext") as "Hi08".
    iPoseProof (pki_0a with "Htext") as "Hi0a".
    iPoseProof (pki_0c with "Htext") as "Hi0c".
    iPoseProof (pki_0e with "Htext") as "Hi0e".
    iPoseProof (pki_10 with "Htext") as "Hi10".
    iPoseProof (pki_12 with "Htext") as "Hi12".
    iPoseProof (pki_14 with "Htext") as "Hi14".
    iPoseProof (pki_16 with "Htext") as "Hi16".
    iPoseProof (pki_1a with "Htext") as "Hi1a".
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
    (* +0x00 the 24-slot push *)
    iApply (wp_caddi16sp_push_s_sconf γ Φ (mword_of_int PK) (mword_of_int 52 : mword 6) m K 24
              HK Hpush with "Hcg Hpc Hi00 [-]").
    iIntros "Hcg Hframe Hpc".
    set (W1 := <[Regidx csp_rs1 := regval_into_reg spd]> m).
    iEval (rewrite stack_own_slots; cbn [seq]) in "Hframe".
    iDestruct "Hframe" as "(T1 & T2 & T3 & T4 & T5 & T6 & T7 & T8 & T9 & T10 & T11 & T12 &
                            T13 & T14 & T15 & T16 & T17 & T18 & T19 & T20 & T21 & T22 & T23 & T24 & _)".
    iDestruct "T9" as (u9) "H9". iDestruct "T10" as (u10) "H10".
    iDestruct "T12" as (u12) "H12".
    iDestruct "T1" as (u1) "V1". iDestruct "T2" as (u2) "V2". iDestruct "T3" as (u3) "V3".
    iDestruct "T4" as (u4) "V4". iDestruct "T5" as (u5) "V5". iDestruct "T6" as (u6) "V6".
    iDestruct "T7" as (u7) "V7".
    assert (HW1sp : W1 !!! Regidx csp_rs1 = spd) by (rewrite /W1 upd_eq; reflexivity).
    assert (Hp02 : add_vec_int (mword_of_int PK : mword 64) 2 = mword_of_int (PK + 0x02)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp02) in "Hpc".
    iApply (wp_csdsp_s_sconf γ Φ (mword_of_int (PK + 0x02)) (mword_of_int 15 : mword 6) ra_idx
              W1 (K - 24)%nat u9 with "Hcg Hpc Hi02 [H9] [-]").
    { iEval (rewrite HW1sp Hb9). iExact "H9". }
    iIntros "Hcg Hpc H9". iEval (rewrite HW1sp Hb9) in "H9".
    assert (HW1r1 : W1 !!! Regidx ra_idx = m !!! Regidx ra_idx) by (rewrite /W1 upd_ne; [reflexivity | reg_neq]).
    iEval (rewrite HW1r1) in "H9".
    assert (Hp04 : add_vec_int (mword_of_int (PK + 0x02) : mword 64) 2 = mword_of_int (PK + 0x04)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp04) in "Hpc".
    iApply (wp_csdsp_s_sconf γ Φ (mword_of_int (PK + 0x04)) (mword_of_int 14 : mword 6) s0_idx
              W1 (K - 24)%nat u10 with "Hcg Hpc Hi04 [H10] [-]").
    { iEval (rewrite HW1sp Hb10). iExact "H10". }
    iIntros "Hcg Hpc H10". iEval (rewrite HW1sp Hb10) in "H10".
    assert (HW1r8 : W1 !!! Regidx s0_idx = m !!! Regidx s0_idx) by (rewrite /W1 upd_ne; [reflexivity | reg_neq]).
    iEval (rewrite HW1r8) in "H10".
    assert (Hp06 : add_vec_int (mword_of_int (PK + 0x04) : mword 64) 2 = mword_of_int (PK + 0x06)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp06) in "Hpc".
    iApply (wp_csdsp_s_sconf γ Φ (mword_of_int (PK + 0x06)) (mword_of_int 12 : mword 6) s2_idx
              W1 (K - 24)%nat u12 with "Hcg Hpc Hi06 [H12] [-]").
    { iEval (rewrite HW1sp Hb12). iExact "H12". }
    iIntros "Hcg Hpc H12". iEval (rewrite HW1sp Hb12) in "H12".
    assert (HW1r18 : W1 !!! Regidx s2_idx = m !!! Regidx s2_idx) by (rewrite /W1 upd_ne; [reflexivity | reg_neq]).
    iEval (rewrite HW1r18) in "H12".
    assert (Hp08 : add_vec_int (mword_of_int (PK + 0x06) : mword 64) 2 = mword_of_int (PK + 0x08)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp08) in "Hpc".
    (* +0x08 addi s0,sp,128 : s0 := sp0 - 64, the va_list's base *)
    iApply (wp_caddi4spn_s_sconf γ Φ (mword_of_int (PK + 0x08)) (Cregidx (mword_of_int 0)) (mword_of_int 32 : mword 8) s0_idx
              W1 (K - 24)%nat ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi08 [-]").
    iIntros "Hcg Hpc".
    set (W2 := <[Regidx s0_idx := regval_into_reg (add_vec (W1 !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm (mword_of_int 32 : mword 8))))]> W1).
    assert (HW2s0 : W2 !!! Regidx s0_idx = add_vec sp0 (sign_extend' 64 (mword_of_int (-64) : mword 12))).
    { rewrite /W2 upd_eq. unfold regval_into_reg. rewrite HW1sp. unfold spd.
      rewrite pa_stk_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (HW2sp : W2 !!! Regidx csp_rs1 = spd) by (rewrite /W2 upd_ne; [exact HW1sp | reg_neq]).
    assert (Hp0a : add_vec_int (mword_of_int (PK + 0x08) : mword 64) 2 = mword_of_int (PK + 0x0a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp0a) in "Hpc".
    (* +0x0a c.mv s2,a0 : s2 := fmt *)
    iApply (wp_cmv_s_sconf γ Φ (mword_of_int (PK + 0x0a)) s2_idx a0_idx W2 (K - 24)%nat
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi0a [-]").
    iIntros "Hcg Hpc".
    set (W3 := <[Regidx s2_idx := regval_into_reg (add_vec zero_reg (W2 !!! Regidx a0_idx))]> W2).
    assert (HW3s2 : W3 !!! Regidx s2_idx = m !!! Regidx a0_idx).
    { rewrite /W3 upd_eq. unfold regval_into_reg.
      rewrite /W2 upd_ne; [| reg_neq]. rewrite /W1 upd_ne; [| reg_neq].
      apply pi_addv_zero_l. }
    assert (HW3s0 : W3 !!! Regidx s0_idx = add_vec sp0 (sign_extend' 64 (mword_of_int (-64) : mword 12)))
      by (rewrite /W3 upd_ne; [exact HW2s0 | reg_neq]).
    assert (HW3sp : W3 !!! Regidx csp_rs1 = spd) by (rewrite /W3 upd_ne; [exact HW2sp | reg_neq]).
    assert (Hp0c : add_vec_int (mword_of_int (PK + 0x0a) : mword 64) 2 = mword_of_int (PK + 0x0c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp0c) in "Hpc".
    (* +0x0c sd a1,8(s0) -> slot 7 *)
    assert (Hva7 : add_vec (W3 !!! Regidx s0_idx) (sign_extend' 64 (mword_of_int 8 : mword 12)) = pa_stk sp0 7).
    { rewrite HW3s0. unfold pa_stk, add_vec_int. rewrite pa_stk_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    iApply (wp_csd_s_sconf γ Φ (mword_of_int (PK + 0x0c)) (mword_of_int 11 : mword 5) s0_idx (mword_of_int 8 : mword 12)
              W3 (K - 24)%nat u7 with "Hcg Hpc Hi0c [V7] [-]").
    { iEval (rewrite Hva7). iExact "V7". }
    iIntros "Hcg Hpc V7". iEval (rewrite Hva7) in "V7".
    assert (HW3r11 : W3 !!! Regidx (mword_of_int 11 : mword 5) = m !!! Regidx (mword_of_int 11 : mword 5)).
    { rewrite /W3 upd_ne; [| reg_neq]. rewrite /W2 upd_ne; [| reg_neq].
      rewrite /W1 upd_ne; [reflexivity | reg_neq]. }
    iEval (rewrite HW3r11) in "V7".
    assert (Hp0e : add_vec_int (mword_of_int (PK + 0x0c) : mword 64) 2 = mword_of_int (PK + 0x0e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp0e) in "Hpc".
    (* +0x0e sd a2,16(s0) -> slot 6 *)
    assert (Hva6 : add_vec (W3 !!! Regidx s0_idx) (sign_extend' 64 (mword_of_int 16 : mword 12)) = pa_stk sp0 6).
    { rewrite HW3s0. unfold pa_stk, add_vec_int. rewrite pa_stk_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    iApply (wp_csd_s_sconf γ Φ (mword_of_int (PK + 0x0e)) (mword_of_int 12 : mword 5) s0_idx (mword_of_int 16 : mword 12)
              W3 (K - 24)%nat u6 with "Hcg Hpc Hi0e [V6] [-]").
    { iEval (rewrite Hva6). iExact "V6". }
    iIntros "Hcg Hpc V6". iEval (rewrite Hva6) in "V6".
    assert (HW3r12 : W3 !!! Regidx (mword_of_int 12 : mword 5) = m !!! Regidx (mword_of_int 12 : mword 5)).
    { rewrite /W3 upd_ne; [| reg_neq]. rewrite /W2 upd_ne; [| reg_neq].
      rewrite /W1 upd_ne; [reflexivity | reg_neq]. }
    iEval (rewrite HW3r12) in "V6".
    assert (Hp10 : add_vec_int (mword_of_int (PK + 0x0e) : mword 64) 2 = mword_of_int (PK + 0x10)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp10) in "Hpc".
    (* +0x10 sd a3,24(s0) -> slot 5 *)
    assert (Hva5 : add_vec (W3 !!! Regidx s0_idx) (sign_extend' 64 (mword_of_int 24 : mword 12)) = pa_stk sp0 5).
    { rewrite HW3s0. unfold pa_stk, add_vec_int. rewrite pa_stk_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    iApply (wp_csd_s_sconf γ Φ (mword_of_int (PK + 0x10)) (mword_of_int 13 : mword 5) s0_idx (mword_of_int 24 : mword 12)
              W3 (K - 24)%nat u5 with "Hcg Hpc Hi10 [V5] [-]").
    { iEval (rewrite Hva5). iExact "V5". }
    iIntros "Hcg Hpc V5". iEval (rewrite Hva5) in "V5".
    assert (HW3r13 : W3 !!! Regidx (mword_of_int 13 : mword 5) = m !!! Regidx (mword_of_int 13 : mword 5)).
    { rewrite /W3 upd_ne; [| reg_neq]. rewrite /W2 upd_ne; [| reg_neq].
      rewrite /W1 upd_ne; [reflexivity | reg_neq]. }
    iEval (rewrite HW3r13) in "V5".
    assert (Hp12 : add_vec_int (mword_of_int (PK + 0x10) : mword 64) 2 = mword_of_int (PK + 0x12)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp12) in "Hpc".
    (* +0x12 sd a4,32(s0) -> slot 4 *)
    assert (Hva4 : add_vec (W3 !!! Regidx s0_idx) (sign_extend' 64 (mword_of_int 32 : mword 12)) = pa_stk sp0 4).
    { rewrite HW3s0. unfold pa_stk, add_vec_int. rewrite pa_stk_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    iApply (wp_csd_s_sconf γ Φ (mword_of_int (PK + 0x12)) (mword_of_int 14 : mword 5) s0_idx (mword_of_int 32 : mword 12)
              W3 (K - 24)%nat u4 with "Hcg Hpc Hi12 [V4] [-]").
    { iEval (rewrite Hva4). iExact "V4". }
    iIntros "Hcg Hpc V4". iEval (rewrite Hva4) in "V4".
    assert (HW3r14 : W3 !!! Regidx (mword_of_int 14 : mword 5) = m !!! Regidx (mword_of_int 14 : mword 5)).
    { rewrite /W3 upd_ne; [| reg_neq]. rewrite /W2 upd_ne; [| reg_neq].
      rewrite /W1 upd_ne; [reflexivity | reg_neq]. }
    iEval (rewrite HW3r14) in "V4".
    assert (Hp14 : add_vec_int (mword_of_int (PK + 0x12) : mword 64) 2 = mword_of_int (PK + 0x14)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp14) in "Hpc".
    (* +0x14 sd a5,40(s0) -> slot 3 *)
    assert (Hva3 : add_vec (W3 !!! Regidx s0_idx) (sign_extend' 64 (mword_of_int 40 : mword 12)) = pa_stk sp0 3).
    { rewrite HW3s0. unfold pa_stk, add_vec_int. rewrite pa_stk_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    iApply (wp_csd_s_sconf γ Φ (mword_of_int (PK + 0x14)) (mword_of_int 15 : mword 5) s0_idx (mword_of_int 40 : mword 12)
              W3 (K - 24)%nat u3 with "Hcg Hpc Hi14 [V3] [-]").
    { iEval (rewrite Hva3). iExact "V3". }
    iIntros "Hcg Hpc V3". iEval (rewrite Hva3) in "V3".
    assert (HW3r15 : W3 !!! Regidx (mword_of_int 15 : mword 5) = m !!! Regidx (mword_of_int 15 : mword 5)).
    { rewrite /W3 upd_ne; [| reg_neq]. rewrite /W2 upd_ne; [| reg_neq].
      rewrite /W1 upd_ne; [reflexivity | reg_neq]. }
    iEval (rewrite HW3r15) in "V3".
    assert (Hp16 : add_vec_int (mword_of_int (PK + 0x14) : mword 64) 2 = mword_of_int (PK + 0x16)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp16) in "Hpc".
    (* +0x16 sd a6,48(s0) -> slot 2 *)
    assert (Hva2 : add_vec (W3 !!! Regidx s0_idx) (sign_extend' 64 (mword_of_int 48 : mword 12)) = pa_stk sp0 2).
    { rewrite HW3s0. unfold pa_stk, add_vec_int. rewrite pa_stk_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    iApply (wp_sd_s_sconf γ Φ (mword_of_int (PK + 0x16)) (mword_of_int 16 : mword 5) s0_idx (mword_of_int 48 : mword 12)
              W3 (K - 24)%nat u2 with "Hcg Hpc Hi16 [V2] [-]").
    { iEval (rewrite Hva2). iExact "V2". }
    iIntros "Hcg Hpc V2". iEval (rewrite Hva2) in "V2".
    assert (HW3r16 : W3 !!! Regidx (mword_of_int 16 : mword 5) = m !!! Regidx (mword_of_int 16 : mword 5)).
    { rewrite /W3 upd_ne; [| reg_neq]. rewrite /W2 upd_ne; [| reg_neq].
      rewrite /W1 upd_ne; [reflexivity | reg_neq]. }
    iEval (rewrite HW3r16) in "V2".
    assert (Hp1a : add_vec_int (mword_of_int (PK + 0x16) : mword 64) 4 = mword_of_int (PK + 0x1a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp1a) in "Hpc".
    (* +0x1a sd a7,56(s0) -> slot 1 *)
    assert (Hva1 : add_vec (W3 !!! Regidx s0_idx) (sign_extend' 64 (mword_of_int 56 : mword 12)) = pa_stk sp0 1).
    { rewrite HW3s0. unfold pa_stk, add_vec_int. rewrite pa_stk_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    iApply (wp_sd_s_sconf γ Φ (mword_of_int (PK + 0x1a)) (mword_of_int 17 : mword 5) s0_idx (mword_of_int 56 : mword 12)
              W3 (K - 24)%nat u1 with "Hcg Hpc Hi1a [V1] [-]").
    { iEval (rewrite Hva1). iExact "V1". }
    iIntros "Hcg Hpc V1". iEval (rewrite Hva1) in "V1".
    assert (HW3r17 : W3 !!! Regidx (mword_of_int 17 : mword 5) = m !!! Regidx (mword_of_int 17 : mword 5)).
    { rewrite /W3 upd_ne; [| reg_neq]. rewrite /W2 upd_ne; [| reg_neq].
      rewrite /W1 upd_ne; [reflexivity | reg_neq]. }
    iEval (rewrite HW3r17) in "V1".
    assert (Hp1e : add_vec_int (mword_of_int (PK + 0x1a) : mword 64) 4 = mword_of_int (PK + 0x1e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp1e) in "Hpc".
    (* hand over: the frame in the shape the body reads it *)
    iApply ("Hcont" $! W3 with "[%] Hcg Hpc H9 H10 H12 [V1 V2 V3 V4 V5 V6 V7]
                                [T8 T11 T13 T14 T15 T16 T17 T18 T19 T20 T21 T22 T23 T24]").
    { split; [exact HW3sp | ]. split; [exact HW3s0 | ]. split; [exact HW3s2 | ].
      intros c Nsp N8 N18.
      rewrite /W3 upd_ne; [| congruence]. rewrite /W2 upd_ne; [| congruence].
      rewrite /W1 upd_ne; [reflexivity | congruence]. }
    { rewrite /pk_va. iFrame "V7 V6 V5 V4 V3 V2 V1". }
    { cbn [big_opL]. iFrame "T8 T11 T13 T14 T15 T16 T17 T18 T19 T20 T21 T22 T23 T24". }
  Qed.

  (* ================================================================== *)
  (*  THE RESTORE BLOCK (0x24e and 0x276): nine [ld]s undoing the LAZY   *)
  (*  saves.  The same nine instructions sit at two addresses -- the     *)
  (*  end-of-string exit and the "%" -at-end-of-string exit -- so the    *)
  (*  block is proved ONCE, over the nine [instr] facts bundled as       *)
  (*  [pk_restore_instrs B], and instantiated at both.                    *)
  (* ================================================================== *)

  Definition pk_ld (B off : Z) (u rd : Z) : iProp Σ :=
    instr (mword_of_int (PK + B + off) : mword 64) true
      (LOAD (zero_extend' 12 (concat_vec (mword_of_int u : mword 6) ('b"000")),
             sp, Regidx (mword_of_int rd), false, 8)).

  Definition pk_restore_instrs (B : Z) : iProp Σ :=
    (     pk_ld B 0 13 9 ∗
     pk_ld B 2 11 19 ∗
     pk_ld B 4 10 20 ∗
     pk_ld B 6 9 21 ∗
     pk_ld B 8 8 22 ∗
     pk_ld B 10 7 23 ∗
     pk_ld B 12 6 24 ∗
     pk_ld B 14 4 26 ∗
     pk_ld B 16 3 27)%I.


  (* the nine saved slots, at the slot indices the offsets denote *)
  Definition pk_saved (sp0 : mword 64) (v9 v19 v20 v21 v22 v23 v24 v26 v27 : mword 64) : iProp Σ :=
    (     (pa_stk sp0 11) ↦₈ v9 ∗
     (pa_stk sp0 13) ↦₈ v19 ∗
     (pa_stk sp0 14) ↦₈ v20 ∗
     (pa_stk sp0 15) ↦₈ v21 ∗
     (pa_stk sp0 16) ↦₈ v22 ∗
     (pa_stk sp0 17) ↦₈ v23 ∗
     (pa_stk sp0 18) ↦₈ v24 ∗
     (pa_stk sp0 20) ↦₈ v26 ∗
     (pa_stk sp0 21) ↦₈ v27)%I.

  (* the block itself: nine loads, ending at [B + 18] *)
  Lemma wp_printk_restore (γ : gname) (Φ : mval -> iProp Σ)
      (mc : regfile) (K : nat) (B : Z) (sp0 : mword 64) (v9 v19 v20 v21 v22 v23 v24 v26 v27 : mword 64) :
    let spd := add_vec sp0 (sign_extend' 64 (caddi16sp_imm (mword_of_int 52 : mword 6))) in
    mc !!! Regidx csp_rs1 = spd ->
    sie_cap_gpr γ mc (K - 24)%nat -∗
    pk_restore_instrs B -∗
    pc_is (mword_of_int (PK + B + 0) : mword 64) -∗
    pk_saved sp0 v9 v19 v20 v21 v22 v23 v24 v26 v27 -∗
    ( ∀ mf : regfile,
      ⌜ (forall c : mword 5,
           c <> mword_of_int 9 -> c <> mword_of_int 19 -> c <> mword_of_int 20 ->
           c <> mword_of_int 21 -> c <> mword_of_int 22 -> c <> mword_of_int 23 ->
           c <> mword_of_int 24 -> c <> mword_of_int 26 -> c <> mword_of_int 27 ->
           mf !!! Regidx c = mc !!! Regidx c)
        /\ mf !!! Regidx (mword_of_int 9 : mword 5) = v9
        /\ mf !!! Regidx (mword_of_int 19 : mword 5) = v19
        /\ mf !!! Regidx (mword_of_int 20 : mword 5) = v20
        /\ mf !!! Regidx (mword_of_int 21 : mword 5) = v21
        /\ mf !!! Regidx (mword_of_int 22 : mword 5) = v22
        /\ mf !!! Regidx (mword_of_int 23 : mword 5) = v23
        /\ mf !!! Regidx (mword_of_int 24 : mword 5) = v24
        /\ mf !!! Regidx (mword_of_int 26 : mword 5) = v26
        /\ mf !!! Regidx (mword_of_int 27 : mword 5) = v27
        ⌝ -∗
      sie_cap_gpr γ mf (K - 24)%nat -∗
      pc_is (mword_of_int (PK + B + 18) : mword 64) -∗
      pk_saved sp0 v9 v19 v20 v21 v22 v23 v24 v26 v27 -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    intros spd Hsp.
    iIntros "Hcg Hinstrs Hpc Hsv Hcont".
    rewrite /pk_restore_instrs.
    iDestruct "Hinstrs" as "(I0 & I2 & I4 & I6 & I8 & I10 & I12 & I14 & I16)".
    rewrite /pk_saved.
    iDestruct "Hsv" as "(S9 & S19 & S20 & S21 & S22 & S23 & S24 & S26 & S27)".
    assert (Hpush : spd = pa_stk sp0 24).
    { unfold spd, pa_stk, add_vec_int. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb9 : add_vec spd (zero_extend' 64 (concat_vec (mword_of_int 13 : mword 6) ('b"000"))) = pa_stk sp0 11).
    { rewrite Hpush. unfold pa_stk, add_vec_int. rewrite pa_stk_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb19 : add_vec spd (zero_extend' 64 (concat_vec (mword_of_int 11 : mword 6) ('b"000"))) = pa_stk sp0 13).
    { rewrite Hpush. unfold pa_stk, add_vec_int. rewrite pa_stk_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb20 : add_vec spd (zero_extend' 64 (concat_vec (mword_of_int 10 : mword 6) ('b"000"))) = pa_stk sp0 14).
    { rewrite Hpush. unfold pa_stk, add_vec_int. rewrite pa_stk_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb21 : add_vec spd (zero_extend' 64 (concat_vec (mword_of_int 9 : mword 6) ('b"000"))) = pa_stk sp0 15).
    { rewrite Hpush. unfold pa_stk, add_vec_int. rewrite pa_stk_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb22 : add_vec spd (zero_extend' 64 (concat_vec (mword_of_int 8 : mword 6) ('b"000"))) = pa_stk sp0 16).
    { rewrite Hpush. unfold pa_stk, add_vec_int. rewrite pa_stk_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb23 : add_vec spd (zero_extend' 64 (concat_vec (mword_of_int 7 : mword 6) ('b"000"))) = pa_stk sp0 17).
    { rewrite Hpush. unfold pa_stk, add_vec_int. rewrite pa_stk_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb24 : add_vec spd (zero_extend' 64 (concat_vec (mword_of_int 6 : mword 6) ('b"000"))) = pa_stk sp0 18).
    { rewrite Hpush. unfold pa_stk, add_vec_int. rewrite pa_stk_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb26 : add_vec spd (zero_extend' 64 (concat_vec (mword_of_int 4 : mword 6) ('b"000"))) = pa_stk sp0 20).
    { rewrite Hpush. unfold pa_stk, add_vec_int. rewrite pa_stk_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb27 : add_vec spd (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000"))) = pa_stk sp0 21).
    { rewrite Hpush. unfold pa_stk, add_vec_int. rewrite pa_stk_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    iApply (wp_cldsp_s_sconf γ Φ (mword_of_int (PK + B + 0)) (mword_of_int 13 : mword 6) (mword_of_int 9 : mword 5)
              mc (K - 24)%nat v9
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hcg Hpc I0 [S9] [-]").
    { iEval (rewrite Hsp Hb9). iExact "S9". }
    iIntros "Hcg Hpc S9". iEval (rewrite Hsp Hb9) in "S9".
    set (M9 := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg v9]> mc).
    assert (HM9sp : M9 !!! Regidx csp_rs1 = spd)
      by (rewrite /M9 upd_ne; [exact Hsp | reg_neq]).
    assert (Hp0 : add_vec_int (mword_of_int (PK + B + 0) : mword 64) 2 = mword_of_int (PK + B + 2))
      by (unfold add_vec_int; rewrite moi_add; f_equal; lia).
    iEval (rewrite Hp0) in "Hpc".
    iApply (wp_cldsp_s_sconf γ Φ (mword_of_int (PK + B + 2)) (mword_of_int 11 : mword 6) (mword_of_int 19 : mword 5)
              M9 (K - 24)%nat v19
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hcg Hpc I2 [S19] [-]").
    { iEval (rewrite HM9sp Hb19). iExact "S19". }
    iIntros "Hcg Hpc S19". iEval (rewrite HM9sp Hb19) in "S19".
    set (M19 := <[Regidx (mword_of_int 19 : mword 5) := regval_into_reg v19]> M9).
    assert (HM19sp : M19 !!! Regidx csp_rs1 = spd)
      by (rewrite /M19 upd_ne; [exact HM9sp | reg_neq]).
    assert (Hp2 : add_vec_int (mword_of_int (PK + B + 2) : mword 64) 2 = mword_of_int (PK + B + 4))
      by (unfold add_vec_int; rewrite moi_add; f_equal; lia).
    iEval (rewrite Hp2) in "Hpc".
    iApply (wp_cldsp_s_sconf γ Φ (mword_of_int (PK + B + 4)) (mword_of_int 10 : mword 6) (mword_of_int 20 : mword 5)
              M19 (K - 24)%nat v20
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hcg Hpc I4 [S20] [-]").
    { iEval (rewrite HM19sp Hb20). iExact "S20". }
    iIntros "Hcg Hpc S20". iEval (rewrite HM19sp Hb20) in "S20".
    set (M20 := <[Regidx (mword_of_int 20 : mword 5) := regval_into_reg v20]> M19).
    assert (HM20sp : M20 !!! Regidx csp_rs1 = spd)
      by (rewrite /M20 upd_ne; [exact HM19sp | reg_neq]).
    assert (Hp4 : add_vec_int (mword_of_int (PK + B + 4) : mword 64) 2 = mword_of_int (PK + B + 6))
      by (unfold add_vec_int; rewrite moi_add; f_equal; lia).
    iEval (rewrite Hp4) in "Hpc".
    iApply (wp_cldsp_s_sconf γ Φ (mword_of_int (PK + B + 6)) (mword_of_int 9 : mword 6) (mword_of_int 21 : mword 5)
              M20 (K - 24)%nat v21
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hcg Hpc I6 [S21] [-]").
    { iEval (rewrite HM20sp Hb21). iExact "S21". }
    iIntros "Hcg Hpc S21". iEval (rewrite HM20sp Hb21) in "S21".
    set (M21 := <[Regidx (mword_of_int 21 : mword 5) := regval_into_reg v21]> M20).
    assert (HM21sp : M21 !!! Regidx csp_rs1 = spd)
      by (rewrite /M21 upd_ne; [exact HM20sp | reg_neq]).
    assert (Hp6 : add_vec_int (mword_of_int (PK + B + 6) : mword 64) 2 = mword_of_int (PK + B + 8))
      by (unfold add_vec_int; rewrite moi_add; f_equal; lia).
    iEval (rewrite Hp6) in "Hpc".
    iApply (wp_cldsp_s_sconf γ Φ (mword_of_int (PK + B + 8)) (mword_of_int 8 : mword 6) (mword_of_int 22 : mword 5)
              M21 (K - 24)%nat v22
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hcg Hpc I8 [S22] [-]").
    { iEval (rewrite HM21sp Hb22). iExact "S22". }
    iIntros "Hcg Hpc S22". iEval (rewrite HM21sp Hb22) in "S22".
    set (M22 := <[Regidx (mword_of_int 22 : mword 5) := regval_into_reg v22]> M21).
    assert (HM22sp : M22 !!! Regidx csp_rs1 = spd)
      by (rewrite /M22 upd_ne; [exact HM21sp | reg_neq]).
    assert (Hp8 : add_vec_int (mword_of_int (PK + B + 8) : mword 64) 2 = mword_of_int (PK + B + 10))
      by (unfold add_vec_int; rewrite moi_add; f_equal; lia).
    iEval (rewrite Hp8) in "Hpc".
    iApply (wp_cldsp_s_sconf γ Φ (mword_of_int (PK + B + 10)) (mword_of_int 7 : mword 6) (mword_of_int 23 : mword 5)
              M22 (K - 24)%nat v23
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hcg Hpc I10 [S23] [-]").
    { iEval (rewrite HM22sp Hb23). iExact "S23". }
    iIntros "Hcg Hpc S23". iEval (rewrite HM22sp Hb23) in "S23".
    set (M23 := <[Regidx (mword_of_int 23 : mword 5) := regval_into_reg v23]> M22).
    assert (HM23sp : M23 !!! Regidx csp_rs1 = spd)
      by (rewrite /M23 upd_ne; [exact HM22sp | reg_neq]).
    assert (Hp10 : add_vec_int (mword_of_int (PK + B + 10) : mword 64) 2 = mword_of_int (PK + B + 12))
      by (unfold add_vec_int; rewrite moi_add; f_equal; lia).
    iEval (rewrite Hp10) in "Hpc".
    iApply (wp_cldsp_s_sconf γ Φ (mword_of_int (PK + B + 12)) (mword_of_int 6 : mword 6) (mword_of_int 24 : mword 5)
              M23 (K - 24)%nat v24
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hcg Hpc I12 [S24] [-]").
    { iEval (rewrite HM23sp Hb24). iExact "S24". }
    iIntros "Hcg Hpc S24". iEval (rewrite HM23sp Hb24) in "S24".
    set (M24 := <[Regidx (mword_of_int 24 : mword 5) := regval_into_reg v24]> M23).
    assert (HM24sp : M24 !!! Regidx csp_rs1 = spd)
      by (rewrite /M24 upd_ne; [exact HM23sp | reg_neq]).
    assert (Hp12 : add_vec_int (mword_of_int (PK + B + 12) : mword 64) 2 = mword_of_int (PK + B + 14))
      by (unfold add_vec_int; rewrite moi_add; f_equal; lia).
    iEval (rewrite Hp12) in "Hpc".
    iApply (wp_cldsp_s_sconf γ Φ (mword_of_int (PK + B + 14)) (mword_of_int 4 : mword 6) (mword_of_int 26 : mword 5)
              M24 (K - 24)%nat v26
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hcg Hpc I14 [S26] [-]").
    { iEval (rewrite HM24sp Hb26). iExact "S26". }
    iIntros "Hcg Hpc S26". iEval (rewrite HM24sp Hb26) in "S26".
    set (M26 := <[Regidx (mword_of_int 26 : mword 5) := regval_into_reg v26]> M24).
    assert (HM26sp : M26 !!! Regidx csp_rs1 = spd)
      by (rewrite /M26 upd_ne; [exact HM24sp | reg_neq]).
    assert (Hp14 : add_vec_int (mword_of_int (PK + B + 14) : mword 64) 2 = mword_of_int (PK + B + 16))
      by (unfold add_vec_int; rewrite moi_add; f_equal; lia).
    iEval (rewrite Hp14) in "Hpc".
    iApply (wp_cldsp_s_sconf γ Φ (mword_of_int (PK + B + 16)) (mword_of_int 3 : mword 6) (mword_of_int 27 : mword 5)
              M26 (K - 24)%nat v27
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hcg Hpc I16 [S27] [-]").
    { iEval (rewrite HM26sp Hb27). iExact "S27". }
    iIntros "Hcg Hpc S27". iEval (rewrite HM26sp Hb27) in "S27".
    set (M27 := <[Regidx (mword_of_int 27 : mword 5) := regval_into_reg v27]> M26).
    assert (HM27sp : M27 !!! Regidx csp_rs1 = spd)
      by (rewrite /M27 upd_ne; [exact HM26sp | reg_neq]).
    assert (Hp16 : add_vec_int (mword_of_int (PK + B + 16) : mword 64) 2 = mword_of_int (PK + B + 18))
      by (unfold add_vec_int; rewrite moi_add; f_equal; lia).
    iEval (rewrite Hp16) in "Hpc".
    iApply ("Hcont" $! M27 with "[%] Hcg Hpc [S9 S19 S20 S21 S22 S23 S24 S26 S27]").
    { split.
      { intros c N9 N19 N20 N21 N22 N23 N24 N26 N27.
        rewrite /M27 upd_ne; [| congruence].
        rewrite /M26 upd_ne; [| congruence].
        rewrite /M24 upd_ne; [| congruence].
        rewrite /M23 upd_ne; [| congruence].
        rewrite /M22 upd_ne; [| congruence].
        rewrite /M21 upd_ne; [| congruence].
        rewrite /M20 upd_ne; [| congruence].
        rewrite /M19 upd_ne; [| congruence].
        rewrite /M9 upd_ne; [reflexivity | congruence]. }
      split.
      {rewrite /M27 upd_ne; [| reg_neq]. rewrite /M26 upd_ne; [| reg_neq]. rewrite /M24 upd_ne; [| reg_neq]. rewrite /M23 upd_ne; [| reg_neq]. rewrite /M22 upd_ne; [| reg_neq]. rewrite /M21 upd_ne; [| reg_neq]. rewrite /M20 upd_ne; [| reg_neq]. rewrite /M19 upd_ne; [| reg_neq]. rewrite /M9 upd_eq; reflexivity. }
      split.
      {rewrite /M27 upd_ne; [| reg_neq]. rewrite /M26 upd_ne; [| reg_neq]. rewrite /M24 upd_ne; [| reg_neq]. rewrite /M23 upd_ne; [| reg_neq]. rewrite /M22 upd_ne; [| reg_neq]. rewrite /M21 upd_ne; [| reg_neq]. rewrite /M20 upd_ne; [| reg_neq]. rewrite /M19 upd_eq; reflexivity. }
      split.
      {rewrite /M27 upd_ne; [| reg_neq]. rewrite /M26 upd_ne; [| reg_neq]. rewrite /M24 upd_ne; [| reg_neq]. rewrite /M23 upd_ne; [| reg_neq]. rewrite /M22 upd_ne; [| reg_neq]. rewrite /M21 upd_ne; [| reg_neq]. rewrite /M20 upd_eq; reflexivity. }
      split.
      {rewrite /M27 upd_ne; [| reg_neq]. rewrite /M26 upd_ne; [| reg_neq]. rewrite /M24 upd_ne; [| reg_neq]. rewrite /M23 upd_ne; [| reg_neq]. rewrite /M22 upd_ne; [| reg_neq]. rewrite /M21 upd_eq; reflexivity. }
      split.
      {rewrite /M27 upd_ne; [| reg_neq]. rewrite /M26 upd_ne; [| reg_neq]. rewrite /M24 upd_ne; [| reg_neq]. rewrite /M23 upd_ne; [| reg_neq]. rewrite /M22 upd_eq; reflexivity. }
      split.
      {rewrite /M27 upd_ne; [| reg_neq]. rewrite /M26 upd_ne; [| reg_neq]. rewrite /M24 upd_ne; [| reg_neq]. rewrite /M23 upd_eq; reflexivity. }
      split.
      {rewrite /M27 upd_ne; [| reg_neq]. rewrite /M26 upd_ne; [| reg_neq]. rewrite /M24 upd_eq; reflexivity. }
      split.
      {rewrite /M27 upd_ne; [| reg_neq]. rewrite /M26 upd_eq; reflexivity. }
      { rewrite /M27 upd_eq; reflexivity. }
    }
    rewrite /pk_saved. iFrame.
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
    pk_cs_kept m mc ->
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
    - destruct Hagree as (Ktp & K9 & K19 & K20 & K21 & K22 & K23 & K24 & K25 & K26 & K27).
      assert (Hthread : forall c : mword 5,
                c <> csp_rs1 -> c <> s0_idx -> c <> s2_idx ->
                c <> ra_idx -> c <> a0_idx -> c <> a5_idx ->
                mc !!! Regidx c = m !!! Regidx c -> E7 !!! Regidx c = m !!! Regidx c).
      { intros c Nsp N8 N18 N1 N10 N15 Hc.
        rewrite /E7 upd_ne; [| congruence]. rewrite /E6 upd_ne; [| congruence].
        rewrite /E5 upd_ne; [| congruence]. rewrite /E4 upd_ne; [| congruence].
        rewrite /E3 upd_ne; [| congruence]. rewrite /E2 upd_ne; [| congruence].
        rewrite /E1 upd_ne; [| congruence]. exact Hc. }
      unfold callee_saved.
      split. { rewrite /E7 upd_eq. exact Hwv. }
      split. { apply Hthread; solve [ mw_neq | exact Ktp ]. }
      split. { rewrite /E7 upd_ne; [| reg_neq]. rewrite /E6 upd_ne; [| reg_neq].
               rewrite /E5 upd_eq; reflexivity. }
      split. { apply Hthread; solve [ mw_neq | exact K9 ]. }
      split. { rewrite /E7 upd_ne; [| reg_neq]. rewrite /E6 upd_eq; reflexivity. }
      split. { apply Hthread; solve [ mw_neq | exact K19 ]. }
      split. { apply Hthread; solve [ mw_neq | exact K20 ]. }
      split. { apply Hthread; solve [ mw_neq | exact K21 ]. }
      split. { apply Hthread; solve [ mw_neq | exact K22 ]. }
      split. { apply Hthread; solve [ mw_neq | exact K23 ]. }
      split. { apply Hthread; solve [ mw_neq | exact K24 ]. }
      split. { apply Hthread; solve [ mw_neq | exact K25 ]. }
      split. { apply Hthread; solve [ mw_neq | exact K26 ]. }
      apply Hthread; solve [ mw_neq | exact K27 ].
    - rewrite /E7 upd_ne; [| reg_neq]. rewrite /E6 upd_ne; [| reg_neq].
      rewrite /E5 upd_ne; [| reg_neq]. rewrite /E4 upd_ne; [| reg_neq].
      rewrite /E3 upd_eq. reflexivity.
  Qed.

  (* the twelve slots that are neither ra/s0/s2 nor lazily saved *)
  Definition pk_slots_rest (sp0 : mword 64) : iProp Σ :=
    ([∗ list] k ∈ [1;2;3;4;5;6;7;8;19;22;23;24]%nat,
       ∃ w : mword 64, (pa_stk sp0 k) ↦₈ w)%I.

  (* the frame as the LOOP holds it: the nine lazily-saved slots are concrete,
     because the restore block reads them back. *)
  Lemma pk_frame_of_saved (sp0 ra0 s00 s20 : mword 64) (v9 v19 v20 v21 v22 v23 v24 v26 v27 : mword 64) :
    (pa_stk sp0 9) ↦₈ ra0 -∗ (pa_stk sp0 10) ↦₈ s00 -∗ (pa_stk sp0 12) ↦₈ s20 -∗
    pk_saved sp0 v9 v19 v20 v21 v22 v23 v24 v26 v27 -∗ pk_slots_rest sp0 -∗
    pk_frame sp0 ra0 s00 s20.
  Proof.
    rewrite /pk_frame /pk_slots /pk_saved /pk_slots_rest.
    iIntros "H9 H10 H12 (S9 & S19 & S20 & S21 & S22 & S23 & S24 & S26 & S27) Hr".
    cbn [big_opL].
    iDestruct "Hr" as "(K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K19 & K22 & K23 & K24 & _)".
    iFrame "H9 H10 H12 K1 K2 K3 K4 K5 K6 K7 K8 K19 K22 K23 K24".
    iSplitL "S9". { iExists v9. iExact "S9". }
    iSplitL "S19". { iExists v19. iExact "S19". }
    iSplitL "S20". { iExists v20. iExact "S20". }
    iSplitL "S21". { iExists v21. iExact "S21". }
    iSplitL "S22". { iExists v22. iExact "S22". }
    iSplitL "S23". { iExists v23. iExact "S23". }
    iSplitL "S24". { iExists v24. iExact "S24". }
    iSplitL "S26". { iExists v26. iExact "S26". }
    iExists v27. iExact "S27".
  Qed.

  (* the nine [instr] facts, at the two addresses the block sits at *)
  Lemma pk_restore_at_24e : kernel_text -∗ pk_restore_instrs 0x24e.
  Proof.
    iIntros "#Ht". rewrite /pk_restore_instrs /pk_ld.
    iSplitR; [iApply (pki_24e with "Ht") | ].
    iSplitR; [iApply (pki_250 with "Ht") | ].
    iSplitR; [iApply (pki_252 with "Ht") | ].
    iSplitR; [iApply (pki_254 with "Ht") | ].
    iSplitR; [iApply (pki_256 with "Ht") | ].
    iSplitR; [iApply (pki_258 with "Ht") | ].
    iSplitR; [iApply (pki_25a with "Ht") | ].
    iSplitR; [iApply (pki_25c with "Ht") | ].
    iApply (pki_25e with "Ht").
  Qed.

  Lemma pk_restore_at_276 : kernel_text -∗ pk_restore_instrs 0x276.
  Proof.
    iIntros "#Ht". rewrite /pk_restore_instrs /pk_ld.
    iSplitR; [iApply (pki_276 with "Ht") | ].
    iSplitR; [iApply (pki_278 with "Ht") | ].
    iSplitR; [iApply (pki_27a with "Ht") | ].
    iSplitR; [iApply (pki_27c with "Ht") | ].
    iSplitR; [iApply (pki_27e with "Ht") | ].
    iSplitR; [iApply (pki_280 with "Ht") | ].
    iSplitR; [iApply (pki_282 with "Ht") | ].
    iSplitR; [iApply (pki_284 with "Ht") | ].
    iApply (pki_286 with "Ht").
  Qed.

  (* ================================================================== *)
  (*  THE EXIT: restore block -> epilogue.  Two entry addresses, one     *)
  (*  proof body; the second block only differs by the [j] that follows. *)
  (* ================================================================== *)

  Lemma wp_printk_exit (γ : gname) (Φ : mval -> iProp Σ)
      (m mc : regfile) (K : nat) (B : Z) (pv : mword 32) (dqm : dfrac) (R : iProp Σ) :
    let sp0 := m !!! Regidx csp_rs1 in
    let spd := add_vec sp0 (sign_extend' 64 (caddi16sp_imm (mword_of_int 52 : mword 6))) in
    (24 <= K)%nat ->
    eq_vec (sign_extend' 64 pv) zero_reg = false ->
    mc !!! Regidx csp_rs1 = spd ->
    mc !!! Regidx (mword_of_int 4 : mword 5) = m !!! Regidx (mword_of_int 4 : mword 5) ->
    mc !!! Regidx (mword_of_int 25 : mword 5) = m !!! Regidx (mword_of_int 25 : mword 5) ->
    sie_cap_gpr γ mc (K - 24)%nat -∗
    kernel_text -∗
    pk_restore_instrs B -∗
    pc_is (mword_of_int (PK + B + 0) : mword 64) -∗
    ⌜ mword_of_int (PK + B + 18) = (mword_of_int (PK + 0x260) : mword 64) ⌝ -∗
    (pa_stk sp0 9) ↦₈ (m !!! Regidx ra_idx) -∗
    (pa_stk sp0 10) ↦₈ (m !!! Regidx s0_idx) -∗
    (pa_stk sp0 12) ↦₈ (m !!! Regidx s2_idx) -∗
    pk_saved sp0 (m !!! Regidx (mword_of_int 9 : mword 5)) (m !!! Regidx (mword_of_int 19 : mword 5)) (m !!! Regidx (mword_of_int 20 : mword 5)) (m !!! Regidx (mword_of_int 21 : mword 5)) (m !!! Regidx (mword_of_int 22 : mword 5)) (m !!! Regidx (mword_of_int 23 : mword 5)) (m !!! Regidx (mword_of_int 24 : mword 5)) (m !!! Regidx (mword_of_int 26 : mword 5)) (m !!! Regidx (mword_of_int 27 : mword 5)) -∗
    pk_slots_rest sp0 -∗
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
    intros sp0 spd HK Hpv Hsp Htp Hs9.
    iIntros "Hcg #Htext Hinstrs Hpc %Hnext H9 H10 H12 Hsv Hrest Hpanicking HR Hcont".
    iApply (wp_printk_restore γ Φ mc K B sp0 (m !!! Regidx (mword_of_int 9 : mword 5)) (m !!! Regidx (mword_of_int 19 : mword 5)) (m !!! Regidx (mword_of_int 20 : mword 5)) (m !!! Regidx (mword_of_int 21 : mword 5)) (m !!! Regidx (mword_of_int 22 : mword 5)) (m !!! Regidx (mword_of_int 23 : mword 5)) (m !!! Regidx (mword_of_int 24 : mword 5)) (m !!! Regidx (mword_of_int 26 : mword 5)) (m !!! Regidx (mword_of_int 27 : mword 5)) Hsp
              with "Hcg Hinstrs Hpc Hsv [-]").
    iIntros (mf) "%Hpost Hcg Hpc Hsv".
    destruct Hpost as (Hkeep & E9 & E19 & E20 & E21 & E22 & E23 & E24 & E26 & E27).
    iEval (rewrite Hnext) in "Hpc".
    iDestruct (pk_frame_of_saved sp0 (m !!! Regidx ra_idx) (m !!! Regidx s0_idx)
                 (m !!! Regidx s2_idx) (m !!! Regidx (mword_of_int 9 : mword 5)) (m !!! Regidx (mword_of_int 19 : mword 5)) (m !!! Regidx (mword_of_int 20 : mword 5)) (m !!! Regidx (mword_of_int 21 : mword 5)) (m !!! Regidx (mword_of_int 22 : mword 5)) (m !!! Regidx (mword_of_int 23 : mword 5)) (m !!! Regidx (mword_of_int 24 : mword 5)) (m !!! Regidx (mword_of_int 26 : mword 5)) (m !!! Regidx (mword_of_int 27 : mword 5)) with "H9 H10 H12 Hsv Hrest") as "Hfr".
    assert (Hkp : forall c : mword 5,
              c <> mword_of_int 9 -> c <> mword_of_int 19 -> c <> mword_of_int 20 ->
              c <> mword_of_int 21 -> c <> mword_of_int 22 -> c <> mword_of_int 23 ->
              c <> mword_of_int 24 -> c <> mword_of_int 26 -> c <> mword_of_int 27 ->
              mf !!! Regidx c = mc !!! Regidx c) by exact Hkeep.
    assert (Hmfsp : mf !!! Regidx csp_rs1 = spd).
    { rewrite (Hkp csp_rs1 ltac:(mw_neq) ltac:(mw_neq) ltac:(mw_neq) ltac:(mw_neq)
                 ltac:(mw_neq) ltac:(mw_neq) ltac:(mw_neq) ltac:(mw_neq) ltac:(mw_neq)).
      exact Hsp. }
    (* the two registers the block does NOT restore (tp and s9) come from the
       caller; the other nine are its own posts.  [Hkp] is applied at an
       EXPLICIT index -- with [_] the inline [mw_neq] would run against an
       evar. *)
    assert (Hcsk : pk_cs_kept m mf).
    { unfold pk_cs_kept. repeat split.
      - rewrite (Hkp (mword_of_int 4 : mword 5) ltac:(mw_neq) ltac:(mw_neq) ltac:(mw_neq) ltac:(mw_neq) ltac:(mw_neq) ltac:(mw_neq) ltac:(mw_neq) ltac:(mw_neq) ltac:(mw_neq)). exact Htp.
      - exact E9.
      - exact E19.
      - exact E20.
      - exact E21.
      - exact E22.
      - exact E23.
      - exact E24.
      - rewrite (Hkp (mword_of_int 25 : mword 5) ltac:(mw_neq) ltac:(mw_neq) ltac:(mw_neq) ltac:(mw_neq) ltac:(mw_neq) ltac:(mw_neq) ltac:(mw_neq) ltac:(mw_neq) ltac:(mw_neq)). exact Hs9.
      - exact E26.
      - exact E27. }
    iApply (wp_printk_epi γ Φ m mf K pv pv dqm dqm R HK Hpv Hmfsp Hcsk
              with "Hcg Htext Hpc Hfr Hpanicking HR Hcont").
  Qed.

  (* ================================================================== *)
  (*  THE SETUP (0x1e .. 0x62): the panicking test, the va_list cursor,  *)
  (*  the first format byte, the nine LAZY saves and the six hoisted     *)
  (*  constants -- ending either at the epilogue (empty format string,   *)
  (*  before any lazy save) or at the loop head with everything in       *)
  (*  place.                                                             *)
  (* ================================================================== *)

  (* the six constants gcc hoists out of the loop: '%', 10, 'd', 'u', 'x', 'p' *)
  Definition pk_consts (mq : regfile) : Prop :=
    mq !!! Regidx (mword_of_int 19 : mword 5) = (mword_of_int 37 : mword 64) /\
    mq !!! Regidx (mword_of_int 22 : mword 5) = (mword_of_int 10 : mword 64) /\
    mq !!! Regidx (mword_of_int 23 : mword 5) = (mword_of_int 100 : mword 64) /\
    mq !!! Regidx (mword_of_int 24 : mword 5) = (mword_of_int 117 : mword 64) /\
    mq !!! Regidx (mword_of_int 26 : mword 5) = (mword_of_int 120 : mword 64) /\
    mq !!! Regidx (mword_of_int 27 : mword 5) = (mword_of_int 112 : mword 64).

  (* byte [j] of the format string, AT [mword 8] -- the ascription has to live
     in a definition: written inline, [(cstring_bytes f !!! j : mword 8)] sends
     the elaborator looking for a [LookupTotal nat (mword ?n)] instance. *)
  Definition pk_fbyte (f : string) (j : nat) : mword 8 := cstring_bytes f !!! j.

  (* a zero-extended byte is zero exactly when the byte is: the format loop's
     terminator test.  The [bv_zero_extend_unsigned] side condition is an [N]
     inequality, which [lia] cannot see under the bitvector zify hook. *)
  Lemma zext8_zero (b : mword 8) :
    eq_vec (zero_extend' 64 b) (zero_reg : mword 64) = true -> b = (mword_of_int 0 : mword 8).
  Proof.
    intro H. apply eq_vec_true_iff in H.
    apply (f_equal bv_unsigned) in H.
    unfold zero_extend', Operators_mwords.zero_extend, Operators_mwords.extz_vec,
      SailStdpp.Values.to_word, to_word, get_word, MachineWord.MachineWord.zero_extend in H.
    rewrite bv_zero_extend_unsigned in H; [ | vm_compute; intro Hc; discriminate Hc ].
    change (bv_unsigned (zero_reg : mword 64)) with 0 in H.
    apply bv_eq. rewrite H. vm_compute. reflexivity.
  Qed.

  (* one byte of a C string, borrowed and returned *)
  Lemma pk_str_byte (a : Arch.pa) (dq : dfrac) (f : string) (j : nat) :
    (j < length (cstring_bytes f))%nat ->
    a ↦ₛ{dq} f ⊢
    (pa_add a j) ↦ₘ{dq} (pk_fbyte f j) ∗
    ((pa_add a j) ↦ₘ{dq} (pk_fbyte f j) -∗ a ↦ₛ{dq} f).
  Proof.
    intro Hj. rewrite /string_pointsto.
    iIntros "H".
    iDestruct (big_sepL_lookup_acc _ _ j (pk_fbyte f j) with "H") as "[Hb Hcl]".
    { rewrite /pk_fbyte. apply list_lookup_lookup_total_lt. exact Hj. }
    iFrame "Hb Hcl".
  Qed.

  Lemma wp_printk_setup (γ : gname) (Φ : mval -> iProp Σ)
      (m mp : regfile) (K : nat) (pv : mword 32) (dqm dqf : dfrac)
      (f : string) (R : iProp Σ) :
    let sp0 := m !!! Regidx csp_rs1 in
    let spd := add_vec sp0 (sign_extend' 64 (caddi16sp_imm (mword_of_int 52 : mword 6))) in
    let s0v := add_vec sp0 (sign_extend' 64 (mword_of_int (-64) : mword 12)) in
    let fmt := m !!! Regidx a0_idx in
    (24 <= K)%nat ->
    eq_vec (sign_extend' 64 pv) zero_reg = false ->
    nonul f = true ->
    mp !!! Regidx csp_rs1 = spd ->
    mp !!! Regidx s0_idx = s0v ->
    mp !!! Regidx s2_idx = fmt ->
    (forall c : mword 5, c <> csp_rs1 -> c <> s0_idx -> c <> s2_idx ->
       mp !!! Regidx c = m !!! Regidx c) ->
    sie_cap_gpr γ mp (K - 24)%nat -∗
    kernel_text -∗
    pc_is (mword_of_int (PK + 0x1e) : mword 64) -∗
    (mword_of_int KernelSyms.panicking : mword 64) ↦₄{ dqm } pv -∗
    fmt ↦ₛ{ dqf } f -∗
    (pa_stk sp0 9) ↦₈ (m !!! Regidx ra_idx) -∗
    (pa_stk sp0 10) ↦₈ (m !!! Regidx s0_idx) -∗
    (pa_stk sp0 12) ↦₈ (m !!! Regidx s2_idx) -∗
    pk_va sp0 m -∗
    ([∗ list] k ∈ [8;11;13;14;15;16;17;18;19;20;21;22;23;24]%nat,
       ∃ w : mword 64, (pa_stk sp0 k) ↦₈ w) -∗
    R -∗
    (* (a) the empty format string: no lazy save has happened, so the frame is
       already in [pk_frame] shape and the epilogue can run at once *)
    ( ∀ mf,
      sie_cap_gpr γ mf K -∗
      pc_is (ret_pc (m !!! Regidx ra_idx)) -∗
      ⌜ callee_saved m mf /\ mf !!! Regidx ra_idx = m !!! Regidx ra_idx
        /\ mf !!! Regidx a0_idx = zero_reg ⌝ -∗
      (mword_of_int KernelSyms.panicking : mword 64) ↦₄{ dqm } pv -∗
      fmt ↦ₛ{ dqf } f -∗ R -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    (* (b) a nonempty one: the loop head, with i = 0 and a0 = fmt[0] *)
    ( ∀ (mq : regfile),
      ⌜ mq !!! Regidx csp_rs1 = spd
        /\ mq !!! Regidx s0_idx = s0v
        /\ mq !!! Regidx s2_idx = fmt
        /\ mq !!! Regidx (mword_of_int 20 : mword 5) = zero_reg
        /\ mq !!! Regidx a0_idx = zero_extend' 64 (pk_fbyte f 0%nat)
        /\ pk_consts mq
        /\ (forall c : mword 5, c <> csp_rs1 -> c <> s0_idx -> c <> s2_idx ->
              c <> mword_of_int 15 -> c <> a0_idx -> c <> mword_of_int 19 ->
              c <> mword_of_int 20 -> c <> mword_of_int 22 -> c <> mword_of_int 23 ->
              c <> mword_of_int 24 -> c <> mword_of_int 26 -> c <> mword_of_int 27 ->
              mq !!! Regidx c = m !!! Regidx c) ⌝ -∗
      sie_cap_gpr γ mq (K - 24)%nat -∗
      pc_is (mword_of_int (PK + 0x86) : mword 64) -∗
      (mword_of_int KernelSyms.panicking : mword 64) ↦₄{ dqm } pv -∗
      fmt ↦ₛ{ dqf } f -∗
      (pa_stk sp0 9) ↦₈ (m !!! Regidx ra_idx) -∗
      (pa_stk sp0 10) ↦₈ (m !!! Regidx s0_idx) -∗
      (pa_stk sp0 12) ↦₈ (m !!! Regidx s2_idx) -∗
      pk_va sp0 m -∗
      pk_saved sp0 (m !!! Regidx (mword_of_int 9 : mword 5)) (m !!! Regidx (mword_of_int 19 : mword 5))
        (m !!! Regidx (mword_of_int 20 : mword 5)) (m !!! Regidx (mword_of_int 21 : mword 5))
        (m !!! Regidx (mword_of_int 22 : mword 5)) (m !!! Regidx (mword_of_int 23 : mword 5))
        (m !!! Regidx (mword_of_int 24 : mword 5)) (m !!! Regidx (mword_of_int 26 : mword 5))
        (m !!! Regidx (mword_of_int 27 : mword 5)) -∗
      (∃ w : mword 64, (pa_stk sp0 8) ↦₈ w) -∗
      (∃ w : mword 64, (pa_stk sp0 19) ↦₈ w) -∗
      (∃ w : mword 64, (pa_stk sp0 22) ↦₈ w) -∗
      (pa_stk sp0 23) ↦₈ (add_vec s0v (sign_extend' 64 (mword_of_int 8 : mword 12))) -∗
      (∃ w : mword 64, (pa_stk sp0 24) ↦₈ w) -∗
      R -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    intros sp0 spd s0v fmt HK Hpv Hnn Hsp Hs0 Hs2 Hkept.
    iIntros "Hcg #Htext Hpc Hpanicking Hfmt H9 H10 H12 Hva Hrest HR Kend Kloop".
    iPoseProof (pki_1e with "Htext") as "Hi1e".
    iPoseProof (pki_22 with "Htext") as "Hi22".
    iPoseProof (pki_26 with "Htext") as "Hi26".
    iPoseProof (pki_28 with "Htext") as "Hi28".
    iPoseProof (pki_2c with "Htext") as "Hi2c".
    iPoseProof (pki_30 with "Htext") as "Hi30".
    iPoseProof (pki_34 with "Htext") as "Hi34".
    iPoseProof (pki_38 with "Htext") as "Hi38".
    iPoseProof (pki_3a with "Htext") as "Hi3a".
    iPoseProof (pki_3c with "Htext") as "Hi3c".
    iPoseProof (pki_3e with "Htext") as "Hi3e".
    iPoseProof (pki_40 with "Htext") as "Hi40".
    iPoseProof (pki_42 with "Htext") as "Hi42".
    iPoseProof (pki_44 with "Htext") as "Hi44".
    iPoseProof (pki_46 with "Htext") as "Hi46".
    iPoseProof (pki_48 with "Htext") as "Hi48".
    iPoseProof (pki_4a with "Htext") as "Hi4a".
    iPoseProof (pki_4c with "Htext") as "Hi4c".
    iPoseProof (pki_50 with "Htext") as "Hi50".
    iPoseProof (pki_54 with "Htext") as "Hi54".
    iPoseProof (pki_58 with "Htext") as "Hi58".
    iPoseProof (pki_5c with "Htext") as "Hi5c".
    iPoseProof (pki_5e with "Htext") as "Hi5e".
    iPoseProof (pki_62 with "Htext") as "Hi62".
    iDestruct "Hrest" as "(T8 & T11 & T13 & T14 & T15 & T16 & T17 & T18 & T19 & T20 & T21 & T22 & T23 & T24 & _)".
    iDestruct "T11" as (w11) "S9". iDestruct "T13" as (w13) "S19".
    iDestruct "T14" as (w14) "S20". iDestruct "T15" as (w15) "S21".
    iDestruct "T16" as (w16) "S22". iDestruct "T17" as (w17) "S23".
    iDestruct "T18" as (w18) "S24". iDestruct "T20" as (w20) "S26".
    iDestruct "T21" as (w21) "S27". iDestruct "T23" as (w23) "Hap".
    assert (Hpush : spd = pa_stk sp0 24).
    { unfold spd, pa_stk, add_vec_int. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hbs11 : add_vec spd (zero_extend' 64 (concat_vec (mword_of_int 13 : mword 6) ('b"000"))) = pa_stk sp0 11).
    { rewrite Hpush. unfold pa_stk, add_vec_int. rewrite pa_stk_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hbs13 : add_vec spd (zero_extend' 64 (concat_vec (mword_of_int 11 : mword 6) ('b"000"))) = pa_stk sp0 13).
    { rewrite Hpush. unfold pa_stk, add_vec_int. rewrite pa_stk_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hbs14 : add_vec spd (zero_extend' 64 (concat_vec (mword_of_int 10 : mword 6) ('b"000"))) = pa_stk sp0 14).
    { rewrite Hpush. unfold pa_stk, add_vec_int. rewrite pa_stk_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hbs15 : add_vec spd (zero_extend' 64 (concat_vec (mword_of_int 9 : mword 6) ('b"000"))) = pa_stk sp0 15).
    { rewrite Hpush. unfold pa_stk, add_vec_int. rewrite pa_stk_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hbs16 : add_vec spd (zero_extend' 64 (concat_vec (mword_of_int 8 : mword 6) ('b"000"))) = pa_stk sp0 16).
    { rewrite Hpush. unfold pa_stk, add_vec_int. rewrite pa_stk_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hbs17 : add_vec spd (zero_extend' 64 (concat_vec (mword_of_int 7 : mword 6) ('b"000"))) = pa_stk sp0 17).
    { rewrite Hpush. unfold pa_stk, add_vec_int. rewrite pa_stk_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hbs18 : add_vec spd (zero_extend' 64 (concat_vec (mword_of_int 6 : mword 6) ('b"000"))) = pa_stk sp0 18).
    { rewrite Hpush. unfold pa_stk, add_vec_int. rewrite pa_stk_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hbs20 : add_vec spd (zero_extend' 64 (concat_vec (mword_of_int 4 : mword 6) ('b"000"))) = pa_stk sp0 20).
    { rewrite Hpush. unfold pa_stk, add_vec_int. rewrite pa_stk_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hbs21 : add_vec spd (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000"))) = pa_stk sp0 21).
    { rewrite Hpush. unfold pa_stk, add_vec_int. rewrite pa_stk_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    (* +0x1e/0x22 auipc/lw a5 : panicking *)
    iApply (wp_auipc_s_sconf γ Φ (mword_of_int (PK + 0x1e)) a5_idx (mword_of_int 10 : mword 20)
              mp (K - 24)%nat ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi1e [-]").
    iIntros "Hcg Hpc".
    set (Q1 := <[Regidx a5_idx := regval_into_reg (add_vec (mword_of_int (PK + 0x1e) : mword 64) (auipc_off (mword_of_int 10 : mword 20)))]> mp).
    assert (Hpan : add_vec (Q1 !!! Regidx a5_idx) (sign_extend' 64 (mword_of_int 3338 : mword 12))
                   = (mword_of_int KernelSyms.panicking : mword 64)).
    { rewrite /Q1 upd_eq. unfold regval_into_reg. apply bv_eq; vm_compute; reflexivity. }
    assert (Hp22 : add_vec_int (mword_of_int (PK + 0x1e) : mword 64) 4 = mword_of_int (PK + 0x22)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp22) in "Hpc".
    iEval (rewrite -Hpan) in "Hpanicking".
    iApply (wp_lw_s_sconf γ Φ (mword_of_int (PK + 0x22)) a5_idx a5_idx (mword_of_int 3338 : mword 12)
              Q1 (K - 24)%nat pv ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi22 Hpanicking [-]").
    iIntros "Hcg Hpc Hpanicking". iEval (rewrite Hpan) in "Hpanicking".
    set (Q2 := <[Regidx a5_idx := regval_into_reg (sign_extend' 64 pv)]> Q1).
    assert (Hp26 : add_vec_int (mword_of_int (PK + 0x22) : mword 64) 4 = mword_of_int (PK + 0x26)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp26) in "Hpc".
    (* +0x26 beqz a5 : NOT taken -- the panic path takes no lock *)
    iApply (wp_cbeqz_fall_s_sconf γ Φ (mword_of_int (PK + 0x26)) (mword_of_int 31 : mword 8)
              (Cregidx (mword_of_int 7)) a5_idx Q2 (K - 24)%nat
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
              ltac:(rewrite /Q2 upd_eq; exact Hpv)
              with "Hcg Hpc Hi26 [-]").
    iIntros "Hcg Hpc".
    assert (Hp28 : add_vec_int (mword_of_int (PK + 0x26) : mword 64) 2 = mword_of_int (PK + 0x28)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp28) in "Hpc".
    (* +0x28 addi a5,s0,8 : the va_list cursor *)
    assert (HQ2s0 : Q2 !!! Regidx s0_idx = s0v).
    { rewrite /Q2 upd_ne; [| reg_neq]. rewrite /Q1 upd_ne; [exact Hs0 | reg_neq]. }
    iApply (wp_addi4_s_sconf γ Φ (mword_of_int (PK + 0x28)) a5_idx s0_idx (mword_of_int 8 : mword 12)
              Q2 (K - 24)%nat ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi28 [-]").
    iIntros "Hcg Hpc".
    set (Q3 := <[Regidx a5_idx := regval_into_reg (add_vec (Q2 !!! Regidx s0_idx) (sign_extend' 64 (mword_of_int 8 : mword 12)))]> Q2).
    assert (HQ3a5 : Q3 !!! Regidx a5_idx = add_vec s0v (sign_extend' 64 (mword_of_int 8 : mword 12)))
      by (rewrite /Q3 upd_eq; unfold regval_into_reg; rewrite HQ2s0; reflexivity).
    assert (HQ3s0 : Q3 !!! Regidx s0_idx = s0v) by (rewrite /Q3 upd_ne; [exact HQ2s0 | reg_neq]).
    assert (Hp2c : add_vec_int (mword_of_int (PK + 0x28) : mword 64) 4 = mword_of_int (PK + 0x2c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp2c) in "Hpc".
    (* +0x2c sd a5,-120(s0) : ap -> slot 23 *)
    assert (Hap23 : add_vec (Q3 !!! Regidx s0_idx) (sign_extend' 64 (mword_of_int 3976 : mword 12)) = pa_stk sp0 23).
    { rewrite HQ3s0. unfold s0v, pa_stk, add_vec_int. rewrite pa_stk_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    iApply (wp_sd_s_sconf γ Φ (mword_of_int (PK + 0x2c)) a5_idx s0_idx (mword_of_int 3976 : mword 12)
              Q3 (K - 24)%nat w23 with "Hcg Hpc Hi2c [Hap] [-]").
    { iEval (rewrite Hap23). iExact "Hap". }
    iIntros "Hcg Hpc Hap". iEval (rewrite Hap23 HQ3a5) in "Hap".
    assert (Hp30 : add_vec_int (mword_of_int (PK + 0x2c) : mword 64) 4 = mword_of_int (PK + 0x30)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp30) in "Hpc".
    (* +0x30 lbu a0,0(s2) : the first format byte *)
    assert (HQ3s2 : Q3 !!! Regidx s2_idx = fmt).
    { rewrite /Q3 upd_ne; [| reg_neq]. rewrite /Q2 upd_ne; [| reg_neq].
      rewrite /Q1 upd_ne; [exact Hs2 | reg_neq]. }
    assert (Hlen0 : (0 < length (cstring_bytes f))%nat).
    { rewrite cstring_bytes_length. lia. }
    iDestruct (pk_str_byte fmt dqf f 0%nat Hlen0 with "Hfmt") as "[Hb0 Hfcl]".
    assert (Hb0a : add_vec (Q3 !!! Regidx s2_idx) (sign_extend' 64 (mword_of_int 0 : mword 12)) = pa_add fmt 0).
    { rewrite HQ3s2 pa_add_0.
      replace (sign_extend' 64 (mword_of_int 0 : mword 12)) with (mword_of_int 0 : mword 64)
        by (apply bv_eq; vm_compute; reflexivity).
      apply kv_addv_zero. }
    iApply (wp_lbu_s_sconf γ Φ (mword_of_int (PK + 0x30)) a0_idx s2_idx (mword_of_int 0 : mword 12)
              Q3 (K - 24)%nat (pk_fbyte f 0%nat)
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi30 [Hb0] [-]").
    { iEval (rewrite Hb0a). iExact "Hb0". }
    iIntros "Hcg Hpc Hb0". iEval (rewrite Hb0a) in "Hb0".
    iDestruct ("Hfcl" with "Hb0") as "Hfmt".
    set (Q4 := <[Regidx a0_idx := regval_into_reg (zero_extend' 64 (pk_fbyte f 0%nat))]> Q3).
    assert (Hp34 : add_vec_int (mword_of_int (PK + 0x30) : mword 64) 4 = mword_of_int (PK + 0x34)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp34) in "Hpc".
    (* +0x34 beqz a0 : the empty format string leaves at once *)
    destruct (eq_vec (Q4 !!! Regidx a0_idx) zero_reg) eqn:Hz.
    - (* ---- f = "" : straight to the epilogue ---- *)
      iApply (wp_beqz_x0_taken_s_sconf γ Φ (mword_of_int (PK + 0x34)) (mword_of_int 556 : mword 13)
                a0_idx Q4 (K - 24)%nat ltac:(vm_compute; discriminate) Hz
                ltac:(vm_compute; reflexivity)
                with "Hcg Hpc Hi34 [-]").
      iNext. iIntros "Hcg Hpc".
      assert (Htgte : add_vec (mword_of_int (PK + 0x34) : mword 64) (sign_extend' 64 (mword_of_int 556 : mword 13)) = mword_of_int (PK + 0x260)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Htgte) in "Hpc".
      iAssert (pk_frame sp0 (m !!! Regidx ra_idx) (m !!! Regidx s0_idx) (m !!! Regidx s2_idx))
        with "[H9 H10 H12 Hva S9 S19 S20 S21 S22 S23 S24 S26 S27 T8 T19 T22 Hap T24]" as "Hfr".
      { rewrite /pk_frame /pk_slots /pk_va. cbn [big_opL].
        iDestruct "Hva" as "(V7 & V6 & V5 & V4 & V3 & V2 & V1)".
        iFrame "H9 H10 H12".
        iSplitL "V1". { iExists (m !!! Regidx (mword_of_int 17 : mword 5)). iExact "V1". }
        iSplitL "V2". { iExists (m !!! Regidx (mword_of_int 16 : mword 5)). iExact "V2". }
        iSplitL "V3". { iExists (m !!! Regidx (mword_of_int 15 : mword 5)). iExact "V3". }
        iSplitL "V4". { iExists (m !!! Regidx (mword_of_int 14 : mword 5)). iExact "V4". }
        iSplitL "V5". { iExists (m !!! Regidx (mword_of_int 13 : mword 5)). iExact "V5". }
        iSplitL "V6". { iExists (m !!! Regidx (mword_of_int 12 : mword 5)). iExact "V6". }
        iSplitL "V7". { iExists (m !!! Regidx (mword_of_int 11 : mword 5)). iExact "V7". }
        iFrame "T8".
        iSplitL "S9". { iExists w11. iExact "S9". }
        iSplitL "S19". { iExists w13. iExact "S19". }
        iSplitL "S20". { iExists w14. iExact "S20". }
        iSplitL "S21". { iExists w15. iExact "S21". }
        iSplitL "S22". { iExists w16. iExact "S22". }
        iSplitL "S23". { iExists w17. iExact "S23". }
        iSplitL "S24". { iExists w18. iExact "S24". }
        iFrame "T19".
        iSplitL "S26". { iExists w20. iExact "S26". }
        iSplitL "S27". { iExists w21. iExact "S27". }
        iFrame "T22".
        iSplitL "Hap". { iExists (add_vec s0v (sign_extend' 64 (mword_of_int 8 : mword 12))). iExact "Hap". }
        iFrame "T24". }
      assert (HQ4sp : Q4 !!! Regidx csp_rs1 = spd).
      { rewrite /Q4 upd_ne; [| reg_neq]. rewrite /Q3 upd_ne; [| reg_neq].
        rewrite /Q2 upd_ne; [| reg_neq]. rewrite /Q1 upd_ne; [exact Hsp | reg_neq]. }
      assert (HQ4cs : pk_cs_kept m Q4).
      { unfold pk_cs_kept. repeat split;
          (rewrite /Q4 upd_ne; [| reg_neq]; rewrite /Q3 upd_ne; [| reg_neq];
           rewrite /Q2 upd_ne; [| reg_neq]; rewrite /Q1 upd_ne; [| reg_neq];
           apply Hkept; reg_neq). }
      iApply (wp_printk_epi γ Φ m Q4 K pv pv dqm dqm (fmt ↦ₛ{ dqf } f ∗ R)%I HK Hpv HQ4sp HQ4cs
                with "Hcg Htext Hpc Hfr Hpanicking [Hfmt HR] [-]").
      { iFrame "Hfmt HR". }
      iIntros (mf) "Hcg Hpc %Hfin Hpanicking [Hfmt HR]".
      iApply ("Kend" $! mf with "Hcg Hpc [%] Hpanicking Hfmt HR"). exact Hfin.
    - (* ---- f nonempty : the lazy saves, the constants, and into the loop ---- *)
      iApply (wp_beqz_x0_fall_s_sconf γ Φ (mword_of_int (PK + 0x34)) (mword_of_int 556 : mword 13)
                a0_idx Q4 (K - 24)%nat ltac:(vm_compute; discriminate) Hz
                with "Hcg Hpc Hi34 [-]").
      iIntros "Hcg Hpc".
      assert (Hp38 : add_vec_int (mword_of_int (PK + 0x34) : mword 64) 4 = mword_of_int (PK + 0x38)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hp38) in "Hpc".

      (* the sp fact and the "agrees with the entry map" fact, once: the nine
         stores below write MEMORY only, so the map stays [Q4] throughout *)
      assert (HQ4sp : Q4 !!! Regidx csp_rs1 = spd).
      { rewrite /Q4 upd_ne; [| reg_neq]. rewrite /Q3 upd_ne; [| reg_neq].
        rewrite /Q2 upd_ne; [| reg_neq]. rewrite /Q1 upd_ne; [exact Hsp | reg_neq]. }
      assert (HQ4k : forall c : mword 5, c <> csp_rs1 -> c <> s0_idx -> c <> s2_idx ->
                c <> a5_idx -> c <> a0_idx -> Q4 !!! Regidx c = m !!! Regidx c).
      { intros c Nsp N8 N18 N15 N10.
        rewrite /Q4 upd_ne; [| congruence]. rewrite /Q3 upd_ne; [| congruence].
        rewrite /Q2 upd_ne; [| congruence]. rewrite /Q1 upd_ne; [| congruence].
        apply Hkept; assumption. }
      (* +0x38 sd x9,104(sp) -> slot 11 *)
      iApply (wp_csdsp_s_sconf γ Φ (mword_of_int (PK + 0x38)) (mword_of_int 13 : mword 6) (mword_of_int 9 : mword 5)
                Q4 (K - 24)%nat w11 with "Hcg Hpc Hi38 [S9] [-]").
      { iEval (rewrite HQ4sp Hbs11). iExact "S9". }
      iIntros "Hcg Hpc S9". iEval (rewrite HQ4sp Hbs11) in "S9".
      iEval (rewrite (HQ4k (mword_of_int 9 : mword 5) ltac:(mw_neq) ltac:(mw_neq) ltac:(mw_neq) ltac:(mw_neq) ltac:(mw_neq))) in "S9".
      assert (Hp3a : add_vec_int (mword_of_int (PK + 0x38) : mword 64) 2 = mword_of_int (PK + 0x3a)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hp3a) in "Hpc".
      (* +0x3a sd x19,88(sp) -> slot 13 *)
      iApply (wp_csdsp_s_sconf γ Φ (mword_of_int (PK + 0x3a)) (mword_of_int 11 : mword 6) (mword_of_int 19 : mword 5)
                Q4 (K - 24)%nat w13 with "Hcg Hpc Hi3a [S19] [-]").
      { iEval (rewrite HQ4sp Hbs13). iExact "S19". }
      iIntros "Hcg Hpc S19". iEval (rewrite HQ4sp Hbs13) in "S19".
      iEval (rewrite (HQ4k (mword_of_int 19 : mword 5) ltac:(mw_neq) ltac:(mw_neq) ltac:(mw_neq) ltac:(mw_neq) ltac:(mw_neq))) in "S19".
      assert (Hp3c : add_vec_int (mword_of_int (PK + 0x3a) : mword 64) 2 = mword_of_int (PK + 0x3c)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hp3c) in "Hpc".
      (* +0x3c sd x20,80(sp) -> slot 14 *)
      iApply (wp_csdsp_s_sconf γ Φ (mword_of_int (PK + 0x3c)) (mword_of_int 10 : mword 6) (mword_of_int 20 : mword 5)
                Q4 (K - 24)%nat w14 with "Hcg Hpc Hi3c [S20] [-]").
      { iEval (rewrite HQ4sp Hbs14). iExact "S20". }
      iIntros "Hcg Hpc S20". iEval (rewrite HQ4sp Hbs14) in "S20".
      iEval (rewrite (HQ4k (mword_of_int 20 : mword 5) ltac:(mw_neq) ltac:(mw_neq) ltac:(mw_neq) ltac:(mw_neq) ltac:(mw_neq))) in "S20".
      assert (Hp3e : add_vec_int (mword_of_int (PK + 0x3c) : mword 64) 2 = mword_of_int (PK + 0x3e)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hp3e) in "Hpc".
      (* +0x3e sd x21,72(sp) -> slot 15 *)
      iApply (wp_csdsp_s_sconf γ Φ (mword_of_int (PK + 0x3e)) (mword_of_int 9 : mword 6) (mword_of_int 21 : mword 5)
                Q4 (K - 24)%nat w15 with "Hcg Hpc Hi3e [S21] [-]").
      { iEval (rewrite HQ4sp Hbs15). iExact "S21". }
      iIntros "Hcg Hpc S21". iEval (rewrite HQ4sp Hbs15) in "S21".
      iEval (rewrite (HQ4k (mword_of_int 21 : mword 5) ltac:(mw_neq) ltac:(mw_neq) ltac:(mw_neq) ltac:(mw_neq) ltac:(mw_neq))) in "S21".
      assert (Hp40 : add_vec_int (mword_of_int (PK + 0x3e) : mword 64) 2 = mword_of_int (PK + 0x40)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hp40) in "Hpc".
      (* +0x40 sd x22,64(sp) -> slot 16 *)
      iApply (wp_csdsp_s_sconf γ Φ (mword_of_int (PK + 0x40)) (mword_of_int 8 : mword 6) (mword_of_int 22 : mword 5)
                Q4 (K - 24)%nat w16 with "Hcg Hpc Hi40 [S22] [-]").
      { iEval (rewrite HQ4sp Hbs16). iExact "S22". }
      iIntros "Hcg Hpc S22". iEval (rewrite HQ4sp Hbs16) in "S22".
      iEval (rewrite (HQ4k (mword_of_int 22 : mword 5) ltac:(mw_neq) ltac:(mw_neq) ltac:(mw_neq) ltac:(mw_neq) ltac:(mw_neq))) in "S22".
      assert (Hp42 : add_vec_int (mword_of_int (PK + 0x40) : mword 64) 2 = mword_of_int (PK + 0x42)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hp42) in "Hpc".
      (* +0x42 sd x23,56(sp) -> slot 17 *)
      iApply (wp_csdsp_s_sconf γ Φ (mword_of_int (PK + 0x42)) (mword_of_int 7 : mword 6) (mword_of_int 23 : mword 5)
                Q4 (K - 24)%nat w17 with "Hcg Hpc Hi42 [S23] [-]").
      { iEval (rewrite HQ4sp Hbs17). iExact "S23". }
      iIntros "Hcg Hpc S23". iEval (rewrite HQ4sp Hbs17) in "S23".
      iEval (rewrite (HQ4k (mword_of_int 23 : mword 5) ltac:(mw_neq) ltac:(mw_neq) ltac:(mw_neq) ltac:(mw_neq) ltac:(mw_neq))) in "S23".
      assert (Hp44 : add_vec_int (mword_of_int (PK + 0x42) : mword 64) 2 = mword_of_int (PK + 0x44)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hp44) in "Hpc".
      (* +0x44 sd x24,48(sp) -> slot 18 *)
      iApply (wp_csdsp_s_sconf γ Φ (mword_of_int (PK + 0x44)) (mword_of_int 6 : mword 6) (mword_of_int 24 : mword 5)
                Q4 (K - 24)%nat w18 with "Hcg Hpc Hi44 [S24] [-]").
      { iEval (rewrite HQ4sp Hbs18). iExact "S24". }
      iIntros "Hcg Hpc S24". iEval (rewrite HQ4sp Hbs18) in "S24".
      iEval (rewrite (HQ4k (mword_of_int 24 : mword 5) ltac:(mw_neq) ltac:(mw_neq) ltac:(mw_neq) ltac:(mw_neq) ltac:(mw_neq))) in "S24".
      assert (Hp46 : add_vec_int (mword_of_int (PK + 0x44) : mword 64) 2 = mword_of_int (PK + 0x46)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hp46) in "Hpc".
      (* +0x46 sd x26,32(sp) -> slot 20 *)
      iApply (wp_csdsp_s_sconf γ Φ (mword_of_int (PK + 0x46)) (mword_of_int 4 : mword 6) (mword_of_int 26 : mword 5)
                Q4 (K - 24)%nat w20 with "Hcg Hpc Hi46 [S26] [-]").
      { iEval (rewrite HQ4sp Hbs20). iExact "S26". }
      iIntros "Hcg Hpc S26". iEval (rewrite HQ4sp Hbs20) in "S26".
      iEval (rewrite (HQ4k (mword_of_int 26 : mword 5) ltac:(mw_neq) ltac:(mw_neq) ltac:(mw_neq) ltac:(mw_neq) ltac:(mw_neq))) in "S26".
      assert (Hp48 : add_vec_int (mword_of_int (PK + 0x46) : mword 64) 2 = mword_of_int (PK + 0x48)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hp48) in "Hpc".
      (* +0x48 sd x27,24(sp) -> slot 21 *)
      iApply (wp_csdsp_s_sconf γ Φ (mword_of_int (PK + 0x48)) (mword_of_int 3 : mword 6) (mword_of_int 27 : mword 5)
                Q4 (K - 24)%nat w21 with "Hcg Hpc Hi48 [S27] [-]").
      { iEval (rewrite HQ4sp Hbs21). iExact "S27". }
      iIntros "Hcg Hpc S27". iEval (rewrite HQ4sp Hbs21) in "S27".
      iEval (rewrite (HQ4k (mword_of_int 27 : mword 5) ltac:(mw_neq) ltac:(mw_neq) ltac:(mw_neq) ltac:(mw_neq) ltac:(mw_neq))) in "S27".
      assert (Hp4a : add_vec_int (mword_of_int (PK + 0x48) : mword 64) 2 = mword_of_int (PK + 0x4a)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hp4a) in "Hpc".
      iApply (wp_cli_s_sconf γ Φ (mword_of_int (PK + 0x4a)) (mword_of_int 20 : mword 5) (mword_of_int 0 : mword 6)
                (mword_of_int 0 : mword 64) Q4 (K - 24)%nat
                ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                with "Hcg Hpc Hi4a [-]").
      iIntros "Hcg Hpc".
      set (C0 := <[Regidx (mword_of_int 20 : mword 5) := regval_into_reg (mword_of_int 0 : mword 64)]> Q4).
      assert (Hp4c : add_vec_int (mword_of_int (PK + 0x4a) : mword 64) 2 = mword_of_int (PK + 0x4c)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hp4c) in "Hpc".
      iApply (wp_li4_s_sconf γ Φ (mword_of_int (PK + 0x4c)) (mword_of_int 19 : mword 5) (mword_of_int 37 : mword 12)
                (mword_of_int 37 : mword 64) C0 (K - 24)%nat
                ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                with "Hcg Hpc Hi4c [-]").
      iIntros "Hcg Hpc".
      set (C1 := <[Regidx (mword_of_int 19 : mword 5) := regval_into_reg (mword_of_int 37 : mword 64)]> C0).
      assert (Hp50 : add_vec_int (mword_of_int (PK + 0x4c) : mword 64) 4 = mword_of_int (PK + 0x50)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hp50) in "Hpc".
      iApply (wp_li4_s_sconf γ Φ (mword_of_int (PK + 0x50)) (mword_of_int 24 : mword 5) (mword_of_int 117 : mword 12)
                (mword_of_int 117 : mword 64) C1 (K - 24)%nat
                ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                with "Hcg Hpc Hi50 [-]").
      iIntros "Hcg Hpc".
      set (C2 := <[Regidx (mword_of_int 24 : mword 5) := regval_into_reg (mword_of_int 117 : mword 64)]> C1).
      assert (Hp54 : add_vec_int (mword_of_int (PK + 0x50) : mword 64) 4 = mword_of_int (PK + 0x54)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hp54) in "Hpc".
      iApply (wp_li4_s_sconf γ Φ (mword_of_int (PK + 0x54)) (mword_of_int 26 : mword 5) (mword_of_int 120 : mword 12)
                (mword_of_int 120 : mword 64) C2 (K - 24)%nat
                ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                with "Hcg Hpc Hi54 [-]").
      iIntros "Hcg Hpc".
      set (C3 := <[Regidx (mword_of_int 26 : mword 5) := regval_into_reg (mword_of_int 120 : mword 64)]> C2).
      assert (Hp58 : add_vec_int (mword_of_int (PK + 0x54) : mword 64) 4 = mword_of_int (PK + 0x58)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hp58) in "Hpc".
      iApply (wp_li4_s_sconf γ Φ (mword_of_int (PK + 0x58)) (mword_of_int 27 : mword 5) (mword_of_int 112 : mword 12)
                (mword_of_int 112 : mword 64) C3 (K - 24)%nat
                ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                with "Hcg Hpc Hi58 [-]").
      iIntros "Hcg Hpc".
      set (C4 := <[Regidx (mword_of_int 27 : mword 5) := regval_into_reg (mword_of_int 112 : mword 64)]> C3).
      assert (Hp5c : add_vec_int (mword_of_int (PK + 0x58) : mword 64) 4 = mword_of_int (PK + 0x5c)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hp5c) in "Hpc".
      iApply (wp_cli_s_sconf γ Φ (mword_of_int (PK + 0x5c)) (mword_of_int 22 : mword 5) (mword_of_int 10 : mword 6)
                (mword_of_int 10 : mword 64) C4 (K - 24)%nat
                ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                with "Hcg Hpc Hi5c [-]").
      iIntros "Hcg Hpc".
      set (C5 := <[Regidx (mword_of_int 22 : mword 5) := regval_into_reg (mword_of_int 10 : mword 64)]> C4).
      assert (Hp5e : add_vec_int (mword_of_int (PK + 0x5c) : mword 64) 2 = mword_of_int (PK + 0x5e)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hp5e) in "Hpc".
      iApply (wp_li4_s_sconf γ Φ (mword_of_int (PK + 0x5e)) (mword_of_int 23 : mword 5) (mword_of_int 100 : mword 12)
                (mword_of_int 100 : mword 64) C5 (K - 24)%nat
                ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                with "Hcg Hpc Hi5e [-]").
      iIntros "Hcg Hpc".
      set (C6 := <[Regidx (mword_of_int 23 : mword 5) := regval_into_reg (mword_of_int 100 : mword 64)]> C5).
      assert (Hp62 : add_vec_int (mword_of_int (PK + 0x5e) : mword 64) 4 = mword_of_int (PK + 0x62)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hp62) in "Hpc".
      (* +0x62 j 0x86 : into the loop *)
      iApply (wp_cj_s_sconf γ Φ (mword_of_int (PK + 0x62)) (sign_extend' 21 (concat_vec (mword_of_int 18 : mword 11) ('b"0")))
                C6 (K - 24)%nat ltac:(vm_compute; reflexivity)
                with "Hcg Hpc Hi62 [-]").
      iNext. iIntros "Hcg Hpc".
      assert (Htgtl : add_vec (mword_of_int (PK + 0x62) : mword 64) (sign_extend' 64 (sign_extend' 21 (concat_vec (mword_of_int 18 : mword 11) ('b"0")))) = mword_of_int (PK + 0x86)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Htgtl) in "Hpc".
      iApply ("Kloop" $! C6 with "[%] Hcg Hpc Hpanicking Hfmt H9 H10 H12 Hva
                [S9 S19 S20 S21 S22 S23 S24 S26 S27] T8 T19 T22 Hap T24 HR").
      { (* the register facts the loop runs on *)
        assert (Hpeel : forall c : mword 5,
                  c <> mword_of_int 20 -> c <> mword_of_int 19 -> c <> mword_of_int 24 ->
                  c <> mword_of_int 26 -> c <> mword_of_int 27 -> c <> mword_of_int 22 ->
                  c <> mword_of_int 23 -> C6 !!! Regidx c = Q4 !!! Regidx c).
        { intros c N20 N19 N24 N26 N27 N22 N23.
          rewrite /C6 upd_ne; [| congruence]. rewrite /C5 upd_ne; [| congruence].
          rewrite /C4 upd_ne; [| congruence]. rewrite /C3 upd_ne; [| congruence].
          rewrite /C2 upd_ne; [| congruence]. rewrite /C1 upd_ne; [| congruence].
          rewrite /C0 upd_ne; [reflexivity | congruence]. }
        split.
        { rewrite (Hpeel csp_rs1 ltac:(mw_neq) ltac:(mw_neq) ltac:(mw_neq) ltac:(mw_neq)
                      ltac:(mw_neq) ltac:(mw_neq) ltac:(mw_neq)). exact HQ4sp. }
        split.
        { rewrite (Hpeel s0_idx ltac:(mw_neq) ltac:(mw_neq) ltac:(mw_neq) ltac:(mw_neq)
                      ltac:(mw_neq) ltac:(mw_neq) ltac:(mw_neq)).
          rewrite /Q4 upd_ne; [| reg_neq]. exact HQ3s0. }
        split.
        { rewrite (Hpeel s2_idx ltac:(mw_neq) ltac:(mw_neq) ltac:(mw_neq) ltac:(mw_neq)
                      ltac:(mw_neq) ltac:(mw_neq) ltac:(mw_neq)).
          rewrite /Q4 upd_ne; [| reg_neq]. exact HQ3s2. }
        split.
        { rewrite /C6 upd_ne; [| reg_neq]. rewrite /C5 upd_ne; [| reg_neq].
          rewrite /C4 upd_ne; [| reg_neq]. rewrite /C3 upd_ne; [| reg_neq].
          rewrite /C2 upd_ne; [| reg_neq]. rewrite /C1 upd_ne; [| reg_neq].
          rewrite /C0 upd_eq. apply bv_eq; vm_compute; reflexivity. }
        split.
        { rewrite (Hpeel a0_idx ltac:(mw_neq) ltac:(mw_neq) ltac:(mw_neq) ltac:(mw_neq)
                      ltac:(mw_neq) ltac:(mw_neq) ltac:(mw_neq)).
          rewrite /Q4 upd_eq. reflexivity. }
        split.
        { unfold pk_consts. split_and!.
          { rewrite /C6 upd_ne; [| reg_neq]. rewrite /C5 upd_ne; [| reg_neq].
            rewrite /C4 upd_ne; [| reg_neq]. rewrite /C3 upd_ne; [| reg_neq].
            rewrite /C2 upd_ne; [| reg_neq]. rewrite /C1 upd_eq. reflexivity. }
          { rewrite /C6 upd_ne; [| reg_neq]. rewrite /C5 upd_eq. reflexivity. }
          { rewrite /C6 upd_eq. reflexivity. }
          { rewrite /C6 upd_ne; [| reg_neq]. rewrite /C5 upd_ne; [| reg_neq].
            rewrite /C4 upd_ne; [| reg_neq]. rewrite /C3 upd_ne; [| reg_neq].
            rewrite /C2 upd_eq. reflexivity. }
          { rewrite /C6 upd_ne; [| reg_neq]. rewrite /C5 upd_ne; [| reg_neq].
            rewrite /C4 upd_ne; [| reg_neq]. rewrite /C3 upd_eq. reflexivity. }
          { rewrite /C6 upd_ne; [| reg_neq]. rewrite /C5 upd_ne; [| reg_neq].
            rewrite /C4 upd_eq. reflexivity. } }
        intros c Nsp N8 N18 N15 N10 N19 N20 N22 N23 N24 N26 N27.
        rewrite (Hpeel c ltac:(congruence) ltac:(congruence) ltac:(congruence)
                   ltac:(congruence) ltac:(congruence) ltac:(congruence) ltac:(congruence)).
        exact (HQ4k c Nsp N8 N18 N15 N10). }
      rewrite /pk_saved. iFrame "S9 S19 S20 S21 S22 S23 S24 S26 S27".
  Qed.


  (* ================================================================== *)
  (*  THE ADVANCE BLOCK (0x78 .. 0x82): [i++], load fmt[i], and the      *)
  (*  end-of-string test.  Every arm of the dispatch jumps here with s1  *)
  (*  holding (the index to continue at) - 1, which is what makes the    *)
  (*  fifteen arms differ only in how far they set s1.                   *)
  (* ================================================================== *)

  (* the registers this block writes *)
  Definition pk_adv_kept (mf mc : regfile) : Prop :=
    forall c : mword 5, c <> mword_of_int 9 -> c <> mword_of_int 20 -> c <> a0_idx ->
      mf !!! Regidx c = mc !!! Regidx c.

  Lemma wp_printk_advance (γ : gname) (Φ : mval -> iProp Σ)
      (mc : regfile) (K : nat) (fmt : mword 64) (dqf : dfrac) (f : string) (p : nat)
      (Rest : iProp Σ) :
    (S p < length (cstring_bytes f))%nat ->
    (Z.of_nat p + 1 < 2^31) ->
    mc !!! Regidx (mword_of_int 9 : mword 5) = mword_of_int (Z.of_nat p) ->
    mc !!! Regidx s2_idx = fmt ->
    sie_cap_gpr γ mc (K - 24)%nat -∗
    kernel_text -∗
    pc_is (mword_of_int (PK + 0x78) : mword 64) -∗
    fmt ↦ₛ{ dqf } f -∗
    Rest -∗
    (* the string ended: leave through the restore block at 0x24e *)
    ( ∀ mf : regfile,
      ⌜ pk_adv_kept mf mc /\ pk_fbyte f (S p) = (mword_of_int 0 : mword 8) ⌝ -∗
      sie_cap_gpr γ mf (K - 24)%nat -∗
      pc_is (mword_of_int (PK + 0x24e) : mword 64) -∗
      fmt ↦ₛ{ dqf } f -∗ Rest -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    (* another character: the loop test at 0x86 *)
    ( ∀ mf : regfile,
      ⌜ pk_adv_kept mf mc
        /\ mf !!! Regidx (mword_of_int 20 : mword 5) = mword_of_int (Z.of_nat (S p))
        /\ mf !!! Regidx a0_idx = zero_extend' 64 (pk_fbyte f (S p))
        /\ pk_fbyte f (S p) <> (mword_of_int 0 : mword 8) ⌝ -∗
      sie_cap_gpr γ mf (K - 24)%nat -∗
      pc_is (mword_of_int (PK + 0x86) : mword 64) -∗
      fmt ↦ₛ{ dqf } f -∗ Rest -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    intros Hlen Hp31 Hs1 Hs2.
    iIntros "Hcg #Htext Hpc Hfmt HR Kend Kgo".
    iPoseProof (pki_78 with "Htext") as "Hi78".
    iPoseProof (pki_7a with "Htext") as "Hi7a".
    iPoseProof (pki_7c with "Htext") as "Hi7c".
    iPoseProof (pki_7e with "Htext") as "Hi7e".
    iPoseProof (pki_82 with "Htext") as "Hi82".
    (* +0x78 c.addiw s1,s1,1 *)
    iApply (wp_caddiw_s_sconf γ Φ (mword_of_int (PK + 0x78)) (mword_of_int 9 : mword 5) (mword_of_int 1 : mword 6)
              mc (K - 24)%nat ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi78 [-]").
    iIntros "Hcg Hpc".
    set (A1 := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg (sign_extend' 64 (subrange_vec_dec
                 (add_vec (mc !!! Regidx (mword_of_int 9 : mword 5)) (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6)))) 31 0))]> mc).
    assert (HA1s1 : A1 !!! Regidx (mword_of_int 9 : mword 5) = mword_of_int (Z.of_nat (S p))).
    { rewrite /A1 upd_eq. unfold regval_into_reg. rewrite Hs1.
      rewrite (addiw_lit (Z.of_nat p) 1 (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6)))
                 ltac:(apply bv_eq; vm_compute; reflexivity)
                 ltac:(change (2^31) with 2147483648; lia)).
      f_equal. lia. }
    assert (HA1s2 : A1 !!! Regidx s2_idx = fmt) by (rewrite /A1 upd_ne; [exact Hs2 | reg_neq]).
    assert (Hp7a : add_vec_int (mword_of_int (PK + 0x78) : mword 64) 2 = mword_of_int (PK + 0x7a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp7a) in "Hpc".
    (* +0x7a c.mv s4,s1 : the C variable [i] *)
    iApply (wp_cmv_s_sconf γ Φ (mword_of_int (PK + 0x7a)) (mword_of_int 20 : mword 5) (mword_of_int 9 : mword 5)
              A1 (K - 24)%nat ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi7a [-]").
    iIntros "Hcg Hpc".
    set (A2 := <[Regidx (mword_of_int 20 : mword 5) := regval_into_reg (add_vec zero_reg (A1 !!! Regidx (mword_of_int 9 : mword 5)))]> A1).
    assert (HA2s4 : A2 !!! Regidx (mword_of_int 20 : mword 5) = mword_of_int (Z.of_nat (S p))).
    { rewrite /A2 upd_eq. unfold regval_into_reg. rewrite HA1s1. apply pi_addv_zero_l. }
    assert (HA2s1 : A2 !!! Regidx (mword_of_int 9 : mword 5) = mword_of_int (Z.of_nat (S p)))
      by (rewrite /A2 upd_ne; [exact HA1s1 | reg_neq]).
    assert (HA2s2 : A2 !!! Regidx s2_idx = fmt) by (rewrite /A2 upd_ne; [exact HA1s2 | reg_neq]).
    assert (Hp7c : add_vec_int (mword_of_int (PK + 0x7a) : mword 64) 2 = mword_of_int (PK + 0x7c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp7c) in "Hpc".
    (* +0x7c c.add s1,s1,s2 : &fmt[i] *)
    iApply (wp_cadd_s_sconf γ Φ (mword_of_int (PK + 0x7c)) (mword_of_int 9 : mword 5) s2_idx
              A2 (K - 24)%nat ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi7c [-]").
    iIntros "Hcg Hpc".
    set (A3 := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg (add_vec (A2 !!! Regidx (mword_of_int 9 : mword 5)) (A2 !!! Regidx s2_idx))]> A2).
    assert (HA3s1 : A3 !!! Regidx (mword_of_int 9 : mword 5) = pa_add fmt (S p)).
    { rewrite /A3 upd_eq. unfold regval_into_reg. rewrite HA2s1 HA2s2.
      rewrite add_vec_pa_add. f_equal.
      rewrite (uint_moi_small (Z.of_nat (S p)) ltac:(change (2^64) with 18446744073709551616;
        change (2^31) with 2147483648 in Hp31; lia)).
      apply Nat2Z.id. }
    assert (Hp7e : add_vec_int (mword_of_int (PK + 0x7c) : mword 64) 2 = mword_of_int (PK + 0x7e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp7e) in "Hpc".
    (* +0x7e lbu a0,0(s1) : the next format byte *)
    iDestruct (pk_str_byte fmt dqf f (S p) Hlen with "Hfmt") as "[Hb Hfcl]".
    assert (Hba : add_vec (A3 !!! Regidx (mword_of_int 9 : mword 5)) (sign_extend' 64 (mword_of_int 0 : mword 12)) = pa_add fmt (S p)).
    { rewrite HA3s1.
      replace (sign_extend' 64 (mword_of_int 0 : mword 12)) with (mword_of_int 0 : mword 64)
        by (apply bv_eq; vm_compute; reflexivity).
      apply kv_addv_zero. }
    iApply (wp_lbu_s_sconf γ Φ (mword_of_int (PK + 0x7e)) a0_idx (mword_of_int 9 : mword 5) (mword_of_int 0 : mword 12)
              A3 (K - 24)%nat (pk_fbyte f (S p))
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi7e [Hb] [-]").
    { iEval (rewrite Hba). iExact "Hb". }
    iIntros "Hcg Hpc Hb". iEval (rewrite Hba) in "Hb".
    iDestruct ("Hfcl" with "Hb") as "Hfmt".
    set (A4 := <[Regidx a0_idx := regval_into_reg (zero_extend' 64 (pk_fbyte f (S p)))]> A3).
    assert (Hp82 : add_vec_int (mword_of_int (PK + 0x7e) : mword 64) 4 = mword_of_int (PK + 0x82)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp82) in "Hpc".
    (* the map facts both arms report *)
    assert (Hkept : pk_adv_kept A4 mc).
    { intros c N9 N20 N10.
      rewrite /A4 upd_ne; [| congruence]. rewrite /A3 upd_ne; [| congruence].
      rewrite /A2 upd_ne; [| congruence]. rewrite /A1 upd_ne; [reflexivity | congruence]. }
    assert (HA4s4 : A4 !!! Regidx (mword_of_int 20 : mword 5) = mword_of_int (Z.of_nat (S p))).
    { rewrite /A4 upd_ne; [| reg_neq]. rewrite /A3 upd_ne; [| reg_neq]. exact HA2s4. }
    assert (HA4a0 : A4 !!! Regidx a0_idx = zero_extend' 64 (pk_fbyte f (S p)))
      by (rewrite /A4 upd_eq; reflexivity).
    (* +0x82 beqz a0 : the terminator *)
    destruct (eq_vec (A4 !!! Regidx a0_idx) zero_reg) eqn:Hz.
    - iApply (wp_beqz_x0_taken_s_sconf γ Φ (mword_of_int (PK + 0x82)) (mword_of_int 460 : mword 13)
                a0_idx A4 (K - 24)%nat ltac:(vm_compute; discriminate) Hz
                ltac:(vm_compute; reflexivity)
                with "Hcg Hpc Hi82 [-]").
      iNext. iIntros "Hcg Hpc".
      assert (Htgt : add_vec (mword_of_int (PK + 0x82) : mword 64) (sign_extend' 64 (mword_of_int 460 : mword 13)) = mword_of_int (PK + 0x24e)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Htgt) in "Hpc".
      iApply ("Kend" $! A4 with "[%] Hcg Hpc Hfmt HR").
      split; [exact Hkept | ].
      (* the loaded byte is zero, so the string ended here *)
      rewrite HA4a0 in Hz. exact (zext8_zero _ Hz).
    - iApply (wp_beqz_x0_fall_s_sconf γ Φ (mword_of_int (PK + 0x82)) (mword_of_int 460 : mword 13)
                a0_idx A4 (K - 24)%nat ltac:(vm_compute; discriminate) Hz
                with "Hcg Hpc Hi82 [-]").
      iIntros "Hcg Hpc".
      assert (Hp86 : add_vec_int (mword_of_int (PK + 0x82) : mword 64) 4 = mword_of_int (PK + 0x86)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hp86) in "Hpc".
      iApply ("Kgo" $! A4 with "[%] Hcg Hpc Hfmt HR").
      split; [exact Hkept | ]. split; [exact HA4s4 | ]. split; [exact HA4a0 | ].
      intro Hc. rewrite HA4a0 Hc in Hz.
      assert (Hz0 : eq_vec (zero_extend' 64 (mword_of_int 0 : mword 8)) (zero_reg : mword 64) = true)
        by (vm_compute; reflexivity).
      rewrite Hz0 in Hz. discriminate.
  Qed.

  (* ================================================================== *)
  (*  THE LITERAL-CHARACTER ARM (0x86 taken -> 0x72 -> 0x76).            *)
  (*  [cx != '%']: print the byte and go round.  This is the only arm    *)
  (*  that consumes no vararg, and the only one whose byte reaches the   *)
  (*  UART directly rather than through printint.                        *)
  (* ================================================================== *)

  Hypothesis wp_consputc :
    forall (γ : gname) (γd : uart_names) (Φ : mval -> iProp Σ) (m0 : regfile) (K : nat)
      (l : list (bv 8)) (pv pkv : mword 32) (dqm dqm2 : dfrac),
      wp_consputc_sconf_body γ γd Φ m0 K l pv pkv dqm dqm2.

  Lemma wp_printk_char (γ : gname) (γd : uart_names) (Φ : mval -> iProp Σ)
      (mc : regfile) (K : nat) (l : list (bv 8)) (pv pkv : mword 32)
      (dqm dqm2 : dfrac) (Rest : iProp Σ) :
    (30 <= K)%nat ->
    eq_vec (sign_extend' 64 pv) zero_reg = false ->
    neq_vec (sign_extend' 64 pkv) zero_reg = false ->
    neq_vec (mc !!! Regidx a0_idx) (mc !!! Regidx (mword_of_int 19 : mword 5)) = true ->
    sie_cap_gpr γ mc (K - 24)%nat -∗
    kernel_text -∗
    pc_is (mword_of_int (PK + 0x86) : mword 64) -∗
    (mword_of_int KernelSyms.panicking : mword 64) ↦₄{ dqm } pv -∗
    (mword_of_int KernelSyms.panicked : mword 64) ↦₄{ dqm2 } pkv -∗
    dev_inv γd -∗ uart_tx_own γd l -∗ uart_dlab_off γd -∗
    Rest -∗
    ( ∀ (mf : regfile) (bs : list (bv 8)),
      ⌜ (forall c : mword 5, is_cs_idx c = true -> c <> mword_of_int 9 ->
           mf !!! Regidx c = mc !!! Regidx c)
        /\ mf !!! Regidx (mword_of_int 9 : mword 5)
           = mc !!! Regidx (mword_of_int 20 : mword 5) ⌝ -∗
      sie_cap_gpr γ mf (K - 24)%nat -∗
      pc_is (mword_of_int (PK + 0x78) : mword 64) -∗
      (mword_of_int KernelSyms.panicking : mword 64) ↦₄{ dqm } pv -∗
      (mword_of_int KernelSyms.panicked : mword 64) ↦₄{ dqm2 } pkv -∗
      uart_tx_own γd (l ++ bs) -∗ uart_sent γd (l ++ bs) -∗
      Rest -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    intros HK Hpv Hpkv Hne.
    assert (HK6 : (6 <= K - 24)%nat) by lia.
    iIntros "Hcg #Htext Hpc Hpanicking Hpanicked #Hdev Htx #Hdlab HR Hcont".
    iPoseProof (pki_86 with "Htext") as "Hi86".
    iPoseProof (pki_72 with "Htext") as "Hi72".
    iPoseProof (pki_76 with "Htext") as "Hi76".
    (* +0x86 bne a0,s3 : not a '%' -- print it *)
    iApply (wp_bne_taken_s_sconf γ Φ (mword_of_int (PK + 0x86)) (mword_of_int 8172 : mword 13)
              (mword_of_int 19 : mword 5) a0_idx mc (K - 24)%nat
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) Hne
              ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi86 [-]").
    iNext. iIntros "Hcg Hpc".
    assert (Htgt72 : add_vec (mword_of_int (PK + 0x86) : mword 64) (sign_extend' 64 (mword_of_int 8172 : mword 13)) = mword_of_int (PK + 0x72)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgt72) in "Hpc".
    (* +0x72 jal consputc *)
    iApply (wp_jal_s_sconf γ Φ (mword_of_int (PK + 0x72)) ra_idx (mword_of_int 2096398 : mword 21)
              mc (K - 24)%nat ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi72 [-]").
    iIntros "Hcg Hpc".
    set (P1 := <[Regidx ra_idx := regval_into_reg (add_vec_int (mword_of_int (PK + 0x72) : mword 64) 4)]> mc).
    assert (Htgtc : add_vec (mword_of_int (PK + 0x72) : mword 64) (sign_extend' 64 (mword_of_int 2096398 : mword 21)) = mword_of_int KernelSyms.consputc) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgtc) in "Hpc".
    iApply (wp_consputc γ γd Φ P1 (K - 24)%nat l pv pkv dqm dqm2 HK6 Hpv Hpkv
              with "Hcg Htext Hpc Hpanicking Hpanicked Hdev Htx Hdlab [-]").
    iIntros (mk bs) "Hcg Hpc %Hcs Hpanicking Hpanicked Htx #Hsent".
    destruct Hcs as [Hcs Hra].
    assert (Hret : ret_pc (P1 !!! Regidx ra_idx) = mword_of_int (PK + 0x76))
      by (rewrite /P1 upd_eq; unfold ret_pc; apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hret) in "Hpc".
    (* +0x76 c.mv s1,s4 : s1 := i, the index the advance block bumps *)
    iApply (wp_cmv_s_sconf γ Φ (mword_of_int (PK + 0x76)) (mword_of_int 9 : mword 5) (mword_of_int 20 : mword 5)
              mk (K - 24)%nat ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi76 [-]").
    iIntros "Hcg Hpc".
    set (P2 := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg (add_vec zero_reg (mk !!! Regidx (mword_of_int 20 : mword 5)))]> mk).
    assert (Hp78 : add_vec_int (mword_of_int (PK + 0x76) : mword 64) 2 = mword_of_int (PK + 0x78)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp78) in "Hpc".
    (* s4 is callee-saved, so it still holds [i] *)
    assert (Hmks4 : mk !!! Regidx (mword_of_int 20 : mword 5) = mc !!! Regidx (mword_of_int 20 : mword 5)).
    { rewrite (callee_saved_lookup Hcs (mword_of_int 20 : mword 5) ltac:(vm_compute; reflexivity)).
      rewrite /P1 upd_ne; [reflexivity | reg_neq]. }
    iApply ("Hcont" $! P2 bs with "[%] Hcg Hpc Hpanicking Hpanicked Htx Hsent HR").
    split.
    - intros c Hc N9.
      pose proof (is_cs_idx_true_neq ra_idx c ltac:(vm_compute; reflexivity) Hc) as N1.
      rewrite /P2 upd_ne; [| congruence].
      rewrite (callee_saved_lookup Hcs c Hc).
      rewrite /P1 upd_ne; [reflexivity | congruence].
    - rewrite /P2 upd_eq. unfold regval_into_reg. rewrite Hmks4. apply pi_addv_zero_l.
  Qed.

  (* ================================================================== *)
  (*  THE va_list ACCESSOR and the first dispatch arm.                   *)
  (*                                                                     *)
  (*  [pk_va] is spelled out slot by slot (the prologue needs that), but  *)
  (*  an arm reaches the k-th vararg for a SYMBOLIC k, so the seven-way   *)
  (*  case analysis is done ONCE here and every arm uses the accessor.    *)
  (* ================================================================== *)

  Lemma pk_va_acc (sp0 : mword 64) (m : regfile) (k : nat) :
    (k < 7)%nat ->
    pk_va sp0 m ⊢
    (pa_stk sp0 (7 - k)) ↦₈ (pk_vararg m k) ∗
    ((pa_stk sp0 (7 - k)) ↦₈ (pk_vararg m k) -∗ pk_va sp0 m).
  Proof.
    intro Hk. rewrite /pk_va /pk_vararg.
    iIntros "(V7 & V6 & V5 & V4 & V3 & V2 & V1)".
    destruct k as [|[|[|[|[|[|[|k]]]]]]]; cbn [Nat.sub];
      [ replace (mword_of_int (11 + Z.of_nat 0) : mword 5) with (mword_of_int 11 : mword 5)
          by (apply bv_eq; vm_compute; reflexivity)
      | replace (mword_of_int (11 + Z.of_nat 1) : mword 5) with (mword_of_int 12 : mword 5)
          by (apply bv_eq; vm_compute; reflexivity)
      | replace (mword_of_int (11 + Z.of_nat 2) : mword 5) with (mword_of_int 13 : mword 5)
          by (apply bv_eq; vm_compute; reflexivity)
      | replace (mword_of_int (11 + Z.of_nat 3) : mword 5) with (mword_of_int 14 : mword 5)
          by (apply bv_eq; vm_compute; reflexivity)
      | replace (mword_of_int (11 + Z.of_nat 4) : mword 5) with (mword_of_int 15 : mword 5)
          by (apply bv_eq; vm_compute; reflexivity)
      | replace (mword_of_int (11 + Z.of_nat 5) : mword 5) with (mword_of_int 16 : mword 5)
          by (apply bv_eq; vm_compute; reflexivity)
      | replace (mword_of_int (11 + Z.of_nat 6) : mword 5) with (mword_of_int 17 : mword 5)
          by (apply bv_eq; vm_compute; reflexivity)
      | lia ].
    - iFrame "V7". iIntros "V7". iFrame.
    - iFrame "V6". iIntros "V6". iFrame.
    - iFrame "V5". iIntros "V5". iFrame.
    - iFrame "V4". iIntros "V4". iFrame.
    - iFrame "V3". iIntros "V3". iFrame.
    - iFrame "V2". iIntros "V2". iFrame.
    - iFrame "V1". iIntros "V1". iFrame.
  Qed.

  (* the low half of a vararg slot, AT [mword 32] -- same ascription problem as
     [pk_fbyte]: [word_lo] lands in [bv 32] and a leaf wants an [mword]. *)
  Definition pk_lo (m : regfile) (k : nat) : mword 32 := word_lo (pk_vararg m k).

  (* the va_list cursor's value after [k] arguments have been taken *)
  Definition pk_ap (s0v : mword 64) (k : nat) : mword 64 :=
    add_vec s0v (mword_of_int (8 + 8 * Z.of_nat k)).

  (* the cursor points at the k-th vararg's slot *)
  Lemma pk_ap_slot (sp0 : mword 64) (k : nat) :
    (k < 7)%nat ->
    pk_ap (add_vec sp0 (sign_extend' 64 (mword_of_int (-64) : mword 12))) k
    = pa_stk sp0 (7 - k).
  Proof.
    intro Hk. unfold pk_ap, pa_stk, add_vec_int.
    rewrite pa_stk_off2. f_equal.
    apply bv_eq. rewrite !moi64_unsigned.
    change (bv_wrap 64 ?x) with (x `mod` 18446744073709551616).
    destruct k as [|[|[|[|[|[|[|k]]]]]]]; try lia; vm_compute; reflexivity.
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  [va_arg], the three instructions every value arm starts with:      *)
  (*  read the cursor out of slot 23, bump it by 8, write it back.       *)
  (*  Shared over the arm's base offset [B] so the nine arms do not each *)
  (*  re-prove it.                                                       *)
  (* ------------------------------------------------------------------ *)

  Definition pk_vaarg_instrs (B : Z) : iProp Σ :=
    (instr (mword_of_int (PK + B + 0) : mword 64) false
       (LOAD (mword_of_int 3976 : mword 12, Regidx s0_idx, Regidx a5_idx, false, 8)) ∗
     instr (mword_of_int (PK + B + 4) : mword 64) false
       (ITYPE (mword_of_int 8 : mword 12, Regidx a5_idx, Regidx (mword_of_int 14 : mword 5), ADDI)) ∗
     instr (mword_of_int (PK + B + 8) : mword 64) false
       (STORE (mword_of_int 3976 : mword 12, Regidx (mword_of_int 14 : mword 5), Regidx s0_idx, 8)))%I.

  Lemma wp_printk_vaarg (γ : gname) (Φ : mval -> iProp Σ)
      (mc : regfile) (K : nat) (B : Z) (sp0 s0v : mword 64) (k : nat) :
    mc !!! Regidx s0_idx = s0v ->
    s0v = add_vec sp0 (sign_extend' 64 (mword_of_int (-64) : mword 12)) ->
    sie_cap_gpr γ mc (K - 24)%nat -∗
    pk_vaarg_instrs B -∗
    pc_is (mword_of_int (PK + B + 0) : mword 64) -∗
    (pa_stk sp0 23) ↦₈ (pk_ap s0v k) -∗
    ( ∀ mf : regfile,
      ⌜ mf !!! Regidx a5_idx = pk_ap s0v k
        /\ mf !!! Regidx s0_idx = s0v
        /\ (forall c : mword 5, c <> a5_idx -> c <> mword_of_int 14 ->
              mf !!! Regidx c = mc !!! Regidx c) ⌝ -∗
      sie_cap_gpr γ mf (K - 24)%nat -∗
      pc_is (mword_of_int (PK + B + 12) : mword 64) -∗
      (pa_stk sp0 23) ↦₈ (pk_ap s0v (S k)) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    intros Hs0 Hs0v.
    iIntros "Hcg Hinstrs Hpc Hap Hcont".
    rewrite /pk_vaarg_instrs. iDestruct "Hinstrs" as "(I0 & I4 & I8)".
    assert (Hap23 : add_vec (mc !!! Regidx s0_idx) (sign_extend' 64 (mword_of_int 3976 : mword 12)) = pa_stk sp0 23).
    { rewrite Hs0 Hs0v. unfold pa_stk, add_vec_int. rewrite pa_stk_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    iEval (rewrite -Hap23) in "Hap".
    iApply (wp_ld_s_sconf γ Φ (mword_of_int (PK + B + 0)) a5_idx s0_idx (mword_of_int 3976 : mword 12)
              mc (K - 24)%nat (pk_ap s0v k)
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hcg Hpc I0 Hap [-]").
    iIntros "Hcg Hpc Hap".
    set (V1 := <[Regidx a5_idx := regval_into_reg (pk_ap s0v k)]> mc).
    assert (HV1a5 : V1 !!! Regidx a5_idx = pk_ap s0v k) by (rewrite /V1 upd_eq; reflexivity).
    assert (HV1s0 : V1 !!! Regidx s0_idx = s0v) by (rewrite /V1 upd_ne; [exact Hs0 | reg_neq]).
    assert (Hp4 : add_vec_int (mword_of_int (PK + B + 0) : mword 64) 4 = mword_of_int (PK + B + 4))
      by (unfold add_vec_int; rewrite moi_add; f_equal; lia).
    iEval (rewrite Hp4) in "Hpc".
    iApply (wp_addi4_s_sconf γ Φ (mword_of_int (PK + B + 4)) (mword_of_int 14 : mword 5) a5_idx (mword_of_int 8 : mword 12)
              V1 (K - 24)%nat ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hcg Hpc I4 [-]").
    iIntros "Hcg Hpc".
    set (V2 := <[Regidx (mword_of_int 14 : mword 5) := regval_into_reg (add_vec (V1 !!! Regidx a5_idx) (sign_extend' 64 (mword_of_int 8 : mword 12)))]> V1).
    assert (HV2a4 : V2 !!! Regidx (mword_of_int 14 : mword 5) = pk_ap s0v (S k)).
    { rewrite /V2 upd_eq. unfold regval_into_reg. rewrite HV1a5. unfold pk_ap.
      replace (sign_extend' 64 (mword_of_int 8 : mword 12)) with (mword_of_int 8 : mword 64)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite addv_moi_moi. f_equal. f_equal. rewrite Nat2Z.inj_succ. ring. }
    assert (HV2a5 : V2 !!! Regidx a5_idx = pk_ap s0v k) by (rewrite /V2 upd_ne; [exact HV1a5 | reg_neq]).
    assert (HV2s0 : V2 !!! Regidx s0_idx = s0v) by (rewrite /V2 upd_ne; [exact HV1s0 | reg_neq]).
    assert (Hp8 : add_vec_int (mword_of_int (PK + B + 4) : mword 64) 4 = mword_of_int (PK + B + 8))
      by (unfold add_vec_int; rewrite moi_add; f_equal; lia).
    iEval (rewrite Hp8) in "Hpc".
    assert (Hap23' : add_vec (V2 !!! Regidx s0_idx) (sign_extend' 64 (mword_of_int 3976 : mword 12)) = pa_stk sp0 23).
    { rewrite HV2s0 Hs0v. unfold pa_stk, add_vec_int. rewrite pa_stk_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    iEval (rewrite Hap23 -Hap23') in "Hap".
    iApply (wp_sd_s_sconf γ Φ (mword_of_int (PK + B + 8)) (mword_of_int 14 : mword 5) s0_idx (mword_of_int 3976 : mword 12)
              V2 (K - 24)%nat (pk_ap s0v k) with "Hcg Hpc I8 Hap [-]").
    iIntros "Hcg Hpc Hap". iEval (rewrite Hap23' HV2a4) in "Hap".
    assert (Hp12 : add_vec_int (mword_of_int (PK + B + 8) : mword 64) 4 = mword_of_int (PK + B + 12))
      by (unfold add_vec_int; rewrite moi_add; f_equal; lia).
    iEval (rewrite Hp12) in "Hpc".
    iApply ("Hcont" $! V2 with "[%] Hcg Hpc Hap").
    split; [exact HV2a5 | ]. split; [exact HV2s0 | ].
    intros c N15 N14.
    rewrite /V2 upd_ne; [| congruence]. rewrite /V1 upd_ne; [reflexivity | congruence].
  Qed.

  (* ================================================================== *)
  (*  THE "%d" ARM (0xd4 .. 0xea) -- the shape TEN of the fifteen share: *)
  (*  take one vararg off the va_list, hand it to printint with a        *)
  (*  (base, sign) pair, and jump back to the advance block.             *)
  (*                                                                     *)
  (*  The three instructions at 0xd4/0xd8/0xdc ARE [va_arg]: read the     *)
  (*  cursor out of slot 23, bump it by 8, write it back.  The argument   *)
  (*  itself is then read at the OLD cursor, which [pk_ap_slot] says is   *)
  (*  vararg slot [7 - k].  "%d" reads it with [c.lw] -- a 4-byte load of *)
  (*  an 8-byte slot -- so the slot is split with [word_pointsto_split4]  *)
  (*  and rejoined afterwards.                                           *)
  (* ================================================================== *)

  (* splitting an 8-byte slot into halves and rejoining it is the identity --
     the [%d]/[%u]/[%x] arms read the low half of a vararg slot with a 4-byte
     load and must hand the slot back whole. *)
  Lemma word_of_words_id (w : bv 64) : word_of_words (word_lo w) (word_hi w) = w.
  Proof.
    apply (bv_eq_of_bytes (n:=8)). intros j Hj.
    assert (Hj8 : (j < 8)%nat) by lia.
    destruct (decide (j < 4)%nat) as [Hlt | Hge].
    - rewrite nth_byte_word_of_words_lo; [| exact Hlt].
      apply nth_byte_word_lo. exact Hlt.
    - replace j with (4 + (j - 4))%nat by lia.
      rewrite nth_byte_word_of_words_hi; [| lia].
      rewrite nth_byte_word_hi; [reflexivity | lia].
  Qed.

  Hypothesis wp_printint :
    forall (γ : gname) (γd : uart_names) (Φ : mval -> iProp Σ) (m0 : regfile) (K : nat)
      (l : list (bv 8)) (pv pkv : mword 32) (dqm dqm2 : dfrac),
      wp_printint_sconf_body γ γd Φ m0 K l pv pkv dqm dqm2.

  Lemma wp_printk_arm_d (γ : gname) (γd : uart_names) (Φ : mval -> iProp Σ)
      (m mc : regfile) (K : nat) (k : nat) (l : list (bv 8)) (pv pkv : mword 32)
      (dqm dqm2 : dfrac) (Rest : iProp Σ) :
    let sp0 := m !!! Regidx csp_rs1 in
    let s0v := add_vec sp0 (sign_extend' 64 (mword_of_int (-64) : mword 12)) in
    (38 <= K)%nat ->
    (k < 7)%nat ->
    eq_vec (sign_extend' 64 pv) zero_reg = false ->
    neq_vec (sign_extend' 64 pkv) zero_reg = false ->
    mc !!! Regidx s0_idx = s0v ->
    mc !!! Regidx (mword_of_int 22 : mword 5) = (mword_of_int 10 : mword 64) ->
    sie_cap_gpr γ mc (K - 24)%nat -∗
    kernel_text -∗ kernel_data -∗
    pc_is (mword_of_int (PK + 0xd4) : mword 64) -∗
    (pa_stk sp0 23) ↦₈ (pk_ap s0v k) -∗
    pk_va sp0 m -∗
    (mword_of_int KernelSyms.panicking : mword 64) ↦₄{ dqm } pv -∗
    (mword_of_int KernelSyms.panicked : mword 64) ↦₄{ dqm2 } pkv -∗
    dev_inv γd -∗ uart_tx_own γd l -∗ uart_dlab_off γd -∗
    Rest -∗
    ( ∀ (mf : regfile) (bs : list (bv 8)),
      ⌜ forall c : mword 5, is_cs_idx c = true -> mf !!! Regidx c = mc !!! Regidx c ⌝ -∗
      sie_cap_gpr γ mf (K - 24)%nat -∗
      pc_is (mword_of_int (PK + 0x78) : mword 64) -∗
      (pa_stk sp0 23) ↦₈ (pk_ap s0v (S k)) -∗
      pk_va sp0 m -∗
      (mword_of_int KernelSyms.panicking : mword 64) ↦₄{ dqm } pv -∗
      (mword_of_int KernelSyms.panicked : mword 64) ↦₄{ dqm2 } pkv -∗
      uart_tx_own γd (l ++ bs) -∗ uart_sent γd (l ++ bs) -∗
      Rest -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    intros sp0 s0v HK Hk Hpv Hpkv Hs0 Hs6.
    assert (HK14 : (14 <= K - 24)%nat) by lia.
    iIntros "Hcg #Htext #Hkdata Hpc Hap Hva Hpanicking Hpanicked #Hdev Htx #Hdlab HR Hcont".
    iPoseProof (pki_d4 with "Htext") as "Hid4".
    iPoseProof (pki_d8 with "Htext") as "Hid8".
    iPoseProof (pki_dc with "Htext") as "Hidc".
    iPoseProof (pki_e0 with "Htext") as "Hie0".
    iPoseProof (pki_e2 with "Htext") as "Hie2".
    iPoseProof (pki_e4 with "Htext") as "Hie4".
    iPoseProof (pki_e6 with "Htext") as "Hie6".
    iPoseProof (pki_ea with "Htext") as "Hiea".
    assert (Hap23 : add_vec (mc !!! Regidx s0_idx) (sign_extend' 64 (mword_of_int 3976 : mword 12)) = pa_stk sp0 23).
    { rewrite Hs0. unfold s0v, pa_stk, add_vec_int. rewrite pa_stk_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    (* +0xd4 ld a5,-120(s0) : a5 := ap *)
    iEval (rewrite -Hap23) in "Hap".
    iApply (wp_ld_s_sconf γ Φ (mword_of_int (PK + 0xd4)) a5_idx s0_idx (mword_of_int 3976 : mword 12)
              mc (K - 24)%nat (pk_ap s0v k)
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hid4 Hap [-]").
    iIntros "Hcg Hpc Hap".
    set (D1 := <[Regidx a5_idx := regval_into_reg (pk_ap s0v k)]> mc).
    assert (HD1a5 : D1 !!! Regidx a5_idx = pk_ap s0v k) by (rewrite /D1 upd_eq; reflexivity).
    assert (HD1s0 : D1 !!! Regidx s0_idx = s0v) by (rewrite /D1 upd_ne; [exact Hs0 | reg_neq]).
    assert (Hpd8 : add_vec_int (mword_of_int (PK + 0xd4) : mword 64) 4 = mword_of_int (PK + 0xd8)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpd8) in "Hpc".
    (* +0xd8 addi a4,a5,8 : the bumped cursor *)
    iApply (wp_addi4_s_sconf γ Φ (mword_of_int (PK + 0xd8)) (mword_of_int 14 : mword 5) a5_idx (mword_of_int 8 : mword 12)
              D1 (K - 24)%nat ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hid8 [-]").
    iIntros "Hcg Hpc".
    set (D2 := <[Regidx (mword_of_int 14 : mword 5) := regval_into_reg (add_vec (D1 !!! Regidx a5_idx) (sign_extend' 64 (mword_of_int 8 : mword 12)))]> D1).
    assert (HD2a4 : D2 !!! Regidx (mword_of_int 14 : mword 5) = pk_ap s0v (S k)).
    { rewrite /D2 upd_eq. unfold regval_into_reg. rewrite HD1a5. unfold pk_ap.
      replace (sign_extend' 64 (mword_of_int 8 : mword 12)) with (mword_of_int 8 : mword 64)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite addv_moi_moi. f_equal. f_equal. rewrite Nat2Z.inj_succ. ring. }
    assert (HD2a5 : D2 !!! Regidx a5_idx = pk_ap s0v k) by (rewrite /D2 upd_ne; [exact HD1a5 | reg_neq]).
    assert (HD2s0 : D2 !!! Regidx s0_idx = s0v) by (rewrite /D2 upd_ne; [exact HD1s0 | reg_neq]).
    assert (Hpdc : add_vec_int (mword_of_int (PK + 0xd8) : mword 64) 4 = mword_of_int (PK + 0xdc)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpdc) in "Hpc".
    (* +0xdc sd a4,-120(s0) : ap := ap + 8 *)
    assert (Hap23' : add_vec (D2 !!! Regidx s0_idx) (sign_extend' 64 (mword_of_int 3976 : mword 12)) = pa_stk sp0 23).
    { rewrite HD2s0. unfold s0v, pa_stk, add_vec_int. rewrite pa_stk_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    iEval (rewrite Hap23 -Hap23') in "Hap".
    iApply (wp_sd_s_sconf γ Φ (mword_of_int (PK + 0xdc)) (mword_of_int 14 : mword 5) s0_idx (mword_of_int 3976 : mword 12)
              D2 (K - 24)%nat (pk_ap s0v k) with "Hcg Hpc Hidc Hap [-]").
    iIntros "Hcg Hpc Hap". iEval (rewrite Hap23' HD2a4) in "Hap".
    assert (Hpe0 : add_vec_int (mword_of_int (PK + 0xdc) : mword 64) 4 = mword_of_int (PK + 0xe0)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpe0) in "Hpc".
    (* +0xe0 c.li a2,1 : sign *)
    iApply (wp_cli_s_sconf γ Φ (mword_of_int (PK + 0xe0)) (mword_of_int 12 : mword 5) (mword_of_int 1 : mword 6)
              (mword_of_int 1 : mword 64) D2 (K - 24)%nat
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc Hie0 [-]").
    iIntros "Hcg Hpc".
    set (D3 := <[Regidx (mword_of_int 12 : mword 5) := regval_into_reg (mword_of_int 1 : mword 64)]> D2).
    assert (Hpe2 : add_vec_int (mword_of_int (PK + 0xe0) : mword 64) 2 = mword_of_int (PK + 0xe2)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpe2) in "Hpc".
    (* +0xe2 c.mv a1,s6 : base = 10 *)
    iApply (wp_cmv_s_sconf γ Φ (mword_of_int (PK + 0xe2)) a1_idx (mword_of_int 22 : mword 5)
              D3 (K - 24)%nat ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hie2 [-]").
    iIntros "Hcg Hpc".
    set (D4 := <[Regidx a1_idx := regval_into_reg (add_vec zero_reg (D3 !!! Regidx (mword_of_int 22 : mword 5)))]> D3).
    assert (HD4a1 : D4 !!! Regidx a1_idx = (mword_of_int 10 : mword 64)).
    { rewrite /D4 upd_eq. unfold regval_into_reg.
      rewrite /D3 upd_ne; [| reg_neq]. rewrite /D2 upd_ne; [| reg_neq].
      rewrite /D1 upd_ne; [| reg_neq]. rewrite Hs6. apply pi_addv_zero_l. }
    assert (HD4a5 : D4 !!! Regidx a5_idx = pk_ap s0v k).
    { rewrite /D4 upd_ne; [| reg_neq]. rewrite /D3 upd_ne; [| reg_neq]. exact HD2a5. }
    assert (Hpe4 : add_vec_int (mword_of_int (PK + 0xe2) : mword 64) 2 = mword_of_int (PK + 0xe4)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpe4) in "Hpc".
    (* +0xe4 c.lw a0,0(a5) : the argument -- a 4-byte read of an 8-byte slot *)
    iDestruct (pk_va_acc sp0 m k Hk with "Hva") as "[Hslot Hvacl]".
    iDestruct (word_pointsto_aligned_p with "Hslot") as %Halv.
    iDestruct (word_pointsto_split4 with "Hslot") as "[Hlo Hhi]".
    iEval (rewrite -/(pk_lo m k)) in "Hlo".
    assert (Hlwa : add_vec (D4 !!! Regidx a5_idx) (sign_extend' 64 (mword_of_int 0 : mword 12)) = pa_stk sp0 (7 - k)).
    { rewrite HD4a5.
      replace (sign_extend' 64 (mword_of_int 0 : mword 12)) with (mword_of_int 0 : mword 64)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite kv_addv_zero. apply pk_ap_slot. exact Hk. }
    iEval (rewrite -Hlwa) in "Hlo".
    iApply (wp_clw_s_sconf γ Φ (mword_of_int (PK + 0xe4)) a0_idx a5_idx (mword_of_int 0 : mword 12)
              D4 (K - 24)%nat (pk_lo m k)
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hie4 Hlo [-]").
    iIntros "Hcg Hpc Hlo". iEval (rewrite Hlwa) in "Hlo".
    iDestruct (word_pointsto_join4 _ _ _ _ Halv with "Hlo Hhi") as "Hslot".
    rewrite word_of_words_id.
    iDestruct ("Hvacl" with "Hslot") as "Hva".
    set (D5 := <[Regidx a0_idx := regval_into_reg (sign_extend' 64 (pk_lo m k))]> D4).
    assert (Hpe6 : add_vec_int (mword_of_int (PK + 0xe4) : mword 64) 2 = mword_of_int (PK + 0xe6)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpe6) in "Hpc".
    (* +0xe6 jal printint *)
    iApply (wp_jal_s_sconf γ Φ (mword_of_int (PK + 0xe6)) ra_idx (mword_of_int 2096772 : mword 21)
              D5 (K - 24)%nat ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hie6 [-]").
    iIntros "Hcg Hpc".
    set (D6 := <[Regidx ra_idx := regval_into_reg (add_vec_int (mword_of_int (PK + 0xe6) : mword 64) 4)]> D5).
    assert (Htgtp : add_vec (mword_of_int (PK + 0xe6) : mword 64) (sign_extend' 64 (mword_of_int 2096772 : mword 21)) = mword_of_int KernelSyms.printint) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgtp) in "Hpc".
    assert (HD6a1 : (10 <= uint (D6 !!! Regidx a1_idx) <= 16)%Z).
    { rewrite /D6 upd_ne; [| reg_neq]. rewrite /D5 upd_ne; [| reg_neq]. rewrite HD4a1.
      rewrite (uint_moi_small 10 ltac:(change (2^64) with 18446744073709551616; lia)). lia. }
    iApply (wp_printint γ γd Φ D6 (K - 24)%nat l pv pkv dqm dqm2 HK14 HD6a1 Hpv Hpkv
              with "Hcg Htext Hkdata Hpc Hpanicking Hpanicked Hdev Htx Hdlab [-]").
    iIntros (mf bs) "Hcg Hpc %Hcs Hpanicking Hpanicked Htx #Hsent".
    destruct Hcs as [Hcs Hra].
    assert (Hret : ret_pc (D6 !!! Regidx ra_idx) = mword_of_int (PK + 0xea))
      by (rewrite /D6 upd_eq; unfold ret_pc; apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hret) in "Hpc".
    (* +0xea j 0x78 *)
    iApply (wp_cj_s_sconf γ Φ (mword_of_int (PK + 0xea)) (sign_extend' 21 (concat_vec (mword_of_int 1991 : mword 11) ('b"0")))
              mf (K - 24)%nat ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hiea [-]").
    iNext. iIntros "Hcg Hpc".
    assert (Htgt78 : add_vec (mword_of_int (PK + 0xea) : mword 64) (sign_extend' 64 (sign_extend' 21 (concat_vec (mword_of_int 1991 : mword 11) ('b"0")))) = mword_of_int (PK + 0x78)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgt78) in "Hpc".
    iApply ("Hcont" $! mf bs with "[%] Hcg Hpc Hap Hva Hpanicking Hpanicked Htx Hsent HR").
    intros c Hc.
    pose proof (is_cs_idx_true_neq ra_idx c ltac:(vm_compute; reflexivity) Hc) as N1.
    pose proof (is_cs_idx_true_neq a0_idx c ltac:(vm_compute; reflexivity) Hc) as N10.
    pose proof (is_cs_idx_true_neq a1_idx c ltac:(vm_compute; reflexivity) Hc) as N11.
    pose proof (is_cs_idx_true_neq (mword_of_int 12 : mword 5) c ltac:(vm_compute; reflexivity) Hc) as N12.
    pose proof (is_cs_idx_true_neq (mword_of_int 14 : mword 5) c ltac:(vm_compute; reflexivity) Hc) as N14.
    pose proof (is_cs_idx_true_neq a5_idx c ltac:(vm_compute; reflexivity) Hc) as N15.
    rewrite (callee_saved_lookup Hcs c Hc).
    rewrite /D6 upd_ne; [| congruence]. rewrite /D5 upd_ne; [| congruence].
    rewrite /D4 upd_ne; [| congruence]. rewrite /D3 upd_ne; [| congruence].
    rewrite /D2 upd_ne; [| congruence]. rewrite /D1 upd_ne; [reflexivity | congruence].
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  The six other 64-bit value arms.  Each is [va_arg] (shared above), *)
  (*  the (sign, base) pair, a [c.ld] of the whole slot, printint, the   *)
  (*  [addiw s1,s4,n] that says how many format characters the directive *)
  (*  consumed, and the jump back to the advance block.  They differ in  *)
  (*  nothing else -- [%lx] does not even set [a2], because printint's   *)
  (*  contract is indifferent to [sign].                                 *)
  (* ------------------------------------------------------------------ *)


  Lemma wp_printk_arm_ld (γ : gname) (γd : uart_names) (Φ : mval -> iProp Σ)
      (m mc : regfile) (K : nat) (k i : nat) (l : list (bv 8)) (pv pkv : mword 32)
      (dqm dqm2 : dfrac) (Rest : iProp Σ) :
    let sp0 := m !!! Regidx csp_rs1 in
    let s0v := add_vec sp0 (sign_extend' 64 (mword_of_int (-64) : mword 12)) in
    (38 <= K)%nat ->
    (k < 7)%nat ->
    (Z.of_nat i + 2 < 2^31) ->
    eq_vec (sign_extend' 64 pv) zero_reg = false ->
    neq_vec (sign_extend' 64 pkv) zero_reg = false ->
    mc !!! Regidx s0_idx = s0v ->
    mc !!! Regidx (mword_of_int 22 : mword 5) = (mword_of_int 10 : mword 64) ->
    mc !!! Regidx (mword_of_int 20 : mword 5) = mword_of_int (Z.of_nat i) ->
    sie_cap_gpr γ mc (K - 24)%nat -∗
    kernel_text -∗ kernel_data -∗
    pc_is (mword_of_int (PK + 0xb8 + 0) : mword 64) -∗
    (pa_stk sp0 23) ↦₈ (pk_ap s0v k) -∗
    pk_va sp0 m -∗
    (mword_of_int KernelSyms.panicking : mword 64) ↦₄{ dqm } pv -∗
    (mword_of_int KernelSyms.panicked : mword 64) ↦₄{ dqm2 } pkv -∗
    dev_inv γd -∗ uart_tx_own γd l -∗ uart_dlab_off γd -∗
    Rest -∗
    ( ∀ (mf : regfile) (bs : list (bv 8)),
      ⌜ (forall c : mword 5, is_cs_idx c = true -> c <> mword_of_int 9 ->
           mf !!! Regidx c = mc !!! Regidx c)
        /\ mf !!! Regidx (mword_of_int 9 : mword 5) = mword_of_int (Z.of_nat i + 2) ⌝ -∗
      sie_cap_gpr γ mf (K - 24)%nat -∗
      pc_is (mword_of_int (PK + 0x78) : mword 64) -∗
      (pa_stk sp0 23) ↦₈ (pk_ap s0v (S k)) -∗
      pk_va sp0 m -∗
      (mword_of_int KernelSyms.panicking : mword 64) ↦₄{ dqm } pv -∗
      (mword_of_int KernelSyms.panicked : mword 64) ↦₄{ dqm2 } pkv -∗
      uart_tx_own γd (l ++ bs) -∗ uart_sent γd (l ++ bs) -∗
      Rest -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    intros sp0 s0v HK Hk Hi31 Hpv Hpkv Hs0 Hs6 Hs4.
    assert (HK14 : (14 <= K - 24)%nat) by lia.
    iIntros "Hcg #Htext #Hkdata Hpc Hap Hva Hpanicking Hpanicked #Hdev Htx #Hdlab HR Hcont".
    iApply (wp_printk_vaarg γ Φ mc K 0xb8 sp0 s0v k Hs0 eq_refl
              with "Hcg [] Hpc Hap [-]").
    { rewrite /pk_vaarg_instrs.
      iSplitR; [iApply (pki_b8 with "Htext") | ].
      iSplitR; [iApply (pki_bc with "Htext") | ].
      iApply (pki_c0 with "Htext"). }
    iIntros (V) "%Hv Hcg Hpc Hap".
    destruct Hv as (Hva5 & Hvs0 & Hvk).
    iApply (wp_cli_s_sconf γ Φ (mword_of_int (PK + 0xc4)) (mword_of_int 12 : mword 5) (mword_of_int 1 : mword 6)
              (mword_of_int 1 : mword 64) V (K - 24)%nat
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc [] [-]").
    { iApply (pki_c4 with "Htext"). }
    iIntros "Hcg Hpc".
    set (S0 := <[Regidx (mword_of_int 12 : mword 5) := regval_into_reg (mword_of_int 1 : mword 64)]> V).
    assert (Hpac6 : add_vec_int (mword_of_int (PK + 0xc4) : mword 64) 2 = mword_of_int (PK + 0xc6)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpac6) in "Hpc".
    iApply (wp_cmv_s_sconf γ Φ (mword_of_int (PK + 0xc6)) a1_idx (mword_of_int 22 : mword 5)
              S0 (K - 24)%nat ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hcg Hpc [] [-]").
    { iApply (pki_c6 with "Htext"). }
    iIntros "Hcg Hpc".
    set (S1 := <[Regidx a1_idx := regval_into_reg (add_vec zero_reg (S0 !!! Regidx (mword_of_int 22 : mword 5)))]> S0).
    assert (HS1a1 : S1 !!! Regidx a1_idx = (mword_of_int 10 : mword 64)).
    { rewrite /S1 upd_eq. unfold regval_into_reg.
      rewrite /S0 upd_ne; [| reg_neq].
      rewrite (Hvk (mword_of_int 22 : mword 5) ltac:(mw_neq) ltac:(mw_neq)).
      rewrite Hs6. apply pi_addv_zero_l. }
    assert (HS1a5 : S1 !!! Regidx a5_idx = pk_ap s0v k).
    { rewrite /S1 upd_ne; [| reg_neq]. rewrite /S0 upd_ne; [| reg_neq]. exact Hva5. }
    assert (Hpac8 : add_vec_int (mword_of_int (PK + 0xc6) : mword 64) 2 = mword_of_int (PK + 0xc8)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpac8) in "Hpc".
    (* the argument: a whole 8-byte slot this time *)
    iDestruct (pk_va_acc sp0 m k Hk with "Hva") as "[Hslot Hvacl]".
    assert (Hlda : add_vec (S1 !!! Regidx a5_idx) (sign_extend' 64 (mword_of_int 0 : mword 12)) = pa_stk sp0 (7 - k)).
    { rewrite HS1a5.
      replace (sign_extend' 64 (mword_of_int 0 : mword 12)) with (mword_of_int 0 : mword 64)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite kv_addv_zero. apply pk_ap_slot. exact Hk. }
    iEval (rewrite -Hlda) in "Hslot".
    iApply (wp_cld_s_sconf γ Φ (mword_of_int (PK + 0xc8)) a0_idx a5_idx (mword_of_int 0 : mword 12)
              S1 (K - 24)%nat (pk_vararg m k)
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hcg Hpc [] Hslot [-]").
    { iApply (pki_c8 with "Htext"). }
    iIntros "Hcg Hpc Hslot". iEval (rewrite Hlda) in "Hslot".
    iDestruct ("Hvacl" with "Hslot") as "Hva".
    set (S2 := <[Regidx a0_idx := regval_into_reg (pk_vararg m k)]> S1).
    assert (HS2a1 : S2 !!! Regidx a1_idx = (mword_of_int 10 : mword 64))
      by (rewrite /S2 upd_ne; [exact HS1a1 | reg_neq]).
    assert (Hpaca : add_vec_int (mword_of_int (PK + 0xc8) : mword 64) 2 = mword_of_int (PK + 0xca)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpaca) in "Hpc".
    iApply (wp_jal_s_sconf γ Φ (mword_of_int (PK + 0xca)) ra_idx (mword_of_int 2096800 : mword 21)
              S2 (K - 24)%nat ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              ltac:(vm_compute; reflexivity)
              with "Hcg Hpc [] [-]").
    { iApply (pki_ca with "Htext"). }
    iIntros "Hcg Hpc".
    set (S3 := <[Regidx ra_idx := regval_into_reg (add_vec_int (mword_of_int (PK + 0xca) : mword 64) 4)]> S2).
    assert (Htgtp : add_vec (mword_of_int (PK + 0xca) : mword 64) (sign_extend' 64 (mword_of_int 2096800 : mword 21)) = mword_of_int KernelSyms.printint) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgtp) in "Hpc".
    assert (HS3a1 : (10 <= uint (S3 !!! Regidx a1_idx) <= 16)%Z).
    { rewrite /S3 upd_ne; [| reg_neq]. rewrite HS2a1.
      rewrite (uint_moi_small 10 ltac:(change (2^64) with 18446744073709551616; lia)). lia. }
    iApply (wp_printint γ γd Φ S3 (K - 24)%nat l pv pkv dqm dqm2 HK14 HS3a1 Hpv Hpkv
              with "Hcg Htext Hkdata Hpc Hpanicking Hpanicked Hdev Htx Hdlab [-]").
    iIntros (mf bs) "Hcg Hpc %Hcs Hpanicking Hpanicked Htx #Hsent".
    destruct Hcs as [Hcs Hra].
    assert (Hret : ret_pc (S3 !!! Regidx ra_idx) = mword_of_int (PK + 0xce))
      by (rewrite /S3 upd_eq; unfold ret_pc; apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hret) in "Hpc".
    (* +0xce addiw s1,s4,2 : how far the directive advanced the scan *)
    assert (Hmfs4 : mf !!! Regidx (mword_of_int 20 : mword 5) = mword_of_int (Z.of_nat i)).
    { rewrite (callee_saved_lookup Hcs (mword_of_int 20 : mword 5) ltac:(vm_compute; reflexivity)).
      rewrite /S3 upd_ne; [| reg_neq]. rewrite /S2 upd_ne; [| reg_neq].
      rewrite /S1 upd_ne; [| reg_neq]. rewrite /S0 upd_ne; [| reg_neq]. 
      rewrite (Hvk (mword_of_int 20 : mword 5) ltac:(mw_neq) ltac:(mw_neq)). exact Hs4. }
    iApply (wp_addiw_s_sconf γ Φ (mword_of_int (PK + 0xce)) (mword_of_int 9 : mword 5) (mword_of_int 20 : mword 5) (mword_of_int 2 : mword 12)
              mf (K - 24)%nat ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hcg Hpc [] [-]").
    { iApply (pki_ce with "Htext"). }
    iIntros "Hcg Hpc".
    set (T := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg (sign_extend' 64 (subrange_vec_dec
                 (add_vec (mf !!! Regidx (mword_of_int 20 : mword 5)) (sign_extend' 64 (mword_of_int 2 : mword 12))) 31 0))]> mf).
    assert (HTs1 : T !!! Regidx (mword_of_int 9 : mword 5) = mword_of_int (Z.of_nat i + 2)).
    { rewrite /T upd_eq. unfold regval_into_reg. rewrite Hmfs4.
      apply (addiw_lit (Z.of_nat i) 2 (sign_extend' 64 (mword_of_int 2 : mword 12))
               ltac:(apply bv_eq; vm_compute; reflexivity)
               ltac:(change (2^31) with 2147483648 in Hi31 |- *; lia)). }
    assert (Hpad2 : add_vec_int (mword_of_int (PK + 0xce) : mword 64) 4 = mword_of_int (PK + 0xd2)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpad2) in "Hpc".
    (* +0xd2 j 0x78 *)
    iApply (wp_cj_s_sconf γ Φ (mword_of_int (PK + 0xd2)) (sign_extend' 21 (concat_vec (mword_of_int 2003 : mword 11) ('b"0")))
              T (K - 24)%nat ltac:(vm_compute; reflexivity)
              with "Hcg Hpc [] [-]").
    { iApply (pki_d2 with "Htext"). }
    iNext. iIntros "Hcg Hpc".
    assert (Htgt78 : add_vec (mword_of_int (PK + 0xd2) : mword 64) (sign_extend' 64 (sign_extend' 21 (concat_vec (mword_of_int 2003 : mword 11) ('b"0")))) = mword_of_int (PK + 0x78)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgt78) in "Hpc".
    iApply ("Hcont" $! T bs with "[%] Hcg Hpc Hap Hva Hpanicking Hpanicked Htx Hsent HR").
    split; [| exact HTs1].
    intros c Hc N9.
    pose proof (is_cs_idx_true_neq ra_idx c ltac:(vm_compute; reflexivity) Hc) as N1.
    pose proof (is_cs_idx_true_neq a0_idx c ltac:(vm_compute; reflexivity) Hc) as N10.
    pose proof (is_cs_idx_true_neq a1_idx c ltac:(vm_compute; reflexivity) Hc) as N11.
    pose proof (is_cs_idx_true_neq (mword_of_int 12 : mword 5) c ltac:(vm_compute; reflexivity) Hc) as N12.
    pose proof (is_cs_idx_true_neq (mword_of_int 14 : mword 5) c ltac:(vm_compute; reflexivity) Hc) as N14.
    pose proof (is_cs_idx_true_neq a5_idx c ltac:(vm_compute; reflexivity) Hc) as N15.
    rewrite /T upd_ne; [| congruence].
    rewrite (callee_saved_lookup Hcs c Hc).
    rewrite /S3 upd_ne; [| congruence]. rewrite /S2 upd_ne; [| congruence].
    rewrite /S1 upd_ne; [| congruence]. rewrite /S0 upd_ne; [| congruence]. 
    apply Hvk; congruence.
  Qed.


  Lemma wp_printk_arm_lld (γ : gname) (γd : uart_names) (Φ : mval -> iProp Σ)
      (m mc : regfile) (K : nat) (k i : nat) (l : list (bv 8)) (pv pkv : mword 32)
      (dqm dqm2 : dfrac) (Rest : iProp Σ) :
    let sp0 := m !!! Regidx csp_rs1 in
    let s0v := add_vec sp0 (sign_extend' 64 (mword_of_int (-64) : mword 12)) in
    (38 <= K)%nat ->
    (k < 7)%nat ->
    (Z.of_nat i + 3 < 2^31) ->
    eq_vec (sign_extend' 64 pv) zero_reg = false ->
    neq_vec (sign_extend' 64 pkv) zero_reg = false ->
    mc !!! Regidx s0_idx = s0v ->
    mc !!! Regidx (mword_of_int 22 : mword 5) = (mword_of_int 10 : mword 64) ->
    mc !!! Regidx (mword_of_int 20 : mword 5) = mword_of_int (Z.of_nat i) ->
    sie_cap_gpr γ mc (K - 24)%nat -∗
    kernel_text -∗ kernel_data -∗
    pc_is (mword_of_int (PK + 0xf6 + 0) : mword 64) -∗
    (pa_stk sp0 23) ↦₈ (pk_ap s0v k) -∗
    pk_va sp0 m -∗
    (mword_of_int KernelSyms.panicking : mword 64) ↦₄{ dqm } pv -∗
    (mword_of_int KernelSyms.panicked : mword 64) ↦₄{ dqm2 } pkv -∗
    dev_inv γd -∗ uart_tx_own γd l -∗ uart_dlab_off γd -∗
    Rest -∗
    ( ∀ (mf : regfile) (bs : list (bv 8)),
      ⌜ (forall c : mword 5, is_cs_idx c = true -> c <> mword_of_int 9 ->
           mf !!! Regidx c = mc !!! Regidx c)
        /\ mf !!! Regidx (mword_of_int 9 : mword 5) = mword_of_int (Z.of_nat i + 3) ⌝ -∗
      sie_cap_gpr γ mf (K - 24)%nat -∗
      pc_is (mword_of_int (PK + 0x78) : mword 64) -∗
      (pa_stk sp0 23) ↦₈ (pk_ap s0v (S k)) -∗
      pk_va sp0 m -∗
      (mword_of_int KernelSyms.panicking : mword 64) ↦₄{ dqm } pv -∗
      (mword_of_int KernelSyms.panicked : mword 64) ↦₄{ dqm2 } pkv -∗
      uart_tx_own γd (l ++ bs) -∗ uart_sent γd (l ++ bs) -∗
      Rest -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    intros sp0 s0v HK Hk Hi31 Hpv Hpkv Hs0 Hs6 Hs4.
    assert (HK14 : (14 <= K - 24)%nat) by lia.
    iIntros "Hcg #Htext #Hkdata Hpc Hap Hva Hpanicking Hpanicked #Hdev Htx #Hdlab HR Hcont".
    iApply (wp_printk_vaarg γ Φ mc K 0xf6 sp0 s0v k Hs0 eq_refl
              with "Hcg [] Hpc Hap [-]").
    { rewrite /pk_vaarg_instrs.
      iSplitR; [iApply (pki_f6 with "Htext") | ].
      iSplitR; [iApply (pki_fa with "Htext") | ].
      iApply (pki_fe with "Htext"). }
    iIntros (V) "%Hv Hcg Hpc Hap".
    destruct Hv as (Hva5 & Hvs0 & Hvk).
    iApply (wp_cli_s_sconf γ Φ (mword_of_int (PK + 0x102)) (mword_of_int 12 : mword 5) (mword_of_int 1 : mword 6)
              (mword_of_int 1 : mword 64) V (K - 24)%nat
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc [] [-]").
    { iApply (pki_102 with "Htext"). }
    iIntros "Hcg Hpc".
    set (S0 := <[Regidx (mword_of_int 12 : mword 5) := regval_into_reg (mword_of_int 1 : mword 64)]> V).
    assert (Hpa104 : add_vec_int (mword_of_int (PK + 0x102) : mword 64) 2 = mword_of_int (PK + 0x104)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpa104) in "Hpc".
    iApply (wp_cli_s_sconf γ Φ (mword_of_int (PK + 0x104)) a1_idx (mword_of_int 10 : mword 6)
              (mword_of_int 10 : mword 64) S0 (K - 24)%nat
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc [] [-]").
    { iApply (pki_104 with "Htext"). }
    iIntros "Hcg Hpc".
    set (S1 := <[Regidx a1_idx := regval_into_reg (mword_of_int 10 : mword 64)]> S0).
    assert (HS1a1 : S1 !!! Regidx a1_idx = (mword_of_int 10 : mword 64))
      by (rewrite /S1 upd_eq; reflexivity).
    assert (HS1a5 : S1 !!! Regidx a5_idx = pk_ap s0v k).
    { rewrite /S1 upd_ne; [| reg_neq]. rewrite /S0 upd_ne; [| reg_neq]. exact Hva5. }
    assert (Hpa106 : add_vec_int (mword_of_int (PK + 0x104) : mword 64) 2 = mword_of_int (PK + 0x106)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpa106) in "Hpc".
    (* the argument: a whole 8-byte slot this time *)
    iDestruct (pk_va_acc sp0 m k Hk with "Hva") as "[Hslot Hvacl]".
    assert (Hlda : add_vec (S1 !!! Regidx a5_idx) (sign_extend' 64 (mword_of_int 0 : mword 12)) = pa_stk sp0 (7 - k)).
    { rewrite HS1a5.
      replace (sign_extend' 64 (mword_of_int 0 : mword 12)) with (mword_of_int 0 : mword 64)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite kv_addv_zero. apply pk_ap_slot. exact Hk. }
    iEval (rewrite -Hlda) in "Hslot".
    iApply (wp_cld_s_sconf γ Φ (mword_of_int (PK + 0x106)) a0_idx a5_idx (mword_of_int 0 : mword 12)
              S1 (K - 24)%nat (pk_vararg m k)
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hcg Hpc [] Hslot [-]").
    { iApply (pki_106 with "Htext"). }
    iIntros "Hcg Hpc Hslot". iEval (rewrite Hlda) in "Hslot".
    iDestruct ("Hvacl" with "Hslot") as "Hva".
    set (S2 := <[Regidx a0_idx := regval_into_reg (pk_vararg m k)]> S1).
    assert (HS2a1 : S2 !!! Regidx a1_idx = (mword_of_int 10 : mword 64))
      by (rewrite /S2 upd_ne; [exact HS1a1 | reg_neq]).
    assert (Hpa108 : add_vec_int (mword_of_int (PK + 0x106) : mword 64) 2 = mword_of_int (PK + 0x108)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpa108) in "Hpc".
    iApply (wp_jal_s_sconf γ Φ (mword_of_int (PK + 0x108)) ra_idx (mword_of_int 2096738 : mword 21)
              S2 (K - 24)%nat ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              ltac:(vm_compute; reflexivity)
              with "Hcg Hpc [] [-]").
    { iApply (pki_108 with "Htext"). }
    iIntros "Hcg Hpc".
    set (S3 := <[Regidx ra_idx := regval_into_reg (add_vec_int (mword_of_int (PK + 0x108) : mword 64) 4)]> S2).
    assert (Htgtp : add_vec (mword_of_int (PK + 0x108) : mword 64) (sign_extend' 64 (mword_of_int 2096738 : mword 21)) = mword_of_int KernelSyms.printint) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgtp) in "Hpc".
    assert (HS3a1 : (10 <= uint (S3 !!! Regidx a1_idx) <= 16)%Z).
    { rewrite /S3 upd_ne; [| reg_neq]. rewrite HS2a1.
      rewrite (uint_moi_small 10 ltac:(change (2^64) with 18446744073709551616; lia)). lia. }
    iApply (wp_printint γ γd Φ S3 (K - 24)%nat l pv pkv dqm dqm2 HK14 HS3a1 Hpv Hpkv
              with "Hcg Htext Hkdata Hpc Hpanicking Hpanicked Hdev Htx Hdlab [-]").
    iIntros (mf bs) "Hcg Hpc %Hcs Hpanicking Hpanicked Htx #Hsent".
    destruct Hcs as [Hcs Hra].
    assert (Hret : ret_pc (S3 !!! Regidx ra_idx) = mword_of_int (PK + 0x10c))
      by (rewrite /S3 upd_eq; unfold ret_pc; apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hret) in "Hpc".
    (* +0x10c addiw s1,s4,3 : how far the directive advanced the scan *)
    assert (Hmfs4 : mf !!! Regidx (mword_of_int 20 : mword 5) = mword_of_int (Z.of_nat i)).
    { rewrite (callee_saved_lookup Hcs (mword_of_int 20 : mword 5) ltac:(vm_compute; reflexivity)).
      rewrite /S3 upd_ne; [| reg_neq]. rewrite /S2 upd_ne; [| reg_neq].
      rewrite /S1 upd_ne; [| reg_neq]. rewrite /S0 upd_ne; [| reg_neq]. 
      rewrite (Hvk (mword_of_int 20 : mword 5) ltac:(mw_neq) ltac:(mw_neq)). exact Hs4. }
    iApply (wp_addiw_s_sconf γ Φ (mword_of_int (PK + 0x10c)) (mword_of_int 9 : mword 5) (mword_of_int 20 : mword 5) (mword_of_int 3 : mword 12)
              mf (K - 24)%nat ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hcg Hpc [] [-]").
    { iApply (pki_10c with "Htext"). }
    iIntros "Hcg Hpc".
    set (T := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg (sign_extend' 64 (subrange_vec_dec
                 (add_vec (mf !!! Regidx (mword_of_int 20 : mword 5)) (sign_extend' 64 (mword_of_int 3 : mword 12))) 31 0))]> mf).
    assert (HTs1 : T !!! Regidx (mword_of_int 9 : mword 5) = mword_of_int (Z.of_nat i + 3)).
    { rewrite /T upd_eq. unfold regval_into_reg. rewrite Hmfs4.
      apply (addiw_lit (Z.of_nat i) 3 (sign_extend' 64 (mword_of_int 3 : mword 12))
               ltac:(apply bv_eq; vm_compute; reflexivity)
               ltac:(change (2^31) with 2147483648 in Hi31 |- *; lia)). }
    assert (Hpa110 : add_vec_int (mword_of_int (PK + 0x10c) : mword 64) 4 = mword_of_int (PK + 0x110)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpa110) in "Hpc".
    (* +0x110 j 0x78 *)
    iApply (wp_cj_s_sconf γ Φ (mword_of_int (PK + 0x110)) (sign_extend' 21 (concat_vec (mword_of_int 1972 : mword 11) ('b"0")))
              T (K - 24)%nat ltac:(vm_compute; reflexivity)
              with "Hcg Hpc [] [-]").
    { iApply (pki_110 with "Htext"). }
    iNext. iIntros "Hcg Hpc".
    assert (Htgt78 : add_vec (mword_of_int (PK + 0x110) : mword 64) (sign_extend' 64 (sign_extend' 21 (concat_vec (mword_of_int 1972 : mword 11) ('b"0")))) = mword_of_int (PK + 0x78)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgt78) in "Hpc".
    iApply ("Hcont" $! T bs with "[%] Hcg Hpc Hap Hva Hpanicking Hpanicked Htx Hsent HR").
    split; [| exact HTs1].
    intros c Hc N9.
    pose proof (is_cs_idx_true_neq ra_idx c ltac:(vm_compute; reflexivity) Hc) as N1.
    pose proof (is_cs_idx_true_neq a0_idx c ltac:(vm_compute; reflexivity) Hc) as N10.
    pose proof (is_cs_idx_true_neq a1_idx c ltac:(vm_compute; reflexivity) Hc) as N11.
    pose proof (is_cs_idx_true_neq (mword_of_int 12 : mword 5) c ltac:(vm_compute; reflexivity) Hc) as N12.
    pose proof (is_cs_idx_true_neq (mword_of_int 14 : mword 5) c ltac:(vm_compute; reflexivity) Hc) as N14.
    pose proof (is_cs_idx_true_neq a5_idx c ltac:(vm_compute; reflexivity) Hc) as N15.
    rewrite /T upd_ne; [| congruence].
    rewrite (callee_saved_lookup Hcs c Hc).
    rewrite /S3 upd_ne; [| congruence]. rewrite /S2 upd_ne; [| congruence].
    rewrite /S1 upd_ne; [| congruence]. rewrite /S0 upd_ne; [| congruence]. 
    apply Hvk; congruence.
  Qed.


  Lemma wp_printk_arm_lu (γ : gname) (γd : uart_names) (Φ : mval -> iProp Σ)
      (m mc : regfile) (K : nat) (k i : nat) (l : list (bv 8)) (pv pkv : mword 32)
      (dqm dqm2 : dfrac) (Rest : iProp Σ) :
    let sp0 := m !!! Regidx csp_rs1 in
    let s0v := add_vec sp0 (sign_extend' 64 (mword_of_int (-64) : mword 12)) in
    (38 <= K)%nat ->
    (k < 7)%nat ->
    (Z.of_nat i + 2 < 2^31) ->
    eq_vec (sign_extend' 64 pv) zero_reg = false ->
    neq_vec (sign_extend' 64 pkv) zero_reg = false ->
    mc !!! Regidx s0_idx = s0v ->
    mc !!! Regidx (mword_of_int 22 : mword 5) = (mword_of_int 10 : mword 64) ->
    mc !!! Regidx (mword_of_int 20 : mword 5) = mword_of_int (Z.of_nat i) ->
    sie_cap_gpr γ mc (K - 24)%nat -∗
    kernel_text -∗ kernel_data -∗
    pc_is (mword_of_int (PK + 0x12c + 0) : mword 64) -∗
    (pa_stk sp0 23) ↦₈ (pk_ap s0v k) -∗
    pk_va sp0 m -∗
    (mword_of_int KernelSyms.panicking : mword 64) ↦₄{ dqm } pv -∗
    (mword_of_int KernelSyms.panicked : mword 64) ↦₄{ dqm2 } pkv -∗
    dev_inv γd -∗ uart_tx_own γd l -∗ uart_dlab_off γd -∗
    Rest -∗
    ( ∀ (mf : regfile) (bs : list (bv 8)),
      ⌜ (forall c : mword 5, is_cs_idx c = true -> c <> mword_of_int 9 ->
           mf !!! Regidx c = mc !!! Regidx c)
        /\ mf !!! Regidx (mword_of_int 9 : mword 5) = mword_of_int (Z.of_nat i + 2) ⌝ -∗
      sie_cap_gpr γ mf (K - 24)%nat -∗
      pc_is (mword_of_int (PK + 0x78) : mword 64) -∗
      (pa_stk sp0 23) ↦₈ (pk_ap s0v (S k)) -∗
      pk_va sp0 m -∗
      (mword_of_int KernelSyms.panicking : mword 64) ↦₄{ dqm } pv -∗
      (mword_of_int KernelSyms.panicked : mword 64) ↦₄{ dqm2 } pkv -∗
      uart_tx_own γd (l ++ bs) -∗ uart_sent γd (l ++ bs) -∗
      Rest -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    intros sp0 s0v HK Hk Hi31 Hpv Hpkv Hs0 Hs6 Hs4.
    assert (HK14 : (14 <= K - 24)%nat) by lia.
    iIntros "Hcg #Htext #Hkdata Hpc Hap Hva Hpanicking Hpanicked #Hdev Htx #Hdlab HR Hcont".
    iApply (wp_printk_vaarg γ Φ mc K 0x12c sp0 s0v k Hs0 eq_refl
              with "Hcg [] Hpc Hap [-]").
    { rewrite /pk_vaarg_instrs.
      iSplitR; [iApply (pki_12c with "Htext") | ].
      iSplitR; [iApply (pki_130 with "Htext") | ].
      iApply (pki_134 with "Htext"). }
    iIntros (V) "%Hv Hcg Hpc Hap".
    destruct Hv as (Hva5 & Hvs0 & Hvk).
    iApply (wp_cli_s_sconf γ Φ (mword_of_int (PK + 0x138)) (mword_of_int 12 : mword 5) (mword_of_int 0 : mword 6)
              (mword_of_int 0 : mword 64) V (K - 24)%nat
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc [] [-]").
    { iApply (pki_138 with "Htext"). }
    iIntros "Hcg Hpc".
    set (S0 := <[Regidx (mword_of_int 12 : mword 5) := regval_into_reg (mword_of_int 0 : mword 64)]> V).
    assert (Hpa13a : add_vec_int (mword_of_int (PK + 0x138) : mword 64) 2 = mword_of_int (PK + 0x13a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpa13a) in "Hpc".
    iApply (wp_cmv_s_sconf γ Φ (mword_of_int (PK + 0x13a)) a1_idx (mword_of_int 22 : mword 5)
              S0 (K - 24)%nat ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hcg Hpc [] [-]").
    { iApply (pki_13a with "Htext"). }
    iIntros "Hcg Hpc".
    set (S1 := <[Regidx a1_idx := regval_into_reg (add_vec zero_reg (S0 !!! Regidx (mword_of_int 22 : mword 5)))]> S0).
    assert (HS1a1 : S1 !!! Regidx a1_idx = (mword_of_int 10 : mword 64)).
    { rewrite /S1 upd_eq. unfold regval_into_reg.
      rewrite /S0 upd_ne; [| reg_neq].
      rewrite (Hvk (mword_of_int 22 : mword 5) ltac:(mw_neq) ltac:(mw_neq)).
      rewrite Hs6. apply pi_addv_zero_l. }
    assert (HS1a5 : S1 !!! Regidx a5_idx = pk_ap s0v k).
    { rewrite /S1 upd_ne; [| reg_neq]. rewrite /S0 upd_ne; [| reg_neq]. exact Hva5. }
    assert (Hpa13c : add_vec_int (mword_of_int (PK + 0x13a) : mword 64) 2 = mword_of_int (PK + 0x13c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpa13c) in "Hpc".
    (* the argument: a whole 8-byte slot this time *)
    iDestruct (pk_va_acc sp0 m k Hk with "Hva") as "[Hslot Hvacl]".
    assert (Hlda : add_vec (S1 !!! Regidx a5_idx) (sign_extend' 64 (mword_of_int 0 : mword 12)) = pa_stk sp0 (7 - k)).
    { rewrite HS1a5.
      replace (sign_extend' 64 (mword_of_int 0 : mword 12)) with (mword_of_int 0 : mword 64)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite kv_addv_zero. apply pk_ap_slot. exact Hk. }
    iEval (rewrite -Hlda) in "Hslot".
    iApply (wp_cld_s_sconf γ Φ (mword_of_int (PK + 0x13c)) a0_idx a5_idx (mword_of_int 0 : mword 12)
              S1 (K - 24)%nat (pk_vararg m k)
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hcg Hpc [] Hslot [-]").
    { iApply (pki_13c with "Htext"). }
    iIntros "Hcg Hpc Hslot". iEval (rewrite Hlda) in "Hslot".
    iDestruct ("Hvacl" with "Hslot") as "Hva".
    set (S2 := <[Regidx a0_idx := regval_into_reg (pk_vararg m k)]> S1).
    assert (HS2a1 : S2 !!! Regidx a1_idx = (mword_of_int 10 : mword 64))
      by (rewrite /S2 upd_ne; [exact HS1a1 | reg_neq]).
    assert (Hpa13e : add_vec_int (mword_of_int (PK + 0x13c) : mword 64) 2 = mword_of_int (PK + 0x13e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpa13e) in "Hpc".
    iApply (wp_jal_s_sconf γ Φ (mword_of_int (PK + 0x13e)) ra_idx (mword_of_int 2096684 : mword 21)
              S2 (K - 24)%nat ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              ltac:(vm_compute; reflexivity)
              with "Hcg Hpc [] [-]").
    { iApply (pki_13e with "Htext"). }
    iIntros "Hcg Hpc".
    set (S3 := <[Regidx ra_idx := regval_into_reg (add_vec_int (mword_of_int (PK + 0x13e) : mword 64) 4)]> S2).
    assert (Htgtp : add_vec (mword_of_int (PK + 0x13e) : mword 64) (sign_extend' 64 (mword_of_int 2096684 : mword 21)) = mword_of_int KernelSyms.printint) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgtp) in "Hpc".
    assert (HS3a1 : (10 <= uint (S3 !!! Regidx a1_idx) <= 16)%Z).
    { rewrite /S3 upd_ne; [| reg_neq]. rewrite HS2a1.
      rewrite (uint_moi_small 10 ltac:(change (2^64) with 18446744073709551616; lia)). lia. }
    iApply (wp_printint γ γd Φ S3 (K - 24)%nat l pv pkv dqm dqm2 HK14 HS3a1 Hpv Hpkv
              with "Hcg Htext Hkdata Hpc Hpanicking Hpanicked Hdev Htx Hdlab [-]").
    iIntros (mf bs) "Hcg Hpc %Hcs Hpanicking Hpanicked Htx #Hsent".
    destruct Hcs as [Hcs Hra].
    assert (Hret : ret_pc (S3 !!! Regidx ra_idx) = mword_of_int (PK + 0x142))
      by (rewrite /S3 upd_eq; unfold ret_pc; apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hret) in "Hpc".
    (* +0x142 addiw s1,s4,2 : how far the directive advanced the scan *)
    assert (Hmfs4 : mf !!! Regidx (mword_of_int 20 : mword 5) = mword_of_int (Z.of_nat i)).
    { rewrite (callee_saved_lookup Hcs (mword_of_int 20 : mword 5) ltac:(vm_compute; reflexivity)).
      rewrite /S3 upd_ne; [| reg_neq]. rewrite /S2 upd_ne; [| reg_neq].
      rewrite /S1 upd_ne; [| reg_neq]. rewrite /S0 upd_ne; [| reg_neq]. 
      rewrite (Hvk (mword_of_int 20 : mword 5) ltac:(mw_neq) ltac:(mw_neq)). exact Hs4. }
    iApply (wp_addiw_s_sconf γ Φ (mword_of_int (PK + 0x142)) (mword_of_int 9 : mword 5) (mword_of_int 20 : mword 5) (mword_of_int 2 : mword 12)
              mf (K - 24)%nat ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hcg Hpc [] [-]").
    { iApply (pki_142 with "Htext"). }
    iIntros "Hcg Hpc".
    set (T := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg (sign_extend' 64 (subrange_vec_dec
                 (add_vec (mf !!! Regidx (mword_of_int 20 : mword 5)) (sign_extend' 64 (mword_of_int 2 : mword 12))) 31 0))]> mf).
    assert (HTs1 : T !!! Regidx (mword_of_int 9 : mword 5) = mword_of_int (Z.of_nat i + 2)).
    { rewrite /T upd_eq. unfold regval_into_reg. rewrite Hmfs4.
      apply (addiw_lit (Z.of_nat i) 2 (sign_extend' 64 (mword_of_int 2 : mword 12))
               ltac:(apply bv_eq; vm_compute; reflexivity)
               ltac:(change (2^31) with 2147483648 in Hi31 |- *; lia)). }
    assert (Hpa146 : add_vec_int (mword_of_int (PK + 0x142) : mword 64) 4 = mword_of_int (PK + 0x146)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpa146) in "Hpc".
    (* +0x146 j 0x78 *)
    iApply (wp_cj_s_sconf γ Φ (mword_of_int (PK + 0x146)) (sign_extend' 21 (concat_vec (mword_of_int 1945 : mword 11) ('b"0")))
              T (K - 24)%nat ltac:(vm_compute; reflexivity)
              with "Hcg Hpc [] [-]").
    { iApply (pki_146 with "Htext"). }
    iNext. iIntros "Hcg Hpc".
    assert (Htgt78 : add_vec (mword_of_int (PK + 0x146) : mword 64) (sign_extend' 64 (sign_extend' 21 (concat_vec (mword_of_int 1945 : mword 11) ('b"0")))) = mword_of_int (PK + 0x78)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgt78) in "Hpc".
    iApply ("Hcont" $! T bs with "[%] Hcg Hpc Hap Hva Hpanicking Hpanicked Htx Hsent HR").
    split; [| exact HTs1].
    intros c Hc N9.
    pose proof (is_cs_idx_true_neq ra_idx c ltac:(vm_compute; reflexivity) Hc) as N1.
    pose proof (is_cs_idx_true_neq a0_idx c ltac:(vm_compute; reflexivity) Hc) as N10.
    pose proof (is_cs_idx_true_neq a1_idx c ltac:(vm_compute; reflexivity) Hc) as N11.
    pose proof (is_cs_idx_true_neq (mword_of_int 12 : mword 5) c ltac:(vm_compute; reflexivity) Hc) as N12.
    pose proof (is_cs_idx_true_neq (mword_of_int 14 : mword 5) c ltac:(vm_compute; reflexivity) Hc) as N14.
    pose proof (is_cs_idx_true_neq a5_idx c ltac:(vm_compute; reflexivity) Hc) as N15.
    rewrite /T upd_ne; [| congruence].
    rewrite (callee_saved_lookup Hcs c Hc).
    rewrite /S3 upd_ne; [| congruence]. rewrite /S2 upd_ne; [| congruence].
    rewrite /S1 upd_ne; [| congruence]. rewrite /S0 upd_ne; [| congruence]. 
    apply Hvk; congruence.
  Qed.


  Lemma wp_printk_arm_llu (γ : gname) (γd : uart_names) (Φ : mval -> iProp Σ)
      (m mc : regfile) (K : nat) (k i : nat) (l : list (bv 8)) (pv pkv : mword 32)
      (dqm dqm2 : dfrac) (Rest : iProp Σ) :
    let sp0 := m !!! Regidx csp_rs1 in
    let s0v := add_vec sp0 (sign_extend' 64 (mword_of_int (-64) : mword 12)) in
    (38 <= K)%nat ->
    (k < 7)%nat ->
    (Z.of_nat i + 3 < 2^31) ->
    eq_vec (sign_extend' 64 pv) zero_reg = false ->
    neq_vec (sign_extend' 64 pkv) zero_reg = false ->
    mc !!! Regidx s0_idx = s0v ->
    mc !!! Regidx (mword_of_int 22 : mword 5) = (mword_of_int 10 : mword 64) ->
    mc !!! Regidx (mword_of_int 20 : mword 5) = mword_of_int (Z.of_nat i) ->
    sie_cap_gpr γ mc (K - 24)%nat -∗
    kernel_text -∗ kernel_data -∗
    pc_is (mword_of_int (PK + 0x148 + 0) : mword 64) -∗
    (pa_stk sp0 23) ↦₈ (pk_ap s0v k) -∗
    pk_va sp0 m -∗
    (mword_of_int KernelSyms.panicking : mword 64) ↦₄{ dqm } pv -∗
    (mword_of_int KernelSyms.panicked : mword 64) ↦₄{ dqm2 } pkv -∗
    dev_inv γd -∗ uart_tx_own γd l -∗ uart_dlab_off γd -∗
    Rest -∗
    ( ∀ (mf : regfile) (bs : list (bv 8)),
      ⌜ (forall c : mword 5, is_cs_idx c = true -> c <> mword_of_int 9 ->
           mf !!! Regidx c = mc !!! Regidx c)
        /\ mf !!! Regidx (mword_of_int 9 : mword 5) = mword_of_int (Z.of_nat i + 3) ⌝ -∗
      sie_cap_gpr γ mf (K - 24)%nat -∗
      pc_is (mword_of_int (PK + 0x78) : mword 64) -∗
      (pa_stk sp0 23) ↦₈ (pk_ap s0v (S k)) -∗
      pk_va sp0 m -∗
      (mword_of_int KernelSyms.panicking : mword 64) ↦₄{ dqm } pv -∗
      (mword_of_int KernelSyms.panicked : mword 64) ↦₄{ dqm2 } pkv -∗
      uart_tx_own γd (l ++ bs) -∗ uart_sent γd (l ++ bs) -∗
      Rest -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    intros sp0 s0v HK Hk Hi31 Hpv Hpkv Hs0 Hs6 Hs4.
    assert (HK14 : (14 <= K - 24)%nat) by lia.
    iIntros "Hcg #Htext #Hkdata Hpc Hap Hva Hpanicking Hpanicked #Hdev Htx #Hdlab HR Hcont".
    iApply (wp_printk_vaarg γ Φ mc K 0x148 sp0 s0v k Hs0 eq_refl
              with "Hcg [] Hpc Hap [-]").
    { rewrite /pk_vaarg_instrs.
      iSplitR; [iApply (pki_148 with "Htext") | ].
      iSplitR; [iApply (pki_14c with "Htext") | ].
      iApply (pki_150 with "Htext"). }
    iIntros (V) "%Hv Hcg Hpc Hap".
    destruct Hv as (Hva5 & Hvs0 & Hvk).
    iApply (wp_cli_s_sconf γ Φ (mword_of_int (PK + 0x154)) (mword_of_int 12 : mword 5) (mword_of_int 0 : mword 6)
              (mword_of_int 0 : mword 64) V (K - 24)%nat
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc [] [-]").
    { iApply (pki_154 with "Htext"). }
    iIntros "Hcg Hpc".
    set (S0 := <[Regidx (mword_of_int 12 : mword 5) := regval_into_reg (mword_of_int 0 : mword 64)]> V).
    assert (Hpa156 : add_vec_int (mword_of_int (PK + 0x154) : mword 64) 2 = mword_of_int (PK + 0x156)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpa156) in "Hpc".
    iApply (wp_cli_s_sconf γ Φ (mword_of_int (PK + 0x156)) a1_idx (mword_of_int 10 : mword 6)
              (mword_of_int 10 : mword 64) S0 (K - 24)%nat
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc [] [-]").
    { iApply (pki_156 with "Htext"). }
    iIntros "Hcg Hpc".
    set (S1 := <[Regidx a1_idx := regval_into_reg (mword_of_int 10 : mword 64)]> S0).
    assert (HS1a1 : S1 !!! Regidx a1_idx = (mword_of_int 10 : mword 64))
      by (rewrite /S1 upd_eq; reflexivity).
    assert (HS1a5 : S1 !!! Regidx a5_idx = pk_ap s0v k).
    { rewrite /S1 upd_ne; [| reg_neq]. rewrite /S0 upd_ne; [| reg_neq]. exact Hva5. }
    assert (Hpa158 : add_vec_int (mword_of_int (PK + 0x156) : mword 64) 2 = mword_of_int (PK + 0x158)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpa158) in "Hpc".
    (* the argument: a whole 8-byte slot this time *)
    iDestruct (pk_va_acc sp0 m k Hk with "Hva") as "[Hslot Hvacl]".
    assert (Hlda : add_vec (S1 !!! Regidx a5_idx) (sign_extend' 64 (mword_of_int 0 : mword 12)) = pa_stk sp0 (7 - k)).
    { rewrite HS1a5.
      replace (sign_extend' 64 (mword_of_int 0 : mword 12)) with (mword_of_int 0 : mword 64)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite kv_addv_zero. apply pk_ap_slot. exact Hk. }
    iEval (rewrite -Hlda) in "Hslot".
    iApply (wp_cld_s_sconf γ Φ (mword_of_int (PK + 0x158)) a0_idx a5_idx (mword_of_int 0 : mword 12)
              S1 (K - 24)%nat (pk_vararg m k)
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hcg Hpc [] Hslot [-]").
    { iApply (pki_158 with "Htext"). }
    iIntros "Hcg Hpc Hslot". iEval (rewrite Hlda) in "Hslot".
    iDestruct ("Hvacl" with "Hslot") as "Hva".
    set (S2 := <[Regidx a0_idx := regval_into_reg (pk_vararg m k)]> S1).
    assert (HS2a1 : S2 !!! Regidx a1_idx = (mword_of_int 10 : mword 64))
      by (rewrite /S2 upd_ne; [exact HS1a1 | reg_neq]).
    assert (Hpa15a : add_vec_int (mword_of_int (PK + 0x158) : mword 64) 2 = mword_of_int (PK + 0x15a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpa15a) in "Hpc".
    iApply (wp_jal_s_sconf γ Φ (mword_of_int (PK + 0x15a)) ra_idx (mword_of_int 2096656 : mword 21)
              S2 (K - 24)%nat ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              ltac:(vm_compute; reflexivity)
              with "Hcg Hpc [] [-]").
    { iApply (pki_15a with "Htext"). }
    iIntros "Hcg Hpc".
    set (S3 := <[Regidx ra_idx := regval_into_reg (add_vec_int (mword_of_int (PK + 0x15a) : mword 64) 4)]> S2).
    assert (Htgtp : add_vec (mword_of_int (PK + 0x15a) : mword 64) (sign_extend' 64 (mword_of_int 2096656 : mword 21)) = mword_of_int KernelSyms.printint) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgtp) in "Hpc".
    assert (HS3a1 : (10 <= uint (S3 !!! Regidx a1_idx) <= 16)%Z).
    { rewrite /S3 upd_ne; [| reg_neq]. rewrite HS2a1.
      rewrite (uint_moi_small 10 ltac:(change (2^64) with 18446744073709551616; lia)). lia. }
    iApply (wp_printint γ γd Φ S3 (K - 24)%nat l pv pkv dqm dqm2 HK14 HS3a1 Hpv Hpkv
              with "Hcg Htext Hkdata Hpc Hpanicking Hpanicked Hdev Htx Hdlab [-]").
    iIntros (mf bs) "Hcg Hpc %Hcs Hpanicking Hpanicked Htx #Hsent".
    destruct Hcs as [Hcs Hra].
    assert (Hret : ret_pc (S3 !!! Regidx ra_idx) = mword_of_int (PK + 0x15e))
      by (rewrite /S3 upd_eq; unfold ret_pc; apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hret) in "Hpc".
    (* +0x15e addiw s1,s4,3 : how far the directive advanced the scan *)
    assert (Hmfs4 : mf !!! Regidx (mword_of_int 20 : mword 5) = mword_of_int (Z.of_nat i)).
    { rewrite (callee_saved_lookup Hcs (mword_of_int 20 : mword 5) ltac:(vm_compute; reflexivity)).
      rewrite /S3 upd_ne; [| reg_neq]. rewrite /S2 upd_ne; [| reg_neq].
      rewrite /S1 upd_ne; [| reg_neq]. rewrite /S0 upd_ne; [| reg_neq]. 
      rewrite (Hvk (mword_of_int 20 : mword 5) ltac:(mw_neq) ltac:(mw_neq)). exact Hs4. }
    iApply (wp_addiw_s_sconf γ Φ (mword_of_int (PK + 0x15e)) (mword_of_int 9 : mword 5) (mword_of_int 20 : mword 5) (mword_of_int 3 : mword 12)
              mf (K - 24)%nat ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hcg Hpc [] [-]").
    { iApply (pki_15e with "Htext"). }
    iIntros "Hcg Hpc".
    set (T := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg (sign_extend' 64 (subrange_vec_dec
                 (add_vec (mf !!! Regidx (mword_of_int 20 : mword 5)) (sign_extend' 64 (mword_of_int 3 : mword 12))) 31 0))]> mf).
    assert (HTs1 : T !!! Regidx (mword_of_int 9 : mword 5) = mword_of_int (Z.of_nat i + 3)).
    { rewrite /T upd_eq. unfold regval_into_reg. rewrite Hmfs4.
      apply (addiw_lit (Z.of_nat i) 3 (sign_extend' 64 (mword_of_int 3 : mword 12))
               ltac:(apply bv_eq; vm_compute; reflexivity)
               ltac:(change (2^31) with 2147483648 in Hi31 |- *; lia)). }
    assert (Hpa162 : add_vec_int (mword_of_int (PK + 0x15e) : mword 64) 4 = mword_of_int (PK + 0x162)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpa162) in "Hpc".
    (* +0x162 j 0x78 *)
    iApply (wp_cj_s_sconf γ Φ (mword_of_int (PK + 0x162)) (sign_extend' 21 (concat_vec (mword_of_int 1931 : mword 11) ('b"0")))
              T (K - 24)%nat ltac:(vm_compute; reflexivity)
              with "Hcg Hpc [] [-]").
    { iApply (pki_162 with "Htext"). }
    iNext. iIntros "Hcg Hpc".
    assert (Htgt78 : add_vec (mword_of_int (PK + 0x162) : mword 64) (sign_extend' 64 (sign_extend' 21 (concat_vec (mword_of_int 1931 : mword 11) ('b"0")))) = mword_of_int (PK + 0x78)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgt78) in "Hpc".
    iApply ("Hcont" $! T bs with "[%] Hcg Hpc Hap Hva Hpanicking Hpanicked Htx Hsent HR").
    split; [| exact HTs1].
    intros c Hc N9.
    pose proof (is_cs_idx_true_neq ra_idx c ltac:(vm_compute; reflexivity) Hc) as N1.
    pose proof (is_cs_idx_true_neq a0_idx c ltac:(vm_compute; reflexivity) Hc) as N10.
    pose proof (is_cs_idx_true_neq a1_idx c ltac:(vm_compute; reflexivity) Hc) as N11.
    pose proof (is_cs_idx_true_neq (mword_of_int 12 : mword 5) c ltac:(vm_compute; reflexivity) Hc) as N12.
    pose proof (is_cs_idx_true_neq (mword_of_int 14 : mword 5) c ltac:(vm_compute; reflexivity) Hc) as N14.
    pose proof (is_cs_idx_true_neq a5_idx c ltac:(vm_compute; reflexivity) Hc) as N15.
    rewrite /T upd_ne; [| congruence].
    rewrite (callee_saved_lookup Hcs c Hc).
    rewrite /S3 upd_ne; [| congruence]. rewrite /S2 upd_ne; [| congruence].
    rewrite /S1 upd_ne; [| congruence]. rewrite /S0 upd_ne; [| congruence]. 
    apply Hvk; congruence.
  Qed.


  Lemma wp_printk_arm_lx (γ : gname) (γd : uart_names) (Φ : mval -> iProp Σ)
      (m mc : regfile) (K : nat) (k i : nat) (l : list (bv 8)) (pv pkv : mword 32)
      (dqm dqm2 : dfrac) (Rest : iProp Σ) :
    let sp0 := m !!! Regidx csp_rs1 in
    let s0v := add_vec sp0 (sign_extend' 64 (mword_of_int (-64) : mword 12)) in
    (38 <= K)%nat ->
    (k < 7)%nat ->
    (Z.of_nat i + 2 < 2^31) ->
    eq_vec (sign_extend' 64 pv) zero_reg = false ->
    neq_vec (sign_extend' 64 pkv) zero_reg = false ->
    mc !!! Regidx s0_idx = s0v ->
    mc !!! Regidx (mword_of_int 22 : mword 5) = (mword_of_int 10 : mword 64) ->
    mc !!! Regidx (mword_of_int 20 : mword 5) = mword_of_int (Z.of_nat i) ->
    sie_cap_gpr γ mc (K - 24)%nat -∗
    kernel_text -∗ kernel_data -∗
    pc_is (mword_of_int (PK + 0x17e + 0) : mword 64) -∗
    (pa_stk sp0 23) ↦₈ (pk_ap s0v k) -∗
    pk_va sp0 m -∗
    (mword_of_int KernelSyms.panicking : mword 64) ↦₄{ dqm } pv -∗
    (mword_of_int KernelSyms.panicked : mword 64) ↦₄{ dqm2 } pkv -∗
    dev_inv γd -∗ uart_tx_own γd l -∗ uart_dlab_off γd -∗
    Rest -∗
    ( ∀ (mf : regfile) (bs : list (bv 8)),
      ⌜ (forall c : mword 5, is_cs_idx c = true -> c <> mword_of_int 9 ->
           mf !!! Regidx c = mc !!! Regidx c)
        /\ mf !!! Regidx (mword_of_int 9 : mword 5) = mword_of_int (Z.of_nat i + 2) ⌝ -∗
      sie_cap_gpr γ mf (K - 24)%nat -∗
      pc_is (mword_of_int (PK + 0x78) : mword 64) -∗
      (pa_stk sp0 23) ↦₈ (pk_ap s0v (S k)) -∗
      pk_va sp0 m -∗
      (mword_of_int KernelSyms.panicking : mword 64) ↦₄{ dqm } pv -∗
      (mword_of_int KernelSyms.panicked : mword 64) ↦₄{ dqm2 } pkv -∗
      uart_tx_own γd (l ++ bs) -∗ uart_sent γd (l ++ bs) -∗
      Rest -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    intros sp0 s0v HK Hk Hi31 Hpv Hpkv Hs0 Hs6 Hs4.
    assert (HK14 : (14 <= K - 24)%nat) by lia.
    iIntros "Hcg #Htext #Hkdata Hpc Hap Hva Hpanicking Hpanicked #Hdev Htx #Hdlab HR Hcont".
    iApply (wp_printk_vaarg γ Φ mc K 0x17e sp0 s0v k Hs0 eq_refl
              with "Hcg [] Hpc Hap [-]").
    { rewrite /pk_vaarg_instrs.
      iSplitR; [iApply (pki_17e with "Htext") | ].
      iSplitR; [iApply (pki_182 with "Htext") | ].
      iApply (pki_186 with "Htext"). }
    iIntros (V) "%Hv Hcg Hpc Hap".
    destruct Hv as (Hva5 & Hvs0 & Hvk).
    assert (Hpa18a : (mword_of_int (PK + 0x17e + 12) : mword 64) = mword_of_int (PK + 0x18a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpa18a) in "Hpc".
    iApply (wp_cli_s_sconf γ Φ (mword_of_int (PK + 0x18a)) a1_idx (mword_of_int 16 : mword 6)
              (mword_of_int 16 : mword 64) V (K - 24)%nat
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc [] [-]").
    { iApply (pki_18a with "Htext"). }
    iIntros "Hcg Hpc".
    set (S0 := <[Regidx a1_idx := regval_into_reg (mword_of_int 16 : mword 64)]> V).
    assert (HS0a1 : S0 !!! Regidx a1_idx = (mword_of_int 16 : mword 64))
      by (rewrite /S0 upd_eq; reflexivity).
    assert (HS0a5 : S0 !!! Regidx a5_idx = pk_ap s0v k).
    { rewrite /S0 upd_ne; [| reg_neq]. exact Hva5. }
    assert (Hpa18c : add_vec_int (mword_of_int (PK + 0x18a) : mword 64) 2 = mword_of_int (PK + 0x18c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpa18c) in "Hpc".
    (* the argument: a whole 8-byte slot this time *)
    iDestruct (pk_va_acc sp0 m k Hk with "Hva") as "[Hslot Hvacl]".
    assert (Hlda : add_vec (S0 !!! Regidx a5_idx) (sign_extend' 64 (mword_of_int 0 : mword 12)) = pa_stk sp0 (7 - k)).
    { rewrite HS0a5.
      replace (sign_extend' 64 (mword_of_int 0 : mword 12)) with (mword_of_int 0 : mword 64)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite kv_addv_zero. apply pk_ap_slot. exact Hk. }
    iEval (rewrite -Hlda) in "Hslot".
    iApply (wp_cld_s_sconf γ Φ (mword_of_int (PK + 0x18c)) a0_idx a5_idx (mword_of_int 0 : mword 12)
              S0 (K - 24)%nat (pk_vararg m k)
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hcg Hpc [] Hslot [-]").
    { iApply (pki_18c with "Htext"). }
    iIntros "Hcg Hpc Hslot". iEval (rewrite Hlda) in "Hslot".
    iDestruct ("Hvacl" with "Hslot") as "Hva".
    set (S1 := <[Regidx a0_idx := regval_into_reg (pk_vararg m k)]> S0).
    assert (HS1a1 : S1 !!! Regidx a1_idx = (mword_of_int 16 : mword 64))
      by (rewrite /S1 upd_ne; [exact HS0a1 | reg_neq]).
    assert (Hpa18e : add_vec_int (mword_of_int (PK + 0x18c) : mword 64) 2 = mword_of_int (PK + 0x18e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpa18e) in "Hpc".
    iApply (wp_jal_s_sconf γ Φ (mword_of_int (PK + 0x18e)) ra_idx (mword_of_int 2096604 : mword 21)
              S1 (K - 24)%nat ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              ltac:(vm_compute; reflexivity)
              with "Hcg Hpc [] [-]").
    { iApply (pki_18e with "Htext"). }
    iIntros "Hcg Hpc".
    set (S2 := <[Regidx ra_idx := regval_into_reg (add_vec_int (mword_of_int (PK + 0x18e) : mword 64) 4)]> S1).
    assert (Htgtp : add_vec (mword_of_int (PK + 0x18e) : mword 64) (sign_extend' 64 (mword_of_int 2096604 : mword 21)) = mword_of_int KernelSyms.printint) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgtp) in "Hpc".
    assert (HS2a1 : (10 <= uint (S2 !!! Regidx a1_idx) <= 16)%Z).
    { rewrite /S2 upd_ne; [| reg_neq]. rewrite HS1a1.
      rewrite (uint_moi_small 16 ltac:(change (2^64) with 18446744073709551616; lia)). lia. }
    iApply (wp_printint γ γd Φ S2 (K - 24)%nat l pv pkv dqm dqm2 HK14 HS2a1 Hpv Hpkv
              with "Hcg Htext Hkdata Hpc Hpanicking Hpanicked Hdev Htx Hdlab [-]").
    iIntros (mf bs) "Hcg Hpc %Hcs Hpanicking Hpanicked Htx #Hsent".
    destruct Hcs as [Hcs Hra].
    assert (Hret : ret_pc (S2 !!! Regidx ra_idx) = mword_of_int (PK + 0x192))
      by (rewrite /S2 upd_eq; unfold ret_pc; apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hret) in "Hpc".
    (* +0x192 addiw s1,s4,2 : how far the directive advanced the scan *)
    assert (Hmfs4 : mf !!! Regidx (mword_of_int 20 : mword 5) = mword_of_int (Z.of_nat i)).
    { rewrite (callee_saved_lookup Hcs (mword_of_int 20 : mword 5) ltac:(vm_compute; reflexivity)).
      rewrite /S2 upd_ne; [| reg_neq]. rewrite /S1 upd_ne; [| reg_neq].
      rewrite /S0 upd_ne; [| reg_neq]. 
      rewrite (Hvk (mword_of_int 20 : mword 5) ltac:(mw_neq) ltac:(mw_neq)). exact Hs4. }
    iApply (wp_addiw_s_sconf γ Φ (mword_of_int (PK + 0x192)) (mword_of_int 9 : mword 5) (mword_of_int 20 : mword 5) (mword_of_int 2 : mword 12)
              mf (K - 24)%nat ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hcg Hpc [] [-]").
    { iApply (pki_192 with "Htext"). }
    iIntros "Hcg Hpc".
    set (T := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg (sign_extend' 64 (subrange_vec_dec
                 (add_vec (mf !!! Regidx (mword_of_int 20 : mword 5)) (sign_extend' 64 (mword_of_int 2 : mword 12))) 31 0))]> mf).
    assert (HTs1 : T !!! Regidx (mword_of_int 9 : mword 5) = mword_of_int (Z.of_nat i + 2)).
    { rewrite /T upd_eq. unfold regval_into_reg. rewrite Hmfs4.
      apply (addiw_lit (Z.of_nat i) 2 (sign_extend' 64 (mword_of_int 2 : mword 12))
               ltac:(apply bv_eq; vm_compute; reflexivity)
               ltac:(change (2^31) with 2147483648 in Hi31 |- *; lia)). }
    assert (Hpa196 : add_vec_int (mword_of_int (PK + 0x192) : mword 64) 4 = mword_of_int (PK + 0x196)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpa196) in "Hpc".
    (* +0x196 j 0x78 *)
    iApply (wp_cj_s_sconf γ Φ (mword_of_int (PK + 0x196)) (sign_extend' 21 (concat_vec (mword_of_int 1905 : mword 11) ('b"0")))
              T (K - 24)%nat ltac:(vm_compute; reflexivity)
              with "Hcg Hpc [] [-]").
    { iApply (pki_196 with "Htext"). }
    iNext. iIntros "Hcg Hpc".
    assert (Htgt78 : add_vec (mword_of_int (PK + 0x196) : mword 64) (sign_extend' 64 (sign_extend' 21 (concat_vec (mword_of_int 1905 : mword 11) ('b"0")))) = mword_of_int (PK + 0x78)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgt78) in "Hpc".
    iApply ("Hcont" $! T bs with "[%] Hcg Hpc Hap Hva Hpanicking Hpanicked Htx Hsent HR").
    split; [| exact HTs1].
    intros c Hc N9.
    pose proof (is_cs_idx_true_neq ra_idx c ltac:(vm_compute; reflexivity) Hc) as N1.
    pose proof (is_cs_idx_true_neq a0_idx c ltac:(vm_compute; reflexivity) Hc) as N10.
    pose proof (is_cs_idx_true_neq a1_idx c ltac:(vm_compute; reflexivity) Hc) as N11.
    pose proof (is_cs_idx_true_neq (mword_of_int 12 : mword 5) c ltac:(vm_compute; reflexivity) Hc) as N12.
    pose proof (is_cs_idx_true_neq (mword_of_int 14 : mword 5) c ltac:(vm_compute; reflexivity) Hc) as N14.
    pose proof (is_cs_idx_true_neq a5_idx c ltac:(vm_compute; reflexivity) Hc) as N15.
    rewrite /T upd_ne; [| congruence].
    rewrite (callee_saved_lookup Hcs c Hc).
    rewrite /S2 upd_ne; [| congruence]. rewrite /S1 upd_ne; [| congruence].
    rewrite /S0 upd_ne; [| congruence]. 
    apply Hvk; congruence.
  Qed.


  Lemma wp_printk_arm_llx (γ : gname) (γd : uart_names) (Φ : mval -> iProp Σ)
      (m mc : regfile) (K : nat) (k i : nat) (l : list (bv 8)) (pv pkv : mword 32)
      (dqm dqm2 : dfrac) (Rest : iProp Σ) :
    let sp0 := m !!! Regidx csp_rs1 in
    let s0v := add_vec sp0 (sign_extend' 64 (mword_of_int (-64) : mword 12)) in
    (38 <= K)%nat ->
    (k < 7)%nat ->
    (Z.of_nat i + 3 < 2^31) ->
    eq_vec (sign_extend' 64 pv) zero_reg = false ->
    neq_vec (sign_extend' 64 pkv) zero_reg = false ->
    mc !!! Regidx s0_idx = s0v ->
    mc !!! Regidx (mword_of_int 22 : mword 5) = (mword_of_int 10 : mword 64) ->
    mc !!! Regidx (mword_of_int 20 : mword 5) = mword_of_int (Z.of_nat i) ->
    sie_cap_gpr γ mc (K - 24)%nat -∗
    kernel_text -∗ kernel_data -∗
    pc_is (mword_of_int (PK + 0x198 + 0) : mword 64) -∗
    (pa_stk sp0 23) ↦₈ (pk_ap s0v k) -∗
    pk_va sp0 m -∗
    (mword_of_int KernelSyms.panicking : mword 64) ↦₄{ dqm } pv -∗
    (mword_of_int KernelSyms.panicked : mword 64) ↦₄{ dqm2 } pkv -∗
    dev_inv γd -∗ uart_tx_own γd l -∗ uart_dlab_off γd -∗
    Rest -∗
    ( ∀ (mf : regfile) (bs : list (bv 8)),
      ⌜ (forall c : mword 5, is_cs_idx c = true -> c <> mword_of_int 9 ->
           mf !!! Regidx c = mc !!! Regidx c)
        /\ mf !!! Regidx (mword_of_int 9 : mword 5) = mword_of_int (Z.of_nat i + 3) ⌝ -∗
      sie_cap_gpr γ mf (K - 24)%nat -∗
      pc_is (mword_of_int (PK + 0x78) : mword 64) -∗
      (pa_stk sp0 23) ↦₈ (pk_ap s0v (S k)) -∗
      pk_va sp0 m -∗
      (mword_of_int KernelSyms.panicking : mword 64) ↦₄{ dqm } pv -∗
      (mword_of_int KernelSyms.panicked : mword 64) ↦₄{ dqm2 } pkv -∗
      uart_tx_own γd (l ++ bs) -∗ uart_sent γd (l ++ bs) -∗
      Rest -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    intros sp0 s0v HK Hk Hi31 Hpv Hpkv Hs0 Hs6 Hs4.
    assert (HK14 : (14 <= K - 24)%nat) by lia.
    iIntros "Hcg #Htext #Hkdata Hpc Hap Hva Hpanicking Hpanicked #Hdev Htx #Hdlab HR Hcont".
    iApply (wp_printk_vaarg γ Φ mc K 0x198 sp0 s0v k Hs0 eq_refl
              with "Hcg [] Hpc Hap [-]").
    { rewrite /pk_vaarg_instrs.
      iSplitR; [iApply (pki_198 with "Htext") | ].
      iSplitR; [iApply (pki_19c with "Htext") | ].
      iApply (pki_1a0 with "Htext"). }
    iIntros (V) "%Hv Hcg Hpc Hap".
    destruct Hv as (Hva5 & Hvs0 & Hvk).
    iApply (wp_cli_s_sconf γ Φ (mword_of_int (PK + 0x1a4)) (mword_of_int 12 : mword 5) (mword_of_int 0 : mword 6)
              (mword_of_int 0 : mword 64) V (K - 24)%nat
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc [] [-]").
    { iApply (pki_1a4 with "Htext"). }
    iIntros "Hcg Hpc".
    set (S0 := <[Regidx (mword_of_int 12 : mword 5) := regval_into_reg (mword_of_int 0 : mword 64)]> V).
    assert (Hpa1a6 : add_vec_int (mword_of_int (PK + 0x1a4) : mword 64) 2 = mword_of_int (PK + 0x1a6)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpa1a6) in "Hpc".
    iApply (wp_cli_s_sconf γ Φ (mword_of_int (PK + 0x1a6)) a1_idx (mword_of_int 16 : mword 6)
              (mword_of_int 16 : mword 64) S0 (K - 24)%nat
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc [] [-]").
    { iApply (pki_1a6 with "Htext"). }
    iIntros "Hcg Hpc".
    set (S1 := <[Regidx a1_idx := regval_into_reg (mword_of_int 16 : mword 64)]> S0).
    assert (HS1a1 : S1 !!! Regidx a1_idx = (mword_of_int 16 : mword 64))
      by (rewrite /S1 upd_eq; reflexivity).
    assert (HS1a5 : S1 !!! Regidx a5_idx = pk_ap s0v k).
    { rewrite /S1 upd_ne; [| reg_neq]. rewrite /S0 upd_ne; [| reg_neq]. exact Hva5. }
    assert (Hpa1a8 : add_vec_int (mword_of_int (PK + 0x1a6) : mword 64) 2 = mword_of_int (PK + 0x1a8)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpa1a8) in "Hpc".
    (* the argument: a whole 8-byte slot this time *)
    iDestruct (pk_va_acc sp0 m k Hk with "Hva") as "[Hslot Hvacl]".
    assert (Hlda : add_vec (S1 !!! Regidx a5_idx) (sign_extend' 64 (mword_of_int 0 : mword 12)) = pa_stk sp0 (7 - k)).
    { rewrite HS1a5.
      replace (sign_extend' 64 (mword_of_int 0 : mword 12)) with (mword_of_int 0 : mword 64)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite kv_addv_zero. apply pk_ap_slot. exact Hk. }
    iEval (rewrite -Hlda) in "Hslot".
    iApply (wp_cld_s_sconf γ Φ (mword_of_int (PK + 0x1a8)) a0_idx a5_idx (mword_of_int 0 : mword 12)
              S1 (K - 24)%nat (pk_vararg m k)
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hcg Hpc [] Hslot [-]").
    { iApply (pki_1a8 with "Htext"). }
    iIntros "Hcg Hpc Hslot". iEval (rewrite Hlda) in "Hslot".
    iDestruct ("Hvacl" with "Hslot") as "Hva".
    set (S2 := <[Regidx a0_idx := regval_into_reg (pk_vararg m k)]> S1).
    assert (HS2a1 : S2 !!! Regidx a1_idx = (mword_of_int 16 : mword 64))
      by (rewrite /S2 upd_ne; [exact HS1a1 | reg_neq]).
    assert (Hpa1aa : add_vec_int (mword_of_int (PK + 0x1a8) : mword 64) 2 = mword_of_int (PK + 0x1aa)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpa1aa) in "Hpc".
    iApply (wp_jal_s_sconf γ Φ (mword_of_int (PK + 0x1aa)) ra_idx (mword_of_int 2096576 : mword 21)
              S2 (K - 24)%nat ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              ltac:(vm_compute; reflexivity)
              with "Hcg Hpc [] [-]").
    { iApply (pki_1aa with "Htext"). }
    iIntros "Hcg Hpc".
    set (S3 := <[Regidx ra_idx := regval_into_reg (add_vec_int (mword_of_int (PK + 0x1aa) : mword 64) 4)]> S2).
    assert (Htgtp : add_vec (mword_of_int (PK + 0x1aa) : mword 64) (sign_extend' 64 (mword_of_int 2096576 : mword 21)) = mword_of_int KernelSyms.printint) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgtp) in "Hpc".
    assert (HS3a1 : (10 <= uint (S3 !!! Regidx a1_idx) <= 16)%Z).
    { rewrite /S3 upd_ne; [| reg_neq]. rewrite HS2a1.
      rewrite (uint_moi_small 16 ltac:(change (2^64) with 18446744073709551616; lia)). lia. }
    iApply (wp_printint γ γd Φ S3 (K - 24)%nat l pv pkv dqm dqm2 HK14 HS3a1 Hpv Hpkv
              with "Hcg Htext Hkdata Hpc Hpanicking Hpanicked Hdev Htx Hdlab [-]").
    iIntros (mf bs) "Hcg Hpc %Hcs Hpanicking Hpanicked Htx #Hsent".
    destruct Hcs as [Hcs Hra].
    assert (Hret : ret_pc (S3 !!! Regidx ra_idx) = mword_of_int (PK + 0x1ae))
      by (rewrite /S3 upd_eq; unfold ret_pc; apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hret) in "Hpc".
    (* +0x1ae addiw s1,s4,3 : how far the directive advanced the scan *)
    assert (Hmfs4 : mf !!! Regidx (mword_of_int 20 : mword 5) = mword_of_int (Z.of_nat i)).
    { rewrite (callee_saved_lookup Hcs (mword_of_int 20 : mword 5) ltac:(vm_compute; reflexivity)).
      rewrite /S3 upd_ne; [| reg_neq]. rewrite /S2 upd_ne; [| reg_neq].
      rewrite /S1 upd_ne; [| reg_neq]. rewrite /S0 upd_ne; [| reg_neq]. 
      rewrite (Hvk (mword_of_int 20 : mword 5) ltac:(mw_neq) ltac:(mw_neq)). exact Hs4. }
    iApply (wp_addiw_s_sconf γ Φ (mword_of_int (PK + 0x1ae)) (mword_of_int 9 : mword 5) (mword_of_int 20 : mword 5) (mword_of_int 3 : mword 12)
              mf (K - 24)%nat ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hcg Hpc [] [-]").
    { iApply (pki_1ae with "Htext"). }
    iIntros "Hcg Hpc".
    set (T := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg (sign_extend' 64 (subrange_vec_dec
                 (add_vec (mf !!! Regidx (mword_of_int 20 : mword 5)) (sign_extend' 64 (mword_of_int 3 : mword 12))) 31 0))]> mf).
    assert (HTs1 : T !!! Regidx (mword_of_int 9 : mword 5) = mword_of_int (Z.of_nat i + 3)).
    { rewrite /T upd_eq. unfold regval_into_reg. rewrite Hmfs4.
      apply (addiw_lit (Z.of_nat i) 3 (sign_extend' 64 (mword_of_int 3 : mword 12))
               ltac:(apply bv_eq; vm_compute; reflexivity)
               ltac:(change (2^31) with 2147483648 in Hi31 |- *; lia)). }
    assert (Hpa1b2 : add_vec_int (mword_of_int (PK + 0x1ae) : mword 64) 4 = mword_of_int (PK + 0x1b2)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpa1b2) in "Hpc".
    (* +0x1b2 j 0x78 *)
    iApply (wp_cj_s_sconf γ Φ (mword_of_int (PK + 0x1b2)) (sign_extend' 21 (concat_vec (mword_of_int 1891 : mword 11) ('b"0")))
              T (K - 24)%nat ltac:(vm_compute; reflexivity)
              with "Hcg Hpc [] [-]").
    { iApply (pki_1b2 with "Htext"). }
    iNext. iIntros "Hcg Hpc".
    assert (Htgt78 : add_vec (mword_of_int (PK + 0x1b2) : mword 64) (sign_extend' 64 (sign_extend' 21 (concat_vec (mword_of_int 1891 : mword 11) ('b"0")))) = mword_of_int (PK + 0x78)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgt78) in "Hpc".
    iApply ("Hcont" $! T bs with "[%] Hcg Hpc Hap Hva Hpanicking Hpanicked Htx Hsent HR").
    split; [| exact HTs1].
    intros c Hc N9.
    pose proof (is_cs_idx_true_neq ra_idx c ltac:(vm_compute; reflexivity) Hc) as N1.
    pose proof (is_cs_idx_true_neq a0_idx c ltac:(vm_compute; reflexivity) Hc) as N10.
    pose proof (is_cs_idx_true_neq a1_idx c ltac:(vm_compute; reflexivity) Hc) as N11.
    pose proof (is_cs_idx_true_neq (mword_of_int 12 : mword 5) c ltac:(vm_compute; reflexivity) Hc) as N12.
    pose proof (is_cs_idx_true_neq (mword_of_int 14 : mword 5) c ltac:(vm_compute; reflexivity) Hc) as N14.
    pose proof (is_cs_idx_true_neq a5_idx c ltac:(vm_compute; reflexivity) Hc) as N15.
    rewrite /T upd_ne; [| congruence].
    rewrite (callee_saved_lookup Hcs c Hc).
    rewrite /S3 upd_ne; [| congruence]. rewrite /S2 upd_ne; [| congruence].
    rewrite /S1 upd_ne; [| congruence]. rewrite /S0 upd_ne; [| congruence]. 
    apply Hvk; congruence.
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  [%u] and [%x]: the same shape, but the argument is a [uint32] read  *)
  (*  with [lwu] out of the low half of its slot, and the directive is    *)
  (*  one character long, so s1 is left as the dispatch set it.           *)
  (* ------------------------------------------------------------------ *)


  Lemma wp_printk_arm_u (γ : gname) (γd : uart_names) (Φ : mval -> iProp Σ)
      (m mc : regfile) (K : nat) (k : nat) (l : list (bv 8)) (pv pkv : mword 32)
      (dqm dqm2 : dfrac) (Rest : iProp Σ) :
    let sp0 := m !!! Regidx csp_rs1 in
    let s0v := add_vec sp0 (sign_extend' 64 (mword_of_int (-64) : mword 12)) in
    (38 <= K)%nat ->
    (k < 7)%nat ->
    eq_vec (sign_extend' 64 pv) zero_reg = false ->
    neq_vec (sign_extend' 64 pkv) zero_reg = false ->
    mc !!! Regidx s0_idx = s0v ->
    mc !!! Regidx (mword_of_int 22 : mword 5) = (mword_of_int 10 : mword 64) ->
    sie_cap_gpr γ mc (K - 24)%nat -∗
    kernel_text -∗ kernel_data -∗
    pc_is (mword_of_int (PK + 0x112 + 0) : mword 64) -∗
    (pa_stk sp0 23) ↦₈ (pk_ap s0v k) -∗
    pk_va sp0 m -∗
    (mword_of_int KernelSyms.panicking : mword 64) ↦₄{ dqm } pv -∗
    (mword_of_int KernelSyms.panicked : mword 64) ↦₄{ dqm2 } pkv -∗
    dev_inv γd -∗ uart_tx_own γd l -∗ uart_dlab_off γd -∗
    Rest -∗
    ( ∀ (mf : regfile) (bs : list (bv 8)),
      ⌜ forall c : mword 5, is_cs_idx c = true -> mf !!! Regidx c = mc !!! Regidx c ⌝ -∗
      sie_cap_gpr γ mf (K - 24)%nat -∗
      pc_is (mword_of_int (PK + 0x78) : mword 64) -∗
      (pa_stk sp0 23) ↦₈ (pk_ap s0v (S k)) -∗
      pk_va sp0 m -∗
      (mword_of_int KernelSyms.panicking : mword 64) ↦₄{ dqm } pv -∗
      (mword_of_int KernelSyms.panicked : mword 64) ↦₄{ dqm2 } pkv -∗
      uart_tx_own γd (l ++ bs) -∗ uart_sent γd (l ++ bs) -∗
      Rest -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    intros sp0 s0v HK Hk Hpv Hpkv Hs0 Hs6.
    assert (HK14 : (14 <= K - 24)%nat) by lia.
    iIntros "Hcg #Htext #Hkdata Hpc Hap Hva Hpanicking Hpanicked #Hdev Htx #Hdlab HR Hcont".
    iApply (wp_printk_vaarg γ Φ mc K 0x112 sp0 s0v k Hs0 eq_refl
              with "Hcg [] Hpc Hap [-]").
    { rewrite /pk_vaarg_instrs.
      iSplitR; [iApply (pki_112 with "Htext") | ].
      iSplitR; [iApply (pki_116 with "Htext") | ].
      iApply (pki_11a with "Htext"). }
    iIntros (V) "%Hv Hcg Hpc Hap".
    destruct Hv as (Hva5 & Hvs0 & Hvk).
    iApply (wp_cli_s_sconf γ Φ (mword_of_int (PK + 0x11e)) (mword_of_int 12 : mword 5) (mword_of_int 0 : mword 6)
              (mword_of_int 0 : mword 64) V (K - 24)%nat
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc [] [-]").
    { iApply (pki_11e with "Htext"). }
    iIntros "Hcg Hpc".
    set (S0 := <[Regidx (mword_of_int 12 : mword 5) := regval_into_reg (mword_of_int 0 : mword 64)]> V).
    assert (Hpa120 : add_vec_int (mword_of_int (PK + 0x11e) : mword 64) 2 = mword_of_int (PK + 0x120)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpa120) in "Hpc".
    iApply (wp_cmv_s_sconf γ Φ (mword_of_int (PK + 0x120)) a1_idx (mword_of_int 22 : mword 5)
              S0 (K - 24)%nat ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hcg Hpc [] [-]").
    { iApply (pki_120 with "Htext"). }
    iIntros "Hcg Hpc".
    set (S1 := <[Regidx a1_idx := regval_into_reg (add_vec zero_reg (S0 !!! Regidx (mword_of_int 22 : mword 5)))]> S0).
    assert (HS1a1 : S1 !!! Regidx a1_idx = (mword_of_int 10 : mword 64)).
    { rewrite /S1 upd_eq. unfold regval_into_reg.
      rewrite /S0 upd_ne; [| reg_neq].
      rewrite (Hvk (mword_of_int 22 : mword 5) ltac:(mw_neq) ltac:(mw_neq)).
      rewrite Hs6. apply pi_addv_zero_l. }
    assert (HS1a5 : S1 !!! Regidx a5_idx = pk_ap s0v k).
    { rewrite /S1 upd_ne; [| reg_neq]. rewrite /S0 upd_ne; [| reg_neq]. exact Hva5. }
    assert (Hpa122 : add_vec_int (mword_of_int (PK + 0x120) : mword 64) 2 = mword_of_int (PK + 0x122)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpa122) in "Hpc".
    (* the argument: the LOW half of the slot, read unsigned *)
    iDestruct (pk_va_acc sp0 m k Hk with "Hva") as "[Hslot Hvacl]".
    iDestruct (word_pointsto_aligned_p with "Hslot") as %Halv.
    iDestruct (word_pointsto_split4 with "Hslot") as "[Hlo Hhi]".
    iEval (rewrite -/(pk_lo m k)) in "Hlo".
    assert (Hlwa : add_vec (S1 !!! Regidx a5_idx) (sign_extend' 64 (mword_of_int 0 : mword 12)) = pa_stk sp0 (7 - k)).
    { rewrite HS1a5.
      replace (sign_extend' 64 (mword_of_int 0 : mword 12)) with (mword_of_int 0 : mword 64)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite kv_addv_zero. apply pk_ap_slot. exact Hk. }
    iEval (rewrite -Hlwa) in "Hlo".
    iApply (wp_lwu_s_sconf γ Φ (mword_of_int (PK + 0x122)) a0_idx a5_idx (mword_of_int 0 : mword 12)
              S1 (K - 24)%nat (pk_lo m k)
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hcg Hpc [] Hlo [-]").
    { iApply (pki_122 with "Htext"). }
    iIntros "Hcg Hpc Hlo". iEval (rewrite Hlwa) in "Hlo".
    iDestruct (word_pointsto_join4 _ _ _ _ Halv with "Hlo Hhi") as "Hslot".
    rewrite word_of_words_id.
    iDestruct ("Hvacl" with "Hslot") as "Hva".
    set (S2 := <[Regidx a0_idx := regval_into_reg (zero_extend' 64 (pk_lo m k))]> S1).
    assert (HS2a1 : S2 !!! Regidx a1_idx = (mword_of_int 10 : mword 64))
      by (rewrite /S2 upd_ne; [exact HS1a1 | reg_neq]).
    assert (Hpa126 : add_vec_int (mword_of_int (PK + 0x122) : mword 64) 4 = mword_of_int (PK + 0x126)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpa126) in "Hpc".
    iApply (wp_jal_s_sconf γ Φ (mword_of_int (PK + 0x126)) ra_idx (mword_of_int 2096708 : mword 21)
              S2 (K - 24)%nat ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              ltac:(vm_compute; reflexivity)
              with "Hcg Hpc [] [-]").
    { iApply (pki_126 with "Htext"). }
    iIntros "Hcg Hpc".
    set (S3 := <[Regidx ra_idx := regval_into_reg (add_vec_int (mword_of_int (PK + 0x126) : mword 64) 4)]> S2).
    assert (Htgtp : add_vec (mword_of_int (PK + 0x126) : mword 64) (sign_extend' 64 (mword_of_int 2096708 : mword 21)) = mword_of_int KernelSyms.printint) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgtp) in "Hpc".
    assert (HS3a1 : (10 <= uint (S3 !!! Regidx a1_idx) <= 16)%Z).
    { rewrite /S3 upd_ne; [| reg_neq]. rewrite HS2a1.
      rewrite (uint_moi_small 10 ltac:(change (2^64) with 18446744073709551616; lia)). lia. }
    iApply (wp_printint γ γd Φ S3 (K - 24)%nat l pv pkv dqm dqm2 HK14 HS3a1 Hpv Hpkv
              with "Hcg Htext Hkdata Hpc Hpanicking Hpanicked Hdev Htx Hdlab [-]").
    iIntros (mf bs) "Hcg Hpc %Hcs Hpanicking Hpanicked Htx #Hsent".
    destruct Hcs as [Hcs Hra].
    assert (Hret : ret_pc (S3 !!! Regidx ra_idx) = mword_of_int (PK + 0x12a))
      by (rewrite /S3 upd_eq; unfold ret_pc; apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hret) in "Hpc".
    iApply (wp_cj_s_sconf γ Φ (mword_of_int (PK + 0x12a)) (sign_extend' 21 (concat_vec (mword_of_int 1959 : mword 11) ('b"0")))
              mf (K - 24)%nat ltac:(vm_compute; reflexivity)
              with "Hcg Hpc [] [-]").
    { iApply (pki_12a with "Htext"). }
    iNext. iIntros "Hcg Hpc".
    assert (Htgt78 : add_vec (mword_of_int (PK + 0x12a) : mword 64) (sign_extend' 64 (sign_extend' 21 (concat_vec (mword_of_int 1959 : mword 11) ('b"0")))) = mword_of_int (PK + 0x78)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgt78) in "Hpc".
    iApply ("Hcont" $! mf bs with "[%] Hcg Hpc Hap Hva Hpanicking Hpanicked Htx Hsent HR").
    intros c Hc.
    pose proof (is_cs_idx_true_neq ra_idx c ltac:(vm_compute; reflexivity) Hc) as N1.
    pose proof (is_cs_idx_true_neq a0_idx c ltac:(vm_compute; reflexivity) Hc) as N10.
    pose proof (is_cs_idx_true_neq a1_idx c ltac:(vm_compute; reflexivity) Hc) as N11.
    pose proof (is_cs_idx_true_neq (mword_of_int 12 : mword 5) c ltac:(vm_compute; reflexivity) Hc) as N12.
    pose proof (is_cs_idx_true_neq (mword_of_int 14 : mword 5) c ltac:(vm_compute; reflexivity) Hc) as N14.
    pose proof (is_cs_idx_true_neq a5_idx c ltac:(vm_compute; reflexivity) Hc) as N15.
    rewrite (callee_saved_lookup Hcs c Hc).
    rewrite /S3 upd_ne; [| congruence]. rewrite /S2 upd_ne; [| congruence].
    rewrite /S1 upd_ne; [| congruence]. rewrite /S0 upd_ne; [| congruence].
    apply Hvk; congruence.
  Qed.


  Lemma wp_printk_arm_x (γ : gname) (γd : uart_names) (Φ : mval -> iProp Σ)
      (m mc : regfile) (K : nat) (k : nat) (l : list (bv 8)) (pv pkv : mword 32)
      (dqm dqm2 : dfrac) (Rest : iProp Σ) :
    let sp0 := m !!! Regidx csp_rs1 in
    let s0v := add_vec sp0 (sign_extend' 64 (mword_of_int (-64) : mword 12)) in
    (38 <= K)%nat ->
    (k < 7)%nat ->
    eq_vec (sign_extend' 64 pv) zero_reg = false ->
    neq_vec (sign_extend' 64 pkv) zero_reg = false ->
    mc !!! Regidx s0_idx = s0v ->
    mc !!! Regidx (mword_of_int 22 : mword 5) = (mword_of_int 10 : mword 64) ->
    sie_cap_gpr γ mc (K - 24)%nat -∗
    kernel_text -∗ kernel_data -∗
    pc_is (mword_of_int (PK + 0x164 + 0) : mword 64) -∗
    (pa_stk sp0 23) ↦₈ (pk_ap s0v k) -∗
    pk_va sp0 m -∗
    (mword_of_int KernelSyms.panicking : mword 64) ↦₄{ dqm } pv -∗
    (mword_of_int KernelSyms.panicked : mword 64) ↦₄{ dqm2 } pkv -∗
    dev_inv γd -∗ uart_tx_own γd l -∗ uart_dlab_off γd -∗
    Rest -∗
    ( ∀ (mf : regfile) (bs : list (bv 8)),
      ⌜ forall c : mword 5, is_cs_idx c = true -> mf !!! Regidx c = mc !!! Regidx c ⌝ -∗
      sie_cap_gpr γ mf (K - 24)%nat -∗
      pc_is (mword_of_int (PK + 0x78) : mword 64) -∗
      (pa_stk sp0 23) ↦₈ (pk_ap s0v (S k)) -∗
      pk_va sp0 m -∗
      (mword_of_int KernelSyms.panicking : mword 64) ↦₄{ dqm } pv -∗
      (mword_of_int KernelSyms.panicked : mword 64) ↦₄{ dqm2 } pkv -∗
      uart_tx_own γd (l ++ bs) -∗ uart_sent γd (l ++ bs) -∗
      Rest -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    intros sp0 s0v HK Hk Hpv Hpkv Hs0 Hs6.
    assert (HK14 : (14 <= K - 24)%nat) by lia.
    iIntros "Hcg #Htext #Hkdata Hpc Hap Hva Hpanicking Hpanicked #Hdev Htx #Hdlab HR Hcont".
    iApply (wp_printk_vaarg γ Φ mc K 0x164 sp0 s0v k Hs0 eq_refl
              with "Hcg [] Hpc Hap [-]").
    { rewrite /pk_vaarg_instrs.
      iSplitR; [iApply (pki_164 with "Htext") | ].
      iSplitR; [iApply (pki_168 with "Htext") | ].
      iApply (pki_16c with "Htext"). }
    iIntros (V) "%Hv Hcg Hpc Hap".
    destruct Hv as (Hva5 & Hvs0 & Hvk).
    iApply (wp_cli_s_sconf γ Φ (mword_of_int (PK + 0x170)) (mword_of_int 12 : mword 5) (mword_of_int 0 : mword 6)
              (mword_of_int 0 : mword 64) V (K - 24)%nat
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc [] [-]").
    { iApply (pki_170 with "Htext"). }
    iIntros "Hcg Hpc".
    set (S0 := <[Regidx (mword_of_int 12 : mword 5) := regval_into_reg (mword_of_int 0 : mword 64)]> V).
    assert (Hpa172 : add_vec_int (mword_of_int (PK + 0x170) : mword 64) 2 = mword_of_int (PK + 0x172)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpa172) in "Hpc".
    iApply (wp_cli_s_sconf γ Φ (mword_of_int (PK + 0x172)) a1_idx (mword_of_int 16 : mword 6)
              (mword_of_int 16 : mword 64) S0 (K - 24)%nat
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc [] [-]").
    { iApply (pki_172 with "Htext"). }
    iIntros "Hcg Hpc".
    set (S1 := <[Regidx a1_idx := regval_into_reg (mword_of_int 16 : mword 64)]> S0).
    assert (HS1a1 : S1 !!! Regidx a1_idx = (mword_of_int 16 : mword 64))
      by (rewrite /S1 upd_eq; reflexivity).
    assert (HS1a5 : S1 !!! Regidx a5_idx = pk_ap s0v k).
    { rewrite /S1 upd_ne; [| reg_neq]. rewrite /S0 upd_ne; [| reg_neq]. exact Hva5. }
    assert (Hpa174 : add_vec_int (mword_of_int (PK + 0x172) : mword 64) 2 = mword_of_int (PK + 0x174)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpa174) in "Hpc".
    (* the argument: the LOW half of the slot, read unsigned *)
    iDestruct (pk_va_acc sp0 m k Hk with "Hva") as "[Hslot Hvacl]".
    iDestruct (word_pointsto_aligned_p with "Hslot") as %Halv.
    iDestruct (word_pointsto_split4 with "Hslot") as "[Hlo Hhi]".
    iEval (rewrite -/(pk_lo m k)) in "Hlo".
    assert (Hlwa : add_vec (S1 !!! Regidx a5_idx) (sign_extend' 64 (mword_of_int 0 : mword 12)) = pa_stk sp0 (7 - k)).
    { rewrite HS1a5.
      replace (sign_extend' 64 (mword_of_int 0 : mword 12)) with (mword_of_int 0 : mword 64)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite kv_addv_zero. apply pk_ap_slot. exact Hk. }
    iEval (rewrite -Hlwa) in "Hlo".
    iApply (wp_lwu_s_sconf γ Φ (mword_of_int (PK + 0x174)) a0_idx a5_idx (mword_of_int 0 : mword 12)
              S1 (K - 24)%nat (pk_lo m k)
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hcg Hpc [] Hlo [-]").
    { iApply (pki_174 with "Htext"). }
    iIntros "Hcg Hpc Hlo". iEval (rewrite Hlwa) in "Hlo".
    iDestruct (word_pointsto_join4 _ _ _ _ Halv with "Hlo Hhi") as "Hslot".
    rewrite word_of_words_id.
    iDestruct ("Hvacl" with "Hslot") as "Hva".
    set (S2 := <[Regidx a0_idx := regval_into_reg (zero_extend' 64 (pk_lo m k))]> S1).
    assert (HS2a1 : S2 !!! Regidx a1_idx = (mword_of_int 16 : mword 64))
      by (rewrite /S2 upd_ne; [exact HS1a1 | reg_neq]).
    assert (Hpa178 : add_vec_int (mword_of_int (PK + 0x174) : mword 64) 4 = mword_of_int (PK + 0x178)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpa178) in "Hpc".
    iApply (wp_jal_s_sconf γ Φ (mword_of_int (PK + 0x178)) ra_idx (mword_of_int 2096626 : mword 21)
              S2 (K - 24)%nat ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              ltac:(vm_compute; reflexivity)
              with "Hcg Hpc [] [-]").
    { iApply (pki_178 with "Htext"). }
    iIntros "Hcg Hpc".
    set (S3 := <[Regidx ra_idx := regval_into_reg (add_vec_int (mword_of_int (PK + 0x178) : mword 64) 4)]> S2).
    assert (Htgtp : add_vec (mword_of_int (PK + 0x178) : mword 64) (sign_extend' 64 (mword_of_int 2096626 : mword 21)) = mword_of_int KernelSyms.printint) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgtp) in "Hpc".
    assert (HS3a1 : (10 <= uint (S3 !!! Regidx a1_idx) <= 16)%Z).
    { rewrite /S3 upd_ne; [| reg_neq]. rewrite HS2a1.
      rewrite (uint_moi_small 16 ltac:(change (2^64) with 18446744073709551616; lia)). lia. }
    iApply (wp_printint γ γd Φ S3 (K - 24)%nat l pv pkv dqm dqm2 HK14 HS3a1 Hpv Hpkv
              with "Hcg Htext Hkdata Hpc Hpanicking Hpanicked Hdev Htx Hdlab [-]").
    iIntros (mf bs) "Hcg Hpc %Hcs Hpanicking Hpanicked Htx #Hsent".
    destruct Hcs as [Hcs Hra].
    assert (Hret : ret_pc (S3 !!! Regidx ra_idx) = mword_of_int (PK + 0x17c))
      by (rewrite /S3 upd_eq; unfold ret_pc; apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hret) in "Hpc".
    iApply (wp_cj_s_sconf γ Φ (mword_of_int (PK + 0x17c)) (sign_extend' 21 (concat_vec (mword_of_int 1918 : mword 11) ('b"0")))
              mf (K - 24)%nat ltac:(vm_compute; reflexivity)
              with "Hcg Hpc [] [-]").
    { iApply (pki_17c with "Htext"). }
    iNext. iIntros "Hcg Hpc".
    assert (Htgt78 : add_vec (mword_of_int (PK + 0x17c) : mword 64) (sign_extend' 64 (sign_extend' 21 (concat_vec (mword_of_int 1918 : mword 11) ('b"0")))) = mword_of_int (PK + 0x78)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgt78) in "Hpc".
    iApply ("Hcont" $! mf bs with "[%] Hcg Hpc Hap Hva Hpanicking Hpanicked Htx Hsent HR").
    intros c Hc.
    pose proof (is_cs_idx_true_neq ra_idx c ltac:(vm_compute; reflexivity) Hc) as N1.
    pose proof (is_cs_idx_true_neq a0_idx c ltac:(vm_compute; reflexivity) Hc) as N10.
    pose proof (is_cs_idx_true_neq a1_idx c ltac:(vm_compute; reflexivity) Hc) as N11.
    pose proof (is_cs_idx_true_neq (mword_of_int 12 : mword 5) c ltac:(vm_compute; reflexivity) Hc) as N12.
    pose proof (is_cs_idx_true_neq (mword_of_int 14 : mword 5) c ltac:(vm_compute; reflexivity) Hc) as N14.
    pose proof (is_cs_idx_true_neq a5_idx c ltac:(vm_compute; reflexivity) Hc) as N15.
    rewrite (callee_saved_lookup Hcs c Hc).
    rewrite /S3 upd_ne; [| congruence]. rewrite /S2 upd_ne; [| congruence].
    rewrite /S1 upd_ne; [| congruence]. rewrite /S0 upd_ne; [| congruence].
    apply Hvk; congruence.
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  The three consputc arms: [%c], [%%] and the unknown-directive case. *)
  (*  None of them goes through printint, and only [%c] takes a vararg.    *)
  (* ------------------------------------------------------------------ *)

  (* [%c] (0x1fa..0x20c): va_arg, then the low half of the slot straight to
     consputc.  Like the value arms, but with no (base, sign) pair. *)
  Lemma wp_printk_arm_c (γ : gname) (γd : uart_names) (Φ : mval -> iProp Σ)
      (m mc : regfile) (K : nat) (k : nat) (l : list (bv 8)) (pv pkv : mword 32)
      (dqm dqm2 : dfrac) (Rest : iProp Σ) :
    let sp0 := m !!! Regidx csp_rs1 in
    let s0v := add_vec sp0 (sign_extend' 64 (mword_of_int (-64) : mword 12)) in
    (30 <= K)%nat ->
    (k < 7)%nat ->
    eq_vec (sign_extend' 64 pv) zero_reg = false ->
    neq_vec (sign_extend' 64 pkv) zero_reg = false ->
    mc !!! Regidx s0_idx = s0v ->
    sie_cap_gpr γ mc (K - 24)%nat -∗
    kernel_text -∗
    pc_is (mword_of_int (PK + 0x1fa + 0) : mword 64) -∗
    (pa_stk sp0 23) ↦₈ (pk_ap s0v k) -∗
    pk_va sp0 m -∗
    (mword_of_int KernelSyms.panicking : mword 64) ↦₄{ dqm } pv -∗
    (mword_of_int KernelSyms.panicked : mword 64) ↦₄{ dqm2 } pkv -∗
    dev_inv γd -∗ uart_tx_own γd l -∗ uart_dlab_off γd -∗
    Rest -∗
    ( ∀ (mf : regfile) (bs : list (bv 8)),
      ⌜ forall c : mword 5, is_cs_idx c = true -> mf !!! Regidx c = mc !!! Regidx c ⌝ -∗
      sie_cap_gpr γ mf (K - 24)%nat -∗
      pc_is (mword_of_int (PK + 0x78) : mword 64) -∗
      (pa_stk sp0 23) ↦₈ (pk_ap s0v (S k)) -∗
      pk_va sp0 m -∗
      (mword_of_int KernelSyms.panicking : mword 64) ↦₄{ dqm } pv -∗
      (mword_of_int KernelSyms.panicked : mword 64) ↦₄{ dqm2 } pkv -∗
      uart_tx_own γd (l ++ bs) -∗ uart_sent γd (l ++ bs) -∗
      Rest -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    intros sp0 s0v HK Hk Hpv Hpkv Hs0.
    assert (HK6 : (6 <= K - 24)%nat) by lia.
    iIntros "Hcg #Htext Hpc Hap Hva Hpanicking Hpanicked #Hdev Htx #Hdlab HR Hcont".
    iApply (wp_printk_vaarg γ Φ mc K 0x1fa sp0 s0v k Hs0 eq_refl
              with "Hcg [] Hpc Hap [-]").
    { rewrite /pk_vaarg_instrs.
      iSplitR; [iApply (pki_1fa with "Htext") | ].
      iSplitR; [iApply (pki_1fe with "Htext") | ].
      iApply (pki_202 with "Htext"). }
    iIntros (V) "%Hv Hcg Hpc Hap".
    destruct Hv as (Hva5 & Hvs0 & Hvk).
    assert (Hp206 : (mword_of_int (PK + 0x1fa + 12) : mword 64) = mword_of_int (PK + 0x206))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp206) in "Hpc".
    (* the argument: the low half of the slot *)
    iDestruct (pk_va_acc sp0 m k Hk with "Hva") as "[Hslot Hvacl]".
    iDestruct (word_pointsto_aligned_p with "Hslot") as %Halv.
    iDestruct (word_pointsto_split4 with "Hslot") as "[Hlo Hhi]".
    iEval (rewrite -/(pk_lo m k)) in "Hlo".
    assert (Hlwa : add_vec (V !!! Regidx a5_idx) (sign_extend' 64 (mword_of_int 0 : mword 12)) = pa_stk sp0 (7 - k)).
    { rewrite Hva5.
      replace (sign_extend' 64 (mword_of_int 0 : mword 12)) with (mword_of_int 0 : mword 64)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite kv_addv_zero. apply pk_ap_slot. exact Hk. }
    iEval (rewrite -Hlwa) in "Hlo".
    iApply (wp_clw_s_sconf γ Φ (mword_of_int (PK + 0x206)) a0_idx a5_idx (mword_of_int 0 : mword 12)
              V (K - 24)%nat (pk_lo m k)
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hcg Hpc [] Hlo [-]").
    { iApply (pki_206 with "Htext"). }
    iIntros "Hcg Hpc Hlo". iEval (rewrite Hlwa) in "Hlo".
    iDestruct (word_pointsto_join4 _ _ _ _ Halv with "Hlo Hhi") as "Hslot".
    rewrite word_of_words_id.
    iDestruct ("Hvacl" with "Hslot") as "Hva".
    set (C1 := <[Regidx a0_idx := regval_into_reg (sign_extend' 64 (pk_lo m k))]> V).
    assert (Hp208 : add_vec_int (mword_of_int (PK + 0x206) : mword 64) 2 = mword_of_int (PK + 0x208)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp208) in "Hpc".
    iApply (wp_jal_s_sconf γ Φ (mword_of_int (PK + 0x208)) ra_idx (mword_of_int 2095992 : mword 21)
              C1 (K - 24)%nat ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              ltac:(vm_compute; reflexivity)
              with "Hcg Hpc [] [-]").
    { iApply (pki_208 with "Htext"). }
    iIntros "Hcg Hpc".
    set (C2 := <[Regidx ra_idx := regval_into_reg (add_vec_int (mword_of_int (PK + 0x208) : mword 64) 4)]> C1).
    assert (Htgtc : add_vec (mword_of_int (PK + 0x208) : mword 64) (sign_extend' 64 (mword_of_int 2095992 : mword 21)) = mword_of_int KernelSyms.consputc) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgtc) in "Hpc".
    iApply (wp_consputc γ γd Φ C2 (K - 24)%nat l pv pkv dqm dqm2 HK6 Hpv Hpkv
              with "Hcg Htext Hpc Hpanicking Hpanicked Hdev Htx Hdlab [-]").
    iIntros (mf bs) "Hcg Hpc %Hcs Hpanicking Hpanicked Htx #Hsent".
    destruct Hcs as [Hcs Hra].
    assert (Hret : ret_pc (C2 !!! Regidx ra_idx) = mword_of_int (PK + 0x20c))
      by (rewrite /C2 upd_eq; unfold ret_pc; apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hret) in "Hpc".
    iApply (wp_cj_s_sconf γ Φ (mword_of_int (PK + 0x20c)) (sign_extend' 21 (concat_vec (mword_of_int 1846 : mword 11) ('b"0")))
              mf (K - 24)%nat ltac:(vm_compute; reflexivity)
              with "Hcg Hpc [] [-]").
    { iApply (pki_20c with "Htext"). }
    iNext. iIntros "Hcg Hpc".
    assert (Htgt78 : add_vec (mword_of_int (PK + 0x20c) : mword 64) (sign_extend' 64 (sign_extend' 21 (concat_vec (mword_of_int 1846 : mword 11) ('b"0")))) = mword_of_int (PK + 0x78)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgt78) in "Hpc".
    iApply ("Hcont" $! mf bs with "[%] Hcg Hpc Hap Hva Hpanicking Hpanicked Htx Hsent HR").
    intros c Hc.
    pose proof (is_cs_idx_true_neq ra_idx c ltac:(vm_compute; reflexivity) Hc) as N1.
    pose proof (is_cs_idx_true_neq a0_idx c ltac:(vm_compute; reflexivity) Hc) as N10.
    pose proof (is_cs_idx_true_neq (mword_of_int 14 : mword 5) c ltac:(vm_compute; reflexivity) Hc) as N14.
    pose proof (is_cs_idx_true_neq a5_idx c ltac:(vm_compute; reflexivity) Hc) as N15.
    rewrite (callee_saved_lookup Hcs c Hc).
    rewrite /C2 upd_ne; [| congruence]. rewrite /C1 upd_ne; [| congruence].
    apply Hvk; congruence.
  Qed.

  (* [%%] (0x246..0x24c) and the UNKNOWN directive (0x31a..0x328): no vararg,
     just one or two characters straight to consputc.  [s5] holds c0, which is
     '%' in the first case and the unrecognised character in the second -- and
     the code prints it either way, which is why one lemma with a parameter
     for the leading character would not be simpler than these two. *)
  Lemma wp_printk_arm_pct (γ : gname) (γd : uart_names) (Φ : mval -> iProp Σ)
      (mc : regfile) (K : nat) (l : list (bv 8)) (pv pkv : mword 32)
      (dqm dqm2 : dfrac) (Rest : iProp Σ) :
    (30 <= K)%nat ->
    eq_vec (sign_extend' 64 pv) zero_reg = false ->
    neq_vec (sign_extend' 64 pkv) zero_reg = false ->
    sie_cap_gpr γ mc (K - 24)%nat -∗
    kernel_text -∗
    pc_is (mword_of_int (PK + 0x246) : mword 64) -∗
    (mword_of_int KernelSyms.panicking : mword 64) ↦₄{ dqm } pv -∗
    (mword_of_int KernelSyms.panicked : mword 64) ↦₄{ dqm2 } pkv -∗
    dev_inv γd -∗ uart_tx_own γd l -∗ uart_dlab_off γd -∗
    Rest -∗
    ( ∀ (mf : regfile) (bs : list (bv 8)),
      ⌜ forall c : mword 5, is_cs_idx c = true -> mf !!! Regidx c = mc !!! Regidx c ⌝ -∗
      sie_cap_gpr γ mf (K - 24)%nat -∗
      pc_is (mword_of_int (PK + 0x78) : mword 64) -∗
      (mword_of_int KernelSyms.panicking : mword 64) ↦₄{ dqm } pv -∗
      (mword_of_int KernelSyms.panicked : mword 64) ↦₄{ dqm2 } pkv -∗
      uart_tx_own γd (l ++ bs) -∗ uart_sent γd (l ++ bs) -∗
      Rest -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    intros HK Hpv Hpkv.
    assert (HK6 : (6 <= K - 24)%nat) by lia.
    iIntros "Hcg #Htext Hpc Hpanicking Hpanicked #Hdev Htx #Hdlab HR Hcont".
    (* +0x246 c.mv a0,s5 : the character after the '%' *)
    iApply (wp_cmv_s_sconf γ Φ (mword_of_int (PK + 0x246)) a0_idx (mword_of_int 21 : mword 5)
              mc (K - 24)%nat ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hcg Hpc [] [-]").
    { iApply (pki_246 with "Htext"). }
    iIntros "Hcg Hpc".
    set (P1 := <[Regidx a0_idx := regval_into_reg (add_vec zero_reg (mc !!! Regidx (mword_of_int 21 : mword 5)))]> mc).
    assert (Hp248 : add_vec_int (mword_of_int (PK + 0x246) : mword 64) 2 = mword_of_int (PK + 0x248)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp248) in "Hpc".
    iApply (wp_jal_s_sconf γ Φ (mword_of_int (PK + 0x248)) ra_idx (mword_of_int 2095928 : mword 21)
              P1 (K - 24)%nat ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              ltac:(vm_compute; reflexivity)
              with "Hcg Hpc [] [-]").
    { iApply (pki_248 with "Htext"). }
    iIntros "Hcg Hpc".
    set (P2 := <[Regidx ra_idx := regval_into_reg (add_vec_int (mword_of_int (PK + 0x248) : mword 64) 4)]> P1).
    assert (Htgtc : add_vec (mword_of_int (PK + 0x248) : mword 64) (sign_extend' 64 (mword_of_int 2095928 : mword 21)) = mword_of_int KernelSyms.consputc) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgtc) in "Hpc".
    iApply (wp_consputc γ γd Φ P2 (K - 24)%nat l pv pkv dqm dqm2 HK6 Hpv Hpkv
              with "Hcg Htext Hpc Hpanicking Hpanicked Hdev Htx Hdlab [-]").
    iIntros (mf bs) "Hcg Hpc %Hcs Hpanicking Hpanicked Htx #Hsent".
    destruct Hcs as [Hcs Hra].
    assert (Hret : ret_pc (P2 !!! Regidx ra_idx) = mword_of_int (PK + 0x24c))
      by (rewrite /P2 upd_eq; unfold ret_pc; apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hret) in "Hpc".
    iApply (wp_cj_s_sconf γ Φ (mword_of_int (PK + 0x24c)) (sign_extend' 21 (concat_vec (mword_of_int 1814 : mword 11) ('b"0")))
              mf (K - 24)%nat ltac:(vm_compute; reflexivity)
              with "Hcg Hpc [] [-]").
    { iApply (pki_24c with "Htext"). }
    iNext. iIntros "Hcg Hpc".
    assert (Htgt78 : add_vec (mword_of_int (PK + 0x24c) : mword 64) (sign_extend' 64 (sign_extend' 21 (concat_vec (mword_of_int 1814 : mword 11) ('b"0")))) = mword_of_int (PK + 0x78)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgt78) in "Hpc".
    iApply ("Hcont" $! mf bs with "[%] Hcg Hpc Hpanicking Hpanicked Htx Hsent HR").
    intros c Hc.
    pose proof (is_cs_idx_true_neq ra_idx c ltac:(vm_compute; reflexivity) Hc) as N1.
    pose proof (is_cs_idx_true_neq a0_idx c ltac:(vm_compute; reflexivity) Hc) as N10.
    rewrite (callee_saved_lookup Hcs c Hc).
    rewrite /P2 upd_ne; [| congruence]. rewrite /P1 upd_ne; [reflexivity | congruence].
  Qed.

  Lemma wp_printk_arm_unknown (γ : gname) (γd : uart_names) (Φ : mval -> iProp Σ)
      (mc : regfile) (K : nat) (l : list (bv 8)) (pv pkv : mword 32)
      (dqm dqm2 : dfrac) (Rest : iProp Σ) :
    (30 <= K)%nat ->
    eq_vec (sign_extend' 64 pv) zero_reg = false ->
    neq_vec (sign_extend' 64 pkv) zero_reg = false ->
    sie_cap_gpr γ mc (K - 24)%nat -∗
    kernel_text -∗
    pc_is (mword_of_int (PK + 0x31a) : mword 64) -∗
    (mword_of_int KernelSyms.panicking : mword 64) ↦₄{ dqm } pv -∗
    (mword_of_int KernelSyms.panicked : mword 64) ↦₄{ dqm2 } pkv -∗
    dev_inv γd -∗ uart_tx_own γd l -∗ uart_dlab_off γd -∗
    Rest -∗
    ( ∀ (mf : regfile) (bs : list (bv 8)),
      ⌜ forall c : mword 5, is_cs_idx c = true -> mf !!! Regidx c = mc !!! Regidx c ⌝ -∗
      sie_cap_gpr γ mf (K - 24)%nat -∗
      pc_is (mword_of_int (PK + 0x78) : mword 64) -∗
      (mword_of_int KernelSyms.panicking : mword 64) ↦₄{ dqm } pv -∗
      (mword_of_int KernelSyms.panicked : mword 64) ↦₄{ dqm2 } pkv -∗
      uart_tx_own γd (l ++ bs) -∗ uart_sent γd (l ++ bs) -∗
      Rest -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    intros HK Hpv Hpkv.
    assert (HK6 : (6 <= K - 24)%nat) by lia.
    iIntros "Hcg #Htext Hpc Hpanicking Hpanicked #Hdev Htx #Hdlab HR Hcont".
    (* +0x31a li a0,'%' *)
    iApply (wp_li4_s_sconf γ Φ (mword_of_int (PK + 0x31a)) a0_idx (mword_of_int 37 : mword 12)
              (mword_of_int 37 : mword 64) mc (K - 24)%nat
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc [] [-]").
    { iApply (pki_31a with "Htext"). }
    iIntros "Hcg Hpc".
    set (U1 := <[Regidx a0_idx := regval_into_reg (mword_of_int 37 : mword 64)]> mc).
    assert (Hp31e : add_vec_int (mword_of_int (PK + 0x31a) : mword 64) 4 = mword_of_int (PK + 0x31e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp31e) in "Hpc".
    iApply (wp_jal_s_sconf γ Φ (mword_of_int (PK + 0x31e)) ra_idx (mword_of_int 2095714 : mword 21)
              U1 (K - 24)%nat ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              ltac:(vm_compute; reflexivity)
              with "Hcg Hpc [] [-]").
    { iApply (pki_31e with "Htext"). }
    iIntros "Hcg Hpc".
    set (U2 := <[Regidx ra_idx := regval_into_reg (add_vec_int (mword_of_int (PK + 0x31e) : mword 64) 4)]> U1).
    assert (Htgtc1 : add_vec (mword_of_int (PK + 0x31e) : mword 64) (sign_extend' 64 (mword_of_int 2095714 : mword 21)) = mword_of_int KernelSyms.consputc) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgtc1) in "Hpc".
    iApply (wp_consputc γ γd Φ U2 (K - 24)%nat l pv pkv dqm dqm2 HK6 Hpv Hpkv
              with "Hcg Htext Hpc Hpanicking Hpanicked Hdev Htx Hdlab [-]").
    iIntros (m1 bs1) "Hcg Hpc %Hcs1 Hpanicking Hpanicked Htx #Hsent1".
    destruct Hcs1 as [Hcs1 Hra1].
    assert (Hret1 : ret_pc (U2 !!! Regidx ra_idx) = mword_of_int (PK + 0x322))
      by (rewrite /U2 upd_eq; unfold ret_pc; apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hret1) in "Hpc".
    (* +0x322 c.mv a0,s5 : and now the character itself *)
    iApply (wp_cmv_s_sconf γ Φ (mword_of_int (PK + 0x322)) a0_idx (mword_of_int 21 : mword 5)
              m1 (K - 24)%nat ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hcg Hpc [] [-]").
    { iApply (pki_322 with "Htext"). }
    iIntros "Hcg Hpc".
    set (U3 := <[Regidx a0_idx := regval_into_reg (add_vec zero_reg (m1 !!! Regidx (mword_of_int 21 : mword 5)))]> m1).
    assert (Hp324 : add_vec_int (mword_of_int (PK + 0x322) : mword 64) 2 = mword_of_int (PK + 0x324)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp324) in "Hpc".
    iApply (wp_jal_s_sconf γ Φ (mword_of_int (PK + 0x324)) ra_idx (mword_of_int 2095708 : mword 21)
              U3 (K - 24)%nat ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              ltac:(vm_compute; reflexivity)
              with "Hcg Hpc [] [-]").
    { iApply (pki_324 with "Htext"). }
    iIntros "Hcg Hpc".
    set (U4 := <[Regidx ra_idx := regval_into_reg (add_vec_int (mword_of_int (PK + 0x324) : mword 64) 4)]> U3).
    assert (Htgtc2 : add_vec (mword_of_int (PK + 0x324) : mword 64) (sign_extend' 64 (mword_of_int 2095708 : mword 21)) = mword_of_int KernelSyms.consputc) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgtc2) in "Hpc".
    iApply (wp_consputc γ γd Φ U4 (K - 24)%nat (l ++ bs1)%list pv pkv dqm dqm2 HK6 Hpv Hpkv
              with "Hcg Htext Hpc Hpanicking Hpanicked Hdev Htx Hdlab [-]").
    iIntros (mf bs2) "Hcg Hpc %Hcs2 Hpanicking Hpanicked Htx #Hsent2".
    destruct Hcs2 as [Hcs2 Hra2].
    assert (Hret2 : ret_pc (U4 !!! Regidx ra_idx) = mword_of_int (PK + 0x328))
      by (rewrite /U4 upd_eq; unfold ret_pc; apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hret2) in "Hpc".
    iApply (wp_cj_s_sconf γ Φ (mword_of_int (PK + 0x328)) (sign_extend' 21 (concat_vec (mword_of_int 1704 : mword 11) ('b"0")))
              mf (K - 24)%nat ltac:(vm_compute; reflexivity)
              with "Hcg Hpc [] [-]").
    { iApply (pki_328 with "Htext"). }
    iNext. iIntros "Hcg Hpc".
    assert (Htgt78 : add_vec (mword_of_int (PK + 0x328) : mword 64) (sign_extend' 64 (sign_extend' 21 (concat_vec (mword_of_int 1704 : mword 11) ('b"0")))) = mword_of_int (PK + 0x78)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgt78) in "Hpc".
    iEval (rewrite -!app_assoc) in "Htx".
    iEval (rewrite -!app_assoc) in "Hsent2".
    iApply ("Hcont" $! mf (bs1 ++ bs2)%list with "[%] Hcg Hpc Hpanicking Hpanicked Htx Hsent2 HR").
    intros c Hc.
    pose proof (is_cs_idx_true_neq ra_idx c ltac:(vm_compute; reflexivity) Hc) as N1.
    pose proof (is_cs_idx_true_neq a0_idx c ltac:(vm_compute; reflexivity) Hc) as N10.
    rewrite (callee_saved_lookup Hcs2 c Hc).
    rewrite /U4 upd_ne; [| congruence]. rewrite /U3 upd_ne; [| congruence].
    rewrite (callee_saved_lookup Hcs1 c Hc).
    rewrite /U2 upd_ne; [| congruence]. rewrite /U1 upd_ne; [reflexivity | congruence].
  Qed.

End ProofPrintk.
