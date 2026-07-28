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

End ProofPrintk.
