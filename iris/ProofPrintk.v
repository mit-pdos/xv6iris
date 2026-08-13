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
From Stdlib Require Import ZArith Bool Lia List Ascii String.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_var gen_heap invariants.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import RiscvLang RiscvPtsto RiscvExtras RiscvModelBytes.
Require Import RegFile InstrBytes WpMmodeLeafBase.
Require Import SmodeCore.
Require Import StackOwn CalleeSaved KernelText KernelDataInv.
Require Import KernelRvcDecode.
Require Import WpSconfAlu WpSconfMem WpSconfCtl WpSconfBtype WpSmodeIntr.
Require Import DiskPtsto WpUart.
Require Import IntrDefs HartTp WpNext WpSconfVc.
Require Import PrintintArith StackBytes.
Require Import CodePrintk.
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

(* Frame assembly compares dozens of [pa_stk sp0 j] cells against one another;
   left transparent, every FAILED comparison makes the unifier unfold through
   [add_vec_int] down to the bitvector records.  Keeping it opaque makes those
   failures first-order (the slot indices are literals).  Proofs that need the
   arithmetic still say [unfold pa_stk] explicitly, which Opaque does not
   block. *)
Local Strategy 1000 [pa_stk].

Module PrintkProof (Consputc : CONSPUTC) (Printint : PRINTINT) : PRINTK.

Section ProofPrintk.
  Context `{!riscvGS Σ, !sieG Σ}.
  Context `{!uartGhostG Σ, !diskGhostG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.


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

  (* the ten callee-saved registers the epilogue does NOT restore: it
     reloads sp, s0 and s2 only, so every other callee-saved register must
     already agree with the entry map.  Spelled out rather than quantified over
     [is_cs_idx], because an [is_cs_idx]-enumeration tactic has to case-split
     many ways inside a large iris context.  (tp is NOT tracked here: the
     explicit-cpuid register file pins tp canonically -- HartTp.v -- and
     [callee_saved] carries no tp conjunct for a caller to need.) *)
  Definition pk_cs_kept (m mc : regfile) : Prop :=
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

  Lemma wp_printk_prologue `{CID0 : CpuId}
      (m : regfile) (K : nat) (b : bool) (pcur : mword 64) :
    let sp0 := m !!! Regidx csp_rs1 in
    let spd := add_vec sp0 (sign_extend' 64 (caddi16sp_imm (mword_of_int 52 : mword 6))) in
    (24 <= K)%nat ->
    sie_cap_gpr m K b pcur -∗
    kernel_text -∗
    pc_is (mword_of_int KernelSyms.printk : mword 64) -∗
    wp_next (CID0 := CID0) b pcur (fun (CID : CpuId) =>
      ∀ mp : regfile,
      ⌜ mp !!! Regidx csp_rs1 = spd
        /\ mp !!! Regidx s0_idx = add_vec sp0 (sign_extend' 64 (mword_of_int (-64) : mword 12))
        /\ mp !!! Regidx s2_idx = m !!! Regidx a0_idx
        /\ (forall c : mword 5, c <> csp_rs1 -> c <> s0_idx -> c <> s2_idx ->
              mp !!! Regidx c = m !!! Regidx c) ⌝ -∗
      sie_cap_gpr mp (K - 24)%nat b pcur -∗
      pc_is (mword_of_int (KernelSyms.printk + 0x1e) : mword 64) -∗
      (pa_stk sp0 9) ↦₈ (m !!! Regidx ra_idx) -∗
      (pa_stk sp0 10) ↦₈ (m !!! Regidx s0_idx) -∗
      (pa_stk sp0 12) ↦₈ (m !!! Regidx s2_idx) -∗
      pk_va sp0 m -∗
      ([∗ list] k ∈ [8;11;13;14;15;16;17;18;19;20;21;22;23;24]%nat,
         ∃ w : mword 64, (pa_stk sp0 k) ↦₈ w) -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
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
    iApply (wp_caddi16sp_push_s_sconf (mword_of_int KernelSyms.printk) (mword_of_int 52 : mword 6) m K 24 b
              HK Hpush with "Hcg Hpc Hi00 [-]").
    iIntros (CID1 Hs1) "Hcg Hframe Hpc".
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
    assert (Hp02 : add_vec_int (mword_of_int KernelSyms.printk : mword 64) 2 = mword_of_int (KernelSyms.printk + 0x02)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp02) in "Hpc".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.printk + 0x02)) (mword_of_int 15 : mword 6) ra_idx
              W1 (K - 24)%nat u9 b with "Hcg Hpc Hi02 [H9] [-]").
    { iEval (rewrite HW1sp Hb9). iExact "H9". }
    iIntros (CID2 Hs2) "Hcg Hpc H9". iEval (rewrite HW1sp Hb9) in "H9".
    iEval (rgne) in "H9".
    assert (HW1r1 : W1 !!! Regidx ra_idx = m !!! Regidx ra_idx) by (rewrite /W1 upd_ne; [reflexivity | reg_neq]).
    iEval (rewrite HW1r1) in "H9".
    assert (Hp04 : add_vec_int (mword_of_int (KernelSyms.printk + 0x02) : mword 64) 2 = mword_of_int (KernelSyms.printk + 0x04)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp04) in "Hpc".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.printk + 0x04)) (mword_of_int 14 : mword 6) s0_idx
              W1 (K - 24)%nat u10 b with "Hcg Hpc Hi04 [H10] [-]").
    { iEval (rewrite HW1sp Hb10). iExact "H10". }
    iIntros (CID3 Hs3) "Hcg Hpc H10". iEval (rewrite HW1sp Hb10) in "H10".
    iEval (rgne) in "H10".
    assert (HW1r8 : W1 !!! Regidx s0_idx = m !!! Regidx s0_idx) by (rewrite /W1 upd_ne; [reflexivity | reg_neq]).
    iEval (rewrite HW1r8) in "H10".
    assert (Hp06 : add_vec_int (mword_of_int (KernelSyms.printk + 0x04) : mword 64) 2 = mword_of_int (KernelSyms.printk + 0x06)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp06) in "Hpc".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.printk + 0x06)) (mword_of_int 12 : mword 6) s2_idx
              W1 (K - 24)%nat u12 b with "Hcg Hpc Hi06 [H12] [-]").
    { iEval (rewrite HW1sp Hb12). iExact "H12". }
    iIntros (CID4 Hs4) "Hcg Hpc H12". iEval (rewrite HW1sp Hb12) in "H12".
    iEval (rgne) in "H12".
    assert (HW1r18 : W1 !!! Regidx s2_idx = m !!! Regidx s2_idx) by (rewrite /W1 upd_ne; [reflexivity | reg_neq]).
    iEval (rewrite HW1r18) in "H12".
    assert (Hp08 : add_vec_int (mword_of_int (KernelSyms.printk + 0x06) : mword 64) 2 = mword_of_int (KernelSyms.printk + 0x08)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp08) in "Hpc".
    (* +0x08 addi s0,sp,128 : s0 := sp0 - 64, the va_list's base *)
    iApply (wp_caddi4spn_s_sconf (mword_of_int (KernelSyms.printk + 0x08)) (Cregidx (mword_of_int 0)) (mword_of_int 32 : mword 8) s0_idx
              W1 (K - 24)%nat b ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi08 [-]").
    iIntros (CID5 Hs5) "Hcg Hpc".
    set (W2 := <[Regidx s0_idx := regval_into_reg (add_vec (W1 !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm (mword_of_int 32 : mword 8))))]> W1).
    assert (HW2s0 : W2 !!! Regidx s0_idx = add_vec sp0 (sign_extend' 64 (mword_of_int (-64) : mword 12))).
    { rewrite /W2 upd_eq. unfold regval_into_reg. rewrite HW1sp. unfold spd.
      rewrite pa_stk_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (HW2sp : W2 !!! Regidx csp_rs1 = spd) by (rewrite /W2 upd_ne; [exact HW1sp | reg_neq]).
    assert (Hp0a : add_vec_int (mword_of_int (KernelSyms.printk + 0x08) : mword 64) 2 = mword_of_int (KernelSyms.printk + 0x0a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp0a) in "Hpc".
    (* +0x0a c.mv s2,a0 : s2 := fmt *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.printk + 0x0a)) s2_idx a0_idx W2 (K - 24)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi0a [-]").
    iIntros (CID6 Hs6) "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (W3 := <[Regidx s2_idx := regval_into_reg (add_vec zero_reg (W2 !!! Regidx a0_idx))]> W2).
    assert (HW3s2 : W3 !!! Regidx s2_idx = m !!! Regidx a0_idx).
    { rewrite /W3 upd_eq. unfold regval_into_reg.
      rewrite /W2 upd_ne; [| reg_neq]. rewrite /W1 upd_ne; [| reg_neq].
      apply add_vec_zero_l. }
    assert (HW3s0 : W3 !!! Regidx s0_idx = add_vec sp0 (sign_extend' 64 (mword_of_int (-64) : mword 12)))
      by (rewrite /W3 upd_ne; [exact HW2s0 | reg_neq]).
    assert (HW3sp : W3 !!! Regidx csp_rs1 = spd) by (rewrite /W3 upd_ne; [exact HW2sp | reg_neq]).
    assert (Hp0c : add_vec_int (mword_of_int (KernelSyms.printk + 0x0a) : mword 64) 2 = mword_of_int (KernelSyms.printk + 0x0c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp0c) in "Hpc".
    (* +0x0c sd a1,8(s0) -> slot 7 *)
    assert (Hva7 : add_vec (W3 !!! Regidx s0_idx) (sign_extend' 64 (mword_of_int 8 : mword 12)) = pa_stk sp0 7).
    { rewrite HW3s0. unfold pa_stk, add_vec_int. rewrite pa_stk_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    iApply (wp_csd_s_sconf (mword_of_int (KernelSyms.printk + 0x0c)) (mword_of_int 11 : mword 5) s0_idx (mword_of_int 8 : mword 12)
              W3 (K - 24)%nat u7 b with "Hcg Hpc Hi0c [V7] [-]").
    { iEval (rewrite Hva7). iExact "V7". }
    iIntros (CID7 Hs7) "Hcg Hpc V7". iEval (rewrite Hva7) in "V7".
    iEval (rgne) in "V7".
    assert (HW3r11 : W3 !!! Regidx (mword_of_int 11 : mword 5) = m !!! Regidx (mword_of_int 11 : mword 5)).
    { rewrite /W3 upd_ne; [| reg_neq]. rewrite /W2 upd_ne; [| reg_neq].
      rewrite /W1 upd_ne; [reflexivity | reg_neq]. }
    iEval (rewrite HW3r11) in "V7".
    assert (Hp0e : add_vec_int (mword_of_int (KernelSyms.printk + 0x0c) : mword 64) 2 = mword_of_int (KernelSyms.printk + 0x0e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp0e) in "Hpc".
    (* +0x0e sd a2,16(s0) -> slot 6 *)
    assert (Hva6 : add_vec (W3 !!! Regidx s0_idx) (sign_extend' 64 (mword_of_int 16 : mword 12)) = pa_stk sp0 6).
    { rewrite HW3s0. unfold pa_stk, add_vec_int. rewrite pa_stk_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    iApply (wp_csd_s_sconf (mword_of_int (KernelSyms.printk + 0x0e)) (mword_of_int 12 : mword 5) s0_idx (mword_of_int 16 : mword 12)
              W3 (K - 24)%nat u6 b with "Hcg Hpc Hi0e [V6] [-]").
    { iEval (rewrite Hva6). iExact "V6". }
    iIntros (CID8 Hs8) "Hcg Hpc V6". iEval (rewrite Hva6) in "V6".
    iEval (rgne) in "V6".
    assert (HW3r12 : W3 !!! Regidx (mword_of_int 12 : mword 5) = m !!! Regidx (mword_of_int 12 : mword 5)).
    { rewrite /W3 upd_ne; [| reg_neq]. rewrite /W2 upd_ne; [| reg_neq].
      rewrite /W1 upd_ne; [reflexivity | reg_neq]. }
    iEval (rewrite HW3r12) in "V6".
    assert (Hp10 : add_vec_int (mword_of_int (KernelSyms.printk + 0x0e) : mword 64) 2 = mword_of_int (KernelSyms.printk + 0x10)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp10) in "Hpc".
    (* +0x10 sd a3,24(s0) -> slot 5 *)
    assert (Hva5 : add_vec (W3 !!! Regidx s0_idx) (sign_extend' 64 (mword_of_int 24 : mword 12)) = pa_stk sp0 5).
    { rewrite HW3s0. unfold pa_stk, add_vec_int. rewrite pa_stk_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    iApply (wp_csd_s_sconf (mword_of_int (KernelSyms.printk + 0x10)) (mword_of_int 13 : mword 5) s0_idx (mword_of_int 24 : mword 12)
              W3 (K - 24)%nat u5 b with "Hcg Hpc Hi10 [V5] [-]").
    { iEval (rewrite Hva5). iExact "V5". }
    iIntros (CID9 Hs9) "Hcg Hpc V5". iEval (rewrite Hva5) in "V5".
    iEval (rgne) in "V5".
    assert (HW3r13 : W3 !!! Regidx (mword_of_int 13 : mword 5) = m !!! Regidx (mword_of_int 13 : mword 5)).
    { rewrite /W3 upd_ne; [| reg_neq]. rewrite /W2 upd_ne; [| reg_neq].
      rewrite /W1 upd_ne; [reflexivity | reg_neq]. }
    iEval (rewrite HW3r13) in "V5".
    assert (Hp12 : add_vec_int (mword_of_int (KernelSyms.printk + 0x10) : mword 64) 2 = mword_of_int (KernelSyms.printk + 0x12)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp12) in "Hpc".
    (* +0x12 sd a4,32(s0) -> slot 4 *)
    assert (Hva4 : add_vec (W3 !!! Regidx s0_idx) (sign_extend' 64 (mword_of_int 32 : mword 12)) = pa_stk sp0 4).
    { rewrite HW3s0. unfold pa_stk, add_vec_int. rewrite pa_stk_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    iApply (wp_csd_s_sconf (mword_of_int (KernelSyms.printk + 0x12)) (mword_of_int 14 : mword 5) s0_idx (mword_of_int 32 : mword 12)
              W3 (K - 24)%nat u4 b with "Hcg Hpc Hi12 [V4] [-]").
    { iEval (rewrite Hva4). iExact "V4". }
    iIntros (CID10 Hs10) "Hcg Hpc V4". iEval (rewrite Hva4) in "V4".
    iEval (rgne) in "V4".
    assert (HW3r14 : W3 !!! Regidx (mword_of_int 14 : mword 5) = m !!! Regidx (mword_of_int 14 : mword 5)).
    { rewrite /W3 upd_ne; [| reg_neq]. rewrite /W2 upd_ne; [| reg_neq].
      rewrite /W1 upd_ne; [reflexivity | reg_neq]. }
    iEval (rewrite HW3r14) in "V4".
    assert (Hp14 : add_vec_int (mword_of_int (KernelSyms.printk + 0x12) : mword 64) 2 = mword_of_int (KernelSyms.printk + 0x14)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp14) in "Hpc".
    (* +0x14 sd a5,40(s0) -> slot 3 *)
    assert (Hva3 : add_vec (W3 !!! Regidx s0_idx) (sign_extend' 64 (mword_of_int 40 : mword 12)) = pa_stk sp0 3).
    { rewrite HW3s0. unfold pa_stk, add_vec_int. rewrite pa_stk_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    iApply (wp_csd_s_sconf (mword_of_int (KernelSyms.printk + 0x14)) (mword_of_int 15 : mword 5) s0_idx (mword_of_int 40 : mword 12)
              W3 (K - 24)%nat u3 b with "Hcg Hpc Hi14 [V3] [-]").
    { iEval (rewrite Hva3). iExact "V3". }
    iIntros (CID11 Hs11) "Hcg Hpc V3". iEval (rewrite Hva3) in "V3".
    iEval (rgne) in "V3".
    assert (HW3r15 : W3 !!! Regidx (mword_of_int 15 : mword 5) = m !!! Regidx (mword_of_int 15 : mword 5)).
    { rewrite /W3 upd_ne; [| reg_neq]. rewrite /W2 upd_ne; [| reg_neq].
      rewrite /W1 upd_ne; [reflexivity | reg_neq]. }
    iEval (rewrite HW3r15) in "V3".
    assert (Hp16 : add_vec_int (mword_of_int (KernelSyms.printk + 0x14) : mword 64) 2 = mword_of_int (KernelSyms.printk + 0x16)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp16) in "Hpc".
    (* +0x16 sd a6,48(s0) -> slot 2 *)
    assert (Hva2 : add_vec (W3 !!! Regidx s0_idx) (sign_extend' 64 (mword_of_int 48 : mword 12)) = pa_stk sp0 2).
    { rewrite HW3s0. unfold pa_stk, add_vec_int. rewrite pa_stk_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    iApply (wp_sd_s_sconf (mword_of_int (KernelSyms.printk + 0x16)) (mword_of_int 16 : mword 5) s0_idx (mword_of_int 48 : mword 12)
              W3 (K - 24)%nat u2 b with "Hcg Hpc Hi16 [V2] [-]").
    { iEval (rewrite Hva2). iExact "V2". }
    iIntros (CID12 Hs12) "Hcg Hpc V2". iEval (rewrite Hva2) in "V2".
    iEval (rgne) in "V2".
    assert (HW3r16 : W3 !!! Regidx (mword_of_int 16 : mword 5) = m !!! Regidx (mword_of_int 16 : mword 5)).
    { rewrite /W3 upd_ne; [| reg_neq]. rewrite /W2 upd_ne; [| reg_neq].
      rewrite /W1 upd_ne; [reflexivity | reg_neq]. }
    iEval (rewrite HW3r16) in "V2".
    assert (Hp1a : add_vec_int (mword_of_int (KernelSyms.printk + 0x16) : mword 64) 4 = mword_of_int (KernelSyms.printk + 0x1a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp1a) in "Hpc".
    (* +0x1a sd a7,56(s0) -> slot 1 *)
    assert (Hva1 : add_vec (W3 !!! Regidx s0_idx) (sign_extend' 64 (mword_of_int 56 : mword 12)) = pa_stk sp0 1).
    { rewrite HW3s0. unfold pa_stk, add_vec_int. rewrite pa_stk_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    iApply (wp_sd_s_sconf (mword_of_int (KernelSyms.printk + 0x1a)) (mword_of_int 17 : mword 5) s0_idx (mword_of_int 56 : mword 12)
              W3 (K - 24)%nat u1 b with "Hcg Hpc Hi1a [V1] [-]").
    { iEval (rewrite Hva1). iExact "V1". }
    iIntros (CID13 Hs13) "Hcg Hpc V1". iEval (rewrite Hva1) in "V1".
    iEval (rgne) in "V1".
    assert (HW3r17 : W3 !!! Regidx (mword_of_int 17 : mword 5) = m !!! Regidx (mword_of_int 17 : mword 5)).
    { rewrite /W3 upd_ne; [| reg_neq]. rewrite /W2 upd_ne; [| reg_neq].
      rewrite /W1 upd_ne; [reflexivity | reg_neq]. }
    iEval (rewrite HW3r17) in "V1".
    assert (Hp1e : add_vec_int (mword_of_int (KernelSyms.printk + 0x1a) : mword 64) 4 = mword_of_int (KernelSyms.printk + 0x1e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp1e) in "Hpc".
    (* hand over: the frame in the shape the body reads it *)
    iSpecialize ("Hcont" $! CID13 with "[%]"); [wp_next_chain|].
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
    instr (mword_of_int (KernelSyms.printk + B + off) : mword 64) true
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
  Lemma wp_printk_restore `{CID0 : CpuId}
      (mc : regfile) (K : nat) (B : Z) (sp0 : mword 64) (v9 v19 v20 v21 v22 v23 v24 v26 v27 : mword 64)
      (b : bool) (pcur : mword 64) :
    let spd := add_vec sp0 (sign_extend' 64 (caddi16sp_imm (mword_of_int 52 : mword 6))) in
    mc !!! Regidx csp_rs1 = spd ->
    sie_cap_gpr mc (K - 24)%nat b pcur -∗
    pk_restore_instrs B -∗
    pc_is (mword_of_int (KernelSyms.printk + B + 0) : mword 64) -∗
    pk_saved sp0 v9 v19 v20 v21 v22 v23 v24 v26 v27 -∗
    wp_next (CID0 := CID0) b pcur (fun (CID : CpuId) =>
      ∀ mf : regfile,
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
      sie_cap_gpr mf (K - 24)%nat b pcur -∗
      pc_is (mword_of_int (KernelSyms.printk + B + 18) : mword 64) -∗
      pk_saved sp0 v9 v19 v20 v21 v22 v23 v24 v26 v27 -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
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
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.printk + B + 0)) (mword_of_int 13 : mword 6) (mword_of_int 9 : mword 5)
              mc (K - 24)%nat v9 b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc I0 [S9] [-]").
    { iEval (rewrite Hsp Hb9). iExact "S9". }
    iIntros (CID2 Hs2) "Hcg Hpc S9". iEval (rewrite Hsp Hb9) in "S9".
    set (M9 := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg v9]> mc).
    assert (HM9sp : M9 !!! Regidx csp_rs1 = spd)
      by (rewrite /M9 upd_ne; [exact Hsp | reg_neq]).
    assert (Hp0 : add_vec_int (mword_of_int (KernelSyms.printk + B + 0) : mword 64) 2 = mword_of_int (KernelSyms.printk + B + 2))
      by (unfold add_vec_int; rewrite moi_add; f_equal; lia).
    iEval (rewrite Hp0) in "Hpc".
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.printk + B + 2)) (mword_of_int 11 : mword 6) (mword_of_int 19 : mword 5)
              M9 (K - 24)%nat v19 b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc I2 [S19] [-]").
    { iEval (rewrite HM9sp Hb19). iExact "S19". }
    iIntros (CID3 Hs3) "Hcg Hpc S19". iEval (rewrite HM9sp Hb19) in "S19".
    set (M19 := <[Regidx (mword_of_int 19 : mword 5) := regval_into_reg v19]> M9).
    assert (HM19sp : M19 !!! Regidx csp_rs1 = spd)
      by (rewrite /M19 upd_ne; [exact HM9sp | reg_neq]).
    assert (Hp2 : add_vec_int (mword_of_int (KernelSyms.printk + B + 2) : mword 64) 2 = mword_of_int (KernelSyms.printk + B + 4))
      by (unfold add_vec_int; rewrite moi_add; f_equal; lia).
    iEval (rewrite Hp2) in "Hpc".
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.printk + B + 4)) (mword_of_int 10 : mword 6) (mword_of_int 20 : mword 5)
              M19 (K - 24)%nat v20 b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc I4 [S20] [-]").
    { iEval (rewrite HM19sp Hb20). iExact "S20". }
    iIntros (CID4 Hs4) "Hcg Hpc S20". iEval (rewrite HM19sp Hb20) in "S20".
    set (M20 := <[Regidx (mword_of_int 20 : mword 5) := regval_into_reg v20]> M19).
    assert (HM20sp : M20 !!! Regidx csp_rs1 = spd)
      by (rewrite /M20 upd_ne; [exact HM19sp | reg_neq]).
    assert (Hp4 : add_vec_int (mword_of_int (KernelSyms.printk + B + 4) : mword 64) 2 = mword_of_int (KernelSyms.printk + B + 6))
      by (unfold add_vec_int; rewrite moi_add; f_equal; lia).
    iEval (rewrite Hp4) in "Hpc".
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.printk + B + 6)) (mword_of_int 9 : mword 6) (mword_of_int 21 : mword 5)
              M20 (K - 24)%nat v21 b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc I6 [S21] [-]").
    { iEval (rewrite HM20sp Hb21). iExact "S21". }
    iIntros (CID5 Hs5) "Hcg Hpc S21". iEval (rewrite HM20sp Hb21) in "S21".
    set (M21 := <[Regidx (mword_of_int 21 : mword 5) := regval_into_reg v21]> M20).
    assert (HM21sp : M21 !!! Regidx csp_rs1 = spd)
      by (rewrite /M21 upd_ne; [exact HM20sp | reg_neq]).
    assert (Hp6 : add_vec_int (mword_of_int (KernelSyms.printk + B + 6) : mword 64) 2 = mword_of_int (KernelSyms.printk + B + 8))
      by (unfold add_vec_int; rewrite moi_add; f_equal; lia).
    iEval (rewrite Hp6) in "Hpc".
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.printk + B + 8)) (mword_of_int 8 : mword 6) (mword_of_int 22 : mword 5)
              M21 (K - 24)%nat v22 b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc I8 [S22] [-]").
    { iEval (rewrite HM21sp Hb22). iExact "S22". }
    iIntros (CID6 Hs6) "Hcg Hpc S22". iEval (rewrite HM21sp Hb22) in "S22".
    set (M22 := <[Regidx (mword_of_int 22 : mword 5) := regval_into_reg v22]> M21).
    assert (HM22sp : M22 !!! Regidx csp_rs1 = spd)
      by (rewrite /M22 upd_ne; [exact HM21sp | reg_neq]).
    assert (Hp8 : add_vec_int (mword_of_int (KernelSyms.printk + B + 8) : mword 64) 2 = mword_of_int (KernelSyms.printk + B + 10))
      by (unfold add_vec_int; rewrite moi_add; f_equal; lia).
    iEval (rewrite Hp8) in "Hpc".
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.printk + B + 10)) (mword_of_int 7 : mword 6) (mword_of_int 23 : mword 5)
              M22 (K - 24)%nat v23 b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc I10 [S23] [-]").
    { iEval (rewrite HM22sp Hb23). iExact "S23". }
    iIntros (CID7 Hs7) "Hcg Hpc S23". iEval (rewrite HM22sp Hb23) in "S23".
    set (M23 := <[Regidx (mword_of_int 23 : mword 5) := regval_into_reg v23]> M22).
    assert (HM23sp : M23 !!! Regidx csp_rs1 = spd)
      by (rewrite /M23 upd_ne; [exact HM22sp | reg_neq]).
    assert (Hp10 : add_vec_int (mword_of_int (KernelSyms.printk + B + 10) : mword 64) 2 = mword_of_int (KernelSyms.printk + B + 12))
      by (unfold add_vec_int; rewrite moi_add; f_equal; lia).
    iEval (rewrite Hp10) in "Hpc".
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.printk + B + 12)) (mword_of_int 6 : mword 6) (mword_of_int 24 : mword 5)
              M23 (K - 24)%nat v24 b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc I12 [S24] [-]").
    { iEval (rewrite HM23sp Hb24). iExact "S24". }
    iIntros (CID8 Hs8) "Hcg Hpc S24". iEval (rewrite HM23sp Hb24) in "S24".
    set (M24 := <[Regidx (mword_of_int 24 : mword 5) := regval_into_reg v24]> M23).
    assert (HM24sp : M24 !!! Regidx csp_rs1 = spd)
      by (rewrite /M24 upd_ne; [exact HM23sp | reg_neq]).
    assert (Hp12 : add_vec_int (mword_of_int (KernelSyms.printk + B + 12) : mword 64) 2 = mword_of_int (KernelSyms.printk + B + 14))
      by (unfold add_vec_int; rewrite moi_add; f_equal; lia).
    iEval (rewrite Hp12) in "Hpc".
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.printk + B + 14)) (mword_of_int 4 : mword 6) (mword_of_int 26 : mword 5)
              M24 (K - 24)%nat v26 b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc I14 [S26] [-]").
    { iEval (rewrite HM24sp Hb26). iExact "S26". }
    iIntros (CID9 Hs9) "Hcg Hpc S26". iEval (rewrite HM24sp Hb26) in "S26".
    set (M26 := <[Regidx (mword_of_int 26 : mword 5) := regval_into_reg v26]> M24).
    assert (HM26sp : M26 !!! Regidx csp_rs1 = spd)
      by (rewrite /M26 upd_ne; [exact HM24sp | reg_neq]).
    assert (Hp14 : add_vec_int (mword_of_int (KernelSyms.printk + B + 14) : mword 64) 2 = mword_of_int (KernelSyms.printk + B + 16))
      by (unfold add_vec_int; rewrite moi_add; f_equal; lia).
    iEval (rewrite Hp14) in "Hpc".
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.printk + B + 16)) (mword_of_int 3 : mword 6) (mword_of_int 27 : mword 5)
              M26 (K - 24)%nat v27 b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc I16 [S27] [-]").
    { iEval (rewrite HM26sp Hb27). iExact "S27". }
    iIntros (CID10 Hs10) "Hcg Hpc S27". iEval (rewrite HM26sp Hb27) in "S27".
    set (M27 := <[Regidx (mword_of_int 27 : mword 5) := regval_into_reg v27]> M26).
    assert (HM27sp : M27 !!! Regidx csp_rs1 = spd)
      by (rewrite /M27 upd_ne; [exact HM26sp | reg_neq]).
    assert (Hp16 : add_vec_int (mword_of_int (KernelSyms.printk + B + 16) : mword 64) 2 = mword_of_int (KernelSyms.printk + B + 18))
      by (unfold add_vec_int; rewrite moi_add; f_equal; lia).
    iEval (rewrite Hp16) in "Hpc".
    iSpecialize ("Hcont" $! CID10 with "[%]"); [wp_next_chain|].
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
    rewrite /pk_saved. iFrame "S9 S19 S20 S21 S22 S23 S24 S26 S27".
  Qed.
  (* ================================================================== *)
  (*  THE EPILOGUE (0x260 .. 0x274), the end of every path.              *)
  (* ================================================================== *)

  Lemma wp_printk_epi `{CID0 : CpuId}
      (m mc : regfile) (K : nat) (pv pkv : mword 32) (dqm dqm2 : dfrac) (R : iProp Σ)
      (b : bool) (pcur : mword 64) :
    let sp0 := m !!! Regidx csp_rs1 in
    let spd := add_vec sp0 (sign_extend' 64 (caddi16sp_imm (mword_of_int 52 : mword 6))) in
    (24 <= K)%nat ->
    eq_vec (sign_extend' 64 pv) zero_reg = false ->
    mc !!! Regidx csp_rs1 = spd ->
    pk_cs_kept m mc ->
    sie_cap_gpr mc (K - 24)%nat b pcur -∗
    kernel_text -∗
    pc_is (mword_of_int (KernelSyms.printk + 0x260) : mword 64) -∗
    pk_frame sp0 (m !!! Regidx ra_idx) (m !!! Regidx s0_idx) (m !!! Regidx s2_idx) -∗
    (mword_of_int KernelSyms.panicking : mword 64) ↦₄{ dqm } pv -∗
    R -∗
    wp_next (CID0 := CID0) b pcur (fun (CID : CpuId) =>
      ∀ mf,
      sie_cap_gpr mf K b pcur -∗
      pc_is (ret_pc (m !!! Regidx ra_idx)) -∗
      ⌜ callee_saved m mf /\ mf !!! Regidx ra_idx = m !!! Regidx ra_idx
        /\ mf !!! Regidx a0_idx = zero_reg ⌝ -∗
      (mword_of_int KernelSyms.panicking : mword 64) ↦₄{ dqm } pv -∗
      R -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
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
    iApply (wp_auipc_s_sconf (mword_of_int (KernelSyms.printk + 0x260)) a5_idx (mword_of_int 10 : mword 20)
              mc (K - 24)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi260 [-]").
    iIntros (CID1 Hs1) "Hcg Hpc".
    set (E1 := <[Regidx a5_idx := regval_into_reg (add_vec (mword_of_int (KernelSyms.printk + 0x260) : mword 64) (auipc_off (mword_of_int 10 : mword 20)))]> mc).
    assert (Hpanaddr : add_vec (rget E1 a5_idx) (sign_extend' 64 (mword_of_int 2858 : mword 12))
                       = (mword_of_int KernelSyms.panicking : mword 64)).
    { rgne. rewrite /E1 upd_eq. unfold regval_into_reg. apply bv_eq; vm_compute; reflexivity. }
    assert (Hp264 : add_vec_int (mword_of_int (KernelSyms.printk + 0x260) : mword 64) 4 = mword_of_int (KernelSyms.printk + 0x264)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp264) in "Hpc".
    iEval (rewrite -Hpanaddr) in "Hpanicking".
    iApply (wp_lw_s_sconf (mword_of_int (KernelSyms.printk + 0x264)) a5_idx a5_idx (mword_of_int 2858 : mword 12)
              E1 (K - 24)%nat pv b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi264 Hpanicking [-]").
    iIntros (CID2 Hs2) "Hcg Hpc Hpanicking". iEval (rewrite Hpanaddr) in "Hpanicking".
    set (E2 := <[Regidx a5_idx := regval_into_reg (sign_extend' 64 pv)]> E1).
    assert (Hp268 : add_vec_int (mword_of_int (KernelSyms.printk + 0x264) : mword 64) 4 = mword_of_int (KernelSyms.printk + 0x268)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp268) in "Hpc".
    (* +0x268 beqz a5 : NOT taken -- this is the panic path, so no release *)
    iApply (wp_cbeqz_fall_s_sconf (mword_of_int (KernelSyms.printk + 0x268)) (mword_of_int 17 : mword 8)
              (Cregidx (mword_of_int 7)) a5_idx E2 (K - 24)%nat b
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
              ltac:(rgne; rewrite /E2 upd_eq; exact Hpv)
              with "Hcg Hpc Hi268 [-]").
    iIntros (CID3 Hs3) "Hcg Hpc".
    assert (Hp26a : add_vec_int (mword_of_int (KernelSyms.printk + 0x268) : mword 64) 2 = mword_of_int (KernelSyms.printk + 0x26a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp26a) in "Hpc".
    (* +0x26a c.li a0,0 : the return value *)
    iApply (wp_cli_s_sconf (mword_of_int (KernelSyms.printk + 0x26a)) a0_idx (mword_of_int 0 : mword 6)
              (zero_reg : mword 64) E2 (K - 24)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc Hi26a [-]").
    iIntros (CID4 Hs4) "Hcg Hpc".
    set (E3 := <[Regidx a0_idx := regval_into_reg (zero_reg : mword 64)]> E2).
    assert (HE3sp : E3 !!! Regidx csp_rs1 = spd).
    { rewrite /E3 upd_ne; [| reg_neq]. rewrite /E2 upd_ne; [| reg_neq].
      rewrite /E1 upd_ne; [exact Hsp | reg_neq]. }
    assert (Hp26c : add_vec_int (mword_of_int (KernelSyms.printk + 0x26a) : mword 64) 2 = mword_of_int (KernelSyms.printk + 0x26c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp26c) in "Hpc".
    (* +0x26c/0x26e/0x270 restore ra / s0 / s2 *)
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.printk + 0x26c)) (mword_of_int 15 : mword 6) ra_idx
              E3 (K - 24)%nat (m !!! Regidx ra_idx) b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi26c [H9] [-]").
    { iEval (rewrite HE3sp Hb9). iExact "H9". }
    iIntros (CID5 Hs5) "Hcg Hpc H9". iEval (rewrite HE3sp Hb9) in "H9".
    set (E4 := <[Regidx ra_idx := regval_into_reg (m !!! Regidx ra_idx)]> E3).
    assert (HE4sp : E4 !!! Regidx csp_rs1 = spd) by (rewrite /E4 upd_ne; [exact HE3sp | reg_neq]).
    assert (Hp26e : add_vec_int (mword_of_int (KernelSyms.printk + 0x26c) : mword 64) 2 = mword_of_int (KernelSyms.printk + 0x26e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp26e) in "Hpc".
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.printk + 0x26e)) (mword_of_int 14 : mword 6) s0_idx
              E4 (K - 24)%nat (m !!! Regidx s0_idx) b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi26e [H10] [-]").
    { iEval (rewrite HE4sp Hb10). iExact "H10". }
    iIntros (CID6 Hs6) "Hcg Hpc H10". iEval (rewrite HE4sp Hb10) in "H10".
    set (E5 := <[Regidx s0_idx := regval_into_reg (m !!! Regidx s0_idx)]> E4).
    assert (HE5sp : E5 !!! Regidx csp_rs1 = spd) by (rewrite /E5 upd_ne; [exact HE4sp | reg_neq]).
    assert (Hp270 : add_vec_int (mword_of_int (KernelSyms.printk + 0x26e) : mword 64) 2 = mword_of_int (KernelSyms.printk + 0x270)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp270) in "Hpc".
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.printk + 0x270)) (mword_of_int 12 : mword 6) s2_idx
              E5 (K - 24)%nat (m !!! Regidx s2_idx) b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi270 [H12] [-]").
    { iEval (rewrite HE5sp Hb12). iExact "H12". }
    iIntros (CID7 Hs7) "Hcg Hpc H12". iEval (rewrite HE5sp Hb12) in "H12".
    set (E6 := <[Regidx s2_idx := regval_into_reg (m !!! Regidx s2_idx)]> E5).
    assert (HE6sp : E6 !!! Regidx csp_rs1 = spd) by (rewrite /E6 upd_ne; [exact HE5sp | reg_neq]).
    assert (Hp272 : add_vec_int (mword_of_int (KernelSyms.printk + 0x270) : mword 64) 2 = mword_of_int (KernelSyms.printk + 0x272)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp272) in "Hpc".
    (* +0x272 addi sp,sp,192 : the frame pop *)
    assert (Hwv : add_vec (E6 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 12 : mword 6))) = sp0).
    { rewrite HE6sp. unfold spd. apply frame_cancel_192. }
    assert (Hpop : E6 !!! Regidx csp_rs1 = pa_stk (add_vec (E6 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 12 : mword 6)))) 24).
    { rewrite Hwv HE6sp. exact Hpush. }
    iAssert (stack_own sp0 24) with "[H9 H10 H12 Hrest]" as "Hframe".
    { iApply pk_frame_stack_own. rewrite /pk_frame. iFrame "H9 H10 H12 Hrest". }
    iEval (rewrite -Hwv) in "Hframe".
    iApply (wp_caddi16sp_pop_s_sconf (mword_of_int (KernelSyms.printk + 0x272)) (mword_of_int 12 : mword 6)
              E6 (K - 24)%nat 24 b Hpop with "Hcg Hpc Hi272 Hframe [-]").
    iIntros (CID8 Hs8) "Hcg Hpc".
    set (E7 := <[Regidx csp_rs1 := regval_into_reg (add_vec (E6 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 12 : mword 6))))]> E6).
    iEval (rewrite (pk_nk K HK)) in "Hcg".
    assert (Hp274 : add_vec_int (mword_of_int (KernelSyms.printk + 0x272) : mword 64) 2 = mword_of_int (KernelSyms.printk + 0x274)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp274) in "Hpc".
    (* +0x274 ret *)
    assert (HE7ra : E7 !!! Regidx ra_idx = m !!! Regidx ra_idx).
    { rewrite /E7 upd_ne; [| reg_neq]. rewrite /E6 upd_ne; [| reg_neq].
      rewrite /E5 upd_ne; [| reg_neq]. rewrite /E4 upd_eq. reflexivity. }
    assert (Hrt : ret_pc (E7 !!! Regidx ra_idx) = ret_pc (m !!! Regidx ra_idx)) by (rewrite HE7ra; reflexivity).
    iApply (wp_cret_s_sconf (mword_of_int (KernelSyms.printk + 0x274)) ra_idx E7 K b
              ltac:(vm_compute; discriminate) with "Hcg Hpc Hi274 [-]").
    iIntros (CID9 Hs9) "Hcg Hpc". iEval (rewrite Hrt) in "Hpc".
    iSpecialize ("Hcont" $! CID9 with "[%]"); [wp_next_chain|].
    iApply ("Hcont" $! E7 with "Hcg Hpc [%] Hpanicking HR").
    split; [| split; [exact HE7ra | ] ].
    - destruct Hagree as (K9 & K19 & K20 & K21 & K22 & K23 & K24 & K25 & K26 & K27).
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

  Lemma wp_printk_exit `{CID0 : CpuId}
      (m mc : regfile) (K : nat) (B : Z) (pv : mword 32) (dqm : dfrac) (R : iProp Σ)
      (b : bool) (pcur : mword 64) :
    let sp0 := m !!! Regidx csp_rs1 in
    let spd := add_vec sp0 (sign_extend' 64 (caddi16sp_imm (mword_of_int 52 : mword 6))) in
    (24 <= K)%nat ->
    eq_vec (sign_extend' 64 pv) zero_reg = false ->
    mc !!! Regidx csp_rs1 = spd ->
    mc !!! Regidx (mword_of_int 25 : mword 5) = m !!! Regidx (mword_of_int 25 : mword 5) ->
    mword_of_int (KernelSyms.printk + B + 18) = (mword_of_int (KernelSyms.printk + 0x260) : mword 64) ->
    sie_cap_gpr mc (K - 24)%nat b pcur -∗
    kernel_text -∗
    pk_restore_instrs B -∗
    pc_is (mword_of_int (KernelSyms.printk + B + 0) : mword 64) -∗
    (pa_stk sp0 9) ↦₈ (m !!! Regidx ra_idx) -∗
    (pa_stk sp0 10) ↦₈ (m !!! Regidx s0_idx) -∗
    (pa_stk sp0 12) ↦₈ (m !!! Regidx s2_idx) -∗
    pk_saved sp0 (m !!! Regidx (mword_of_int 9 : mword 5)) (m !!! Regidx (mword_of_int 19 : mword 5)) (m !!! Regidx (mword_of_int 20 : mword 5)) (m !!! Regidx (mword_of_int 21 : mword 5)) (m !!! Regidx (mword_of_int 22 : mword 5)) (m !!! Regidx (mword_of_int 23 : mword 5)) (m !!! Regidx (mword_of_int 24 : mword 5)) (m !!! Regidx (mword_of_int 26 : mword 5)) (m !!! Regidx (mword_of_int 27 : mword 5)) -∗
    pk_slots_rest sp0 -∗
    (mword_of_int KernelSyms.panicking : mword 64) ↦₄{ dqm } pv -∗
    R -∗
    wp_next (CID0 := CID0) b pcur (fun (CID : CpuId) =>
      ∀ mf,
      sie_cap_gpr mf K b pcur -∗
      pc_is (ret_pc (m !!! Regidx ra_idx)) -∗
      ⌜ callee_saved m mf /\ mf !!! Regidx ra_idx = m !!! Regidx ra_idx
        /\ mf !!! Regidx a0_idx = zero_reg ⌝ -∗
      (mword_of_int KernelSyms.panicking : mword 64) ↦₄{ dqm } pv -∗
      R -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros sp0 spd HK Hpv Hsp Hs9 Hnext.
    iIntros "Hcg #Htext Hinstrs Hpc H9 H10 H12 Hsv Hrest Hpanicking HR Hcont".
    iApply (wp_printk_restore mc K B sp0 (m !!! Regidx (mword_of_int 9 : mword 5)) (m !!! Regidx (mword_of_int 19 : mword 5)) (m !!! Regidx (mword_of_int 20 : mword 5)) (m !!! Regidx (mword_of_int 21 : mword 5)) (m !!! Regidx (mword_of_int 22 : mword 5)) (m !!! Regidx (mword_of_int 23 : mword 5)) (m !!! Regidx (mword_of_int 24 : mword 5)) (m !!! Regidx (mword_of_int 26 : mword 5)) (m !!! Regidx (mword_of_int 27 : mword 5)) b pcur Hsp
              with "Hcg Hinstrs Hpc Hsv [-]").
    iIntros (CIDr Hsr mf) "%Hpost Hcg Hpc Hsv".
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
    (* the register the block does NOT restore (s9) comes from the caller;
       the other nine are its own posts (tp is canonical -- HartTp.v -- and
       no longer tracked here).  [Hkp] is applied at an EXPLICIT index --
       with [_] the inline [mw_neq] would run against an evar. *)
    assert (Hcsk : pk_cs_kept m mf).
    { unfold pk_cs_kept. repeat split.
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
    assert (Hshift : b = false \/ pcur = zero_reg -> (CIDr : CPU) = (CID0 : CPU)) by wp_next_chain.
    iDestruct (wp_next_shift Hshift with "Hcont") as "Hcont".
    iApply (wp_printk_epi (CID0 := CIDr) m mf K pv pv dqm dqm R b pcur HK Hpv Hmfsp Hcsk
              with "Hcg Htext Hpc Hfr Hpanicking HR Hcont").
  Qed.

  (* The SECOND restore block (0x276), the [c0 = 0] dispatch exit.  Unlike the
     one at 0x24e it does not fall into the epilogue: a [c.j] at 0x288 jumps
     back to 0x260.  One extra instruction, same tail. *)
  Lemma wp_printk_exit276 `{CID0 : CpuId}
      (m mc : regfile) (K : nat) (pv : mword 32) (dqm : dfrac) (R : iProp Σ)
      (b : bool) (pcur : mword 64) :
    let sp0 := m !!! Regidx csp_rs1 in
    let spd := add_vec sp0 (sign_extend' 64 (caddi16sp_imm (mword_of_int 52 : mword 6))) in
    (24 <= K)%nat ->
    eq_vec (sign_extend' 64 pv) zero_reg = false ->
    mc !!! Regidx csp_rs1 = spd ->
    mc !!! Regidx (mword_of_int 25 : mword 5) = m !!! Regidx (mword_of_int 25 : mword 5) ->
    sie_cap_gpr mc (K - 24)%nat b pcur -∗
    kernel_text -∗
    pc_is (mword_of_int (KernelSyms.printk + 0x276) : mword 64) -∗
    (pa_stk sp0 9) ↦₈ (m !!! Regidx ra_idx) -∗
    (pa_stk sp0 10) ↦₈ (m !!! Regidx s0_idx) -∗
    (pa_stk sp0 12) ↦₈ (m !!! Regidx s2_idx) -∗
    pk_saved sp0 (m !!! Regidx (mword_of_int 9 : mword 5)) (m !!! Regidx (mword_of_int 19 : mword 5)) (m !!! Regidx (mword_of_int 20 : mword 5)) (m !!! Regidx (mword_of_int 21 : mword 5)) (m !!! Regidx (mword_of_int 22 : mword 5)) (m !!! Regidx (mword_of_int 23 : mword 5)) (m !!! Regidx (mword_of_int 24 : mword 5)) (m !!! Regidx (mword_of_int 26 : mword 5)) (m !!! Regidx (mword_of_int 27 : mword 5)) -∗
    pk_slots_rest sp0 -∗
    (mword_of_int KernelSyms.panicking : mword 64) ↦₄{ dqm } pv -∗
    R -∗
    wp_next (CID0 := CID0) b pcur (fun (CID : CpuId) =>
      ∀ mf,
      sie_cap_gpr mf K b pcur -∗
      pc_is (ret_pc (m !!! Regidx ra_idx)) -∗
      ⌜ callee_saved m mf /\ mf !!! Regidx ra_idx = m !!! Regidx ra_idx
        /\ mf !!! Regidx a0_idx = zero_reg ⌝ -∗
      (mword_of_int KernelSyms.panicking : mword 64) ↦₄{ dqm } pv -∗
      R -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros sp0 spd HK Hpv Hsp Hs9.
    iIntros "Hcg #Htext Hpc H9 H10 H12 Hsv Hrest Hpanicking HR Hcont".
    iPoseProof (pk_restore_at_276 with "Htext") as "Hinstrs".
    iPoseProof (pki_288 with "Htext") as "Hi288".
    iApply (wp_printk_restore mc K 0x276 sp0 (m !!! Regidx (mword_of_int 9 : mword 5)) (m !!! Regidx (mword_of_int 19 : mword 5)) (m !!! Regidx (mword_of_int 20 : mword 5)) (m !!! Regidx (mword_of_int 21 : mword 5)) (m !!! Regidx (mword_of_int 22 : mword 5)) (m !!! Regidx (mword_of_int 23 : mword 5)) (m !!! Regidx (mword_of_int 24 : mword 5)) (m !!! Regidx (mword_of_int 26 : mword 5)) (m !!! Regidx (mword_of_int 27 : mword 5)) b pcur Hsp
              with "Hcg Hinstrs Hpc Hsv [-]").
    iIntros (CIDr Hsr mf) "%Hpost Hcg Hpc Hsv".
    destruct Hpost as (Hkeep & E9 & E19 & E20 & E21 & E22 & E23 & E24 & E26 & E27).
    assert (Hp288 : mword_of_int (KernelSyms.printk + 0x276 + 18) = (mword_of_int (KernelSyms.printk + 0x288) : mword 64))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp288) in "Hpc".
    (* +0x288 c.j 0x260 *)
    iApply (wp_cj_s_sconf (mword_of_int (KernelSyms.printk + 0x288))
              (sign_extend' 21 (concat_vec (mword_of_int 2028 : mword 11) ('b"0")))
              mf (K - 24)%nat b ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi288 [-]").
    iIntros (CIDj Hsj). iNext. iIntros "Hcg Hpc".
    assert (Htgt : add_vec (mword_of_int (KernelSyms.printk + 0x288) : mword 64) (sign_extend' 64 (sign_extend' 21 (concat_vec (mword_of_int 2028 : mword 11) ('b"0")))) = mword_of_int (KernelSyms.printk + 0x260)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgt) in "Hpc".
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
    assert (Hcsk : pk_cs_kept m mf).
    { unfold pk_cs_kept. repeat split.
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
    assert (Hshift : b = false \/ pcur = zero_reg -> (CIDj : CPU) = (CID0 : CPU)) by wp_next_chain.
    iDestruct (wp_next_shift Hshift with "Hcont") as "Hcont".
    iApply (wp_printk_epi (CID0 := CIDj) m mf K pv pv dqm dqm R b pcur HK Hpv Hmfsp Hcsk
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

  Lemma wp_printk_setup `{CID0 : CpuId}
      (m mp : regfile) (K : nat) (pv : mword 32) (dqm dqf : dfrac)
      (f : string) (R : iProp Σ) (b : bool) (pcur : mword 64) :
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
    sie_cap_gpr mp (K - 24)%nat b pcur -∗
    kernel_text -∗
    pc_is (mword_of_int (KernelSyms.printk + 0x1e) : mword 64) -∗
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
       already in [pk_frame] shape and the epilogue can run at once.  The
       [beqz] at 0x34 was TAKEN, so the first byte is the terminator -- stated
       so the caller can decide which of the two continuations is live. *)
    wp_next (CID0 := CID0) b pcur (fun (CID : CpuId) =>
      ∀ mf,
      sie_cap_gpr mf K b pcur -∗
      pc_is (ret_pc (m !!! Regidx ra_idx)) -∗
      ⌜ pk_fbyte f 0%nat = (mword_of_int 0 : mword 8) ⌝ -∗
      ⌜ callee_saved m mf /\ mf !!! Regidx ra_idx = m !!! Regidx ra_idx
        /\ mf !!! Regidx a0_idx = zero_reg ⌝ -∗
      (mword_of_int KernelSyms.panicking : mword 64) ↦₄{ dqm } pv -∗
      fmt ↦ₛ{ dqf } f -∗ R -∗
      WP (Loop : expr riscv_lang)) -∗
    (* (b) a nonempty one: the loop head, with i = 0 and a0 = fmt[0] *)
    wp_next (CID0 := CID0) b pcur (fun (CID : CpuId) =>
      ∀ (mq : regfile),
      ⌜ mq !!! Regidx csp_rs1 = spd
        /\ mq !!! Regidx s0_idx = s0v
        /\ mq !!! Regidx s2_idx = fmt
        /\ mq !!! Regidx (mword_of_int 20 : mword 5) = zero_reg
        /\ mq !!! Regidx a0_idx = zero_extend' 64 (pk_fbyte f 0%nat)
        (* the [beqz] at 0x34 fell through, so the first byte is a real
           character -- which is what lets the loop start with i < |f| *)
        /\ pk_fbyte f 0%nat <> (mword_of_int 0 : mword 8)
        /\ pk_consts mq
        /\ (forall c : mword 5, c <> csp_rs1 -> c <> s0_idx -> c <> s2_idx ->
              c <> mword_of_int 15 -> c <> a0_idx -> c <> mword_of_int 19 ->
              c <> mword_of_int 20 -> c <> mword_of_int 22 -> c <> mword_of_int 23 ->
              c <> mword_of_int 24 -> c <> mword_of_int 26 -> c <> mword_of_int 27 ->
              mq !!! Regidx c = m !!! Regidx c) ⌝ -∗
      sie_cap_gpr mq (K - 24)%nat b pcur -∗
      pc_is (mword_of_int (KernelSyms.printk + 0x86) : mword 64) -∗
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
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
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
    iApply (wp_auipc_s_sconf (mword_of_int (KernelSyms.printk + 0x1e)) a5_idx (mword_of_int 10 : mword 20)
              mp (K - 24)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi1e [-]").
    iIntros (CID1 Hst1) "Hcg Hpc".
    set (Q1 := <[Regidx a5_idx := regval_into_reg (add_vec (mword_of_int (KernelSyms.printk + 0x1e) : mword 64) (auipc_off (mword_of_int 10 : mword 20)))]> mp).
    assert (Hpan : add_vec (rget Q1 a5_idx) (sign_extend' 64 (mword_of_int 3436 : mword 12))
                   = (mword_of_int KernelSyms.panicking : mword 64)).
    { rgne. rewrite /Q1 upd_eq. unfold regval_into_reg. apply bv_eq; vm_compute; reflexivity. }
    assert (Hp22 : add_vec_int (mword_of_int (KernelSyms.printk + 0x1e) : mword 64) 4 = mword_of_int (KernelSyms.printk + 0x22)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp22) in "Hpc".
    iEval (rewrite -Hpan) in "Hpanicking".
    iApply (wp_lw_s_sconf (mword_of_int (KernelSyms.printk + 0x22)) a5_idx a5_idx (mword_of_int 3436 : mword 12)
              Q1 (K - 24)%nat pv b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi22 Hpanicking [-]").
    iIntros (CID2 Hst2) "Hcg Hpc Hpanicking". iEval (rewrite Hpan) in "Hpanicking".
    set (Q2 := <[Regidx a5_idx := regval_into_reg (sign_extend' 64 pv)]> Q1).
    assert (Hp26 : add_vec_int (mword_of_int (KernelSyms.printk + 0x22) : mword 64) 4 = mword_of_int (KernelSyms.printk + 0x26)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp26) in "Hpc".
    (* +0x26 beqz a5 : NOT taken -- the panic path takes no lock *)
    iApply (wp_cbeqz_fall_s_sconf (mword_of_int (KernelSyms.printk + 0x26)) (mword_of_int 31 : mword 8)
              (Cregidx (mword_of_int 7)) a5_idx Q2 (K - 24)%nat b
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
              ltac:(rgne; rewrite /Q2 upd_eq; exact Hpv)
              with "Hcg Hpc Hi26 [-]").
    iIntros (CID3 Hst3) "Hcg Hpc".
    assert (Hp28 : add_vec_int (mword_of_int (KernelSyms.printk + 0x26) : mword 64) 2 = mword_of_int (KernelSyms.printk + 0x28)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp28) in "Hpc".
    (* +0x28 addi a5,s0,8 : the va_list cursor *)
    assert (HQ2s0 : Q2 !!! Regidx s0_idx = s0v).
    { rewrite /Q2 upd_ne; [| reg_neq]. rewrite /Q1 upd_ne; [exact Hs0 | reg_neq]. }
    iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.printk + 0x28)) a5_idx s0_idx (mword_of_int 8 : mword 12)
              Q2 (K - 24)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi28 [-]").
    iIntros (CID4 Hst4) "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (Q3 := <[Regidx a5_idx := regval_into_reg (add_vec (Q2 !!! Regidx s0_idx) (sign_extend' 64 (mword_of_int 8 : mword 12)))]> Q2).
    assert (HQ3a5 : Q3 !!! Regidx a5_idx = add_vec s0v (sign_extend' 64 (mword_of_int 8 : mword 12)))
      by (rewrite /Q3 upd_eq; unfold regval_into_reg; rewrite HQ2s0; reflexivity).
    assert (HQ3s0 : Q3 !!! Regidx s0_idx = s0v) by (rewrite /Q3 upd_ne; [exact HQ2s0 | reg_neq]).
    assert (Hp2c : add_vec_int (mword_of_int (KernelSyms.printk + 0x28) : mword 64) 4 = mword_of_int (KernelSyms.printk + 0x2c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp2c) in "Hpc".
    (* +0x2c sd a5,-120(s0) : ap -> slot 23 *)
    assert (Hap23 : add_vec (rget Q3 s0_idx) (sign_extend' 64 (mword_of_int 3976 : mword 12)) = pa_stk sp0 23).
    { rgne. rewrite HQ3s0. unfold s0v, pa_stk, add_vec_int. rewrite pa_stk_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    iApply (wp_sd_s_sconf (mword_of_int (KernelSyms.printk + 0x2c)) a5_idx s0_idx (mword_of_int 3976 : mword 12)
              Q3 (K - 24)%nat w23 b with "Hcg Hpc Hi2c [Hap] [-]").
    { iEval (rewrite Hap23). iExact "Hap". }
    iIntros (CID5 Hst5) "Hcg Hpc Hap". iEval (rewrite Hap23) in "Hap". iEval (rgne) in "Hap". iEval (rewrite HQ3a5) in "Hap".
    assert (Hp30 : add_vec_int (mword_of_int (KernelSyms.printk + 0x2c) : mword 64) 4 = mword_of_int (KernelSyms.printk + 0x30)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp30) in "Hpc".
    (* +0x30 lbu a0,0(s2) : the first format byte *)
    assert (HQ3s2 : Q3 !!! Regidx s2_idx = fmt).
    { rewrite /Q3 upd_ne; [| reg_neq]. rewrite /Q2 upd_ne; [| reg_neq].
      rewrite /Q1 upd_ne; [exact Hs2 | reg_neq]. }
    assert (Hlen0 : (0 < length (cstring_bytes f))%nat).
    { rewrite cstring_bytes_length. lia. }
    iDestruct (pk_str_byte fmt dqf f 0%nat Hlen0 with "Hfmt") as "[Hb0 Hfcl]".
    assert (Hb0a : add_vec (rget Q3 s2_idx) (sign_extend' 64 (mword_of_int 0 : mword 12)) = pa_add fmt 0).
    { rgne. rewrite HQ3s2 pa_add_0.
      replace (sign_extend' 64 (mword_of_int 0 : mword 12)) with (mword_of_int 0 : mword 64)
        by (apply bv_eq; vm_compute; reflexivity).
      apply kv_addv_zero. }
    iApply (wp_lbu_s_sconf (mword_of_int (KernelSyms.printk + 0x30)) a0_idx s2_idx (mword_of_int 0 : mword 12)
              Q3 (K - 24)%nat (pk_fbyte f 0%nat) b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi30 [Hb0] [-]").
    { iEval (rewrite Hb0a). iExact "Hb0". }
    iIntros (CID6 Hst6) "Hcg Hpc Hb0". iEval (rewrite Hb0a) in "Hb0".
    iDestruct ("Hfcl" with "Hb0") as "Hfmt".
    set (Q4 := <[Regidx a0_idx := regval_into_reg (zero_extend' 64 (pk_fbyte f 0%nat))]> Q3).
    assert (Hp34 : add_vec_int (mword_of_int (KernelSyms.printk + 0x30) : mword 64) 4 = mword_of_int (KernelSyms.printk + 0x34)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp34) in "Hpc".
    (* +0x34 beqz a0 : the empty format string leaves at once *)
    destruct (eq_vec (Q4 !!! Regidx a0_idx) zero_reg) eqn:Hz.
    - (* ---- f = "" : straight to the epilogue ---- *)
      iApply (wp_beqz_x0_taken_s_sconf (mword_of_int (KernelSyms.printk + 0x34)) (mword_of_int 556 : mword 13)
                a0_idx Q4 (K - 24)%nat b ltac:(vm_compute; discriminate) Hz
                ltac:(vm_compute; reflexivity)
                with "Hcg Hpc Hi34 [-]").
      iIntros (CID7 Hst7). iNext. iIntros "Hcg Hpc".
      assert (Htgte : add_vec (mword_of_int (KernelSyms.printk + 0x34) : mword 64) (sign_extend' 64 (mword_of_int 556 : mword 13)) = mword_of_int (KernelSyms.printk + 0x260)) by (apply bv_eq; vm_compute; reflexivity).
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
      iApply (wp_printk_epi (CID0 := CID7) m Q4 K pv pv dqm dqm (fmt ↦ₛ{ dqf } f ∗ R)%I b pcur HK Hpv HQ4sp HQ4cs
                with "Hcg Htext Hpc Hfr Hpanicking [Hfmt HR] [-]").
      { iFrame "Hfmt HR". }
      iIntros (CIDe Hse mf) "Hcg Hpc %Hfin Hpanicking [Hfmt HR]".
      iSpecialize ("Kend" $! CIDe with "[%]"); [wp_next_chain|].
      iApply ("Kend" $! mf with "Hcg Hpc [%] [%] Hpanicking Hfmt HR").
      { assert (HQ4a0 : Q4 !!! Regidx a0_idx = zero_extend' 64 (pk_fbyte f 0%nat))
          by (rewrite /Q4 upd_eq; reflexivity).
        rewrite HQ4a0 in Hz. exact (zext8_zero _ Hz). }
      exact Hfin.
    - (* ---- f nonempty : the lazy saves, the constants, and into the loop ---- *)
      iApply (wp_beqz_x0_fall_s_sconf (mword_of_int (KernelSyms.printk + 0x34)) (mword_of_int 556 : mword 13)
                a0_idx Q4 (K - 24)%nat b ltac:(vm_compute; discriminate) Hz
                with "Hcg Hpc Hi34 [-]").
      iIntros (CID7b Hst7b) "Hcg Hpc".
      assert (Hp38 : add_vec_int (mword_of_int (KernelSyms.printk + 0x34) : mword 64) 4 = mword_of_int (KernelSyms.printk + 0x38)) by (apply bv_eq; vm_compute; reflexivity).
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
      iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.printk + 0x38)) (mword_of_int 13 : mword 6) (mword_of_int 9 : mword 5)
                Q4 (K - 24)%nat w11 b with "Hcg Hpc Hi38 [S9] [-]").
      { iEval (rewrite HQ4sp Hbs11). iExact "S9". }
      iIntros (CID7 Hst7) "Hcg Hpc S9". iEval (rewrite HQ4sp Hbs11) in "S9".
      iEval (rgne) in "S9".
      iEval (rewrite (HQ4k (mword_of_int 9 : mword 5) ltac:(mw_neq) ltac:(mw_neq) ltac:(mw_neq) ltac:(mw_neq) ltac:(mw_neq))) in "S9".
      assert (Hp3a : add_vec_int (mword_of_int (KernelSyms.printk + 0x38) : mword 64) 2 = mword_of_int (KernelSyms.printk + 0x3a)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hp3a) in "Hpc".
      (* +0x3a sd x19,88(sp) -> slot 13 *)
      iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.printk + 0x3a)) (mword_of_int 11 : mword 6) (mword_of_int 19 : mword 5)
                Q4 (K - 24)%nat w13 b with "Hcg Hpc Hi3a [S19] [-]").
      { iEval (rewrite HQ4sp Hbs13). iExact "S19". }
      iIntros (CID8 Hst8) "Hcg Hpc S19". iEval (rewrite HQ4sp Hbs13) in "S19".
      iEval (rgne) in "S19".
      iEval (rewrite (HQ4k (mword_of_int 19 : mword 5) ltac:(mw_neq) ltac:(mw_neq) ltac:(mw_neq) ltac:(mw_neq) ltac:(mw_neq))) in "S19".
      assert (Hp3c : add_vec_int (mword_of_int (KernelSyms.printk + 0x3a) : mword 64) 2 = mword_of_int (KernelSyms.printk + 0x3c)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hp3c) in "Hpc".
      (* +0x3c sd x20,80(sp) -> slot 14 *)
      iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.printk + 0x3c)) (mword_of_int 10 : mword 6) (mword_of_int 20 : mword 5)
                Q4 (K - 24)%nat w14 b with "Hcg Hpc Hi3c [S20] [-]").
      { iEval (rewrite HQ4sp Hbs14). iExact "S20". }
      iIntros (CID9 Hst9) "Hcg Hpc S20". iEval (rewrite HQ4sp Hbs14) in "S20".
      iEval (rgne) in "S20".
      iEval (rewrite (HQ4k (mword_of_int 20 : mword 5) ltac:(mw_neq) ltac:(mw_neq) ltac:(mw_neq) ltac:(mw_neq) ltac:(mw_neq))) in "S20".
      assert (Hp3e : add_vec_int (mword_of_int (KernelSyms.printk + 0x3c) : mword 64) 2 = mword_of_int (KernelSyms.printk + 0x3e)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hp3e) in "Hpc".
      (* +0x3e sd x21,72(sp) -> slot 15 *)
      iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.printk + 0x3e)) (mword_of_int 9 : mword 6) (mword_of_int 21 : mword 5)
                Q4 (K - 24)%nat w15 b with "Hcg Hpc Hi3e [S21] [-]").
      { iEval (rewrite HQ4sp Hbs15). iExact "S21". }
      iIntros (CID10 Hst10) "Hcg Hpc S21". iEval (rewrite HQ4sp Hbs15) in "S21".
      iEval (rgne) in "S21".
      iEval (rewrite (HQ4k (mword_of_int 21 : mword 5) ltac:(mw_neq) ltac:(mw_neq) ltac:(mw_neq) ltac:(mw_neq) ltac:(mw_neq))) in "S21".
      assert (Hp40 : add_vec_int (mword_of_int (KernelSyms.printk + 0x3e) : mword 64) 2 = mword_of_int (KernelSyms.printk + 0x40)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hp40) in "Hpc".
      (* +0x40 sd x22,64(sp) -> slot 16 *)
      iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.printk + 0x40)) (mword_of_int 8 : mword 6) (mword_of_int 22 : mword 5)
                Q4 (K - 24)%nat w16 b with "Hcg Hpc Hi40 [S22] [-]").
      { iEval (rewrite HQ4sp Hbs16). iExact "S22". }
      iIntros (CID11 Hst11) "Hcg Hpc S22". iEval (rewrite HQ4sp Hbs16) in "S22".
      iEval (rgne) in "S22".
      iEval (rewrite (HQ4k (mword_of_int 22 : mword 5) ltac:(mw_neq) ltac:(mw_neq) ltac:(mw_neq) ltac:(mw_neq) ltac:(mw_neq))) in "S22".
      assert (Hp42 : add_vec_int (mword_of_int (KernelSyms.printk + 0x40) : mword 64) 2 = mword_of_int (KernelSyms.printk + 0x42)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hp42) in "Hpc".
      (* +0x42 sd x23,56(sp) -> slot 17 *)
      iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.printk + 0x42)) (mword_of_int 7 : mword 6) (mword_of_int 23 : mword 5)
                Q4 (K - 24)%nat w17 b with "Hcg Hpc Hi42 [S23] [-]").
      { iEval (rewrite HQ4sp Hbs17). iExact "S23". }
      iIntros (CID12 Hst12) "Hcg Hpc S23". iEval (rewrite HQ4sp Hbs17) in "S23".
      iEval (rgne) in "S23".
      iEval (rewrite (HQ4k (mword_of_int 23 : mword 5) ltac:(mw_neq) ltac:(mw_neq) ltac:(mw_neq) ltac:(mw_neq) ltac:(mw_neq))) in "S23".
      assert (Hp44 : add_vec_int (mword_of_int (KernelSyms.printk + 0x42) : mword 64) 2 = mword_of_int (KernelSyms.printk + 0x44)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hp44) in "Hpc".
      (* +0x44 sd x24,48(sp) -> slot 18 *)
      iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.printk + 0x44)) (mword_of_int 6 : mword 6) (mword_of_int 24 : mword 5)
                Q4 (K - 24)%nat w18 b with "Hcg Hpc Hi44 [S24] [-]").
      { iEval (rewrite HQ4sp Hbs18). iExact "S24". }
      iIntros (CID13 Hst13) "Hcg Hpc S24". iEval (rewrite HQ4sp Hbs18) in "S24".
      iEval (rgne) in "S24".
      iEval (rewrite (HQ4k (mword_of_int 24 : mword 5) ltac:(mw_neq) ltac:(mw_neq) ltac:(mw_neq) ltac:(mw_neq) ltac:(mw_neq))) in "S24".
      assert (Hp46 : add_vec_int (mword_of_int (KernelSyms.printk + 0x44) : mword 64) 2 = mword_of_int (KernelSyms.printk + 0x46)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hp46) in "Hpc".
      (* +0x46 sd x26,32(sp) -> slot 20 *)
      iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.printk + 0x46)) (mword_of_int 4 : mword 6) (mword_of_int 26 : mword 5)
                Q4 (K - 24)%nat w20 b with "Hcg Hpc Hi46 [S26] [-]").
      { iEval (rewrite HQ4sp Hbs20). iExact "S26". }
      iIntros (CID14 Hst14) "Hcg Hpc S26". iEval (rewrite HQ4sp Hbs20) in "S26".
      iEval (rgne) in "S26".
      iEval (rewrite (HQ4k (mword_of_int 26 : mword 5) ltac:(mw_neq) ltac:(mw_neq) ltac:(mw_neq) ltac:(mw_neq) ltac:(mw_neq))) in "S26".
      assert (Hp48 : add_vec_int (mword_of_int (KernelSyms.printk + 0x46) : mword 64) 2 = mword_of_int (KernelSyms.printk + 0x48)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hp48) in "Hpc".
      (* +0x48 sd x27,24(sp) -> slot 21 *)
      iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.printk + 0x48)) (mword_of_int 3 : mword 6) (mword_of_int 27 : mword 5)
                Q4 (K - 24)%nat w21 b with "Hcg Hpc Hi48 [S27] [-]").
      { iEval (rewrite HQ4sp Hbs21). iExact "S27". }
      iIntros (CID15 Hst15) "Hcg Hpc S27". iEval (rewrite HQ4sp Hbs21) in "S27".
      iEval (rgne) in "S27".
      iEval (rewrite (HQ4k (mword_of_int 27 : mword 5) ltac:(mw_neq) ltac:(mw_neq) ltac:(mw_neq) ltac:(mw_neq) ltac:(mw_neq))) in "S27".
      assert (Hp4a : add_vec_int (mword_of_int (KernelSyms.printk + 0x48) : mword 64) 2 = mword_of_int (KernelSyms.printk + 0x4a)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hp4a) in "Hpc".
      iApply (wp_cli_s_sconf (mword_of_int (KernelSyms.printk + 0x4a)) (mword_of_int 20 : mword 5) (mword_of_int 0 : mword 6)
                (mword_of_int 0 : mword 64) Q4 (K - 24)%nat b
                ltac:(vm_compute; discriminate) ltac:(rdok)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                with "Hcg Hpc Hi4a [-]").
      iIntros (CID22 Hst22) "Hcg Hpc".
      set (C0 := <[Regidx (mword_of_int 20 : mword 5) := regval_into_reg (mword_of_int 0 : mword 64)]> Q4).
      assert (Hp4c : add_vec_int (mword_of_int (KernelSyms.printk + 0x4a) : mword 64) 2 = mword_of_int (KernelSyms.printk + 0x4c)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hp4c) in "Hpc".
      iApply (wp_li4_s_sconf (mword_of_int (KernelSyms.printk + 0x4c)) (mword_of_int 19 : mword 5) (mword_of_int 37 : mword 12)
                (mword_of_int 37 : mword 64) C0 (K - 24)%nat b
                ltac:(vm_compute; discriminate) ltac:(rdok)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                with "Hcg Hpc Hi4c [-]").
      iIntros (CID16 Hst16) "Hcg Hpc".
      set (C1 := <[Regidx (mword_of_int 19 : mword 5) := regval_into_reg (mword_of_int 37 : mword 64)]> C0).
      assert (Hp50 : add_vec_int (mword_of_int (KernelSyms.printk + 0x4c) : mword 64) 4 = mword_of_int (KernelSyms.printk + 0x50)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hp50) in "Hpc".
      iApply (wp_li4_s_sconf (mword_of_int (KernelSyms.printk + 0x50)) (mword_of_int 24 : mword 5) (mword_of_int 117 : mword 12)
                (mword_of_int 117 : mword 64) C1 (K - 24)%nat b
                ltac:(vm_compute; discriminate) ltac:(rdok)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                with "Hcg Hpc Hi50 [-]").
      iIntros (CID17 Hst17) "Hcg Hpc".
      set (C2 := <[Regidx (mword_of_int 24 : mword 5) := regval_into_reg (mword_of_int 117 : mword 64)]> C1).
      assert (Hp54 : add_vec_int (mword_of_int (KernelSyms.printk + 0x50) : mword 64) 4 = mword_of_int (KernelSyms.printk + 0x54)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hp54) in "Hpc".
      iApply (wp_li4_s_sconf (mword_of_int (KernelSyms.printk + 0x54)) (mword_of_int 26 : mword 5) (mword_of_int 120 : mword 12)
                (mword_of_int 120 : mword 64) C2 (K - 24)%nat b
                ltac:(vm_compute; discriminate) ltac:(rdok)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                with "Hcg Hpc Hi54 [-]").
      iIntros (CID18 Hst18) "Hcg Hpc".
      set (C3 := <[Regidx (mword_of_int 26 : mword 5) := regval_into_reg (mword_of_int 120 : mword 64)]> C2).
      assert (Hp58 : add_vec_int (mword_of_int (KernelSyms.printk + 0x54) : mword 64) 4 = mword_of_int (KernelSyms.printk + 0x58)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hp58) in "Hpc".
      iApply (wp_li4_s_sconf (mword_of_int (KernelSyms.printk + 0x58)) (mword_of_int 27 : mword 5) (mword_of_int 112 : mword 12)
                (mword_of_int 112 : mword 64) C3 (K - 24)%nat b
                ltac:(vm_compute; discriminate) ltac:(rdok)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                with "Hcg Hpc Hi58 [-]").
      iIntros (CID19 Hst19) "Hcg Hpc".
      set (C4 := <[Regidx (mword_of_int 27 : mword 5) := regval_into_reg (mword_of_int 112 : mword 64)]> C3).
      assert (Hp5c : add_vec_int (mword_of_int (KernelSyms.printk + 0x58) : mword 64) 4 = mword_of_int (KernelSyms.printk + 0x5c)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hp5c) in "Hpc".
      iApply (wp_cli_s_sconf (mword_of_int (KernelSyms.printk + 0x5c)) (mword_of_int 22 : mword 5) (mword_of_int 10 : mword 6)
                (mword_of_int 10 : mword 64) C4 (K - 24)%nat b
                ltac:(vm_compute; discriminate) ltac:(rdok)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                with "Hcg Hpc Hi5c [-]").
      iIntros (CID20 Hst20) "Hcg Hpc".
      set (C5 := <[Regidx (mword_of_int 22 : mword 5) := regval_into_reg (mword_of_int 10 : mword 64)]> C4).
      assert (Hp5e : add_vec_int (mword_of_int (KernelSyms.printk + 0x5c) : mword 64) 2 = mword_of_int (KernelSyms.printk + 0x5e)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hp5e) in "Hpc".
      iApply (wp_li4_s_sconf (mword_of_int (KernelSyms.printk + 0x5e)) (mword_of_int 23 : mword 5) (mword_of_int 100 : mword 12)
                (mword_of_int 100 : mword 64) C5 (K - 24)%nat b
                ltac:(vm_compute; discriminate) ltac:(rdok)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                with "Hcg Hpc Hi5e [-]").
      iIntros (CID21 Hst21) "Hcg Hpc".
      set (C6 := <[Regidx (mword_of_int 23 : mword 5) := regval_into_reg (mword_of_int 100 : mword 64)]> C5).
      assert (Hp62 : add_vec_int (mword_of_int (KernelSyms.printk + 0x5e) : mword 64) 4 = mword_of_int (KernelSyms.printk + 0x62)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hp62) in "Hpc".
      (* +0x62 j 0x86 : into the loop *)
      iApply (wp_cj_s_sconf (mword_of_int (KernelSyms.printk + 0x62)) (sign_extend' 21 (concat_vec (mword_of_int 18 : mword 11) ('b"0")))
                C6 (K - 24)%nat b ltac:(vm_compute; reflexivity)
                with "Hcg Hpc Hi62 [-]").
      iIntros (CID23 Hst23). iNext. iIntros "Hcg Hpc".
      assert (Htgtl : add_vec (mword_of_int (KernelSyms.printk + 0x62) : mword 64) (sign_extend' 64 (sign_extend' 21 (concat_vec (mword_of_int 18 : mword 11) ('b"0")))) = mword_of_int (KernelSyms.printk + 0x86)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Htgtl) in "Hpc".
      iSpecialize ("Kloop" $! CID23 with "[%]"); [wp_next_chain|].
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
        { intro Hc.
          assert (HQ4a0 : Q4 !!! Regidx a0_idx = zero_extend' 64 (pk_fbyte f 0%nat))
            by (rewrite /Q4 upd_eq; reflexivity).
          rewrite HQ4a0 Hc in Hz.
          assert (Hz0 : eq_vec (zero_extend' 64 (mword_of_int 0 : mword 8)) (zero_reg : mword 64) = true)
            by (vm_compute; reflexivity).
          rewrite Hz0 in Hz. discriminate. }
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

  Lemma wp_printk_advance `{CID0 : CpuId}
      (mc : regfile) (K : nat) (fmt : mword 64) (dqf : dfrac) (f : string) (p : nat)
      (Rest : iProp Σ) (b : bool) (pcur : mword 64) :
    (S p < length (cstring_bytes f))%nat ->
    (Z.of_nat p + 1 < 2^31) ->
    mc !!! Regidx (mword_of_int 9 : mword 5) = mword_of_int (Z.of_nat p) ->
    mc !!! Regidx s2_idx = fmt ->
    sie_cap_gpr mc (K - 24)%nat b pcur -∗
    kernel_text -∗
    pc_is (mword_of_int (KernelSyms.printk + 0x78) : mword 64) -∗
    fmt ↦ₛ{ dqf } f -∗
    Rest -∗
    (* the string ended: leave through the restore block at 0x24e *)
    wp_next (CID0 := CID0) b pcur (fun (CID : CpuId) =>
      ∀ mf : regfile,
      ⌜ pk_adv_kept mf mc /\ pk_fbyte f (S p) = (mword_of_int 0 : mword 8) ⌝ -∗
      sie_cap_gpr mf (K - 24)%nat b pcur -∗
      pc_is (mword_of_int (KernelSyms.printk + 0x24e) : mword 64) -∗
      fmt ↦ₛ{ dqf } f -∗ Rest -∗
      WP (Loop : expr riscv_lang)) -∗
    (* another character: the loop test at 0x86 *)
    wp_next (CID0 := CID0) b pcur (fun (CID : CpuId) =>
      ∀ mf : regfile,
      ⌜ pk_adv_kept mf mc
        /\ mf !!! Regidx (mword_of_int 20 : mword 5) = mword_of_int (Z.of_nat (S p))
        /\ mf !!! Regidx a0_idx = zero_extend' 64 (pk_fbyte f (S p))
        /\ pk_fbyte f (S p) <> (mword_of_int 0 : mword 8) ⌝ -∗
      sie_cap_gpr mf (K - 24)%nat b pcur -∗
      pc_is (mword_of_int (KernelSyms.printk + 0x86) : mword 64) -∗
      fmt ↦ₛ{ dqf } f -∗ Rest -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hlen Hp31 Hs1 Hs2.
    iIntros "Hcg #Htext Hpc Hfmt HR Kend Kgo".
    iPoseProof (pki_78 with "Htext") as "Hi78".
    iPoseProof (pki_7a with "Htext") as "Hi7a".
    iPoseProof (pki_7c with "Htext") as "Hi7c".
    iPoseProof (pki_7e with "Htext") as "Hi7e".
    iPoseProof (pki_82 with "Htext") as "Hi82".
    (* +0x78 c.addiw s1,s1,1 *)
    iApply (wp_caddiw_s_sconf (mword_of_int (KernelSyms.printk + 0x78)) (mword_of_int 9 : mword 5) (mword_of_int 1 : mword 6)
              mc (K - 24)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi78 [-]").
    iIntros (CID1 Hst1) "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (A1 := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg (sign_extend' 64 (subrange_vec_dec
                 (add_vec (mc !!! Regidx (mword_of_int 9 : mword 5)) (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6)))) 31 0))]> mc).
    assert (HA1s1 : A1 !!! Regidx (mword_of_int 9 : mword 5) = mword_of_int (Z.of_nat (S p))).
    { rewrite /A1 upd_eq. unfold regval_into_reg. rewrite Hs1.
      rewrite (addiw_lit (Z.of_nat p) 1 (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6)))
                 ltac:(apply bv_eq; vm_compute; reflexivity)
                 ltac:(change (2^31) with 2147483648; lia)).
      f_equal. lia. }
    assert (HA1s2 : A1 !!! Regidx s2_idx = fmt) by (rewrite /A1 upd_ne; [exact Hs2 | reg_neq]).
    assert (Hp7a : add_vec_int (mword_of_int (KernelSyms.printk + 0x78) : mword 64) 2 = mword_of_int (KernelSyms.printk + 0x7a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp7a) in "Hpc".
    (* +0x7a c.mv s4,s1 : the C variable [i] *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.printk + 0x7a)) (mword_of_int 20 : mword 5) (mword_of_int 9 : mword 5)
              A1 (K - 24)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi7a [-]").
    iIntros (CID2 Hst2) "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (A2 := <[Regidx (mword_of_int 20 : mword 5) := regval_into_reg (add_vec zero_reg (A1 !!! Regidx (mword_of_int 9 : mword 5)))]> A1).
    assert (HA2s4 : A2 !!! Regidx (mword_of_int 20 : mword 5) = mword_of_int (Z.of_nat (S p))).
    { rewrite /A2 upd_eq. unfold regval_into_reg. rewrite HA1s1. apply add_vec_zero_l. }
    assert (HA2s1 : A2 !!! Regidx (mword_of_int 9 : mword 5) = mword_of_int (Z.of_nat (S p)))
      by (rewrite /A2 upd_ne; [exact HA1s1 | reg_neq]).
    assert (HA2s2 : A2 !!! Regidx s2_idx = fmt) by (rewrite /A2 upd_ne; [exact HA1s2 | reg_neq]).
    assert (Hp7c : add_vec_int (mword_of_int (KernelSyms.printk + 0x7a) : mword 64) 2 = mword_of_int (KernelSyms.printk + 0x7c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp7c) in "Hpc".
    (* +0x7c c.add s1,s1,s2 : &fmt[i] *)
    iApply (wp_cadd_s_sconf (mword_of_int (KernelSyms.printk + 0x7c)) (mword_of_int 9 : mword 5) s2_idx
              A2 (K - 24)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi7c [-]").
    iIntros (CID3 Hst3) "Hcg Hpc".
    iEval (rgne; rgne) in "Hcg".
    set (A3 := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg (add_vec (A2 !!! Regidx (mword_of_int 9 : mword 5)) (A2 !!! Regidx s2_idx))]> A2).
    assert (HA3s1 : A3 !!! Regidx (mword_of_int 9 : mword 5) = pa_add fmt (S p)).
    { rewrite /A3 upd_eq. unfold regval_into_reg. rewrite HA2s1 HA2s2.
      rewrite add_vec_pa_add. f_equal.
      rewrite (uint_moi_small (Z.of_nat (S p)) ltac:(change (2^64) with 18446744073709551616;
        change (2^31) with 2147483648 in Hp31; lia)).
      apply Nat2Z.id. }
    assert (Hp7e : add_vec_int (mword_of_int (KernelSyms.printk + 0x7c) : mword 64) 2 = mword_of_int (KernelSyms.printk + 0x7e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp7e) in "Hpc".
    (* +0x7e lbu a0,0(s1) : the next format byte *)
    iDestruct (pk_str_byte fmt dqf f (S p) Hlen with "Hfmt") as "[Hb Hfcl]".
    assert (Hba : add_vec (rget A3 (mword_of_int 9 : mword 5)) (sign_extend' 64 (mword_of_int 0 : mword 12)) = pa_add fmt (S p)).
    { rgne. rewrite HA3s1.
      replace (sign_extend' 64 (mword_of_int 0 : mword 12)) with (mword_of_int 0 : mword 64)
        by (apply bv_eq; vm_compute; reflexivity).
      apply kv_addv_zero. }
    iApply (wp_lbu_s_sconf (mword_of_int (KernelSyms.printk + 0x7e)) a0_idx (mword_of_int 9 : mword 5) (mword_of_int 0 : mword 12)
              A3 (K - 24)%nat (pk_fbyte f (S p)) b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi7e [Hb] [-]").
    { iEval (rewrite Hba). iExact "Hb". }
    iIntros (CID4 Hst4) "Hcg Hpc Hb". iEval (rewrite Hba) in "Hb".
    iDestruct ("Hfcl" with "Hb") as "Hfmt".
    set (A4 := <[Regidx a0_idx := regval_into_reg (zero_extend' 64 (pk_fbyte f (S p)))]> A3).
    assert (Hp82 : add_vec_int (mword_of_int (KernelSyms.printk + 0x7e) : mword 64) 4 = mword_of_int (KernelSyms.printk + 0x82)) by (apply bv_eq; vm_compute; reflexivity).
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
    - iApply (wp_beqz_x0_taken_s_sconf (mword_of_int (KernelSyms.printk + 0x82)) (mword_of_int 460 : mword 13)
                a0_idx A4 (K - 24)%nat b ltac:(vm_compute; discriminate) ltac:(rgne; exact Hz)
                ltac:(vm_compute; reflexivity)
                with "Hcg Hpc Hi82 [-]").
      iIntros (CID5 Hst5). iNext. iIntros "Hcg Hpc".
      assert (Htgt : add_vec (mword_of_int (KernelSyms.printk + 0x82) : mword 64) (sign_extend' 64 (mword_of_int 460 : mword 13)) = mword_of_int (KernelSyms.printk + 0x24e)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Htgt) in "Hpc".
      iSpecialize ("Kend" $! CID5 with "[%]"); [wp_next_chain|].
      iApply ("Kend" $! A4 with "[%] Hcg Hpc Hfmt HR").
      split; [exact Hkept | ].
      (* the loaded byte is zero, so the string ended here *)
      rewrite HA4a0 in Hz. exact (zext8_zero _ Hz).
    - iApply (wp_beqz_x0_fall_s_sconf (mword_of_int (KernelSyms.printk + 0x82)) (mword_of_int 460 : mword 13)
                a0_idx A4 (K - 24)%nat b ltac:(vm_compute; discriminate) ltac:(rgne; exact Hz)
                with "Hcg Hpc Hi82 [-]").
      iIntros (CID6 Hst6) "Hcg Hpc".
      assert (Hp86 : add_vec_int (mword_of_int (KernelSyms.printk + 0x82) : mword 64) 4 = mword_of_int (KernelSyms.printk + 0x86)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hp86) in "Hpc".
      iSpecialize ("Kgo" $! CID6 with "[%]"); [wp_next_chain|].
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
    forall `{CID0 : CpuId} (γd : uart_names) (γv : disk_names) (m0 : regfile) (K : nat)
      (l : list (bv 8)) (pv pkv : mword 32) (dqm dqm2 : dfrac) (b : bool) (pcur : mword 64),
      wp_consputc_sconf_body γd γv m0 K l pv pkv dqm dqm2 b pcur.

  Lemma wp_printk_char `{CID0 : CpuId} (γd : uart_names) (γv : disk_names)
      (mc : regfile) (K : nat) (l : list (bv 8)) (pv pkv : mword 32)
      (dqm dqm2 : dfrac) (Rest : iProp Σ) (b : bool) (pcur : mword 64) :
    (30 <= K)%nat ->
    eq_vec (sign_extend' 64 pv) zero_reg = false ->
    neq_vec (sign_extend' 64 pkv) zero_reg = false ->
    neq_vec (mc !!! Regidx a0_idx) (mc !!! Regidx (mword_of_int 19 : mword 5)) = true ->
    sie_cap_gpr mc (K - 24)%nat b pcur -∗
    kernel_text -∗
    pc_is (mword_of_int (KernelSyms.printk + 0x86) : mword 64) -∗
    (mword_of_int KernelSyms.panicking : mword 64) ↦₄{ dqm } pv -∗
    (mword_of_int KernelSyms.panicked : mword 64) ↦₄{ dqm2 } pkv -∗
    dev_inv γd γv -∗ uart_tx_own γd l -∗ uart_dlab_off γd -∗
    Rest -∗
    wp_next (CID0 := CID0) b pcur (fun (CID : CpuId) =>
      ∀ (mf : regfile) (bs : list (bv 8)),
      ⌜ (forall c : mword 5, is_cs_idx c = true -> c <> mword_of_int 9 ->
           mf !!! Regidx c = mc !!! Regidx c)
        /\ mf !!! Regidx (mword_of_int 9 : mword 5)
           = mc !!! Regidx (mword_of_int 20 : mword 5) ⌝ -∗
      sie_cap_gpr mf (K - 24)%nat b pcur -∗
      pc_is (mword_of_int (KernelSyms.printk + 0x78) : mword 64) -∗
      (mword_of_int KernelSyms.panicking : mword 64) ↦₄{ dqm } pv -∗
      (mword_of_int KernelSyms.panicked : mword 64) ↦₄{ dqm2 } pkv -∗
      uart_tx_own γd (l ++ bs) -∗ uart_sent γd (l ++ bs) -∗
      Rest -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros HK Hpv Hpkv Hne.
    assert (HK6 : (6 <= K - 24)%nat) by lia.
    iIntros "Hcg #Htext Hpc Hpanicking Hpanicked #Hdev Htx #Hdlab HR Hcont".
    iPoseProof (pki_86 with "Htext") as "Hi86".
    iPoseProof (pki_72 with "Htext") as "Hi72".
    iPoseProof (pki_76 with "Htext") as "Hi76".
    (* +0x86 bne a0,s3 : not a '%' -- print it *)
    iApply (wp_bne_taken_s_sconf (mword_of_int (KernelSyms.printk + 0x86)) (mword_of_int 8172 : mword 13)
              (mword_of_int 19 : mword 5) a0_idx mc (K - 24)%nat b
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) ltac:(rgne; rgne; exact Hne)
              ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi86 [-]").
    iIntros (CID1 Hst1). iNext. iIntros "Hcg Hpc".
    assert (Htgt72 : add_vec (mword_of_int (KernelSyms.printk + 0x86) : mword 64) (sign_extend' 64 (mword_of_int 8172 : mword 13)) = mword_of_int (KernelSyms.printk + 0x72)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgt72) in "Hpc".
    (* +0x72 jal consputc *)
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.printk + 0x72)) ra_idx (mword_of_int 2096398 : mword 21)
              mc (K - 24)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi72 [-]").
    iIntros (CID2 Hst2) "Hcg Hpc".
    set (P1 := <[Regidx ra_idx := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.printk + 0x72) : mword 64) 4)]> mc).
    assert (Htgtc : add_vec (mword_of_int (KernelSyms.printk + 0x72) : mword 64) (sign_extend' 64 (mword_of_int 2096398 : mword 21)) = mword_of_int KernelSyms.consputc) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgtc) in "Hpc".
    iApply (wp_consputc (CID0 := CID2) γd γv P1 (K - 24)%nat l pv pkv dqm dqm2 b pcur HK6 Hpv Hpkv
              with "Hcg Htext Hpc Hpanicking Hpanicked Hdev Htx Hdlab [-]").
    iIntros (CID3 Hst3 mk bs) "Hcg Hpc %Hcs Hpanicking Hpanicked Htx #Hsent".
    destruct Hcs as [Hcs Hra].
    assert (Hret : ret_pc (P1 !!! Regidx ra_idx) = mword_of_int (KernelSyms.printk + 0x76))
      by (rewrite /P1 upd_eq; unfold ret_pc; apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hret) in "Hpc".
    (* +0x76 c.mv s1,s4 : s1 := i, the index the advance block bumps *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.printk + 0x76)) (mword_of_int 9 : mword 5) (mword_of_int 20 : mword 5)
              mk (K - 24)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi76 [-]").
    iIntros (CID4 Hst4) "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (P2 := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg (add_vec zero_reg (mk !!! Regidx (mword_of_int 20 : mword 5)))]> mk).
    assert (Hp78 : add_vec_int (mword_of_int (KernelSyms.printk + 0x76) : mword 64) 2 = mword_of_int (KernelSyms.printk + 0x78)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp78) in "Hpc".
    (* s4 is callee-saved, so it still holds [i] *)
    assert (Hmks4 : mk !!! Regidx (mword_of_int 20 : mword 5) = mc !!! Regidx (mword_of_int 20 : mword 5)).
    { rewrite (callee_saved_lookup Hcs (mword_of_int 20 : mword 5) ltac:(vm_compute; reflexivity)).
      rewrite /P1 upd_ne; [reflexivity | reg_neq]. }
    iSpecialize ("Hcont" $! CID4 with "[%]"); [wp_next_chain|].
    iApply ("Hcont" $! P2 bs with "[%] Hcg Hpc Hpanicking Hpanicked Htx Hsent HR").
    split.
    - intros c Hc N9.
      pose proof (is_cs_idx_true_neq ra_idx c ltac:(vm_compute; reflexivity) Hc) as N1.
      rewrite /P2 upd_ne; [| congruence].
      rewrite (callee_saved_lookup Hcs c Hc).
      rewrite /P1 upd_ne; [reflexivity | congruence].
    - rewrite /P2 upd_eq. unfold regval_into_reg. rewrite Hmks4. apply add_vec_zero_l.
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
    - iFrame "V7". iIntros "V7". iFrame "V7 V6 V5 V4 V3 V2 V1".
    - iFrame "V6". iIntros "V6". iFrame "V7 V6 V5 V4 V3 V2 V1".
    - iFrame "V5". iIntros "V5". iFrame "V7 V6 V5 V4 V3 V2 V1".
    - iFrame "V4". iIntros "V4". iFrame "V7 V6 V5 V4 V3 V2 V1".
    - iFrame "V3". iIntros "V3". iFrame "V7 V6 V5 V4 V3 V2 V1".
    - iFrame "V2". iIntros "V2". iFrame "V7 V6 V5 V4 V3 V2 V1".
    - iFrame "V1". iIntros "V1". iFrame "V7 V6 V5 V4 V3 V2 V1".
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
    apply bv_eq. rewrite !moi64_mod.
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
    (instr (mword_of_int (KernelSyms.printk + B + 0) : mword 64) false
       (LOAD (mword_of_int 3976 : mword 12, Regidx s0_idx, Regidx a5_idx, false, 8)) ∗
     instr (mword_of_int (KernelSyms.printk + B + 4) : mword 64) false
       (ITYPE (mword_of_int 8 : mword 12, Regidx a5_idx, Regidx (mword_of_int 14 : mword 5), ADDI)) ∗
     instr (mword_of_int (KernelSyms.printk + B + 8) : mword 64) false
       (STORE (mword_of_int 3976 : mword 12, Regidx (mword_of_int 14 : mword 5), Regidx s0_idx, 8)))%I.

  Lemma wp_printk_vaarg `{CID0 : CpuId}
      (mc : regfile) (K : nat) (B : Z) (sp0 s0v : mword 64) (k : nat) (b : bool) (pcur : mword 64) :
    mc !!! Regidx s0_idx = s0v ->
    s0v = add_vec sp0 (sign_extend' 64 (mword_of_int (-64) : mword 12)) ->
    sie_cap_gpr mc (K - 24)%nat b pcur -∗
    pk_vaarg_instrs B -∗
    pc_is (mword_of_int (KernelSyms.printk + B + 0) : mword 64) -∗
    (pa_stk sp0 23) ↦₈ (pk_ap s0v k) -∗
    wp_next (CID0 := CID0) b pcur (fun (CID : CpuId) =>
      ∀ mf : regfile,
      ⌜ mf !!! Regidx a5_idx = pk_ap s0v k
        /\ mf !!! Regidx s0_idx = s0v
        /\ (forall c : mword 5, c <> a5_idx -> c <> mword_of_int 14 ->
              mf !!! Regidx c = mc !!! Regidx c) ⌝ -∗
      sie_cap_gpr mf (K - 24)%nat b pcur -∗
      pc_is (mword_of_int (KernelSyms.printk + B + 12) : mword 64) -∗
      (pa_stk sp0 23) ↦₈ (pk_ap s0v (S k)) -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hs0 Hs0v.
    iIntros "Hcg Hinstrs Hpc Hap Hcont".
    rewrite /pk_vaarg_instrs. iDestruct "Hinstrs" as "(I0 & I4 & I8)".
    assert (Hap23 : add_vec (rget mc s0_idx) (sign_extend' 64 (mword_of_int 3976 : mword 12)) = pa_stk sp0 23).
    { rgne. rewrite Hs0 Hs0v. unfold pa_stk, add_vec_int. rewrite pa_stk_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    iEval (rewrite -Hap23) in "Hap".
    iApply (wp_ld_s_sconf (mword_of_int (KernelSyms.printk + B + 0)) a5_idx s0_idx (mword_of_int 3976 : mword 12)
              mc (K - 24)%nat (pk_ap s0v k) b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc I0 Hap [-]").
    iIntros (CID1 Hst1) "Hcg Hpc Hap".
    set (V1 := <[Regidx a5_idx := regval_into_reg (pk_ap s0v k)]> mc).
    assert (HV1a5 : V1 !!! Regidx a5_idx = pk_ap s0v k) by (rewrite /V1 upd_eq; reflexivity).
    assert (HV1s0 : V1 !!! Regidx s0_idx = s0v) by (rewrite /V1 upd_ne; [exact Hs0 | reg_neq]).
    assert (Hp4 : add_vec_int (mword_of_int (KernelSyms.printk + B + 0) : mword 64) 4 = mword_of_int (KernelSyms.printk + B + 4))
      by (unfold add_vec_int; rewrite moi_add; f_equal; lia).
    iEval (rewrite Hp4) in "Hpc".
    iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.printk + B + 4)) (mword_of_int 14 : mword 5) a5_idx (mword_of_int 8 : mword 12)
              V1 (K - 24)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc I4 [-]").
    iIntros (CID2 Hst2) "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (V2 := <[Regidx (mword_of_int 14 : mword 5) := regval_into_reg (add_vec (V1 !!! Regidx a5_idx) (sign_extend' 64 (mword_of_int 8 : mword 12)))]> V1).
    assert (HV2a4 : V2 !!! Regidx (mword_of_int 14 : mword 5) = pk_ap s0v (S k)).
    { rewrite /V2 upd_eq. unfold regval_into_reg. rewrite HV1a5. unfold pk_ap.
      replace (sign_extend' 64 (mword_of_int 8 : mword 12)) with (mword_of_int 8 : mword 64)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite addv_moi_moi. f_equal. f_equal. rewrite Nat2Z.inj_succ. ring. }
    assert (HV2a5 : V2 !!! Regidx a5_idx = pk_ap s0v k) by (rewrite /V2 upd_ne; [exact HV1a5 | reg_neq]).
    assert (HV2s0 : V2 !!! Regidx s0_idx = s0v) by (rewrite /V2 upd_ne; [exact HV1s0 | reg_neq]).
    assert (Hp8 : add_vec_int (mword_of_int (KernelSyms.printk + B + 4) : mword 64) 4 = mword_of_int (KernelSyms.printk + B + 8))
      by (unfold add_vec_int; rewrite moi_add; f_equal; lia).
    iEval (rewrite Hp8) in "Hpc".
    assert (Hap23' : add_vec (rget V2 s0_idx) (sign_extend' 64 (mword_of_int 3976 : mword 12)) = pa_stk sp0 23).
    { rgne. rewrite HV2s0 Hs0v. unfold pa_stk, add_vec_int. rewrite pa_stk_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    iEval (rewrite Hap23 -Hap23') in "Hap".
    iApply (wp_sd_s_sconf (mword_of_int (KernelSyms.printk + B + 8)) (mword_of_int 14 : mword 5) s0_idx (mword_of_int 3976 : mword 12)
              V2 (K - 24)%nat (pk_ap s0v k) b with "Hcg Hpc I8 Hap [-]").
    iIntros (CID3 Hst3) "Hcg Hpc Hap". iEval (rewrite Hap23') in "Hap". iEval (rgne) in "Hap". iEval (rewrite HV2a4) in "Hap".
    assert (Hp12 : add_vec_int (mword_of_int (KernelSyms.printk + B + 8) : mword 64) 4 = mword_of_int (KernelSyms.printk + B + 12))
      by (unfold add_vec_int; rewrite moi_add; f_equal; lia).
    iEval (rewrite Hp12) in "Hpc".
    iSpecialize ("Hcont" $! CID3 with "[%]"); [wp_next_chain|].
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
    forall `{CID0 : CpuId} (γd : uart_names) (γv : disk_names) (m0 : regfile) (K : nat)
      (l : list (bv 8)) (pv pkv : mword 32) (dqm dqm2 : dfrac) (b : bool) (pcur : mword 64),
      wp_printint_sconf_body γd γv m0 K l pv pkv dqm dqm2 b pcur.

  Lemma wp_printk_arm_d `{CID0 : CpuId} (γd : uart_names) (γv : disk_names)
      (m mc : regfile) (K : nat) (k : nat) (l : list (bv 8)) (pv pkv : mword 32)
      (dqm dqm2 : dfrac) (Rest : iProp Σ) (b : bool) (pcur : mword 64) :
    let sp0 := m !!! Regidx csp_rs1 in
    let s0v := add_vec sp0 (sign_extend' 64 (mword_of_int (-64) : mword 12)) in
    (38 <= K)%nat ->
    (k < 7)%nat ->
    eq_vec (sign_extend' 64 pv) zero_reg = false ->
    neq_vec (sign_extend' 64 pkv) zero_reg = false ->
    mc !!! Regidx s0_idx = s0v ->
    mc !!! Regidx (mword_of_int 22 : mword 5) = (mword_of_int 10 : mword 64) ->
    sie_cap_gpr mc (K - 24)%nat b pcur -∗
    kernel_text -∗ kernel_data -∗
    pc_is (mword_of_int (KernelSyms.printk + 0xd4) : mword 64) -∗
    (pa_stk sp0 23) ↦₈ (pk_ap s0v k) -∗
    pk_va sp0 m -∗
    (mword_of_int KernelSyms.panicking : mword 64) ↦₄{ dqm } pv -∗
    (mword_of_int KernelSyms.panicked : mword 64) ↦₄{ dqm2 } pkv -∗
    dev_inv γd γv -∗ uart_tx_own γd l -∗ uart_dlab_off γd -∗
    Rest -∗
    wp_next (CID0 := CID0) b pcur (fun (CID : CpuId) =>
      ∀ (mf : regfile) (bs : list (bv 8)),
      ⌜ forall c : mword 5, is_cs_idx c = true -> mf !!! Regidx c = mc !!! Regidx c ⌝ -∗
      sie_cap_gpr mf (K - 24)%nat b pcur -∗
      pc_is (mword_of_int (KernelSyms.printk + 0x78) : mword 64) -∗
      (pa_stk sp0 23) ↦₈ (pk_ap s0v (S k)) -∗
      pk_va sp0 m -∗
      (mword_of_int KernelSyms.panicking : mword 64) ↦₄{ dqm } pv -∗
      (mword_of_int KernelSyms.panicked : mword 64) ↦₄{ dqm2 } pkv -∗
      uart_tx_own γd (l ++ bs) -∗ uart_sent γd (l ++ bs) -∗
      Rest -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
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
    assert (Hap23 : add_vec (rget mc s0_idx) (sign_extend' 64 (mword_of_int 3976 : mword 12)) = pa_stk sp0 23).
    { rgne. rewrite Hs0. unfold s0v, pa_stk, add_vec_int. rewrite pa_stk_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    (* +0xd4 ld a5,-120(s0) : a5 := ap *)
    iEval (rewrite -Hap23) in "Hap".
    iApply (wp_ld_s_sconf (mword_of_int (KernelSyms.printk + 0xd4)) a5_idx s0_idx (mword_of_int 3976 : mword 12)
              mc (K - 24)%nat (pk_ap s0v k) b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hid4 Hap [-]").
    iIntros (CID1 Hst1) "Hcg Hpc Hap".
    set (D1 := <[Regidx a5_idx := regval_into_reg (pk_ap s0v k)]> mc).
    assert (HD1a5 : D1 !!! Regidx a5_idx = pk_ap s0v k) by (rewrite /D1 upd_eq; reflexivity).
    assert (HD1s0 : D1 !!! Regidx s0_idx = s0v) by (rewrite /D1 upd_ne; [exact Hs0 | reg_neq]).
    assert (Hpd8 : add_vec_int (mword_of_int (KernelSyms.printk + 0xd4) : mword 64) 4 = mword_of_int (KernelSyms.printk + 0xd8)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpd8) in "Hpc".
    (* +0xd8 addi a4,a5,8 : the bumped cursor *)
    iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.printk + 0xd8)) (mword_of_int 14 : mword 5) a5_idx (mword_of_int 8 : mword 12)
              D1 (K - 24)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hid8 [-]").
    iIntros (CID2 Hst2) "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (D2 := <[Regidx (mword_of_int 14 : mword 5) := regval_into_reg (add_vec (D1 !!! Regidx a5_idx) (sign_extend' 64 (mword_of_int 8 : mword 12)))]> D1).
    assert (HD2a4 : D2 !!! Regidx (mword_of_int 14 : mword 5) = pk_ap s0v (S k)).
    { rewrite /D2 upd_eq. unfold regval_into_reg. rewrite HD1a5. unfold pk_ap.
      replace (sign_extend' 64 (mword_of_int 8 : mword 12)) with (mword_of_int 8 : mword 64)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite addv_moi_moi. f_equal. f_equal. rewrite Nat2Z.inj_succ. ring. }
    assert (HD2a5 : D2 !!! Regidx a5_idx = pk_ap s0v k) by (rewrite /D2 upd_ne; [exact HD1a5 | reg_neq]).
    assert (HD2s0 : D2 !!! Regidx s0_idx = s0v) by (rewrite /D2 upd_ne; [exact HD1s0 | reg_neq]).
    assert (Hpdc : add_vec_int (mword_of_int (KernelSyms.printk + 0xd8) : mword 64) 4 = mword_of_int (KernelSyms.printk + 0xdc)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpdc) in "Hpc".
    (* +0xdc sd a4,-120(s0) : ap := ap + 8 *)
    assert (Hap23' : add_vec (rget D2 s0_idx) (sign_extend' 64 (mword_of_int 3976 : mword 12)) = pa_stk sp0 23).
    { rgne. rewrite HD2s0. unfold s0v, pa_stk, add_vec_int. rewrite pa_stk_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    iEval (rewrite Hap23 -Hap23') in "Hap".
    iApply (wp_sd_s_sconf (mword_of_int (KernelSyms.printk + 0xdc)) (mword_of_int 14 : mword 5) s0_idx (mword_of_int 3976 : mword 12)
              D2 (K - 24)%nat (pk_ap s0v k) b with "Hcg Hpc Hidc Hap [-]").
    iIntros (CID3 Hst3) "Hcg Hpc Hap". iEval (rewrite Hap23') in "Hap". iEval (rgne) in "Hap". iEval (rewrite HD2a4) in "Hap".
    assert (Hpe0 : add_vec_int (mword_of_int (KernelSyms.printk + 0xdc) : mword 64) 4 = mword_of_int (KernelSyms.printk + 0xe0)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpe0) in "Hpc".
    (* +0xe0 c.li a2,1 : sign *)
    iApply (wp_cli_s_sconf (mword_of_int (KernelSyms.printk + 0xe0)) (mword_of_int 12 : mword 5) (mword_of_int 1 : mword 6)
              (mword_of_int 1 : mword 64) D2 (K - 24)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc Hie0 [-]").
    iIntros (CID4 Hst4) "Hcg Hpc".
    set (D3 := <[Regidx (mword_of_int 12 : mword 5) := regval_into_reg (mword_of_int 1 : mword 64)]> D2).
    assert (Hpe2 : add_vec_int (mword_of_int (KernelSyms.printk + 0xe0) : mword 64) 2 = mword_of_int (KernelSyms.printk + 0xe2)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpe2) in "Hpc".
    (* +0xe2 c.mv a1,s6 : base = 10 *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.printk + 0xe2)) a1_idx (mword_of_int 22 : mword 5)
              D3 (K - 24)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hie2 [-]").
    iIntros (CID5 Hst5) "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (D4 := <[Regidx a1_idx := regval_into_reg (add_vec zero_reg (D3 !!! Regidx (mword_of_int 22 : mword 5)))]> D3).
    assert (HD4a1 : D4 !!! Regidx a1_idx = (mword_of_int 10 : mword 64)).
    { rewrite /D4 upd_eq. unfold regval_into_reg.
      rewrite /D3 upd_ne; [| reg_neq]. rewrite /D2 upd_ne; [| reg_neq].
      rewrite /D1 upd_ne; [| reg_neq]. rewrite Hs6. apply add_vec_zero_l. }
    assert (HD4a5 : D4 !!! Regidx a5_idx = pk_ap s0v k).
    { rewrite /D4 upd_ne; [| reg_neq]. rewrite /D3 upd_ne; [| reg_neq]. exact HD2a5. }
    assert (Hpe4 : add_vec_int (mword_of_int (KernelSyms.printk + 0xe2) : mword 64) 2 = mword_of_int (KernelSyms.printk + 0xe4)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpe4) in "Hpc".
    (* +0xe4 c.lw a0,0(a5) : the argument -- a 4-byte read of an 8-byte slot *)
    iDestruct (pk_va_acc sp0 m k Hk with "Hva") as "[Hslot Hvacl]".
    iDestruct (word_pointsto_aligned_p with "Hslot") as %Halv.
    iDestruct (word_pointsto_split4 with "Hslot") as "[Hlo Hhi]".
    iEval (rewrite -/(pk_lo m k)) in "Hlo".
    assert (Hlwa : add_vec (rget D4 a5_idx) (sign_extend' 64 (mword_of_int 0 : mword 12)) = pa_stk sp0 (7 - k)).
    { rgne. rewrite HD4a5.
      replace (sign_extend' 64 (mword_of_int 0 : mword 12)) with (mword_of_int 0 : mword 64)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite kv_addv_zero. apply pk_ap_slot. exact Hk. }
    iEval (rewrite -Hlwa) in "Hlo".
    iApply (wp_clw_s_sconf (mword_of_int (KernelSyms.printk + 0xe4)) a0_idx a5_idx (mword_of_int 0 : mword 12)
              D4 (K - 24)%nat (pk_lo m k) b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hie4 Hlo [-]").
    iIntros (CID6 Hst6) "Hcg Hpc Hlo". iEval (rewrite Hlwa) in "Hlo".
    iDestruct (word_pointsto_join4 _ _ _ _ Halv with "Hlo Hhi") as "Hslot".
    rewrite word_of_words_id.
    iDestruct ("Hvacl" with "Hslot") as "Hva".
    set (D5 := <[Regidx a0_idx := regval_into_reg (sign_extend' 64 (pk_lo m k))]> D4).
    assert (Hpe6 : add_vec_int (mword_of_int (KernelSyms.printk + 0xe4) : mword 64) 2 = mword_of_int (KernelSyms.printk + 0xe6)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpe6) in "Hpc".
    (* +0xe6 jal printint *)
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.printk + 0xe6)) ra_idx (mword_of_int 2096772 : mword 21)
              D5 (K - 24)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hie6 [-]").
    iIntros (CID7 Hst7) "Hcg Hpc".
    set (D6 := <[Regidx ra_idx := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.printk + 0xe6) : mword 64) 4)]> D5).
    assert (Htgtp : add_vec (mword_of_int (KernelSyms.printk + 0xe6) : mword 64) (sign_extend' 64 (mword_of_int 2096772 : mword 21)) = mword_of_int KernelSyms.printint) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgtp) in "Hpc".
    assert (HD6a1 : (10 <= uint (D6 !!! Regidx a1_idx) <= 16)%Z).
    { rewrite /D6 upd_ne; [| reg_neq]. rewrite /D5 upd_ne; [| reg_neq]. rewrite HD4a1.
      rewrite (uint_moi_small 10 ltac:(change (2^64) with 18446744073709551616; lia)). lia. }
    iApply (wp_printint (CID0 := CID7) γd γv D6 (K - 24)%nat l pv pkv dqm dqm2 b pcur HK14 HD6a1 Hpv Hpkv
              with "Hcg Htext Hkdata Hpc Hpanicking Hpanicked Hdev Htx Hdlab [-]").
    iIntros (CID8 Hst8 mf bs) "Hcg Hpc %Hcs Hpanicking Hpanicked Htx #Hsent".
    destruct Hcs as [Hcs Hra].
    assert (Hret : ret_pc (D6 !!! Regidx ra_idx) = mword_of_int (KernelSyms.printk + 0xea))
      by (rewrite /D6 upd_eq; unfold ret_pc; apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hret) in "Hpc".
    (* +0xea j 0x78 *)
    iApply (wp_cj_s_sconf (mword_of_int (KernelSyms.printk + 0xea)) (sign_extend' 21 (concat_vec (mword_of_int 1991 : mword 11) ('b"0")))
              mf (K - 24)%nat b ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hiea [-]").
    iIntros (CID9 Hst9). iNext. iIntros "Hcg Hpc".
    assert (Htgt78 : add_vec (mword_of_int (KernelSyms.printk + 0xea) : mword 64) (sign_extend' 64 (sign_extend' 21 (concat_vec (mword_of_int 1991 : mword 11) ('b"0")))) = mword_of_int (KernelSyms.printk + 0x78)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgt78) in "Hpc".
    iSpecialize ("Hcont" $! CID9 with "[%]"); [wp_next_chain|].
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


  Lemma wp_printk_arm_ld `{CID0 : CpuId} (γd : uart_names) (γv : disk_names)
      (m mc : regfile) (K : nat) (k i : nat) (l : list (bv 8)) (pv pkv : mword 32)
      (dqm dqm2 : dfrac) (Rest : iProp Σ) (b : bool) (pcur : mword 64) :
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
    sie_cap_gpr mc (K - 24)%nat b pcur -∗
    kernel_text -∗ kernel_data -∗
    pc_is (mword_of_int (KernelSyms.printk + 0xb8 + 0) : mword 64) -∗
    (pa_stk sp0 23) ↦₈ (pk_ap s0v k) -∗
    pk_va sp0 m -∗
    (mword_of_int KernelSyms.panicking : mword 64) ↦₄{ dqm } pv -∗
    (mword_of_int KernelSyms.panicked : mword 64) ↦₄{ dqm2 } pkv -∗
    dev_inv γd γv -∗ uart_tx_own γd l -∗ uart_dlab_off γd -∗
    Rest -∗
    wp_next (CID0 := CID0) b pcur (fun (CID : CpuId) =>
      ∀ (mf : regfile) (bs : list (bv 8)),
      ⌜ (forall c : mword 5, is_cs_idx c = true -> c <> mword_of_int 9 ->
           mf !!! Regidx c = mc !!! Regidx c)
        /\ mf !!! Regidx (mword_of_int 9 : mword 5) = mword_of_int (Z.of_nat i + 2) ⌝ -∗
      sie_cap_gpr mf (K - 24)%nat b pcur -∗
      pc_is (mword_of_int (KernelSyms.printk + 0x78) : mword 64) -∗
      (pa_stk sp0 23) ↦₈ (pk_ap s0v (S k)) -∗
      pk_va sp0 m -∗
      (mword_of_int KernelSyms.panicking : mword 64) ↦₄{ dqm } pv -∗
      (mword_of_int KernelSyms.panicked : mword 64) ↦₄{ dqm2 } pkv -∗
      uart_tx_own γd (l ++ bs) -∗ uart_sent γd (l ++ bs) -∗
      Rest -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros sp0 s0v HK Hk Hi31 Hpv Hpkv Hs0 Hs6 Hs4.
    assert (HK14 : (14 <= K - 24)%nat) by lia.
    iIntros "Hcg #Htext #Hkdata Hpc Hap Hva Hpanicking Hpanicked #Hdev Htx #Hdlab HR Hcont".
    iApply (wp_printk_vaarg mc K 0xb8 sp0 s0v k b pcur Hs0 eq_refl
              with "Hcg [] Hpc Hap [-]").
    { rewrite /pk_vaarg_instrs.
      iSplitR; [iApply (pki_b8 with "Htext") | ].
      iSplitR; [iApply (pki_bc with "Htext") | ].
      iApply (pki_c0 with "Htext"). }
    iIntros (CIDv Hstv V) "%Hv Hcg Hpc Hap".
    destruct Hv as (Hva5 & Hvs0 & Hvk).
    iApply (wp_cli_s_sconf (mword_of_int (KernelSyms.printk + 0xc4)) (mword_of_int 12 : mword 5) (mword_of_int 1 : mword 6)
              (mword_of_int 1 : mword 64) V (K - 24)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc [] [-]").
    { iApply (pki_c4 with "Htext"). }
    iIntros (CID1 Hst1) "Hcg Hpc".
    set (S0 := <[Regidx (mword_of_int 12 : mword 5) := regval_into_reg (mword_of_int 1 : mword 64)]> V).
    assert (Hpac6 : add_vec_int (mword_of_int (KernelSyms.printk + 0xc4) : mword 64) 2 = mword_of_int (KernelSyms.printk + 0xc6)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpac6) in "Hpc".
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.printk + 0xc6)) a1_idx (mword_of_int 22 : mword 5)
              S0 (K - 24)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc [] [-]").
    { iApply (pki_c6 with "Htext"). }
    iIntros (CID2 Hst2) "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (S1 := <[Regidx a1_idx := regval_into_reg (add_vec zero_reg (S0 !!! Regidx (mword_of_int 22 : mword 5)))]> S0).
    assert (HS1a1 : S1 !!! Regidx a1_idx = (mword_of_int 10 : mword 64)).
    { rewrite /S1 upd_eq. unfold regval_into_reg.
      rewrite /S0 upd_ne; [| reg_neq].
      rewrite (Hvk (mword_of_int 22 : mword 5) ltac:(mw_neq) ltac:(mw_neq)).
      rewrite Hs6. apply add_vec_zero_l. }
    assert (HS1a5 : S1 !!! Regidx a5_idx = pk_ap s0v k).
    { rewrite /S1 upd_ne; [| reg_neq]. rewrite /S0 upd_ne; [| reg_neq]. exact Hva5. }
    assert (Hpac8 : add_vec_int (mword_of_int (KernelSyms.printk + 0xc6) : mword 64) 2 = mword_of_int (KernelSyms.printk + 0xc8)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpac8) in "Hpc".
    (* the argument: a whole 8-byte slot this time *)
    iDestruct (pk_va_acc sp0 m k Hk with "Hva") as "[Hslot Hvacl]".
    assert (Hlda : add_vec (rget S1 a5_idx) (sign_extend' 64 (mword_of_int 0 : mword 12)) = pa_stk sp0 (7 - k)).
    { rgne. rewrite HS1a5.
      replace (sign_extend' 64 (mword_of_int 0 : mword 12)) with (mword_of_int 0 : mword 64)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite kv_addv_zero. apply pk_ap_slot. exact Hk. }
    iEval (rewrite -Hlda) in "Hslot".
    iApply (wp_cld_s_sconf (mword_of_int (KernelSyms.printk + 0xc8)) a0_idx a5_idx (mword_of_int 0 : mword 12)
              S1 (K - 24)%nat (pk_vararg m k) b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc [] Hslot [-]").
    { iApply (pki_c8 with "Htext"). }
    iIntros (CID3 Hst3) "Hcg Hpc Hslot". iEval (rewrite Hlda) in "Hslot".
    iDestruct ("Hvacl" with "Hslot") as "Hva".
    set (S2 := <[Regidx a0_idx := regval_into_reg (pk_vararg m k)]> S1).
    assert (HS2a1 : S2 !!! Regidx a1_idx = (mword_of_int 10 : mword 64))
      by (rewrite /S2 upd_ne; [exact HS1a1 | reg_neq]).
    assert (Hpaca : add_vec_int (mword_of_int (KernelSyms.printk + 0xc8) : mword 64) 2 = mword_of_int (KernelSyms.printk + 0xca)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpaca) in "Hpc".
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.printk + 0xca)) ra_idx (mword_of_int 2096800 : mword 21)
              S2 (K - 24)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(vm_compute; reflexivity)
              with "Hcg Hpc [] [-]").
    { iApply (pki_ca with "Htext"). }
    iIntros (CID4 Hst4) "Hcg Hpc".
    set (S3 := <[Regidx ra_idx := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.printk + 0xca) : mword 64) 4)]> S2).
    assert (Htgtp : add_vec (mword_of_int (KernelSyms.printk + 0xca) : mword 64) (sign_extend' 64 (mword_of_int 2096800 : mword 21)) = mword_of_int KernelSyms.printint) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgtp) in "Hpc".
    assert (HS3a1 : (10 <= uint (S3 !!! Regidx a1_idx) <= 16)%Z).
    { rewrite /S3 upd_ne; [| reg_neq]. rewrite HS2a1.
      rewrite (uint_moi_small 10 ltac:(change (2^64) with 18446744073709551616; lia)). lia. }
    iApply (wp_printint (CID0 := CID4) γd γv S3 (K - 24)%nat l pv pkv dqm dqm2 b pcur HK14 HS3a1 Hpv Hpkv
              with "Hcg Htext Hkdata Hpc Hpanicking Hpanicked Hdev Htx Hdlab [-]").
    iIntros (CID5 Hst5 mf bs) "Hcg Hpc %Hcs Hpanicking Hpanicked Htx #Hsent".
    destruct Hcs as [Hcs Hra].
    assert (Hret : ret_pc (S3 !!! Regidx ra_idx) = mword_of_int (KernelSyms.printk + 0xce))
      by (rewrite /S3 upd_eq; unfold ret_pc; apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hret) in "Hpc".
    (* +0xce addiw s1,s4,2 : how far the directive advanced the scan *)
    assert (Hmfs4 : mf !!! Regidx (mword_of_int 20 : mword 5) = mword_of_int (Z.of_nat i)).
    { rewrite (callee_saved_lookup Hcs (mword_of_int 20 : mword 5) ltac:(vm_compute; reflexivity)).
      rewrite /S3 upd_ne; [| reg_neq]. rewrite /S2 upd_ne; [| reg_neq].
      rewrite /S1 upd_ne; [| reg_neq]. rewrite /S0 upd_ne; [| reg_neq].
      rewrite (Hvk (mword_of_int 20 : mword 5) ltac:(mw_neq) ltac:(mw_neq)). exact Hs4. }
    iApply (wp_addiw_s_sconf (mword_of_int (KernelSyms.printk + 0xce)) (mword_of_int 9 : mword 5) (mword_of_int 20 : mword 5) (mword_of_int 2 : mword 12)
              mf (K - 24)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc [] [-]").
    { iApply (pki_ce with "Htext"). }
    iIntros (CID6 Hst6) "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (T := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg (sign_extend' 64 (subrange_vec_dec
                 (add_vec (mf !!! Regidx (mword_of_int 20 : mword 5)) (sign_extend' 64 (mword_of_int 2 : mword 12))) 31 0))]> mf).
    assert (HTs1 : T !!! Regidx (mword_of_int 9 : mword 5) = mword_of_int (Z.of_nat i + 2)).
    { rewrite /T upd_eq. unfold regval_into_reg. rewrite Hmfs4.
      apply (addiw_lit (Z.of_nat i) 2 (sign_extend' 64 (mword_of_int 2 : mword 12))
               ltac:(apply bv_eq; vm_compute; reflexivity)
               ltac:(change (2^31) with 2147483648 in Hi31 |- *; lia)). }
    assert (Hpad2 : add_vec_int (mword_of_int (KernelSyms.printk + 0xce) : mword 64) 4 = mword_of_int (KernelSyms.printk + 0xd2)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpad2) in "Hpc".
    (* +0xd2 j 0x78 *)
    iApply (wp_cj_s_sconf (mword_of_int (KernelSyms.printk + 0xd2)) (sign_extend' 21 (concat_vec (mword_of_int 2003 : mword 11) ('b"0")))
              T (K - 24)%nat b ltac:(vm_compute; reflexivity)
              with "Hcg Hpc [] [-]").
    { iApply (pki_d2 with "Htext"). }
    iIntros (CID7 Hst7). iNext. iIntros "Hcg Hpc".
    assert (Htgt78 : add_vec (mword_of_int (KernelSyms.printk + 0xd2) : mword 64) (sign_extend' 64 (sign_extend' 21 (concat_vec (mword_of_int 2003 : mword 11) ('b"0")))) = mword_of_int (KernelSyms.printk + 0x78)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgt78) in "Hpc".
    iSpecialize ("Hcont" $! CID7 with "[%]"); [wp_next_chain|].
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


  Lemma wp_printk_arm_lld `{CID0 : CpuId} (γd : uart_names) (γv : disk_names)
      (m mc : regfile) (K : nat) (k i : nat) (l : list (bv 8)) (pv pkv : mword 32)
      (dqm dqm2 : dfrac) (Rest : iProp Σ) (b : bool) (pcur : mword 64) :
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
    sie_cap_gpr mc (K - 24)%nat b pcur -∗
    kernel_text -∗ kernel_data -∗
    pc_is (mword_of_int (KernelSyms.printk + 0xf6 + 0) : mword 64) -∗
    (pa_stk sp0 23) ↦₈ (pk_ap s0v k) -∗
    pk_va sp0 m -∗
    (mword_of_int KernelSyms.panicking : mword 64) ↦₄{ dqm } pv -∗
    (mword_of_int KernelSyms.panicked : mword 64) ↦₄{ dqm2 } pkv -∗
    dev_inv γd γv -∗ uart_tx_own γd l -∗ uart_dlab_off γd -∗
    Rest -∗
    wp_next (CID0 := CID0) b pcur (fun (CID : CpuId) =>
      ∀ (mf : regfile) (bs : list (bv 8)),
      ⌜ (forall c : mword 5, is_cs_idx c = true -> c <> mword_of_int 9 ->
           mf !!! Regidx c = mc !!! Regidx c)
        /\ mf !!! Regidx (mword_of_int 9 : mword 5) = mword_of_int (Z.of_nat i + 3) ⌝ -∗
      sie_cap_gpr mf (K - 24)%nat b pcur -∗
      pc_is (mword_of_int (KernelSyms.printk + 0x78) : mword 64) -∗
      (pa_stk sp0 23) ↦₈ (pk_ap s0v (S k)) -∗
      pk_va sp0 m -∗
      (mword_of_int KernelSyms.panicking : mword 64) ↦₄{ dqm } pv -∗
      (mword_of_int KernelSyms.panicked : mword 64) ↦₄{ dqm2 } pkv -∗
      uart_tx_own γd (l ++ bs) -∗ uart_sent γd (l ++ bs) -∗
      Rest -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros sp0 s0v HK Hk Hi31 Hpv Hpkv Hs0 Hs6 Hs4.
    assert (HK14 : (14 <= K - 24)%nat) by lia.
    iIntros "Hcg #Htext #Hkdata Hpc Hap Hva Hpanicking Hpanicked #Hdev Htx #Hdlab HR Hcont".
    iApply (wp_printk_vaarg mc K 0xf6 sp0 s0v k b pcur Hs0 eq_refl
              with "Hcg [] Hpc Hap [-]").
    { rewrite /pk_vaarg_instrs.
      iSplitR; [iApply (pki_f6 with "Htext") | ].
      iSplitR; [iApply (pki_fa with "Htext") | ].
      iApply (pki_fe with "Htext"). }
    iIntros (CIDv Hstv V) "%Hv Hcg Hpc Hap".
    destruct Hv as (Hva5 & Hvs0 & Hvk).
    iApply (wp_cli_s_sconf (mword_of_int (KernelSyms.printk + 0x102)) (mword_of_int 12 : mword 5) (mword_of_int 1 : mword 6)
              (mword_of_int 1 : mword 64) V (K - 24)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc [] [-]").
    { iApply (pki_102 with "Htext"). }
    iIntros (CID1 Hst1) "Hcg Hpc".
    set (S0 := <[Regidx (mword_of_int 12 : mword 5) := regval_into_reg (mword_of_int 1 : mword 64)]> V).
    assert (Hpa104 : add_vec_int (mword_of_int (KernelSyms.printk + 0x102) : mword 64) 2 = mword_of_int (KernelSyms.printk + 0x104)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpa104) in "Hpc".
    iApply (wp_cli_s_sconf (mword_of_int (KernelSyms.printk + 0x104)) a1_idx (mword_of_int 10 : mword 6)
              (mword_of_int 10 : mword 64) S0 (K - 24)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc [] [-]").
    { iApply (pki_104 with "Htext"). }
    iIntros (CID7 Hst7) "Hcg Hpc".
    set (S1 := <[Regidx a1_idx := regval_into_reg (mword_of_int 10 : mword 64)]> S0).
    assert (HS1a1 : S1 !!! Regidx a1_idx = (mword_of_int 10 : mword 64))
      by (rewrite /S1 upd_eq; reflexivity).
    assert (HS1a5 : S1 !!! Regidx a5_idx = pk_ap s0v k).
    { rewrite /S1 upd_ne; [| reg_neq]. rewrite /S0 upd_ne; [| reg_neq]. exact Hva5. }
    assert (Hpa106 : add_vec_int (mword_of_int (KernelSyms.printk + 0x104) : mword 64) 2 = mword_of_int (KernelSyms.printk + 0x106)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpa106) in "Hpc".
    (* the argument: a whole 8-byte slot this time *)
    iDestruct (pk_va_acc sp0 m k Hk with "Hva") as "[Hslot Hvacl]".
    assert (Hlda : add_vec (rget S1 a5_idx) (sign_extend' 64 (mword_of_int 0 : mword 12)) = pa_stk sp0 (7 - k)).
    { rgne. rewrite HS1a5.
      replace (sign_extend' 64 (mword_of_int 0 : mword 12)) with (mword_of_int 0 : mword 64)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite kv_addv_zero. apply pk_ap_slot. exact Hk. }
    iEval (rewrite -Hlda) in "Hslot".
    iApply (wp_cld_s_sconf (mword_of_int (KernelSyms.printk + 0x106)) a0_idx a5_idx (mword_of_int 0 : mword 12)
              S1 (K - 24)%nat (pk_vararg m k) b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc [] Hslot [-]").
    { iApply (pki_106 with "Htext"). }
    iIntros (CID2 Hst2) "Hcg Hpc Hslot". iEval (rewrite Hlda) in "Hslot".
    iDestruct ("Hvacl" with "Hslot") as "Hva".
    set (S2 := <[Regidx a0_idx := regval_into_reg (pk_vararg m k)]> S1).
    assert (HS2a1 : S2 !!! Regidx a1_idx = (mword_of_int 10 : mword 64))
      by (rewrite /S2 upd_ne; [exact HS1a1 | reg_neq]).
    assert (Hpa108 : add_vec_int (mword_of_int (KernelSyms.printk + 0x106) : mword 64) 2 = mword_of_int (KernelSyms.printk + 0x108)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpa108) in "Hpc".
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.printk + 0x108)) ra_idx (mword_of_int 2096738 : mword 21)
              S2 (K - 24)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(vm_compute; reflexivity)
              with "Hcg Hpc [] [-]").
    { iApply (pki_108 with "Htext"). }
    iIntros (CID3 Hst3) "Hcg Hpc".
    set (S3 := <[Regidx ra_idx := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.printk + 0x108) : mword 64) 4)]> S2).
    assert (Htgtp : add_vec (mword_of_int (KernelSyms.printk + 0x108) : mword 64) (sign_extend' 64 (mword_of_int 2096738 : mword 21)) = mword_of_int KernelSyms.printint) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgtp) in "Hpc".
    assert (HS3a1 : (10 <= uint (S3 !!! Regidx a1_idx) <= 16)%Z).
    { rewrite /S3 upd_ne; [| reg_neq]. rewrite HS2a1.
      rewrite (uint_moi_small 10 ltac:(change (2^64) with 18446744073709551616; lia)). lia. }
    iApply (wp_printint (CID0 := CID3) γd γv S3 (K - 24)%nat l pv pkv dqm dqm2 b pcur HK14 HS3a1 Hpv Hpkv
              with "Hcg Htext Hkdata Hpc Hpanicking Hpanicked Hdev Htx Hdlab [-]").
    iIntros (CID4 Hst4 mf bs) "Hcg Hpc %Hcs Hpanicking Hpanicked Htx #Hsent".
    destruct Hcs as [Hcs Hra].
    assert (Hret : ret_pc (S3 !!! Regidx ra_idx) = mword_of_int (KernelSyms.printk + 0x10c))
      by (rewrite /S3 upd_eq; unfold ret_pc; apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hret) in "Hpc".
    (* +0x10c addiw s1,s4,3 : how far the directive advanced the scan *)
    assert (Hmfs4 : mf !!! Regidx (mword_of_int 20 : mword 5) = mword_of_int (Z.of_nat i)).
    { rewrite (callee_saved_lookup Hcs (mword_of_int 20 : mword 5) ltac:(vm_compute; reflexivity)).
      rewrite /S3 upd_ne; [| reg_neq]. rewrite /S2 upd_ne; [| reg_neq].
      rewrite /S1 upd_ne; [| reg_neq]. rewrite /S0 upd_ne; [| reg_neq]. 
      rewrite (Hvk (mword_of_int 20 : mword 5) ltac:(mw_neq) ltac:(mw_neq)). exact Hs4. }
    iApply (wp_addiw_s_sconf (mword_of_int (KernelSyms.printk + 0x10c)) (mword_of_int 9 : mword 5) (mword_of_int 20 : mword 5) (mword_of_int 3 : mword 12)
              mf (K - 24)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc [] [-]").
    { iApply (pki_10c with "Htext"). }
    iIntros (CID5 Hst5) "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (T := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg (sign_extend' 64 (subrange_vec_dec
                 (add_vec (mf !!! Regidx (mword_of_int 20 : mword 5)) (sign_extend' 64 (mword_of_int 3 : mword 12))) 31 0))]> mf).
    assert (HTs1 : T !!! Regidx (mword_of_int 9 : mword 5) = mword_of_int (Z.of_nat i + 3)).
    { rewrite /T upd_eq. unfold regval_into_reg. rewrite Hmfs4.
      apply (addiw_lit (Z.of_nat i) 3 (sign_extend' 64 (mword_of_int 3 : mword 12))
               ltac:(apply bv_eq; vm_compute; reflexivity)
               ltac:(change (2^31) with 2147483648 in Hi31 |- *; lia)). }
    assert (Hpa110 : add_vec_int (mword_of_int (KernelSyms.printk + 0x10c) : mword 64) 4 = mword_of_int (KernelSyms.printk + 0x110)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpa110) in "Hpc".
    (* +0x110 j 0x78 *)
    iApply (wp_cj_s_sconf (mword_of_int (KernelSyms.printk + 0x110)) (sign_extend' 21 (concat_vec (mword_of_int 1972 : mword 11) ('b"0")))
              T (K - 24)%nat b ltac:(vm_compute; reflexivity)
              with "Hcg Hpc [] [-]").
    { iApply (pki_110 with "Htext"). }
    iIntros (CID6 Hst6). iNext. iIntros "Hcg Hpc".
    assert (Htgt78 : add_vec (mword_of_int (KernelSyms.printk + 0x110) : mword 64) (sign_extend' 64 (sign_extend' 21 (concat_vec (mword_of_int 1972 : mword 11) ('b"0")))) = mword_of_int (KernelSyms.printk + 0x78)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgt78) in "Hpc".
    iSpecialize ("Hcont" $! CID6 with "[%]"); [wp_next_chain|].
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


  Lemma wp_printk_arm_lu `{CID0 : CpuId} (γd : uart_names) (γv : disk_names)
      (m mc : regfile) (K : nat) (k i : nat) (l : list (bv 8)) (pv pkv : mword 32)
      (dqm dqm2 : dfrac) (Rest : iProp Σ) (b : bool) (pcur : mword 64) :
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
    sie_cap_gpr mc (K - 24)%nat b pcur -∗
    kernel_text -∗ kernel_data -∗
    pc_is (mword_of_int (KernelSyms.printk + 0x12c + 0) : mword 64) -∗
    (pa_stk sp0 23) ↦₈ (pk_ap s0v k) -∗
    pk_va sp0 m -∗
    (mword_of_int KernelSyms.panicking : mword 64) ↦₄{ dqm } pv -∗
    (mword_of_int KernelSyms.panicked : mword 64) ↦₄{ dqm2 } pkv -∗
    dev_inv γd γv -∗ uart_tx_own γd l -∗ uart_dlab_off γd -∗
    Rest -∗
    wp_next (CID0 := CID0) b pcur (fun (CID : CpuId) =>
      ∀ (mf : regfile) (bs : list (bv 8)),
      ⌜ (forall c : mword 5, is_cs_idx c = true -> c <> mword_of_int 9 ->
           mf !!! Regidx c = mc !!! Regidx c)
        /\ mf !!! Regidx (mword_of_int 9 : mword 5) = mword_of_int (Z.of_nat i + 2) ⌝ -∗
      sie_cap_gpr mf (K - 24)%nat b pcur -∗
      pc_is (mword_of_int (KernelSyms.printk + 0x78) : mword 64) -∗
      (pa_stk sp0 23) ↦₈ (pk_ap s0v (S k)) -∗
      pk_va sp0 m -∗
      (mword_of_int KernelSyms.panicking : mword 64) ↦₄{ dqm } pv -∗
      (mword_of_int KernelSyms.panicked : mword 64) ↦₄{ dqm2 } pkv -∗
      uart_tx_own γd (l ++ bs) -∗ uart_sent γd (l ++ bs) -∗
      Rest -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros sp0 s0v HK Hk Hi31 Hpv Hpkv Hs0 Hs6 Hs4.
    assert (HK14 : (14 <= K - 24)%nat) by lia.
    iIntros "Hcg #Htext #Hkdata Hpc Hap Hva Hpanicking Hpanicked #Hdev Htx #Hdlab HR Hcont".
    iApply (wp_printk_vaarg mc K 0x12c sp0 s0v k b pcur Hs0 eq_refl
              with "Hcg [] Hpc Hap [-]").
    { rewrite /pk_vaarg_instrs.
      iSplitR; [iApply (pki_12c with "Htext") | ].
      iSplitR; [iApply (pki_130 with "Htext") | ].
      iApply (pki_134 with "Htext"). }
    iIntros (CIDv Hstv V) "%Hv Hcg Hpc Hap".
    destruct Hv as (Hva5 & Hvs0 & Hvk).
    iApply (wp_cli_s_sconf (mword_of_int (KernelSyms.printk + 0x138)) (mword_of_int 12 : mword 5) (mword_of_int 0 : mword 6)
              (mword_of_int 0 : mword 64) V (K - 24)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc [] [-]").
    { iApply (pki_138 with "Htext"). }
    iIntros (CID1 Hst1) "Hcg Hpc".
    set (S0 := <[Regidx (mword_of_int 12 : mword 5) := regval_into_reg (mword_of_int 0 : mword 64)]> V).
    assert (Hpa13a : add_vec_int (mword_of_int (KernelSyms.printk + 0x138) : mword 64) 2 = mword_of_int (KernelSyms.printk + 0x13a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpa13a) in "Hpc".
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.printk + 0x13a)) a1_idx (mword_of_int 22 : mword 5)
              S0 (K - 24)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc [] [-]").
    { iApply (pki_13a with "Htext"). }
    iIntros (CID2 Hst2) "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (S1 := <[Regidx a1_idx := regval_into_reg (add_vec zero_reg (S0 !!! Regidx (mword_of_int 22 : mword 5)))]> S0).
    assert (HS1a1 : S1 !!! Regidx a1_idx = (mword_of_int 10 : mword 64)).
    { rewrite /S1 upd_eq. unfold regval_into_reg.
      rewrite /S0 upd_ne; [| reg_neq].
      rewrite (Hvk (mword_of_int 22 : mword 5) ltac:(mw_neq) ltac:(mw_neq)).
      rewrite Hs6. apply add_vec_zero_l. }
    assert (HS1a5 : S1 !!! Regidx a5_idx = pk_ap s0v k).
    { rewrite /S1 upd_ne; [| reg_neq]. rewrite /S0 upd_ne; [| reg_neq]. exact Hva5. }
    assert (Hpa13c : add_vec_int (mword_of_int (KernelSyms.printk + 0x13a) : mword 64) 2 = mword_of_int (KernelSyms.printk + 0x13c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpa13c) in "Hpc".
    (* the argument: a whole 8-byte slot this time *)
    iDestruct (pk_va_acc sp0 m k Hk with "Hva") as "[Hslot Hvacl]".
    assert (Hlda : add_vec (rget S1 a5_idx) (sign_extend' 64 (mword_of_int 0 : mword 12)) = pa_stk sp0 (7 - k)).
    { rgne. rewrite HS1a5.
      replace (sign_extend' 64 (mword_of_int 0 : mword 12)) with (mword_of_int 0 : mword 64)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite kv_addv_zero. apply pk_ap_slot. exact Hk. }
    iEval (rewrite -Hlda) in "Hslot".
    iApply (wp_cld_s_sconf (mword_of_int (KernelSyms.printk + 0x13c)) a0_idx a5_idx (mword_of_int 0 : mword 12)
              S1 (K - 24)%nat (pk_vararg m k) b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc [] Hslot [-]").
    { iApply (pki_13c with "Htext"). }
    iIntros (CID3 Hst3) "Hcg Hpc Hslot". iEval (rewrite Hlda) in "Hslot".
    iDestruct ("Hvacl" with "Hslot") as "Hva".
    set (S2 := <[Regidx a0_idx := regval_into_reg (pk_vararg m k)]> S1).
    assert (HS2a1 : S2 !!! Regidx a1_idx = (mword_of_int 10 : mword 64))
      by (rewrite /S2 upd_ne; [exact HS1a1 | reg_neq]).
    assert (Hpa13e : add_vec_int (mword_of_int (KernelSyms.printk + 0x13c) : mword 64) 2 = mword_of_int (KernelSyms.printk + 0x13e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpa13e) in "Hpc".
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.printk + 0x13e)) ra_idx (mword_of_int 2096684 : mword 21)
              S2 (K - 24)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(vm_compute; reflexivity)
              with "Hcg Hpc [] [-]").
    { iApply (pki_13e with "Htext"). }
    iIntros (CID4 Hst4) "Hcg Hpc".
    set (S3 := <[Regidx ra_idx := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.printk + 0x13e) : mword 64) 4)]> S2).
    assert (Htgtp : add_vec (mword_of_int (KernelSyms.printk + 0x13e) : mword 64) (sign_extend' 64 (mword_of_int 2096684 : mword 21)) = mword_of_int KernelSyms.printint) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgtp) in "Hpc".
    assert (HS3a1 : (10 <= uint (S3 !!! Regidx a1_idx) <= 16)%Z).
    { rewrite /S3 upd_ne; [| reg_neq]. rewrite HS2a1.
      rewrite (uint_moi_small 10 ltac:(change (2^64) with 18446744073709551616; lia)). lia. }
    iApply (wp_printint (CID0 := CID4) γd γv S3 (K - 24)%nat l pv pkv dqm dqm2 b pcur HK14 HS3a1 Hpv Hpkv
              with "Hcg Htext Hkdata Hpc Hpanicking Hpanicked Hdev Htx Hdlab [-]").
    iIntros (CID5 Hst5 mf bs) "Hcg Hpc %Hcs Hpanicking Hpanicked Htx #Hsent".
    destruct Hcs as [Hcs Hra].
    assert (Hret : ret_pc (S3 !!! Regidx ra_idx) = mword_of_int (KernelSyms.printk + 0x142))
      by (rewrite /S3 upd_eq; unfold ret_pc; apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hret) in "Hpc".
    (* +0x142 addiw s1,s4,2 : how far the directive advanced the scan *)
    assert (Hmfs4 : mf !!! Regidx (mword_of_int 20 : mword 5) = mword_of_int (Z.of_nat i)).
    { rewrite (callee_saved_lookup Hcs (mword_of_int 20 : mword 5) ltac:(vm_compute; reflexivity)).
      rewrite /S3 upd_ne; [| reg_neq]. rewrite /S2 upd_ne; [| reg_neq].
      rewrite /S1 upd_ne; [| reg_neq]. rewrite /S0 upd_ne; [| reg_neq]. 
      rewrite (Hvk (mword_of_int 20 : mword 5) ltac:(mw_neq) ltac:(mw_neq)). exact Hs4. }
    iApply (wp_addiw_s_sconf (mword_of_int (KernelSyms.printk + 0x142)) (mword_of_int 9 : mword 5) (mword_of_int 20 : mword 5) (mword_of_int 2 : mword 12)
              mf (K - 24)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc [] [-]").
    { iApply (pki_142 with "Htext"). }
    iIntros (CID6 Hst6) "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (T := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg (sign_extend' 64 (subrange_vec_dec
                 (add_vec (mf !!! Regidx (mword_of_int 20 : mword 5)) (sign_extend' 64 (mword_of_int 2 : mword 12))) 31 0))]> mf).
    assert (HTs1 : T !!! Regidx (mword_of_int 9 : mword 5) = mword_of_int (Z.of_nat i + 2)).
    { rewrite /T upd_eq. unfold regval_into_reg. rewrite Hmfs4.
      apply (addiw_lit (Z.of_nat i) 2 (sign_extend' 64 (mword_of_int 2 : mword 12))
               ltac:(apply bv_eq; vm_compute; reflexivity)
               ltac:(change (2^31) with 2147483648 in Hi31 |- *; lia)). }
    assert (Hpa146 : add_vec_int (mword_of_int (KernelSyms.printk + 0x142) : mword 64) 4 = mword_of_int (KernelSyms.printk + 0x146)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpa146) in "Hpc".
    (* +0x146 j 0x78 *)
    iApply (wp_cj_s_sconf (mword_of_int (KernelSyms.printk + 0x146)) (sign_extend' 21 (concat_vec (mword_of_int 1945 : mword 11) ('b"0")))
              T (K - 24)%nat b ltac:(vm_compute; reflexivity)
              with "Hcg Hpc [] [-]").
    { iApply (pki_146 with "Htext"). }
    iIntros (CID7 Hst7). iNext. iIntros "Hcg Hpc".
    assert (Htgt78 : add_vec (mword_of_int (KernelSyms.printk + 0x146) : mword 64) (sign_extend' 64 (sign_extend' 21 (concat_vec (mword_of_int 1945 : mword 11) ('b"0")))) = mword_of_int (KernelSyms.printk + 0x78)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgt78) in "Hpc".
    iSpecialize ("Hcont" $! CID7 with "[%]"); [wp_next_chain|].
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


  Lemma wp_printk_arm_llu `{CID0 : CpuId} (γd : uart_names) (γv : disk_names)
      (m mc : regfile) (K : nat) (k i : nat) (l : list (bv 8)) (pv pkv : mword 32)
      (dqm dqm2 : dfrac) (Rest : iProp Σ) (b : bool) (pcur : mword 64) :
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
    sie_cap_gpr mc (K - 24)%nat b pcur -∗
    kernel_text -∗ kernel_data -∗
    pc_is (mword_of_int (KernelSyms.printk + 0x148 + 0) : mword 64) -∗
    (pa_stk sp0 23) ↦₈ (pk_ap s0v k) -∗
    pk_va sp0 m -∗
    (mword_of_int KernelSyms.panicking : mword 64) ↦₄{ dqm } pv -∗
    (mword_of_int KernelSyms.panicked : mword 64) ↦₄{ dqm2 } pkv -∗
    dev_inv γd γv -∗ uart_tx_own γd l -∗ uart_dlab_off γd -∗
    Rest -∗
    wp_next (CID0 := CID0) b pcur (fun (CID : CpuId) =>
      ∀ (mf : regfile) (bs : list (bv 8)),
      ⌜ (forall c : mword 5, is_cs_idx c = true -> c <> mword_of_int 9 ->
           mf !!! Regidx c = mc !!! Regidx c)
        /\ mf !!! Regidx (mword_of_int 9 : mword 5) = mword_of_int (Z.of_nat i + 3) ⌝ -∗
      sie_cap_gpr mf (K - 24)%nat b pcur -∗
      pc_is (mword_of_int (KernelSyms.printk + 0x78) : mword 64) -∗
      (pa_stk sp0 23) ↦₈ (pk_ap s0v (S k)) -∗
      pk_va sp0 m -∗
      (mword_of_int KernelSyms.panicking : mword 64) ↦₄{ dqm } pv -∗
      (mword_of_int KernelSyms.panicked : mword 64) ↦₄{ dqm2 } pkv -∗
      uart_tx_own γd (l ++ bs) -∗ uart_sent γd (l ++ bs) -∗
      Rest -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros sp0 s0v HK Hk Hi31 Hpv Hpkv Hs0 Hs6 Hs4.
    assert (HK14 : (14 <= K - 24)%nat) by lia.
    iIntros "Hcg #Htext #Hkdata Hpc Hap Hva Hpanicking Hpanicked #Hdev Htx #Hdlab HR Hcont".
    iApply (wp_printk_vaarg mc K 0x148 sp0 s0v k b pcur Hs0 eq_refl
              with "Hcg [] Hpc Hap [-]").
    { rewrite /pk_vaarg_instrs.
      iSplitR; [iApply (pki_148 with "Htext") | ].
      iSplitR; [iApply (pki_14c with "Htext") | ].
      iApply (pki_150 with "Htext"). }
    iIntros (CIDv Hstv V) "%Hv Hcg Hpc Hap".
    destruct Hv as (Hva5 & Hvs0 & Hvk).
    iApply (wp_cli_s_sconf (mword_of_int (KernelSyms.printk + 0x154)) (mword_of_int 12 : mword 5) (mword_of_int 0 : mword 6)
              (mword_of_int 0 : mword 64) V (K - 24)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc [] [-]").
    { iApply (pki_154 with "Htext"). }
    iIntros (CID1 Hst1) "Hcg Hpc".
    set (S0 := <[Regidx (mword_of_int 12 : mword 5) := regval_into_reg (mword_of_int 0 : mword 64)]> V).
    assert (Hpa156 : add_vec_int (mword_of_int (KernelSyms.printk + 0x154) : mword 64) 2 = mword_of_int (KernelSyms.printk + 0x156)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpa156) in "Hpc".
    iApply (wp_cli_s_sconf (mword_of_int (KernelSyms.printk + 0x156)) a1_idx (mword_of_int 10 : mword 6)
              (mword_of_int 10 : mword 64) S0 (K - 24)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc [] [-]").
    { iApply (pki_156 with "Htext"). }
    iIntros (CID7 Hst7) "Hcg Hpc".
    set (S1 := <[Regidx a1_idx := regval_into_reg (mword_of_int 10 : mword 64)]> S0).
    assert (HS1a1 : S1 !!! Regidx a1_idx = (mword_of_int 10 : mword 64))
      by (rewrite /S1 upd_eq; reflexivity).
    assert (HS1a5 : S1 !!! Regidx a5_idx = pk_ap s0v k).
    { rewrite /S1 upd_ne; [| reg_neq]. rewrite /S0 upd_ne; [| reg_neq]. exact Hva5. }
    assert (Hpa158 : add_vec_int (mword_of_int (KernelSyms.printk + 0x156) : mword 64) 2 = mword_of_int (KernelSyms.printk + 0x158)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpa158) in "Hpc".
    (* the argument: a whole 8-byte slot this time *)
    iDestruct (pk_va_acc sp0 m k Hk with "Hva") as "[Hslot Hvacl]".
    assert (Hlda : add_vec (rget S1 a5_idx) (sign_extend' 64 (mword_of_int 0 : mword 12)) = pa_stk sp0 (7 - k)).
    { rgne. rewrite HS1a5.
      replace (sign_extend' 64 (mword_of_int 0 : mword 12)) with (mword_of_int 0 : mword 64)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite kv_addv_zero. apply pk_ap_slot. exact Hk. }
    iEval (rewrite -Hlda) in "Hslot".
    iApply (wp_cld_s_sconf (mword_of_int (KernelSyms.printk + 0x158)) a0_idx a5_idx (mword_of_int 0 : mword 12)
              S1 (K - 24)%nat (pk_vararg m k) b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc [] Hslot [-]").
    { iApply (pki_158 with "Htext"). }
    iIntros (CID2 Hst2) "Hcg Hpc Hslot". iEval (rewrite Hlda) in "Hslot".
    iDestruct ("Hvacl" with "Hslot") as "Hva".
    set (S2 := <[Regidx a0_idx := regval_into_reg (pk_vararg m k)]> S1).
    assert (HS2a1 : S2 !!! Regidx a1_idx = (mword_of_int 10 : mword 64))
      by (rewrite /S2 upd_ne; [exact HS1a1 | reg_neq]).
    assert (Hpa15a : add_vec_int (mword_of_int (KernelSyms.printk + 0x158) : mword 64) 2 = mword_of_int (KernelSyms.printk + 0x15a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpa15a) in "Hpc".
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.printk + 0x15a)) ra_idx (mword_of_int 2096656 : mword 21)
              S2 (K - 24)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(vm_compute; reflexivity)
              with "Hcg Hpc [] [-]").
    { iApply (pki_15a with "Htext"). }
    iIntros (CID3 Hst3) "Hcg Hpc".
    set (S3 := <[Regidx ra_idx := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.printk + 0x15a) : mword 64) 4)]> S2).
    assert (Htgtp : add_vec (mword_of_int (KernelSyms.printk + 0x15a) : mword 64) (sign_extend' 64 (mword_of_int 2096656 : mword 21)) = mword_of_int KernelSyms.printint) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgtp) in "Hpc".
    assert (HS3a1 : (10 <= uint (S3 !!! Regidx a1_idx) <= 16)%Z).
    { rewrite /S3 upd_ne; [| reg_neq]. rewrite HS2a1.
      rewrite (uint_moi_small 10 ltac:(change (2^64) with 18446744073709551616; lia)). lia. }
    iApply (wp_printint (CID0 := CID3) γd γv S3 (K - 24)%nat l pv pkv dqm dqm2 b pcur HK14 HS3a1 Hpv Hpkv
              with "Hcg Htext Hkdata Hpc Hpanicking Hpanicked Hdev Htx Hdlab [-]").
    iIntros (CID4 Hst4 mf bs) "Hcg Hpc %Hcs Hpanicking Hpanicked Htx #Hsent".
    destruct Hcs as [Hcs Hra].
    assert (Hret : ret_pc (S3 !!! Regidx ra_idx) = mword_of_int (KernelSyms.printk + 0x15e))
      by (rewrite /S3 upd_eq; unfold ret_pc; apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hret) in "Hpc".
    (* +0x15e addiw s1,s4,3 : how far the directive advanced the scan *)
    assert (Hmfs4 : mf !!! Regidx (mword_of_int 20 : mword 5) = mword_of_int (Z.of_nat i)).
    { rewrite (callee_saved_lookup Hcs (mword_of_int 20 : mword 5) ltac:(vm_compute; reflexivity)).
      rewrite /S3 upd_ne; [| reg_neq]. rewrite /S2 upd_ne; [| reg_neq].
      rewrite /S1 upd_ne; [| reg_neq]. rewrite /S0 upd_ne; [| reg_neq]. 
      rewrite (Hvk (mword_of_int 20 : mword 5) ltac:(mw_neq) ltac:(mw_neq)). exact Hs4. }
    iApply (wp_addiw_s_sconf (mword_of_int (KernelSyms.printk + 0x15e)) (mword_of_int 9 : mword 5) (mword_of_int 20 : mword 5) (mword_of_int 3 : mword 12)
              mf (K - 24)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc [] [-]").
    { iApply (pki_15e with "Htext"). }
    iIntros (CID5 Hst5) "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (T := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg (sign_extend' 64 (subrange_vec_dec
                 (add_vec (mf !!! Regidx (mword_of_int 20 : mword 5)) (sign_extend' 64 (mword_of_int 3 : mword 12))) 31 0))]> mf).
    assert (HTs1 : T !!! Regidx (mword_of_int 9 : mword 5) = mword_of_int (Z.of_nat i + 3)).
    { rewrite /T upd_eq. unfold regval_into_reg. rewrite Hmfs4.
      apply (addiw_lit (Z.of_nat i) 3 (sign_extend' 64 (mword_of_int 3 : mword 12))
               ltac:(apply bv_eq; vm_compute; reflexivity)
               ltac:(change (2^31) with 2147483648 in Hi31 |- *; lia)). }
    assert (Hpa162 : add_vec_int (mword_of_int (KernelSyms.printk + 0x15e) : mword 64) 4 = mword_of_int (KernelSyms.printk + 0x162)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpa162) in "Hpc".
    (* +0x162 j 0x78 *)
    iApply (wp_cj_s_sconf (mword_of_int (KernelSyms.printk + 0x162)) (sign_extend' 21 (concat_vec (mword_of_int 1931 : mword 11) ('b"0")))
              T (K - 24)%nat b ltac:(vm_compute; reflexivity)
              with "Hcg Hpc [] [-]").
    { iApply (pki_162 with "Htext"). }
    iIntros (CID6 Hst6). iNext. iIntros "Hcg Hpc".
    assert (Htgt78 : add_vec (mword_of_int (KernelSyms.printk + 0x162) : mword 64) (sign_extend' 64 (sign_extend' 21 (concat_vec (mword_of_int 1931 : mword 11) ('b"0")))) = mword_of_int (KernelSyms.printk + 0x78)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgt78) in "Hpc".
    iSpecialize ("Hcont" $! CID6 with "[%]"); [wp_next_chain|].
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


  Lemma wp_printk_arm_lx `{CID0 : CpuId} (γd : uart_names) (γv : disk_names)
      (m mc : regfile) (K : nat) (k i : nat) (l : list (bv 8)) (pv pkv : mword 32)
      (dqm dqm2 : dfrac) (Rest : iProp Σ) (b : bool) (pcur : mword 64) :
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
    sie_cap_gpr mc (K - 24)%nat b pcur -∗
    kernel_text -∗ kernel_data -∗
    pc_is (mword_of_int (KernelSyms.printk + 0x17e + 0) : mword 64) -∗
    (pa_stk sp0 23) ↦₈ (pk_ap s0v k) -∗
    pk_va sp0 m -∗
    (mword_of_int KernelSyms.panicking : mword 64) ↦₄{ dqm } pv -∗
    (mword_of_int KernelSyms.panicked : mword 64) ↦₄{ dqm2 } pkv -∗
    dev_inv γd γv -∗ uart_tx_own γd l -∗ uart_dlab_off γd -∗
    Rest -∗
    wp_next (CID0 := CID0) b pcur (fun (CID : CpuId) =>
      ∀ (mf : regfile) (bs : list (bv 8)),
      ⌜ (forall c : mword 5, is_cs_idx c = true -> c <> mword_of_int 9 ->
           mf !!! Regidx c = mc !!! Regidx c)
        /\ mf !!! Regidx (mword_of_int 9 : mword 5) = mword_of_int (Z.of_nat i + 2) ⌝ -∗
      sie_cap_gpr mf (K - 24)%nat b pcur -∗
      pc_is (mword_of_int (KernelSyms.printk + 0x78) : mword 64) -∗
      (pa_stk sp0 23) ↦₈ (pk_ap s0v (S k)) -∗
      pk_va sp0 m -∗
      (mword_of_int KernelSyms.panicking : mword 64) ↦₄{ dqm } pv -∗
      (mword_of_int KernelSyms.panicked : mword 64) ↦₄{ dqm2 } pkv -∗
      uart_tx_own γd (l ++ bs) -∗ uart_sent γd (l ++ bs) -∗
      Rest -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros sp0 s0v HK Hk Hi31 Hpv Hpkv Hs0 Hs6 Hs4.
    assert (HK14 : (14 <= K - 24)%nat) by lia.
    iIntros "Hcg #Htext #Hkdata Hpc Hap Hva Hpanicking Hpanicked #Hdev Htx #Hdlab HR Hcont".
    iApply (wp_printk_vaarg mc K 0x17e sp0 s0v k b pcur Hs0 eq_refl
              with "Hcg [] Hpc Hap [-]").
    { rewrite /pk_vaarg_instrs.
      iSplitR; [iApply (pki_17e with "Htext") | ].
      iSplitR; [iApply (pki_182 with "Htext") | ].
      iApply (pki_186 with "Htext"). }
    iIntros (CIDv Hstv V) "%Hv Hcg Hpc Hap".
    destruct Hv as (Hva5 & Hvs0 & Hvk).
    assert (Hpa18a : (mword_of_int (KernelSyms.printk + 0x17e + 12) : mword 64) = mword_of_int (KernelSyms.printk + 0x18a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpa18a) in "Hpc".
    iApply (wp_cli_s_sconf (mword_of_int (KernelSyms.printk + 0x18a)) a1_idx (mword_of_int 16 : mword 6)
              (mword_of_int 16 : mword 64) V (K - 24)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc [] [-]").
    { iApply (pki_18a with "Htext"). }
    iIntros (CID1 Hst1) "Hcg Hpc".
    set (S0 := <[Regidx a1_idx := regval_into_reg (mword_of_int 16 : mword 64)]> V).
    assert (HS0a1 : S0 !!! Regidx a1_idx = (mword_of_int 16 : mword 64))
      by (rewrite /S0 upd_eq; reflexivity).
    assert (HS0a5 : S0 !!! Regidx a5_idx = pk_ap s0v k).
    { rewrite /S0 upd_ne; [| reg_neq]. exact Hva5. }
    assert (Hpa18c : add_vec_int (mword_of_int (KernelSyms.printk + 0x18a) : mword 64) 2 = mword_of_int (KernelSyms.printk + 0x18c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpa18c) in "Hpc".
    (* the argument: a whole 8-byte slot this time *)
    iDestruct (pk_va_acc sp0 m k Hk with "Hva") as "[Hslot Hvacl]".
    assert (Hlda : add_vec (rget S0 a5_idx) (sign_extend' 64 (mword_of_int 0 : mword 12)) = pa_stk sp0 (7 - k)).
    { rgne. rewrite HS0a5.
      replace (sign_extend' 64 (mword_of_int 0 : mword 12)) with (mword_of_int 0 : mword 64)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite kv_addv_zero. apply pk_ap_slot. exact Hk. }
    iEval (rewrite -Hlda) in "Hslot".
    iApply (wp_cld_s_sconf (mword_of_int (KernelSyms.printk + 0x18c)) a0_idx a5_idx (mword_of_int 0 : mword 12)
              S0 (K - 24)%nat (pk_vararg m k) b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc [] Hslot [-]").
    { iApply (pki_18c with "Htext"). }
    iIntros (CID2 Hst2) "Hcg Hpc Hslot". iEval (rewrite Hlda) in "Hslot".
    iDestruct ("Hvacl" with "Hslot") as "Hva".
    set (S1 := <[Regidx a0_idx := regval_into_reg (pk_vararg m k)]> S0).
    assert (HS1a1 : S1 !!! Regidx a1_idx = (mword_of_int 16 : mword 64))
      by (rewrite /S1 upd_ne; [exact HS0a1 | reg_neq]).
    assert (Hpa18e : add_vec_int (mword_of_int (KernelSyms.printk + 0x18c) : mword 64) 2 = mword_of_int (KernelSyms.printk + 0x18e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpa18e) in "Hpc".
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.printk + 0x18e)) ra_idx (mword_of_int 2096604 : mword 21)
              S1 (K - 24)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(vm_compute; reflexivity)
              with "Hcg Hpc [] [-]").
    { iApply (pki_18e with "Htext"). }
    iIntros (CID3 Hst3) "Hcg Hpc".
    set (S2 := <[Regidx ra_idx := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.printk + 0x18e) : mword 64) 4)]> S1).
    assert (Htgtp : add_vec (mword_of_int (KernelSyms.printk + 0x18e) : mword 64) (sign_extend' 64 (mword_of_int 2096604 : mword 21)) = mword_of_int KernelSyms.printint) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgtp) in "Hpc".
    assert (HS2a1 : (10 <= uint (S2 !!! Regidx a1_idx) <= 16)%Z).
    { rewrite /S2 upd_ne; [| reg_neq]. rewrite HS1a1.
      rewrite (uint_moi_small 16 ltac:(change (2^64) with 18446744073709551616; lia)). lia. }
    iApply (wp_printint (CID0 := CID3) γd γv S2 (K - 24)%nat l pv pkv dqm dqm2 b pcur HK14 HS2a1 Hpv Hpkv
              with "Hcg Htext Hkdata Hpc Hpanicking Hpanicked Hdev Htx Hdlab [-]").
    iIntros (CID4 Hst4 mf bs) "Hcg Hpc %Hcs Hpanicking Hpanicked Htx #Hsent".
    destruct Hcs as [Hcs Hra].
    assert (Hret : ret_pc (S2 !!! Regidx ra_idx) = mword_of_int (KernelSyms.printk + 0x192))
      by (rewrite /S2 upd_eq; unfold ret_pc; apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hret) in "Hpc".
    (* +0x192 addiw s1,s4,2 : how far the directive advanced the scan *)
    assert (Hmfs4 : mf !!! Regidx (mword_of_int 20 : mword 5) = mword_of_int (Z.of_nat i)).
    { rewrite (callee_saved_lookup Hcs (mword_of_int 20 : mword 5) ltac:(vm_compute; reflexivity)).
      rewrite /S2 upd_ne; [| reg_neq]. rewrite /S1 upd_ne; [| reg_neq].
      rewrite /S0 upd_ne; [| reg_neq].
      rewrite (Hvk (mword_of_int 20 : mword 5) ltac:(mw_neq) ltac:(mw_neq)). exact Hs4. }
    iApply (wp_addiw_s_sconf (mword_of_int (KernelSyms.printk + 0x192)) (mword_of_int 9 : mword 5) (mword_of_int 20 : mword 5) (mword_of_int 2 : mword 12)
              mf (K - 24)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc [] [-]").
    { iApply (pki_192 with "Htext"). }
    iIntros (CID5 Hst5) "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (T := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg (sign_extend' 64 (subrange_vec_dec
                 (add_vec (mf !!! Regidx (mword_of_int 20 : mword 5)) (sign_extend' 64 (mword_of_int 2 : mword 12))) 31 0))]> mf).
    assert (HTs1 : T !!! Regidx (mword_of_int 9 : mword 5) = mword_of_int (Z.of_nat i + 2)).
    { rewrite /T upd_eq. unfold regval_into_reg. rewrite Hmfs4.
      apply (addiw_lit (Z.of_nat i) 2 (sign_extend' 64 (mword_of_int 2 : mword 12))
               ltac:(apply bv_eq; vm_compute; reflexivity)
               ltac:(change (2^31) with 2147483648 in Hi31 |- *; lia)). }
    assert (Hpa196 : add_vec_int (mword_of_int (KernelSyms.printk + 0x192) : mword 64) 4 = mword_of_int (KernelSyms.printk + 0x196)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpa196) in "Hpc".
    (* +0x196 j 0x78 *)
    iApply (wp_cj_s_sconf (mword_of_int (KernelSyms.printk + 0x196)) (sign_extend' 21 (concat_vec (mword_of_int 1905 : mword 11) ('b"0")))
              T (K - 24)%nat b ltac:(vm_compute; reflexivity)
              with "Hcg Hpc [] [-]").
    { iApply (pki_196 with "Htext"). }
    iIntros (CID6 Hst6). iNext. iIntros "Hcg Hpc".
    assert (Htgt78 : add_vec (mword_of_int (KernelSyms.printk + 0x196) : mword 64) (sign_extend' 64 (sign_extend' 21 (concat_vec (mword_of_int 1905 : mword 11) ('b"0")))) = mword_of_int (KernelSyms.printk + 0x78)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgt78) in "Hpc".
    iSpecialize ("Hcont" $! CID6 with "[%]"); [wp_next_chain|].
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


  Lemma wp_printk_arm_llx `{CID0 : CpuId} (γd : uart_names) (γv : disk_names)
      (m mc : regfile) (K : nat) (k i : nat) (l : list (bv 8)) (pv pkv : mword 32)
      (dqm dqm2 : dfrac) (Rest : iProp Σ) (b : bool) (pcur : mword 64) :
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
    sie_cap_gpr mc (K - 24)%nat b pcur -∗
    kernel_text -∗ kernel_data -∗
    pc_is (mword_of_int (KernelSyms.printk + 0x198 + 0) : mword 64) -∗
    (pa_stk sp0 23) ↦₈ (pk_ap s0v k) -∗
    pk_va sp0 m -∗
    (mword_of_int KernelSyms.panicking : mword 64) ↦₄{ dqm } pv -∗
    (mword_of_int KernelSyms.panicked : mword 64) ↦₄{ dqm2 } pkv -∗
    dev_inv γd γv -∗ uart_tx_own γd l -∗ uart_dlab_off γd -∗
    Rest -∗
    wp_next (CID0 := CID0) b pcur (fun (CID : CpuId) =>
      ∀ (mf : regfile) (bs : list (bv 8)),
      ⌜ (forall c : mword 5, is_cs_idx c = true -> c <> mword_of_int 9 ->
           mf !!! Regidx c = mc !!! Regidx c)
        /\ mf !!! Regidx (mword_of_int 9 : mword 5) = mword_of_int (Z.of_nat i + 3) ⌝ -∗
      sie_cap_gpr mf (K - 24)%nat b pcur -∗
      pc_is (mword_of_int (KernelSyms.printk + 0x78) : mword 64) -∗
      (pa_stk sp0 23) ↦₈ (pk_ap s0v (S k)) -∗
      pk_va sp0 m -∗
      (mword_of_int KernelSyms.panicking : mword 64) ↦₄{ dqm } pv -∗
      (mword_of_int KernelSyms.panicked : mword 64) ↦₄{ dqm2 } pkv -∗
      uart_tx_own γd (l ++ bs) -∗ uart_sent γd (l ++ bs) -∗
      Rest -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros sp0 s0v HK Hk Hi31 Hpv Hpkv Hs0 Hs6 Hs4.
    assert (HK14 : (14 <= K - 24)%nat) by lia.
    iIntros "Hcg #Htext #Hkdata Hpc Hap Hva Hpanicking Hpanicked #Hdev Htx #Hdlab HR Hcont".
    iApply (wp_printk_vaarg mc K 0x198 sp0 s0v k b pcur Hs0 eq_refl
              with "Hcg [] Hpc Hap [-]").
    { rewrite /pk_vaarg_instrs.
      iSplitR; [iApply (pki_198 with "Htext") | ].
      iSplitR; [iApply (pki_19c with "Htext") | ].
      iApply (pki_1a0 with "Htext"). }
    iIntros (CIDv Hstv V) "%Hv Hcg Hpc Hap".
    destruct Hv as (Hva5 & Hvs0 & Hvk).
    iApply (wp_cli_s_sconf (mword_of_int (KernelSyms.printk + 0x1a4)) (mword_of_int 12 : mword 5) (mword_of_int 0 : mword 6)
              (mword_of_int 0 : mword 64) V (K - 24)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc [] [-]").
    { iApply (pki_1a4 with "Htext"). }
    iIntros (CID1 Hst1) "Hcg Hpc".
    set (S0 := <[Regidx (mword_of_int 12 : mword 5) := regval_into_reg (mword_of_int 0 : mword 64)]> V).
    assert (Hpa1a6 : add_vec_int (mword_of_int (KernelSyms.printk + 0x1a4) : mword 64) 2 = mword_of_int (KernelSyms.printk + 0x1a6)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpa1a6) in "Hpc".
    iApply (wp_cli_s_sconf (mword_of_int (KernelSyms.printk + 0x1a6)) a1_idx (mword_of_int 16 : mword 6)
              (mword_of_int 16 : mword 64) S0 (K - 24)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc [] [-]").
    { iApply (pki_1a6 with "Htext"). }
    iIntros (CID2 Hst2) "Hcg Hpc".
    set (S1 := <[Regidx a1_idx := regval_into_reg (mword_of_int 16 : mword 64)]> S0).
    assert (HS1a1 : S1 !!! Regidx a1_idx = (mword_of_int 16 : mword 64))
      by (rewrite /S1 upd_eq; reflexivity).
    assert (HS1a5 : S1 !!! Regidx a5_idx = pk_ap s0v k).
    { rewrite /S1 upd_ne; [| reg_neq]. rewrite /S0 upd_ne; [| reg_neq]. exact Hva5. }
    assert (Hpa1a8 : add_vec_int (mword_of_int (KernelSyms.printk + 0x1a6) : mword 64) 2 = mword_of_int (KernelSyms.printk + 0x1a8)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpa1a8) in "Hpc".
    (* the argument: a whole 8-byte slot this time *)
    iDestruct (pk_va_acc sp0 m k Hk with "Hva") as "[Hslot Hvacl]".
    assert (Hlda : add_vec (rget S1 a5_idx) (sign_extend' 64 (mword_of_int 0 : mword 12)) = pa_stk sp0 (7 - k)).
    { rgne. rewrite HS1a5.
      replace (sign_extend' 64 (mword_of_int 0 : mword 12)) with (mword_of_int 0 : mword 64)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite kv_addv_zero. apply pk_ap_slot. exact Hk. }
    iEval (rewrite -Hlda) in "Hslot".
    iApply (wp_cld_s_sconf (mword_of_int (KernelSyms.printk + 0x1a8)) a0_idx a5_idx (mword_of_int 0 : mword 12)
              S1 (K - 24)%nat (pk_vararg m k) b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc [] Hslot [-]").
    { iApply (pki_1a8 with "Htext"). }
    iIntros (CID3 Hst3) "Hcg Hpc Hslot". iEval (rewrite Hlda) in "Hslot".
    iDestruct ("Hvacl" with "Hslot") as "Hva".
    set (S2 := <[Regidx a0_idx := regval_into_reg (pk_vararg m k)]> S1).
    assert (HS2a1 : S2 !!! Regidx a1_idx = (mword_of_int 16 : mword 64))
      by (rewrite /S2 upd_ne; [exact HS1a1 | reg_neq]).
    assert (Hpa1aa : add_vec_int (mword_of_int (KernelSyms.printk + 0x1a8) : mword 64) 2 = mword_of_int (KernelSyms.printk + 0x1aa)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpa1aa) in "Hpc".
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.printk + 0x1aa)) ra_idx (mword_of_int 2096576 : mword 21)
              S2 (K - 24)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(vm_compute; reflexivity)
              with "Hcg Hpc [] [-]").
    { iApply (pki_1aa with "Htext"). }
    iIntros (CID4 Hst4) "Hcg Hpc".
    set (S3 := <[Regidx ra_idx := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.printk + 0x1aa) : mword 64) 4)]> S2).
    assert (Htgtp : add_vec (mword_of_int (KernelSyms.printk + 0x1aa) : mword 64) (sign_extend' 64 (mword_of_int 2096576 : mword 21)) = mword_of_int KernelSyms.printint) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgtp) in "Hpc".
    assert (HS3a1 : (10 <= uint (S3 !!! Regidx a1_idx) <= 16)%Z).
    { rewrite /S3 upd_ne; [| reg_neq]. rewrite HS2a1.
      rewrite (uint_moi_small 16 ltac:(change (2^64) with 18446744073709551616; lia)). lia. }
    iApply (wp_printint (CID0 := CID4) γd γv S3 (K - 24)%nat l pv pkv dqm dqm2 b pcur HK14 HS3a1 Hpv Hpkv
              with "Hcg Htext Hkdata Hpc Hpanicking Hpanicked Hdev Htx Hdlab [-]").
    iIntros (CID5 Hst5 mf bs) "Hcg Hpc %Hcs Hpanicking Hpanicked Htx #Hsent".
    destruct Hcs as [Hcs Hra].
    assert (Hret : ret_pc (S3 !!! Regidx ra_idx) = mword_of_int (KernelSyms.printk + 0x1ae))
      by (rewrite /S3 upd_eq; unfold ret_pc; apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hret) in "Hpc".
    (* +0x1ae addiw s1,s4,3 : how far the directive advanced the scan *)
    assert (Hmfs4 : mf !!! Regidx (mword_of_int 20 : mword 5) = mword_of_int (Z.of_nat i)).
    { rewrite (callee_saved_lookup Hcs (mword_of_int 20 : mword 5) ltac:(vm_compute; reflexivity)).
      rewrite /S3 upd_ne; [| reg_neq]. rewrite /S2 upd_ne; [| reg_neq].
      rewrite /S1 upd_ne; [| reg_neq]. rewrite /S0 upd_ne; [| reg_neq]. 
      rewrite (Hvk (mword_of_int 20 : mword 5) ltac:(mw_neq) ltac:(mw_neq)). exact Hs4. }
    iApply (wp_addiw_s_sconf (mword_of_int (KernelSyms.printk + 0x1ae)) (mword_of_int 9 : mword 5) (mword_of_int 20 : mword 5) (mword_of_int 3 : mword 12)
              mf (K - 24)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc [] [-]").
    { iApply (pki_1ae with "Htext"). }
    iIntros (CID6 Hst6) "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (T := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg (sign_extend' 64 (subrange_vec_dec
                 (add_vec (mf !!! Regidx (mword_of_int 20 : mword 5)) (sign_extend' 64 (mword_of_int 3 : mword 12))) 31 0))]> mf).
    assert (HTs1 : T !!! Regidx (mword_of_int 9 : mword 5) = mword_of_int (Z.of_nat i + 3)).
    { rewrite /T upd_eq. unfold regval_into_reg. rewrite Hmfs4.
      apply (addiw_lit (Z.of_nat i) 3 (sign_extend' 64 (mword_of_int 3 : mword 12))
               ltac:(apply bv_eq; vm_compute; reflexivity)
               ltac:(change (2^31) with 2147483648 in Hi31 |- *; lia)). }
    assert (Hpa1b2 : add_vec_int (mword_of_int (KernelSyms.printk + 0x1ae) : mword 64) 4 = mword_of_int (KernelSyms.printk + 0x1b2)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpa1b2) in "Hpc".
    (* +0x1b2 j 0x78 *)
    iApply (wp_cj_s_sconf (mword_of_int (KernelSyms.printk + 0x1b2)) (sign_extend' 21 (concat_vec (mword_of_int 1891 : mword 11) ('b"0")))
              T (K - 24)%nat b ltac:(vm_compute; reflexivity)
              with "Hcg Hpc [] [-]").
    { iApply (pki_1b2 with "Htext"). }
    iIntros (CID7 Hst7). iNext. iIntros "Hcg Hpc".
    assert (Htgt78 : add_vec (mword_of_int (KernelSyms.printk + 0x1b2) : mword 64) (sign_extend' 64 (sign_extend' 21 (concat_vec (mword_of_int 1891 : mword 11) ('b"0")))) = mword_of_int (KernelSyms.printk + 0x78)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgt78) in "Hpc".
    iSpecialize ("Hcont" $! CID7 with "[%]"); [wp_next_chain|].
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


  Lemma wp_printk_arm_u `{CID0 : CpuId} (γd : uart_names) (γv : disk_names)
      (m mc : regfile) (K : nat) (k : nat) (l : list (bv 8)) (pv pkv : mword 32)
      (dqm dqm2 : dfrac) (Rest : iProp Σ) (b : bool) (pcur : mword 64) :
    let sp0 := m !!! Regidx csp_rs1 in
    let s0v := add_vec sp0 (sign_extend' 64 (mword_of_int (-64) : mword 12)) in
    (38 <= K)%nat ->
    (k < 7)%nat ->
    eq_vec (sign_extend' 64 pv) zero_reg = false ->
    neq_vec (sign_extend' 64 pkv) zero_reg = false ->
    mc !!! Regidx s0_idx = s0v ->
    mc !!! Regidx (mword_of_int 22 : mword 5) = (mword_of_int 10 : mword 64) ->
    sie_cap_gpr mc (K - 24)%nat b pcur -∗
    kernel_text -∗ kernel_data -∗
    pc_is (mword_of_int (KernelSyms.printk + 0x112 + 0) : mword 64) -∗
    (pa_stk sp0 23) ↦₈ (pk_ap s0v k) -∗
    pk_va sp0 m -∗
    (mword_of_int KernelSyms.panicking : mword 64) ↦₄{ dqm } pv -∗
    (mword_of_int KernelSyms.panicked : mword 64) ↦₄{ dqm2 } pkv -∗
    dev_inv γd γv -∗ uart_tx_own γd l -∗ uart_dlab_off γd -∗
    Rest -∗
    wp_next (CID0 := CID0) b pcur (fun (CID : CpuId) =>
      ∀ (mf : regfile) (bs : list (bv 8)),
      ⌜ forall c : mword 5, is_cs_idx c = true -> mf !!! Regidx c = mc !!! Regidx c ⌝ -∗
      sie_cap_gpr mf (K - 24)%nat b pcur -∗
      pc_is (mword_of_int (KernelSyms.printk + 0x78) : mword 64) -∗
      (pa_stk sp0 23) ↦₈ (pk_ap s0v (S k)) -∗
      pk_va sp0 m -∗
      (mword_of_int KernelSyms.panicking : mword 64) ↦₄{ dqm } pv -∗
      (mword_of_int KernelSyms.panicked : mword 64) ↦₄{ dqm2 } pkv -∗
      uart_tx_own γd (l ++ bs) -∗ uart_sent γd (l ++ bs) -∗
      Rest -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros sp0 s0v HK Hk Hpv Hpkv Hs0 Hs6.
    assert (HK14 : (14 <= K - 24)%nat) by lia.
    iIntros "Hcg #Htext #Hkdata Hpc Hap Hva Hpanicking Hpanicked #Hdev Htx #Hdlab HR Hcont".
    iApply (wp_printk_vaarg mc K 0x112 sp0 s0v k b pcur Hs0 eq_refl
              with "Hcg [] Hpc Hap [-]").
    { rewrite /pk_vaarg_instrs.
      iSplitR; [iApply (pki_112 with "Htext") | ].
      iSplitR; [iApply (pki_116 with "Htext") | ].
      iApply (pki_11a with "Htext"). }
    iIntros (CIDv Hstv V) "%Hv Hcg Hpc Hap".
    destruct Hv as (Hva5 & Hvs0 & Hvk).
    iApply (wp_cli_s_sconf (mword_of_int (KernelSyms.printk + 0x11e)) (mword_of_int 12 : mword 5) (mword_of_int 0 : mword 6)
              (mword_of_int 0 : mword 64) V (K - 24)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc [] [-]").
    { iApply (pki_11e with "Htext"). }
    iIntros (CID1 Hst1) "Hcg Hpc".
    set (S0 := <[Regidx (mword_of_int 12 : mword 5) := regval_into_reg (mword_of_int 0 : mword 64)]> V).
    assert (Hpa120 : add_vec_int (mword_of_int (KernelSyms.printk + 0x11e) : mword 64) 2 = mword_of_int (KernelSyms.printk + 0x120)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpa120) in "Hpc".
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.printk + 0x120)) a1_idx (mword_of_int 22 : mword 5)
              S0 (K - 24)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc [] [-]").
    { iApply (pki_120 with "Htext"). }
    iIntros (CID2 Hst2) "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (S1 := <[Regidx a1_idx := regval_into_reg (add_vec zero_reg (S0 !!! Regidx (mword_of_int 22 : mword 5)))]> S0).
    assert (HS1a1 : S1 !!! Regidx a1_idx = (mword_of_int 10 : mword 64)).
    { rewrite /S1 upd_eq. unfold regval_into_reg.
      rewrite /S0 upd_ne; [| reg_neq].
      rewrite (Hvk (mword_of_int 22 : mword 5) ltac:(mw_neq) ltac:(mw_neq)).
      rewrite Hs6. apply add_vec_zero_l. }
    assert (HS1a5 : S1 !!! Regidx a5_idx = pk_ap s0v k).
    { rewrite /S1 upd_ne; [| reg_neq]. rewrite /S0 upd_ne; [| reg_neq]. exact Hva5. }
    assert (Hpa122 : add_vec_int (mword_of_int (KernelSyms.printk + 0x120) : mword 64) 2 = mword_of_int (KernelSyms.printk + 0x122)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpa122) in "Hpc".
    (* the argument: the LOW half of the slot, read unsigned *)
    iDestruct (pk_va_acc sp0 m k Hk with "Hva") as "[Hslot Hvacl]".
    iDestruct (word_pointsto_aligned_p with "Hslot") as %Halv.
    iDestruct (word_pointsto_split4 with "Hslot") as "[Hlo Hhi]".
    iEval (rewrite -/(pk_lo m k)) in "Hlo".
    assert (Hlwa : add_vec (rget S1 a5_idx) (sign_extend' 64 (mword_of_int 0 : mword 12)) = pa_stk sp0 (7 - k)).
    { rgne. rewrite HS1a5.
      replace (sign_extend' 64 (mword_of_int 0 : mword 12)) with (mword_of_int 0 : mword 64)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite kv_addv_zero. apply pk_ap_slot. exact Hk. }
    iEval (rewrite -Hlwa) in "Hlo".
    iApply (wp_lwu_s_sconf (mword_of_int (KernelSyms.printk + 0x122)) a0_idx a5_idx (mword_of_int 0 : mword 12)
              S1 (K - 24)%nat (pk_lo m k) b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc [] Hlo [-]").
    { iApply (pki_122 with "Htext"). }
    iIntros (CID3 Hst3) "Hcg Hpc Hlo". iEval (rewrite Hlwa) in "Hlo".
    iDestruct (word_pointsto_join4 _ _ _ _ Halv with "Hlo Hhi") as "Hslot".
    rewrite word_of_words_id.
    iDestruct ("Hvacl" with "Hslot") as "Hva".
    set (S2 := <[Regidx a0_idx := regval_into_reg (zero_extend' 64 (pk_lo m k))]> S1).
    assert (HS2a1 : S2 !!! Regidx a1_idx = (mword_of_int 10 : mword 64))
      by (rewrite /S2 upd_ne; [exact HS1a1 | reg_neq]).
    assert (Hpa126 : add_vec_int (mword_of_int (KernelSyms.printk + 0x122) : mword 64) 4 = mword_of_int (KernelSyms.printk + 0x126)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpa126) in "Hpc".
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.printk + 0x126)) ra_idx (mword_of_int 2096708 : mword 21)
              S2 (K - 24)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(vm_compute; reflexivity)
              with "Hcg Hpc [] [-]").
    { iApply (pki_126 with "Htext"). }
    iIntros (CID4 Hst4) "Hcg Hpc".
    set (S3 := <[Regidx ra_idx := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.printk + 0x126) : mword 64) 4)]> S2).
    assert (Htgtp : add_vec (mword_of_int (KernelSyms.printk + 0x126) : mword 64) (sign_extend' 64 (mword_of_int 2096708 : mword 21)) = mword_of_int KernelSyms.printint) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgtp) in "Hpc".
    assert (HS3a1 : (10 <= uint (S3 !!! Regidx a1_idx) <= 16)%Z).
    { rewrite /S3 upd_ne; [| reg_neq]. rewrite HS2a1.
      rewrite (uint_moi_small 10 ltac:(change (2^64) with 18446744073709551616; lia)). lia. }
    iApply (wp_printint (CID0 := CID4) γd γv S3 (K - 24)%nat l pv pkv dqm dqm2 b pcur HK14 HS3a1 Hpv Hpkv
              with "Hcg Htext Hkdata Hpc Hpanicking Hpanicked Hdev Htx Hdlab [-]").
    iIntros (CID5 Hst5 mf bs) "Hcg Hpc %Hcs Hpanicking Hpanicked Htx #Hsent".
    destruct Hcs as [Hcs Hra].
    assert (Hret : ret_pc (S3 !!! Regidx ra_idx) = mword_of_int (KernelSyms.printk + 0x12a))
      by (rewrite /S3 upd_eq; unfold ret_pc; apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hret) in "Hpc".
    iApply (wp_cj_s_sconf (mword_of_int (KernelSyms.printk + 0x12a)) (sign_extend' 21 (concat_vec (mword_of_int 1959 : mword 11) ('b"0")))
              mf (K - 24)%nat b ltac:(vm_compute; reflexivity)
              with "Hcg Hpc [] [-]").
    { iApply (pki_12a with "Htext"). }
    iIntros (CID6 Hst6). iNext. iIntros "Hcg Hpc".
    assert (Htgt78 : add_vec (mword_of_int (KernelSyms.printk + 0x12a) : mword 64) (sign_extend' 64 (sign_extend' 21 (concat_vec (mword_of_int 1959 : mword 11) ('b"0")))) = mword_of_int (KernelSyms.printk + 0x78)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgt78) in "Hpc".
    iSpecialize ("Hcont" $! CID6 with "[%]"); [wp_next_chain|].
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


  Lemma wp_printk_arm_x `{CID0 : CpuId} (γd : uart_names) (γv : disk_names)
      (m mc : regfile) (K : nat) (k : nat) (l : list (bv 8)) (pv pkv : mword 32)
      (dqm dqm2 : dfrac) (Rest : iProp Σ) (b : bool) (pcur : mword 64) :
    let sp0 := m !!! Regidx csp_rs1 in
    let s0v := add_vec sp0 (sign_extend' 64 (mword_of_int (-64) : mword 12)) in
    (38 <= K)%nat ->
    (k < 7)%nat ->
    eq_vec (sign_extend' 64 pv) zero_reg = false ->
    neq_vec (sign_extend' 64 pkv) zero_reg = false ->
    mc !!! Regidx s0_idx = s0v ->
    mc !!! Regidx (mword_of_int 22 : mword 5) = (mword_of_int 10 : mword 64) ->
    sie_cap_gpr mc (K - 24)%nat b pcur -∗
    kernel_text -∗ kernel_data -∗
    pc_is (mword_of_int (KernelSyms.printk + 0x164 + 0) : mword 64) -∗
    (pa_stk sp0 23) ↦₈ (pk_ap s0v k) -∗
    pk_va sp0 m -∗
    (mword_of_int KernelSyms.panicking : mword 64) ↦₄{ dqm } pv -∗
    (mword_of_int KernelSyms.panicked : mword 64) ↦₄{ dqm2 } pkv -∗
    dev_inv γd γv -∗ uart_tx_own γd l -∗ uart_dlab_off γd -∗
    Rest -∗
    wp_next (CID0 := CID0) b pcur (fun (CID : CpuId) =>
      ∀ (mf : regfile) (bs : list (bv 8)),
      ⌜ forall c : mword 5, is_cs_idx c = true -> mf !!! Regidx c = mc !!! Regidx c ⌝ -∗
      sie_cap_gpr mf (K - 24)%nat b pcur -∗
      pc_is (mword_of_int (KernelSyms.printk + 0x78) : mword 64) -∗
      (pa_stk sp0 23) ↦₈ (pk_ap s0v (S k)) -∗
      pk_va sp0 m -∗
      (mword_of_int KernelSyms.panicking : mword 64) ↦₄{ dqm } pv -∗
      (mword_of_int KernelSyms.panicked : mword 64) ↦₄{ dqm2 } pkv -∗
      uart_tx_own γd (l ++ bs) -∗ uart_sent γd (l ++ bs) -∗
      Rest -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros sp0 s0v HK Hk Hpv Hpkv Hs0 Hs6.
    assert (HK14 : (14 <= K - 24)%nat) by lia.
    iIntros "Hcg #Htext #Hkdata Hpc Hap Hva Hpanicking Hpanicked #Hdev Htx #Hdlab HR Hcont".
    iApply (wp_printk_vaarg mc K 0x164 sp0 s0v k b pcur Hs0 eq_refl
              with "Hcg [] Hpc Hap [-]").
    { rewrite /pk_vaarg_instrs.
      iSplitR; [iApply (pki_164 with "Htext") | ].
      iSplitR; [iApply (pki_168 with "Htext") | ].
      iApply (pki_16c with "Htext"). }
    iIntros (CIDv Hstv V) "%Hv Hcg Hpc Hap".
    destruct Hv as (Hva5 & Hvs0 & Hvk).
    iApply (wp_cli_s_sconf (mword_of_int (KernelSyms.printk + 0x170)) (mword_of_int 12 : mword 5) (mword_of_int 0 : mword 6)
              (mword_of_int 0 : mword 64) V (K - 24)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc [] [-]").
    { iApply (pki_170 with "Htext"). }
    iIntros (CID1 Hst1) "Hcg Hpc".
    set (S0 := <[Regidx (mword_of_int 12 : mword 5) := regval_into_reg (mword_of_int 0 : mword 64)]> V).
    assert (Hpa172 : add_vec_int (mword_of_int (KernelSyms.printk + 0x170) : mword 64) 2 = mword_of_int (KernelSyms.printk + 0x172)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpa172) in "Hpc".
    iApply (wp_cli_s_sconf (mword_of_int (KernelSyms.printk + 0x172)) a1_idx (mword_of_int 16 : mword 6)
              (mword_of_int 16 : mword 64) S0 (K - 24)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc [] [-]").
    { iApply (pki_172 with "Htext"). }
    iIntros (CID2 Hst2) "Hcg Hpc".
    set (S1 := <[Regidx a1_idx := regval_into_reg (mword_of_int 16 : mword 64)]> S0).
    assert (HS1a1 : S1 !!! Regidx a1_idx = (mword_of_int 16 : mword 64))
      by (rewrite /S1 upd_eq; reflexivity).
    assert (HS1a5 : S1 !!! Regidx a5_idx = pk_ap s0v k).
    { rewrite /S1 upd_ne; [| reg_neq]. rewrite /S0 upd_ne; [| reg_neq]. exact Hva5. }
    assert (Hpa174 : add_vec_int (mword_of_int (KernelSyms.printk + 0x172) : mword 64) 2 = mword_of_int (KernelSyms.printk + 0x174)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpa174) in "Hpc".
    (* the argument: the LOW half of the slot, read unsigned *)
    iDestruct (pk_va_acc sp0 m k Hk with "Hva") as "[Hslot Hvacl]".
    iDestruct (word_pointsto_aligned_p with "Hslot") as %Halv.
    iDestruct (word_pointsto_split4 with "Hslot") as "[Hlo Hhi]".
    iEval (rewrite -/(pk_lo m k)) in "Hlo".
    assert (Hlwa : add_vec (rget S1 a5_idx) (sign_extend' 64 (mword_of_int 0 : mword 12)) = pa_stk sp0 (7 - k)).
    { rgne. rewrite HS1a5.
      replace (sign_extend' 64 (mword_of_int 0 : mword 12)) with (mword_of_int 0 : mword 64)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite kv_addv_zero. apply pk_ap_slot. exact Hk. }
    iEval (rewrite -Hlwa) in "Hlo".
    iApply (wp_lwu_s_sconf (mword_of_int (KernelSyms.printk + 0x174)) a0_idx a5_idx (mword_of_int 0 : mword 12)
              S1 (K - 24)%nat (pk_lo m k) b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc [] Hlo [-]").
    { iApply (pki_174 with "Htext"). }
    iIntros (CID3 Hst3) "Hcg Hpc Hlo". iEval (rewrite Hlwa) in "Hlo".
    iDestruct (word_pointsto_join4 _ _ _ _ Halv with "Hlo Hhi") as "Hslot".
    rewrite word_of_words_id.
    iDestruct ("Hvacl" with "Hslot") as "Hva".
    set (S2 := <[Regidx a0_idx := regval_into_reg (zero_extend' 64 (pk_lo m k))]> S1).
    assert (HS2a1 : S2 !!! Regidx a1_idx = (mword_of_int 16 : mword 64))
      by (rewrite /S2 upd_ne; [exact HS1a1 | reg_neq]).
    assert (Hpa178 : add_vec_int (mword_of_int (KernelSyms.printk + 0x174) : mword 64) 4 = mword_of_int (KernelSyms.printk + 0x178)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpa178) in "Hpc".
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.printk + 0x178)) ra_idx (mword_of_int 2096626 : mword 21)
              S2 (K - 24)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(vm_compute; reflexivity)
              with "Hcg Hpc [] [-]").
    { iApply (pki_178 with "Htext"). }
    iIntros (CID4 Hst4) "Hcg Hpc".
    set (S3 := <[Regidx ra_idx := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.printk + 0x178) : mword 64) 4)]> S2).
    assert (Htgtp : add_vec (mword_of_int (KernelSyms.printk + 0x178) : mword 64) (sign_extend' 64 (mword_of_int 2096626 : mword 21)) = mword_of_int KernelSyms.printint) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgtp) in "Hpc".
    assert (HS3a1 : (10 <= uint (S3 !!! Regidx a1_idx) <= 16)%Z).
    { rewrite /S3 upd_ne; [| reg_neq]. rewrite HS2a1.
      rewrite (uint_moi_small 16 ltac:(change (2^64) with 18446744073709551616; lia)). lia. }
    iApply (wp_printint (CID0 := CID4) γd γv S3 (K - 24)%nat l pv pkv dqm dqm2 b pcur HK14 HS3a1 Hpv Hpkv
              with "Hcg Htext Hkdata Hpc Hpanicking Hpanicked Hdev Htx Hdlab [-]").
    iIntros (CID5 Hst5 mf bs) "Hcg Hpc %Hcs Hpanicking Hpanicked Htx #Hsent".
    destruct Hcs as [Hcs Hra].
    assert (Hret : ret_pc (S3 !!! Regidx ra_idx) = mword_of_int (KernelSyms.printk + 0x17c))
      by (rewrite /S3 upd_eq; unfold ret_pc; apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hret) in "Hpc".
    iApply (wp_cj_s_sconf (mword_of_int (KernelSyms.printk + 0x17c)) (sign_extend' 21 (concat_vec (mword_of_int 1918 : mword 11) ('b"0")))
              mf (K - 24)%nat b ltac:(vm_compute; reflexivity)
              with "Hcg Hpc [] [-]").
    { iApply (pki_17c with "Htext"). }
    iIntros (CID6 Hst6). iNext. iIntros "Hcg Hpc".
    assert (Htgt78 : add_vec (mword_of_int (KernelSyms.printk + 0x17c) : mword 64) (sign_extend' 64 (sign_extend' 21 (concat_vec (mword_of_int 1918 : mword 11) ('b"0")))) = mword_of_int (KernelSyms.printk + 0x78)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgt78) in "Hpc".
    iSpecialize ("Hcont" $! CID6 with "[%]"); [wp_next_chain|].
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
  Lemma wp_printk_arm_c `{CID0 : CpuId} (γd : uart_names) (γv : disk_names)
      (m mc : regfile) (K : nat) (k : nat) (l : list (bv 8)) (pv pkv : mword 32)
      (dqm dqm2 : dfrac) (Rest : iProp Σ) (b : bool) (pcur : mword 64) :
    let sp0 := m !!! Regidx csp_rs1 in
    let s0v := add_vec sp0 (sign_extend' 64 (mword_of_int (-64) : mword 12)) in
    (30 <= K)%nat ->
    (k < 7)%nat ->
    eq_vec (sign_extend' 64 pv) zero_reg = false ->
    neq_vec (sign_extend' 64 pkv) zero_reg = false ->
    mc !!! Regidx s0_idx = s0v ->
    sie_cap_gpr mc (K - 24)%nat b pcur -∗
    kernel_text -∗
    pc_is (mword_of_int (KernelSyms.printk + 0x1fa + 0) : mword 64) -∗
    (pa_stk sp0 23) ↦₈ (pk_ap s0v k) -∗
    pk_va sp0 m -∗
    (mword_of_int KernelSyms.panicking : mword 64) ↦₄{ dqm } pv -∗
    (mword_of_int KernelSyms.panicked : mword 64) ↦₄{ dqm2 } pkv -∗
    dev_inv γd γv -∗ uart_tx_own γd l -∗ uart_dlab_off γd -∗
    Rest -∗
    wp_next (CID0 := CID0) b pcur (fun (CID : CpuId) =>
      ∀ (mf : regfile) (bs : list (bv 8)),
      ⌜ forall c : mword 5, is_cs_idx c = true -> mf !!! Regidx c = mc !!! Regidx c ⌝ -∗
      sie_cap_gpr mf (K - 24)%nat b pcur -∗
      pc_is (mword_of_int (KernelSyms.printk + 0x78) : mword 64) -∗
      (pa_stk sp0 23) ↦₈ (pk_ap s0v (S k)) -∗
      pk_va sp0 m -∗
      (mword_of_int KernelSyms.panicking : mword 64) ↦₄{ dqm } pv -∗
      (mword_of_int KernelSyms.panicked : mword 64) ↦₄{ dqm2 } pkv -∗
      uart_tx_own γd (l ++ bs) -∗ uart_sent γd (l ++ bs) -∗
      Rest -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros sp0 s0v HK Hk Hpv Hpkv Hs0.
    assert (HK6 : (6 <= K - 24)%nat) by lia.
    iIntros "Hcg #Htext Hpc Hap Hva Hpanicking Hpanicked #Hdev Htx #Hdlab HR Hcont".
    iApply (wp_printk_vaarg mc K 0x1fa sp0 s0v k b pcur Hs0 eq_refl
              with "Hcg [] Hpc Hap [-]").
    { rewrite /pk_vaarg_instrs.
      iSplitR; [iApply (pki_1fa with "Htext") | ].
      iSplitR; [iApply (pki_1fe with "Htext") | ].
      iApply (pki_202 with "Htext"). }
    iIntros (CIDv Hstv V) "%Hv Hcg Hpc Hap".
    destruct Hv as (Hva5 & Hvs0 & Hvk).
    assert (Hp206 : (mword_of_int (KernelSyms.printk + 0x1fa + 12) : mword 64) = mword_of_int (KernelSyms.printk + 0x206))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp206) in "Hpc".
    (* the argument: the low half of the slot *)
    iDestruct (pk_va_acc sp0 m k Hk with "Hva") as "[Hslot Hvacl]".
    iDestruct (word_pointsto_aligned_p with "Hslot") as %Halv.
    iDestruct (word_pointsto_split4 with "Hslot") as "[Hlo Hhi]".
    iEval (rewrite -/(pk_lo m k)) in "Hlo".
    assert (Hlwa : add_vec (rget V a5_idx) (sign_extend' 64 (mword_of_int 0 : mword 12)) = pa_stk sp0 (7 - k)).
    { rgne. rewrite Hva5.
      replace (sign_extend' 64 (mword_of_int 0 : mword 12)) with (mword_of_int 0 : mword 64)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite kv_addv_zero. apply pk_ap_slot. exact Hk. }
    iEval (rewrite -Hlwa) in "Hlo".
    iApply (wp_clw_s_sconf (mword_of_int (KernelSyms.printk + 0x206)) a0_idx a5_idx (mword_of_int 0 : mword 12)
              V (K - 24)%nat (pk_lo m k) b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc [] Hlo [-]").
    { iApply (pki_206 with "Htext"). }
    iIntros (CID1 Hst1) "Hcg Hpc Hlo". iEval (rewrite Hlwa) in "Hlo".
    iDestruct (word_pointsto_join4 _ _ _ _ Halv with "Hlo Hhi") as "Hslot".
    rewrite word_of_words_id.
    iDestruct ("Hvacl" with "Hslot") as "Hva".
    set (C1 := <[Regidx a0_idx := regval_into_reg (sign_extend' 64 (pk_lo m k))]> V).
    assert (Hp208 : add_vec_int (mword_of_int (KernelSyms.printk + 0x206) : mword 64) 2 = mword_of_int (KernelSyms.printk + 0x208)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp208) in "Hpc".
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.printk + 0x208)) ra_idx (mword_of_int 2095992 : mword 21)
              C1 (K - 24)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(vm_compute; reflexivity)
              with "Hcg Hpc [] [-]").
    { iApply (pki_208 with "Htext"). }
    iIntros (CID2 Hst2) "Hcg Hpc".
    set (C2 := <[Regidx ra_idx := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.printk + 0x208) : mword 64) 4)]> C1).
    assert (Htgtc : add_vec (mword_of_int (KernelSyms.printk + 0x208) : mword 64) (sign_extend' 64 (mword_of_int 2095992 : mword 21)) = mword_of_int KernelSyms.consputc) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgtc) in "Hpc".
    iApply (wp_consputc (CID0 := CID2) γd γv C2 (K - 24)%nat l pv pkv dqm dqm2 b pcur HK6 Hpv Hpkv
              with "Hcg Htext Hpc Hpanicking Hpanicked Hdev Htx Hdlab [-]").
    iIntros (CID3 Hst3 mf bs) "Hcg Hpc %Hcs Hpanicking Hpanicked Htx #Hsent".
    destruct Hcs as [Hcs Hra].
    assert (Hret : ret_pc (C2 !!! Regidx ra_idx) = mword_of_int (KernelSyms.printk + 0x20c))
      by (rewrite /C2 upd_eq; unfold ret_pc; apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hret) in "Hpc".
    iApply (wp_cj_s_sconf (mword_of_int (KernelSyms.printk + 0x20c)) (sign_extend' 21 (concat_vec (mword_of_int 1846 : mword 11) ('b"0")))
              mf (K - 24)%nat b ltac:(vm_compute; reflexivity)
              with "Hcg Hpc [] [-]").
    { iApply (pki_20c with "Htext"). }
    iIntros (CID4 Hst4). iNext. iIntros "Hcg Hpc".
    assert (Htgt78 : add_vec (mword_of_int (KernelSyms.printk + 0x20c) : mword 64) (sign_extend' 64 (sign_extend' 21 (concat_vec (mword_of_int 1846 : mword 11) ('b"0")))) = mword_of_int (KernelSyms.printk + 0x78)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgt78) in "Hpc".
    iSpecialize ("Hcont" $! CID4 with "[%]"); [wp_next_chain|].
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
  Lemma wp_printk_arm_pct `{CID0 : CpuId} (γd : uart_names) (γv : disk_names)
      (mc : regfile) (K : nat) (l : list (bv 8)) (pv pkv : mword 32)
      (dqm dqm2 : dfrac) (Rest : iProp Σ) (b : bool) (pcur : mword 64) :
    (30 <= K)%nat ->
    eq_vec (sign_extend' 64 pv) zero_reg = false ->
    neq_vec (sign_extend' 64 pkv) zero_reg = false ->
    sie_cap_gpr mc (K - 24)%nat b pcur -∗
    kernel_text -∗
    pc_is (mword_of_int (KernelSyms.printk + 0x246) : mword 64) -∗
    (mword_of_int KernelSyms.panicking : mword 64) ↦₄{ dqm } pv -∗
    (mword_of_int KernelSyms.panicked : mword 64) ↦₄{ dqm2 } pkv -∗
    dev_inv γd γv -∗ uart_tx_own γd l -∗ uart_dlab_off γd -∗
    Rest -∗
    wp_next (CID0 := CID0) b pcur (fun (CID : CpuId) =>
      ∀ (mf : regfile) (bs : list (bv 8)),
      ⌜ forall c : mword 5, is_cs_idx c = true -> mf !!! Regidx c = mc !!! Regidx c ⌝ -∗
      sie_cap_gpr mf (K - 24)%nat b pcur -∗
      pc_is (mword_of_int (KernelSyms.printk + 0x78) : mword 64) -∗
      (mword_of_int KernelSyms.panicking : mword 64) ↦₄{ dqm } pv -∗
      (mword_of_int KernelSyms.panicked : mword 64) ↦₄{ dqm2 } pkv -∗
      uart_tx_own γd (l ++ bs) -∗ uart_sent γd (l ++ bs) -∗
      Rest -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros HK Hpv Hpkv.
    assert (HK6 : (6 <= K - 24)%nat) by lia.
    iIntros "Hcg #Htext Hpc Hpanicking Hpanicked #Hdev Htx #Hdlab HR Hcont".
    (* +0x246 c.mv a0,s5 : the character after the '%' *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.printk + 0x246)) a0_idx (mword_of_int 21 : mword 5)
              mc (K - 24)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc [] [-]").
    { iApply (pki_246 with "Htext"). }
    iIntros (CID1 Hst1) "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (P1 := <[Regidx a0_idx := regval_into_reg (add_vec zero_reg (mc !!! Regidx (mword_of_int 21 : mword 5)))]> mc).
    assert (Hp248 : add_vec_int (mword_of_int (KernelSyms.printk + 0x246) : mword 64) 2 = mword_of_int (KernelSyms.printk + 0x248)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp248) in "Hpc".
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.printk + 0x248)) ra_idx (mword_of_int 2095928 : mword 21)
              P1 (K - 24)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(vm_compute; reflexivity)
              with "Hcg Hpc [] [-]").
    { iApply (pki_248 with "Htext"). }
    iIntros (CID2 Hst2) "Hcg Hpc".
    set (P2 := <[Regidx ra_idx := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.printk + 0x248) : mword 64) 4)]> P1).
    assert (Htgtc : add_vec (mword_of_int (KernelSyms.printk + 0x248) : mword 64) (sign_extend' 64 (mword_of_int 2095928 : mword 21)) = mword_of_int KernelSyms.consputc) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgtc) in "Hpc".
    iApply (wp_consputc (CID0 := CID2) γd γv P2 (K - 24)%nat l pv pkv dqm dqm2 b pcur HK6 Hpv Hpkv
              with "Hcg Htext Hpc Hpanicking Hpanicked Hdev Htx Hdlab [-]").
    iIntros (CID3 Hst3 mf bs) "Hcg Hpc %Hcs Hpanicking Hpanicked Htx #Hsent".
    destruct Hcs as [Hcs Hra].
    assert (Hret : ret_pc (P2 !!! Regidx ra_idx) = mword_of_int (KernelSyms.printk + 0x24c))
      by (rewrite /P2 upd_eq; unfold ret_pc; apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hret) in "Hpc".
    iApply (wp_cj_s_sconf (mword_of_int (KernelSyms.printk + 0x24c)) (sign_extend' 21 (concat_vec (mword_of_int 1814 : mword 11) ('b"0")))
              mf (K - 24)%nat b ltac:(vm_compute; reflexivity)
              with "Hcg Hpc [] [-]").
    { iApply (pki_24c with "Htext"). }
    iIntros (CID4 Hst4). iNext. iIntros "Hcg Hpc".
    assert (Htgt78 : add_vec (mword_of_int (KernelSyms.printk + 0x24c) : mword 64) (sign_extend' 64 (sign_extend' 21 (concat_vec (mword_of_int 1814 : mword 11) ('b"0")))) = mword_of_int (KernelSyms.printk + 0x78)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgt78) in "Hpc".
    iSpecialize ("Hcont" $! CID4 with "[%]"); [wp_next_chain|].
    iApply ("Hcont" $! mf bs with "[%] Hcg Hpc Hpanicking Hpanicked Htx Hsent HR").
    intros c Hc.
    pose proof (is_cs_idx_true_neq ra_idx c ltac:(vm_compute; reflexivity) Hc) as N1.
    pose proof (is_cs_idx_true_neq a0_idx c ltac:(vm_compute; reflexivity) Hc) as N10.
    rewrite (callee_saved_lookup Hcs c Hc).
    rewrite /P2 upd_ne; [| congruence]. rewrite /P1 upd_ne; [reflexivity | congruence].
  Qed.

  Lemma wp_printk_arm_unknown `{CID0 : CpuId} (γd : uart_names) (γv : disk_names)
      (mc : regfile) (K : nat) (l : list (bv 8)) (pv pkv : mword 32)
      (dqm dqm2 : dfrac) (Rest : iProp Σ) (b : bool) (pcur : mword 64) :
    (30 <= K)%nat ->
    eq_vec (sign_extend' 64 pv) zero_reg = false ->
    neq_vec (sign_extend' 64 pkv) zero_reg = false ->
    sie_cap_gpr mc (K - 24)%nat b pcur -∗
    kernel_text -∗
    pc_is (mword_of_int (KernelSyms.printk + 0x31a) : mword 64) -∗
    (mword_of_int KernelSyms.panicking : mword 64) ↦₄{ dqm } pv -∗
    (mword_of_int KernelSyms.panicked : mword 64) ↦₄{ dqm2 } pkv -∗
    dev_inv γd γv -∗ uart_tx_own γd l -∗ uart_dlab_off γd -∗
    Rest -∗
    wp_next (CID0 := CID0) b pcur (fun (CID : CpuId) =>
      ∀ (mf : regfile) (bs : list (bv 8)),
      ⌜ forall c : mword 5, is_cs_idx c = true -> mf !!! Regidx c = mc !!! Regidx c ⌝ -∗
      sie_cap_gpr mf (K - 24)%nat b pcur -∗
      pc_is (mword_of_int (KernelSyms.printk + 0x78) : mword 64) -∗
      (mword_of_int KernelSyms.panicking : mword 64) ↦₄{ dqm } pv -∗
      (mword_of_int KernelSyms.panicked : mword 64) ↦₄{ dqm2 } pkv -∗
      uart_tx_own γd (l ++ bs) -∗ uart_sent γd (l ++ bs) -∗
      Rest -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros HK Hpv Hpkv.
    assert (HK6 : (6 <= K - 24)%nat) by lia.
    iIntros "Hcg #Htext Hpc Hpanicking Hpanicked #Hdev Htx #Hdlab HR Hcont".
    (* +0x31a li a0,'%' *)
    iApply (wp_li4_s_sconf (mword_of_int (KernelSyms.printk + 0x31a)) a0_idx (mword_of_int 37 : mword 12)
              (mword_of_int 37 : mword 64) mc (K - 24)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc [] [-]").
    { iApply (pki_31a with "Htext"). }
    iIntros (CID1 Hst1) "Hcg Hpc".
    set (U1 := <[Regidx a0_idx := regval_into_reg (mword_of_int 37 : mword 64)]> mc).
    assert (Hp31e : add_vec_int (mword_of_int (KernelSyms.printk + 0x31a) : mword 64) 4 = mword_of_int (KernelSyms.printk + 0x31e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp31e) in "Hpc".
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.printk + 0x31e)) ra_idx (mword_of_int 2095714 : mword 21)
              U1 (K - 24)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(vm_compute; reflexivity)
              with "Hcg Hpc [] [-]").
    { iApply (pki_31e with "Htext"). }
    iIntros (CID2 Hst2) "Hcg Hpc".
    set (U2 := <[Regidx ra_idx := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.printk + 0x31e) : mword 64) 4)]> U1).
    assert (Htgtc1 : add_vec (mword_of_int (KernelSyms.printk + 0x31e) : mword 64) (sign_extend' 64 (mword_of_int 2095714 : mword 21)) = mword_of_int KernelSyms.consputc) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgtc1) in "Hpc".
    iApply (wp_consputc (CID0 := CID2) γd γv U2 (K - 24)%nat l pv pkv dqm dqm2 b pcur HK6 Hpv Hpkv
              with "Hcg Htext Hpc Hpanicking Hpanicked Hdev Htx Hdlab [-]").
    iIntros (CID3 Hst3 m1 bs1) "Hcg Hpc %Hcs1 Hpanicking Hpanicked Htx #Hsent1".
    destruct Hcs1 as [Hcs1 Hra1].
    assert (Hret1 : ret_pc (U2 !!! Regidx ra_idx) = mword_of_int (KernelSyms.printk + 0x322))
      by (rewrite /U2 upd_eq; unfold ret_pc; apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hret1) in "Hpc".
    (* +0x322 c.mv a0,s5 : and now the character itself *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.printk + 0x322)) a0_idx (mword_of_int 21 : mword 5)
              m1 (K - 24)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc [] [-]").
    { iApply (pki_322 with "Htext"). }
    iIntros (CID4 Hst4) "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (U3 := <[Regidx a0_idx := regval_into_reg (add_vec zero_reg (m1 !!! Regidx (mword_of_int 21 : mword 5)))]> m1).
    assert (Hp324 : add_vec_int (mword_of_int (KernelSyms.printk + 0x322) : mword 64) 2 = mword_of_int (KernelSyms.printk + 0x324)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp324) in "Hpc".
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.printk + 0x324)) ra_idx (mword_of_int 2095708 : mword 21)
              U3 (K - 24)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(vm_compute; reflexivity)
              with "Hcg Hpc [] [-]").
    { iApply (pki_324 with "Htext"). }
    iIntros (CID5 Hst5) "Hcg Hpc".
    set (U4 := <[Regidx ra_idx := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.printk + 0x324) : mword 64) 4)]> U3).
    assert (Htgtc2 : add_vec (mword_of_int (KernelSyms.printk + 0x324) : mword 64) (sign_extend' 64 (mword_of_int 2095708 : mword 21)) = mword_of_int KernelSyms.consputc) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgtc2) in "Hpc".
    iApply (wp_consputc (CID0 := CID5) γd γv U4 (K - 24)%nat (l ++ bs1)%list pv pkv dqm dqm2 b pcur HK6 Hpv Hpkv
              with "Hcg Htext Hpc Hpanicking Hpanicked Hdev Htx Hdlab [-]").
    iIntros (CID6 Hst6 mf bs2) "Hcg Hpc %Hcs2 Hpanicking Hpanicked Htx #Hsent2".
    destruct Hcs2 as [Hcs2 Hra2].
    assert (Hret2 : ret_pc (U4 !!! Regidx ra_idx) = mword_of_int (KernelSyms.printk + 0x328))
      by (rewrite /U4 upd_eq; unfold ret_pc; apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hret2) in "Hpc".
    iApply (wp_cj_s_sconf (mword_of_int (KernelSyms.printk + 0x328)) (sign_extend' 21 (concat_vec (mword_of_int 1704 : mword 11) ('b"0")))
              mf (K - 24)%nat b ltac:(vm_compute; reflexivity)
              with "Hcg Hpc [] [-]").
    { iApply (pki_328 with "Htext"). }
    iIntros (CID7 Hst7). iNext. iIntros "Hcg Hpc".
    assert (Htgt78 : add_vec (mword_of_int (KernelSyms.printk + 0x328) : mword 64) (sign_extend' 64 (sign_extend' 21 (concat_vec (mword_of_int 1704 : mword 11) ('b"0")))) = mword_of_int (KernelSyms.printk + 0x78)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgt78) in "Hpc".
    iEval (rewrite -!app_assoc) in "Htx".
    iEval (rewrite -!app_assoc) in "Hsent2".
    iSpecialize ("Hcont" $! CID7 with "[%]"); [wp_next_chain|].
    iApply ("Hcont" $! mf (bs1 ++ bs2)%list with "[%] Hcg Hpc Hpanicking Hpanicked Htx Hsent2 HR").
    intros c Hc.
    pose proof (is_cs_idx_true_neq ra_idx c ltac:(vm_compute; reflexivity) Hc) as N1.
    pose proof (is_cs_idx_true_neq a0_idx c ltac:(vm_compute; reflexivity) Hc) as N10.
    rewrite (callee_saved_lookup Hcs2 c Hc).
    rewrite /U4 upd_ne; [| congruence]. rewrite /U3 upd_ne; [| congruence].
    rewrite (callee_saved_lookup Hcs1 c Hc).
    rewrite /U2 upd_ne; [| congruence]. rewrite /U1 upd_ne; [reflexivity | congruence].
  Qed.

  (* ================================================================== *)
  (*  THE [%s] ARM (0x20e..0x244).                                       *)
  (*                                                                     *)
  (*  The only arm with an inner loop of its own: it walks the argument   *)
  (*  string a byte at a time, one [consputc] per character.  A null      *)
  (*  char* is not a fault -- the code substitutes the literal "(null)"   *)
  (*  and joins the SAME loop at its head, having already loaded '(' into *)
  (*  a0 and left s4 pointing at the literal's first byte.  So both       *)
  (*  entries satisfy one invariant, and there is one loop lemma.        *)
  (*                                                                     *)
  (*  [s4] is the walk cursor, so this is the one arm that does not       *)
  (*  preserve it -- harmless, because 0x78 reloads s4 from s1.          *)
  (* ================================================================== *)

  (* ---- the bytes of a C string, at the indices the walk visits ---- *)

  Lemma string_bytes_length (s : string) :
    length (string_bytes s) = String.length s.
  Proof. induction s as [|c s IH]; [reflexivity | cbn; rewrite IH; reflexivity]. Qed.

  (* a character of a NUL-free string is not the terminator: what makes the
     loop test [bnez] at 0x234 go round again. *)
  Lemma ascii_byte_nonzero (c : Ascii.ascii) :
    Ascii.eqb c pk_nul = false ->
    (Z_to_bv 8 (Z.of_N (Ascii.N_of_ascii c)) : bv 8) <> (Z_to_bv 8 0 : bv 8).
  Proof.
    destruct c as [[|] [|] [|] [|] [|] [|] [|] [|]]; intros Hc Heq;
      try (vm_compute in Hc; discriminate Hc);
      apply (f_equal bv_unsigned) in Heq; vm_compute in Heq; discriminate Heq.
  Qed.

  Lemma string_bytes_lookup_nonzero (s : string) (i : nat) (b : bv 8) :
    nonul s = true -> string_bytes s !! i = Some b -> b <> (Z_to_bv 8 0 : bv 8).
  Proof.
    revert i. induction s as [|c s IH]; intros i Hn Hb; [destruct i; discriminate | ].
    cbn in Hn. apply andb_prop in Hn as [Hc Hn].
    destruct i as [|i]; cbn in Hb.
    - injection Hb as <-. apply ascii_byte_nonzero. by apply negb_true_iff.
    - exact (IH i Hn Hb).
  Qed.

  Lemma pk_fbyte_nonzero (s : string) (i : nat) :
    nonul s = true -> (i < length (string_bytes s))%nat ->
    pk_fbyte s i <> (mword_of_int 0 : mword 8).
  Proof.
    intros Hn Hi.
    destruct (lookup_lt_is_Some_2 (string_bytes s) i Hi) as [b Hb].
    assert (Hc : cstring_bytes s !! i = Some b)
      by (rewrite /cstring_bytes lookup_app_l; [exact Hb | exact Hi]).
    rewrite /pk_fbyte (list_lookup_total_correct _ _ _ Hc).
    intro Heq. apply (string_bytes_lookup_nonzero s i b Hn Hb).
    rewrite Heq. apply bv_eq; vm_compute; reflexivity.
  Qed.

  Lemma pk_fbyte_nul (s : string) :
    pk_fbyte s (length (string_bytes s)) = (mword_of_int 0 : mword 8).
  Proof.
    rewrite /pk_fbyte (list_lookup_total_correct _ _ (Z_to_bv 8 0)).
    - apply bv_eq; vm_compute; reflexivity.
    - rewrite /cstring_bytes lookup_app_r; [| lia]. rewrite Nat.sub_diag. reflexivity.
  Qed.

  (* the [zext8_zero] direction the loop test needs on the OTHER branch *)
  Lemma zext8_nonzero (b : mword 8) :
    b <> (mword_of_int 0 : mword 8) ->
    eq_vec (zero_extend' 64 b) (zero_reg : mword 64) = false.
  Proof.
    intro H. destruct (eq_vec (zero_extend' 64 b) (zero_reg : mword 64)) eqn:E;
      [ exfalso; apply H; exact (zext8_zero b E) | reflexivity ].
  Qed.

  (* ---- the walk (0x22a..0x236) ----

     Entered at the [jal] with a0 holding the character to print and s4 the
     address it came from; leaves at 0x78 when the byte AFTER s4 is the NUL.
     Note the postcondition says nothing about WHICH bytes reached the UART:
     the printk spec promises a byte list and no more, so the walk does not
     have to relate [bs] to [s] -- only to terminate, which is what the
     [nonul] hypothesis and the length bound buy.

     Induction is on FUEL rather than on [s]: the recursive call moves the
     INDEX, not the string, and the string points-to has to stay put. *)
  Lemma wp_printk_str_loop (γd : uart_names) (γv : disk_names)
      (K : nat) (pv pkv : mword 32) (dqm dqm2 dq : dfrac) (s : string) (sv : mword 64)
      (b : bool) (pcur : mword 64) :
    (30 <= K)%nat ->
    eq_vec (sign_extend' 64 pv) zero_reg = false ->
    neq_vec (sign_extend' 64 pkv) zero_reg = false ->
    nonul s = true ->
    forall (fuel i : nat) `(CID0 : CpuId) (mc : regfile) (l : list (bv 8)) (Rest : iProp Σ),
    (length (string_bytes s) - i <= fuel)%nat ->
    (i < length (string_bytes s))%nat ->
    mc !!! Regidx (mword_of_int 20 : mword 5) = pa_add sv i ->
    sie_cap_gpr mc (K - 24)%nat b pcur -∗
    kernel_text -∗
    pc_is (mword_of_int (KernelSyms.printk + 0x22a) : mword 64) -∗
    sv ↦ₛ{ dq } s -∗
    (mword_of_int KernelSyms.panicking : mword 64) ↦₄{ dqm } pv -∗
    (mword_of_int KernelSyms.panicked : mword 64) ↦₄{ dqm2 } pkv -∗
    dev_inv γd γv -∗ uart_tx_own γd l -∗ uart_dlab_off γd -∗
    Rest -∗
    wp_next (CID0 := CID0) b pcur (fun (CID : CpuId) =>
      ∀ (mf : regfile) (bs : list (bv 8)),
      ⌜ forall c : mword 5, is_cs_idx c = true -> c <> mword_of_int 20 ->
          mf !!! Regidx c = mc !!! Regidx c ⌝ -∗
      sie_cap_gpr mf (K - 24)%nat b pcur -∗
      pc_is (mword_of_int (KernelSyms.printk + 0x78) : mword 64) -∗
      sv ↦ₛ{ dq } s -∗
      (mword_of_int KernelSyms.panicking : mword 64) ↦₄{ dqm } pv -∗
      (mword_of_int KernelSyms.panicked : mword 64) ↦₄{ dqm2 } pkv -∗
      uart_tx_own γd (l ++ bs) -∗ uart_sent γd (l ++ bs) -∗
      Rest -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros HK Hpv Hpkv Hnonul.
    assert (HK6 : (6 <= K - 24)%nat) by lia.
    intro fuel. induction fuel as [|fuel IH]; intros i CID0 mc l Rest Hf Hi Hs4; [lia | ].
    iIntros "Hcg #Htext Hpc Hstr Hpanicking Hpanicked #Hdev Htx #Hdlab HR Hcont".
    (* +0x22a jal consputc *)
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.printk + 0x22a)) ra_idx (mword_of_int 2095958 : mword 21)
              mc (K - 24)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(vm_compute; reflexivity)
              with "Hcg Hpc [] [-]").
    { iApply (pki_22a with "Htext"). }
    iIntros (CID1 Hst1) "Hcg Hpc".
    set (L1 := <[Regidx ra_idx := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.printk + 0x22a) : mword 64) 4)]> mc).
    assert (Htgtc : add_vec (mword_of_int (KernelSyms.printk + 0x22a) : mword 64) (sign_extend' 64 (mword_of_int 2095958 : mword 21)) = mword_of_int KernelSyms.consputc) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgtc) in "Hpc".
    iApply (wp_consputc (CID0 := CID1) γd γv L1 (K - 24)%nat l pv pkv dqm dqm2 b pcur HK6 Hpv Hpkv
              with "Hcg Htext Hpc Hpanicking Hpanicked Hdev Htx Hdlab [-]").
    iIntros (CID2 Hst2 m1 bs) "Hcg Hpc %Hcs Hpanicking Hpanicked Htx #Hsent".
    destruct Hcs as [Hcs Hra].
    assert (Hret : ret_pc (L1 !!! Regidx ra_idx) = mword_of_int (KernelSyms.printk + 0x22e))
      by (rewrite /L1 upd_eq; unfold ret_pc; apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hret) in "Hpc".
    (* s4 survives the call *)
    assert (Hm1s4 : m1 !!! Regidx (mword_of_int 20 : mword 5) = pa_add sv i).
    { rewrite (callee_saved_lookup Hcs (mword_of_int 20 : mword 5) ltac:(vm_compute; reflexivity)).
      rewrite /L1 upd_ne; [exact Hs4 | reg_neq]. }
    (* +0x22e c.addi s4,s4,1 *)
    iApply (wp_caddi_s_sconf (mword_of_int (KernelSyms.printk + 0x22e)) (mword_of_int 20 : mword 5) (mword_of_int 1 : mword 6)
              m1 (K - 24)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc [] [-]").
    { iApply (pki_22e with "Htext"). }
    iIntros (CID3 Hst3) "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (L2 := <[Regidx (mword_of_int 20 : mword 5) := regval_into_reg
                   (add_vec (m1 !!! Regidx (mword_of_int 20 : mword 5))
                      (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6))))]> m1).
    assert (HL2s4 : L2 !!! Regidx (mword_of_int 20 : mword 5) = pa_add sv (S i)).
    { rewrite /L2 upd_eq. unfold regval_into_reg. rewrite Hm1s4.
      replace (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6))) with (mword_of_int 1 : mword 64)
        by (apply bv_eq; vm_compute; reflexivity).
      apply pa_add_S. }
    assert (Hp230 : add_vec_int (mword_of_int (KernelSyms.printk + 0x22e) : mword 64) 2 = mword_of_int (KernelSyms.printk + 0x230)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp230) in "Hpc".
    (* +0x230 lbu a0,0(s4) : the next byte *)
    assert (HSi : (S i < length (cstring_bytes s))%nat)
      by (rewrite cstring_bytes_length -string_bytes_length; lia).
    iDestruct (pk_str_byte sv dq s (S i) HSi with "Hstr") as "[Hb Hstrcl]".
    assert (Hlba : add_vec (rget L2 (mword_of_int 20 : mword 5))
                     (sign_extend' 64 (mword_of_int 0 : mword 12)) = pa_add sv (S i)).
    { rgne. rewrite HL2s4.
      replace (sign_extend' 64 (mword_of_int 0 : mword 12)) with (mword_of_int 0 : mword 64)
        by (apply bv_eq; vm_compute; reflexivity).
      apply kv_addv_zero. }
    iEval (rewrite -Hlba) in "Hb".
    iApply (wp_lbu_s_sconf (mword_of_int (KernelSyms.printk + 0x230)) a0_idx (mword_of_int 20 : mword 5)
              (mword_of_int 0 : mword 12) L2 (K - 24)%nat (pk_fbyte s (S i)) b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc [] Hb [-]").
    { iApply (pki_230 with "Htext"). }
    iIntros (CID4 Hst4) "Hcg Hpc Hb". iEval (rewrite Hlba) in "Hb".
    iDestruct ("Hstrcl" with "Hb") as "Hstr".
    set (L3 := <[Regidx a0_idx := regval_into_reg (zero_extend' 64 (pk_fbyte s (S i)))]> L2).
    assert (HL3a0 : L3 !!! Regidx a0_idx = zero_extend' 64 (pk_fbyte s (S i)))
      by (rewrite /L3 upd_eq; reflexivity).
    assert (HL3s4 : L3 !!! Regidx (mword_of_int 20 : mword 5) = pa_add sv (S i))
      by (rewrite /L3 upd_ne; [exact HL2s4 | reg_neq]).
    (* the registers this iteration kept, for either exit *)
    assert (Hkept : forall c : mword 5, is_cs_idx c = true -> c <> mword_of_int 20 ->
                      L3 !!! Regidx c = mc !!! Regidx c).
    { intros c Hc N20.
      pose proof (is_cs_idx_true_neq ra_idx c ltac:(vm_compute; reflexivity) Hc) as N1.
      pose proof (is_cs_idx_true_neq a0_idx c ltac:(vm_compute; reflexivity) Hc) as N10.
      rewrite /L3 upd_ne; [| congruence]. rewrite /L2 upd_ne; [| congruence].
      rewrite (callee_saved_lookup Hcs c Hc).
      rewrite /L1 upd_ne; [reflexivity | congruence]. }
    assert (Hp234 : add_vec_int (mword_of_int (KernelSyms.printk + 0x230) : mword 64) 4 = mword_of_int (KernelSyms.printk + 0x234)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp234) in "Hpc".
    (* +0x234 bnez a0 : one more character, or the terminator *)
    destruct (lt_dec (S i) (length (string_bytes s))) as [Hlt | Hge].
    - (* another character: back to the head with the index bumped *)
      assert (Hne : neq_vec (L3 !!! Regidx a0_idx) zero_reg = true).
      { rewrite HL3a0. unfold neq_vec. rewrite negb_true_iff.
        apply zext8_nonzero. apply pk_fbyte_nonzero; [exact Hnonul | exact Hlt]. }
      iApply (wp_cbnez_taken_s_sconf (mword_of_int (KernelSyms.printk + 0x234)) (mword_of_int 251 : mword 8)
                (Cregidx (mword_of_int 2)) a0_idx L3 (K - 24)%nat b
                ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) ltac:(rgne; exact Hne)
                ltac:(vm_compute; reflexivity)
                with "Hcg Hpc [] [-]").
      { iApply (pki_234 with "Htext"). }
      iIntros (CID5 Hst5). iNext. iIntros "Hcg Hpc".
      assert (Htgth : add_vec (mword_of_int (KernelSyms.printk + 0x234) : mword 64) (sign_extend' 64 (sign_extend' 13 (concat_vec (mword_of_int 251 : mword 8) ('b"0")))) = mword_of_int (KernelSyms.printk + 0x22a)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Htgth) in "Hpc".
      assert (Hshift : b = false \/ pcur = zero_reg -> (CID5 : CPU) = (CID0 : CPU)) by wp_next_chain.
      iDestruct (wp_next_shift Hshift with "Hcont") as "Hcont".
      iApply (IH (S i) CID5 L3 (l ++ bs)%list Rest ltac:(lia) Hlt HL3s4
                with "Hcg Htext Hpc Hstr Hpanicking Hpanicked Hdev Htx Hdlab HR [-]").
      iIntros (CID6 Hst6 mf bs2) "%Hkept2 Hcg Hpc Hstr Hpanicking Hpanicked Htx Hsent2 HR".
      iEval (rewrite -app_assoc) in "Htx".
      iEval (rewrite -app_assoc) in "Hsent2".
      iSpecialize ("Hcont" $! CID6 with "[%]"); [wp_next_chain|].
      iApply ("Hcont" $! mf (bs ++ bs2)%list with "[%] Hcg Hpc Hstr Hpanicking Hpanicked Htx Hsent2 HR").
      intros c Hc N20. rewrite (Hkept2 c Hc N20). exact (Hkept c Hc N20).
    - (* the terminator: fall through to the [j] at 0x236 *)
      assert (Hsi : S i = length (string_bytes s)) by lia.
      assert (Hz : neq_vec (L3 !!! Regidx a0_idx) zero_reg = false).
      { rewrite HL3a0. unfold neq_vec. rewrite negb_false_iff.
        rewrite Hsi pk_fbyte_nul. vm_compute; reflexivity. }
      iApply (wp_cbnez_fall_s_sconf (mword_of_int (KernelSyms.printk + 0x234)) (mword_of_int 251 : mword 8)
                (Cregidx (mword_of_int 2)) a0_idx L3 (K - 24)%nat b
                ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) ltac:(rgne; exact Hz)
                with "Hcg Hpc [] [-]").
      { iApply (pki_234 with "Htext"). }
      iIntros (CID5b Hst5b) "Hcg Hpc".
      assert (Hp236 : add_vec_int (mword_of_int (KernelSyms.printk + 0x234) : mword 64) 2 = mword_of_int (KernelSyms.printk + 0x236)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hp236) in "Hpc".
      iApply (wp_cj_s_sconf (mword_of_int (KernelSyms.printk + 0x236)) (sign_extend' 21 (concat_vec (mword_of_int 1825 : mword 11) ('b"0")))
                L3 (K - 24)%nat b ltac:(vm_compute; reflexivity)
                with "Hcg Hpc [] [-]").
      { iApply (pki_236 with "Htext"). }
      iIntros (CID6b Hst6b). iNext. iIntros "Hcg Hpc".
      assert (Htgt78 : add_vec (mword_of_int (KernelSyms.printk + 0x236) : mword 64) (sign_extend' 64 (sign_extend' 21 (concat_vec (mword_of_int 1825 : mword 11) ('b"0")))) = mword_of_int (KernelSyms.printk + 0x78)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Htgt78) in "Hpc".
      iSpecialize ("Hcont" $! CID6b with "[%]"); [wp_next_chain|].
      iApply ("Hcont" $! L3 bs with "[%] Hcg Hpc Hstr Hpanicking Hpanicked Htx Hsent HR").
      exact Hkept.
  Qed.

  (* the arm proper (0x20e..0x226): take the vararg, and either walk it or,
     for a null pointer, walk the literal instead.  Two lemmas because the
     two are two different DESCRIPTORS, not two branches of one caller. *)
  Lemma wp_printk_arm_s `{CID0 : CpuId} (γd : uart_names) (γv : disk_names)
      (m mc : regfile) (K : nat) (k : nat) (l : list (bv 8)) (pv pkv : mword 32)
      (dqm dqm2 dq : dfrac) (s : string) (Rest : iProp Σ) (b : bool) (pcur : mword 64) :
    let sp0 := m !!! Regidx csp_rs1 in
    let s0v := add_vec sp0 (sign_extend' 64 (mword_of_int (-64) : mword 12)) in
    (30 <= K)%nat ->
    (k < 7)%nat ->
    eq_vec (sign_extend' 64 pv) zero_reg = false ->
    neq_vec (sign_extend' 64 pkv) zero_reg = false ->
    nonul s = true ->
    eq_vec (pk_vararg m k) zero_reg = false ->
    mc !!! Regidx s0_idx = s0v ->
    sie_cap_gpr mc (K - 24)%nat b pcur -∗
    kernel_text -∗
    pc_is (mword_of_int (KernelSyms.printk + 0x20e + 0) : mword 64) -∗
    (pa_stk sp0 23) ↦₈ (pk_ap s0v k) -∗
    pk_va sp0 m -∗
    (pk_vararg m k) ↦ₛ{ dq } s -∗
    (mword_of_int KernelSyms.panicking : mword 64) ↦₄{ dqm } pv -∗
    (mword_of_int KernelSyms.panicked : mword 64) ↦₄{ dqm2 } pkv -∗
    dev_inv γd γv -∗ uart_tx_own γd l -∗ uart_sent γd l -∗ uart_dlab_off γd -∗
    Rest -∗
    wp_next (CID0 := CID0) b pcur (fun (CID : CpuId) =>
      ∀ (mf : regfile) (bs : list (bv 8)),
      ⌜ forall c : mword 5, is_cs_idx c = true -> c <> mword_of_int 20 ->
          mf !!! Regidx c = mc !!! Regidx c ⌝ -∗
      sie_cap_gpr mf (K - 24)%nat b pcur -∗
      pc_is (mword_of_int (KernelSyms.printk + 0x78) : mword 64) -∗
      (pa_stk sp0 23) ↦₈ (pk_ap s0v (S k)) -∗
      pk_va sp0 m -∗
      (pk_vararg m k) ↦ₛ{ dq } s -∗
      (mword_of_int KernelSyms.panicking : mword 64) ↦₄{ dqm } pv -∗
      (mword_of_int KernelSyms.panicked : mword 64) ↦₄{ dqm2 } pkv -∗
      uart_tx_own γd (l ++ bs) -∗ uart_sent γd (l ++ bs) -∗
      Rest -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros sp0 s0v HK Hk Hpv Hpkv Hnonul Hnn Hs0.
    iIntros "Hcg #Htext Hpc Hap Hva Hstr Hpanicking Hpanicked #Hdev Htx #Hsl #Hdlab HR Hcont".
    iApply (wp_printk_vaarg mc K 0x20e sp0 s0v k b pcur Hs0 eq_refl
              with "Hcg [] Hpc Hap [-]").
    { rewrite /pk_vaarg_instrs.
      iSplitR; [iApply (pki_20e with "Htext") | ].
      iSplitR; [iApply (pki_212 with "Htext") | ].
      iApply (pki_216 with "Htext"). }
    iIntros (CIDv Hstv V) "%Hv Hcg Hpc Hap".
    destruct Hv as (Hva5 & Hvs0 & Hvk).
    assert (Hp21a : (mword_of_int (KernelSyms.printk + 0x20e + 12) : mword 64) = mword_of_int (KernelSyms.printk + 0x21a))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp21a) in "Hpc".
    (* +0x21a ld s4,0(a5) : the char* itself *)
    iDestruct (pk_va_acc sp0 m k Hk with "Hva") as "[Hslot Hvacl]".
    assert (Hlda : add_vec (rget V a5_idx) (sign_extend' 64 (mword_of_int 0 : mword 12)) = pa_stk sp0 (7 - k)).
    { rgne. rewrite Hva5.
      replace (sign_extend' 64 (mword_of_int 0 : mword 12)) with (mword_of_int 0 : mword 64)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite kv_addv_zero. apply pk_ap_slot. exact Hk. }
    iEval (rewrite -Hlda) in "Hslot".
    iApply (wp_ld_s_sconf (mword_of_int (KernelSyms.printk + 0x21a)) (mword_of_int 20 : mword 5) a5_idx
              (mword_of_int 0 : mword 12) V (K - 24)%nat (pk_vararg m k) b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc [] Hslot [-]").
    { iApply (pki_21a with "Htext"). }
    iIntros (CID1 Hst1) "Hcg Hpc Hslot". iEval (rewrite Hlda) in "Hslot".
    iDestruct ("Hvacl" with "Hslot") as "Hva".
    set (S1 := <[Regidx (mword_of_int 20 : mword 5) := regval_into_reg (pk_vararg m k)]> V).
    assert (HS1s4 : S1 !!! Regidx (mword_of_int 20 : mword 5) = pk_vararg m k)
      by (rewrite /S1 upd_eq; reflexivity).
    assert (Hp21e : add_vec_int (mword_of_int (KernelSyms.printk + 0x21a) : mword 64) 4 = mword_of_int (KernelSyms.printk + 0x21e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp21e) in "Hpc".
    (* +0x21e beqz s4 : not null, so fall through *)
    iApply (wp_beqz_x0_fall_s_sconf (mword_of_int (KernelSyms.printk + 0x21e)) (mword_of_int 26 : mword 13)
              (mword_of_int 20 : mword 5) S1 (K - 24)%nat b
              ltac:(vm_compute; discriminate) ltac:(rgne; rewrite HS1s4; exact Hnn)
              with "Hcg Hpc [] [-]").
    { iApply (pki_21e with "Htext"). }
    iIntros (CID2 Hst2) "Hcg Hpc".
    assert (Hp222 : add_vec_int (mword_of_int (KernelSyms.printk + 0x21e) : mword 64) 4 = mword_of_int (KernelSyms.printk + 0x222)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp222) in "Hpc".
    (* +0x222 lbu a0,0(s4) : the first character *)
    assert (H0 : (0 < length (cstring_bytes s))%nat)
      by (rewrite cstring_bytes_length; lia).
    iDestruct (pk_str_byte (pk_vararg m k) dq s 0 H0 with "Hstr") as "[Hb Hstrcl]".
    assert (Hlba : add_vec (rget S1 (mword_of_int 20 : mword 5))
                     (sign_extend' 64 (mword_of_int 0 : mword 12)) = pa_add (pk_vararg m k) 0).
    { rgne. rewrite HS1s4 pa_add_0.
      replace (sign_extend' 64 (mword_of_int 0 : mword 12)) with (mword_of_int 0 : mword 64)
        by (apply bv_eq; vm_compute; reflexivity).
      apply kv_addv_zero. }
    iEval (rewrite -Hlba) in "Hb".
    iApply (wp_lbu_s_sconf (mword_of_int (KernelSyms.printk + 0x222)) a0_idx (mword_of_int 20 : mword 5)
              (mword_of_int 0 : mword 12) S1 (K - 24)%nat (pk_fbyte s 0) b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc [] Hb [-]").
    { iApply (pki_222 with "Htext"). }
    iIntros (CID3 Hst3) "Hcg Hpc Hb". iEval (rewrite Hlba) in "Hb".
    iDestruct ("Hstrcl" with "Hb") as "Hstr".
    set (S2 := <[Regidx a0_idx := regval_into_reg (zero_extend' 64 (pk_fbyte s 0))]> S1).
    assert (HS2a0 : S2 !!! Regidx a0_idx = zero_extend' 64 (pk_fbyte s 0))
      by (rewrite /S2 upd_eq; reflexivity).
    assert (HS2s4 : S2 !!! Regidx (mword_of_int 20 : mword 5) = pa_add (pk_vararg m k) 0)
      by (rewrite /S2 upd_ne; [rewrite HS1s4 pa_add_0; reflexivity | reg_neq]).
    assert (Hkept : forall c : mword 5, is_cs_idx c = true -> c <> mword_of_int 20 ->
                      S2 !!! Regidx c = mc !!! Regidx c).
    { intros c Hc N20.
      pose proof (is_cs_idx_true_neq a0_idx c ltac:(vm_compute; reflexivity) Hc) as N10.
      pose proof (is_cs_idx_true_neq (mword_of_int 14 : mword 5) c ltac:(vm_compute; reflexivity) Hc) as N14.
      pose proof (is_cs_idx_true_neq a5_idx c ltac:(vm_compute; reflexivity) Hc) as N15.
      rewrite /S2 upd_ne; [| congruence]. rewrite /S1 upd_ne; [| congruence].
      apply Hvk; congruence. }
    assert (Hp226 : add_vec_int (mword_of_int (KernelSyms.printk + 0x222) : mword 64) 4 = mword_of_int (KernelSyms.printk + 0x226)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp226) in "Hpc".
    (* +0x226 beqz a0 : the empty string prints nothing at all *)
    destruct (lt_dec 0 (length (string_bytes s))) as [Hlt | Hge].
    - assert (Hne : eq_vec (S2 !!! Regidx a0_idx) zero_reg = false).
      { rewrite HS2a0. apply zext8_nonzero. apply pk_fbyte_nonzero; [exact Hnonul | exact Hlt]. }
      iApply (wp_beqz_x0_fall_s_sconf (mword_of_int (KernelSyms.printk + 0x226)) (mword_of_int 7762 : mword 13)
                a0_idx S2 (K - 24)%nat b ltac:(vm_compute; discriminate) ltac:(rgne; exact Hne)
                with "Hcg Hpc [] [-]").
      { iApply (pki_226 with "Htext"). }
      iIntros (CID4 Hst4) "Hcg Hpc".
      assert (Hp22a : add_vec_int (mword_of_int (KernelSyms.printk + 0x226) : mword 64) 4 = mword_of_int (KernelSyms.printk + 0x22a)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hp22a) in "Hpc".
      iApply (wp_printk_str_loop γd γv K pv pkv dqm dqm2 dq s (pk_vararg m k) b pcur
                HK Hpv Hpkv Hnonul (length (string_bytes s)) 0%nat CID4 S2 l
                ((pa_stk sp0 23) ↦₈ (pk_ap s0v (S k)) ∗ pk_va sp0 m ∗ Rest)%I
                ltac:(lia) Hlt HS2s4
                with "Hcg Htext Hpc Hstr Hpanicking Hpanicked Hdev Htx Hdlab [$Hap $Hva $HR] [-]").
      iIntros (CID5 Hst5 mf bs) "%Hkept2 Hcg Hpc Hstr Hpanicking Hpanicked Htx Hsent (Hap & Hva & HR)".
      iSpecialize ("Hcont" $! CID5 with "[%]"); [wp_next_chain|].
      iApply ("Hcont" $! mf bs with "[%] Hcg Hpc Hap Hva Hstr Hpanicking Hpanicked Htx Hsent HR").
      intros c Hc N20. rewrite (Hkept2 c Hc N20). exact (Hkept c Hc N20).
    - (* s = "" : straight back to the loop head at 0x78 *)
      assert (Hs0len : (0%nat = length (string_bytes s))) by lia.
      assert (Hz : eq_vec (S2 !!! Regidx a0_idx) zero_reg = true).
      { rewrite HS2a0 Hs0len pk_fbyte_nul. vm_compute; reflexivity. }
      iApply (wp_beqz_x0_taken_s_sconf (mword_of_int (KernelSyms.printk + 0x226)) (mword_of_int 7762 : mword 13)
                a0_idx S2 (K - 24)%nat b ltac:(vm_compute; discriminate) ltac:(rgne; exact Hz)
                ltac:(vm_compute; reflexivity)
                with "Hcg Hpc [] [-]").
      { iApply (pki_226 with "Htext"). }
      iIntros (CID4b Hst4b). iNext. iIntros "Hcg Hpc".
      assert (Htgt78 : add_vec (mword_of_int (KernelSyms.printk + 0x226) : mword 64) (sign_extend' 64 (mword_of_int 7762 : mword 13)) = mword_of_int (KernelSyms.printk + 0x78)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Htgt78) in "Hpc".
      iAssert (uart_tx_own γd (l ++ [])) with "[Htx]" as "Htx'".
      { rewrite app_nil_r. iApply "Htx". }
      iAssert (uart_sent γd (l ++ [])) as "#Hsl'".
      { rewrite app_nil_r. iApply "Hsl". }
      iSpecialize ("Hcont" $! CID4b with "[%]"); [wp_next_chain|].
      iApply ("Hcont" $! S2 [] with "[%] Hcg Hpc Hap Hva Hstr Hpanicking Hpanicked Htx' Hsl' HR").
      exact Hkept.
  Qed.

  (* the "(null)" literal, at the address the auipc/addi pair computes *)
  Definition pk_null_str : Z := 0x80007008.

  Lemma pk_null_data :
    kernel_data -∗ (mword_of_int pk_null_str : mword 64) ↦ₛ□ "(null)"%string.
  Proof.
    iIntros "#Hd".
    iApply (kernel_data_string pk_null_str "(null)"%string _ eq_refl
              ltac:(unfold text_end, pk_null_str; lia) with "Hd").
    intros j b Hj.
    do 7 (destruct j as [|j];
          [vm_compute in Hj; injection Hj as <-; vm_compute; reflexivity |]).
    vm_compute in Hj; discriminate.
  Qed.

  Lemma wp_printk_arm_s_null `{CID0 : CpuId} (γd : uart_names) (γv : disk_names)
      (m mc : regfile) (K : nat) (k : nat) (l : list (bv 8)) (pv pkv : mword 32)
      (dqm dqm2 : dfrac) (Rest : iProp Σ) (b : bool) (pcur : mword 64) :
    let sp0 := m !!! Regidx csp_rs1 in
    let s0v := add_vec sp0 (sign_extend' 64 (mword_of_int (-64) : mword 12)) in
    (30 <= K)%nat ->
    (k < 7)%nat ->
    eq_vec (sign_extend' 64 pv) zero_reg = false ->
    neq_vec (sign_extend' 64 pkv) zero_reg = false ->
    pk_vararg m k = zero_reg ->
    mc !!! Regidx s0_idx = s0v ->
    sie_cap_gpr mc (K - 24)%nat b pcur -∗
    kernel_text -∗ kernel_data -∗
    pc_is (mword_of_int (KernelSyms.printk + 0x20e + 0) : mword 64) -∗
    (pa_stk sp0 23) ↦₈ (pk_ap s0v k) -∗
    pk_va sp0 m -∗
    (mword_of_int KernelSyms.panicking : mword 64) ↦₄{ dqm } pv -∗
    (mword_of_int KernelSyms.panicked : mword 64) ↦₄{ dqm2 } pkv -∗
    dev_inv γd γv -∗ uart_tx_own γd l -∗ uart_dlab_off γd -∗
    Rest -∗
    wp_next (CID0 := CID0) b pcur (fun (CID : CpuId) =>
      ∀ (mf : regfile) (bs : list (bv 8)),
      ⌜ forall c : mword 5, is_cs_idx c = true -> c <> mword_of_int 20 ->
          mf !!! Regidx c = mc !!! Regidx c ⌝ -∗
      sie_cap_gpr mf (K - 24)%nat b pcur -∗
      pc_is (mword_of_int (KernelSyms.printk + 0x78) : mword 64) -∗
      (pa_stk sp0 23) ↦₈ (pk_ap s0v (S k)) -∗
      pk_va sp0 m -∗
      (mword_of_int KernelSyms.panicking : mword 64) ↦₄{ dqm } pv -∗
      (mword_of_int KernelSyms.panicked : mword 64) ↦₄{ dqm2 } pkv -∗
      uart_tx_own γd (l ++ bs) -∗ uart_sent γd (l ++ bs) -∗
      Rest -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros sp0 s0v HK Hk Hpv Hpkv Hnull Hs0.
    iIntros "Hcg #Htext #Hdata Hpc Hap Hva Hpanicking Hpanicked #Hdev Htx #Hdlab HR Hcont".
    iPoseProof (pk_null_data with "Hdata") as "#Hnull".
    iApply (wp_printk_vaarg mc K 0x20e sp0 s0v k b pcur Hs0 eq_refl
              with "Hcg [] Hpc Hap [-]").
    { rewrite /pk_vaarg_instrs.
      iSplitR; [iApply (pki_20e with "Htext") | ].
      iSplitR; [iApply (pki_212 with "Htext") | ].
      iApply (pki_216 with "Htext"). }
    iIntros (CIDv Hstv V) "%Hv Hcg Hpc Hap".
    destruct Hv as (Hva5 & Hvs0 & Hvk).
    assert (Hp21a : (mword_of_int (KernelSyms.printk + 0x20e + 12) : mword 64) = mword_of_int (KernelSyms.printk + 0x21a))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp21a) in "Hpc".
    iDestruct (pk_va_acc sp0 m k Hk with "Hva") as "[Hslot Hvacl]".
    assert (Hlda : add_vec (rget V a5_idx) (sign_extend' 64 (mword_of_int 0 : mword 12)) = pa_stk sp0 (7 - k)).
    { rgne. rewrite Hva5.
      replace (sign_extend' 64 (mword_of_int 0 : mword 12)) with (mword_of_int 0 : mword 64)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite kv_addv_zero. apply pk_ap_slot. exact Hk. }
    iEval (rewrite -Hlda) in "Hslot".
    iApply (wp_ld_s_sconf (mword_of_int (KernelSyms.printk + 0x21a)) (mword_of_int 20 : mword 5) a5_idx
              (mword_of_int 0 : mword 12) V (K - 24)%nat (pk_vararg m k) b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc [] Hslot [-]").
    { iApply (pki_21a with "Htext"). }
    iIntros (CID1 Hst1) "Hcg Hpc Hslot". iEval (rewrite Hlda) in "Hslot".
    iDestruct ("Hvacl" with "Hslot") as "Hva".
    set (N1 := <[Regidx (mword_of_int 20 : mword 5) := regval_into_reg (pk_vararg m k)]> V).
    assert (HN1s4 : N1 !!! Regidx (mword_of_int 20 : mword 5) = zero_reg)
      by (rewrite /N1 upd_eq; exact Hnull).
    assert (Hp21e : add_vec_int (mword_of_int (KernelSyms.printk + 0x21a) : mword 64) 4 = mword_of_int (KernelSyms.printk + 0x21e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp21e) in "Hpc".
    (* +0x21e beqz s4 : null, so take the literal *)
    iApply (wp_beqz_x0_taken_s_sconf (mword_of_int (KernelSyms.printk + 0x21e)) (mword_of_int 26 : mword 13)
              (mword_of_int 20 : mword 5) N1 (K - 24)%nat b
              ltac:(vm_compute; discriminate) ltac:(rgne; rewrite HN1s4; vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "Hcg Hpc [] [-]").
    { iApply (pki_21e with "Htext"). }
    iIntros (CID2 Hst2). iNext. iIntros "Hcg Hpc".
    assert (Htgt238 : add_vec (mword_of_int (KernelSyms.printk + 0x21e) : mword 64) (sign_extend' 64 (mword_of_int 26 : mword 13)) = mword_of_int (KernelSyms.printk + 0x238)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgt238) in "Hpc".
    (* +0x238 auipc s4,0x7 ; +0x23c addi s4,s4,-1836 : &"(null)" *)
    iApply (wp_auipc_s_sconf (mword_of_int (KernelSyms.printk + 0x238)) (mword_of_int 20 : mword 5)
              (mword_of_int 7 : mword 20) N1 (K - 24)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc [] [-]").
    { iApply (pki_238 with "Htext"). }
    iIntros (CID3 Hst3) "Hcg Hpc".
    set (N2 := <[Regidx (mword_of_int 20 : mword 5) := regval_into_reg
                   (add_vec (mword_of_int (KernelSyms.printk + 0x238) : mword 64) (auipc_off (mword_of_int 7 : mword 20)))]> N1).
    assert (Hp23c : add_vec_int (mword_of_int (KernelSyms.printk + 0x238) : mword 64) 4 = mword_of_int (KernelSyms.printk + 0x23c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp23c) in "Hpc".
    iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.printk + 0x23c)) (mword_of_int 20 : mword 5)
              (mword_of_int 20 : mword 5) (mword_of_int 2246 : mword 12) N2 (K - 24)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc [] [-]").
    { iApply (pki_23c with "Htext"). }
    iIntros (CID4 Hst4) "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (N3 := <[Regidx (mword_of_int 20 : mword 5) := regval_into_reg
                   (add_vec (N2 !!! Regidx (mword_of_int 20 : mword 5))
                      (sign_extend' 64 (mword_of_int 2246 : mword 12)))]> N2).
    assert (HN3s4 : N3 !!! Regidx (mword_of_int 20 : mword 5)
                    = pa_add (mword_of_int pk_null_str : mword 64) 0).
    { rewrite /N3 upd_eq. unfold regval_into_reg. rewrite /N2 upd_eq.
      unfold regval_into_reg. rewrite pa_add_0.
      apply bv_eq; vm_compute; reflexivity. }
    assert (Hp240 : add_vec_int (mword_of_int (KernelSyms.printk + 0x23c) : mword 64) 4 = mword_of_int (KernelSyms.printk + 0x240)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp240) in "Hpc".
    (* +0x240 li a0,'(' : the loop head expects the character already loaded *)
    iApply (wp_li4_s_sconf (mword_of_int (KernelSyms.printk + 0x240)) a0_idx (mword_of_int 40 : mword 12)
              (mword_of_int 40 : mword 64) N3 (K - 24)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc [] [-]").
    { iApply (pki_240 with "Htext"). }
    iIntros (CID5 Hst5) "Hcg Hpc".
    set (N4 := <[Regidx a0_idx := regval_into_reg (mword_of_int 40 : mword 64)]> N3).
    assert (HN4s4 : N4 !!! Regidx (mword_of_int 20 : mword 5)
                    = pa_add (mword_of_int pk_null_str : mword 64) 0)
      by (rewrite /N4 upd_ne; [exact HN3s4 | reg_neq]).
    assert (Hkept : forall c : mword 5, is_cs_idx c = true -> c <> mword_of_int 20 ->
                      N4 !!! Regidx c = mc !!! Regidx c).
    { intros c Hc N20.
      pose proof (is_cs_idx_true_neq a0_idx c ltac:(vm_compute; reflexivity) Hc) as N10.
      pose proof (is_cs_idx_true_neq (mword_of_int 14 : mword 5) c ltac:(vm_compute; reflexivity) Hc) as N14.
      pose proof (is_cs_idx_true_neq a5_idx c ltac:(vm_compute; reflexivity) Hc) as N15.
      rewrite /N4 upd_ne; [| congruence]. rewrite /N3 upd_ne; [| congruence].
      rewrite /N2 upd_ne; [| congruence]. rewrite /N1 upd_ne; [| congruence].
      apply Hvk; congruence. }
    assert (Hp244 : add_vec_int (mword_of_int (KernelSyms.printk + 0x240) : mword 64) 4 = mword_of_int (KernelSyms.printk + 0x244)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp244) in "Hpc".
    (* +0x244 j 0x22a : the SAME walk, over the literal *)
    iApply (wp_cj_s_sconf (mword_of_int (KernelSyms.printk + 0x244)) (sign_extend' 21 (concat_vec (mword_of_int 2035 : mword 11) ('b"0")))
              N4 (K - 24)%nat b ltac:(vm_compute; reflexivity)
              with "Hcg Hpc [] [-]").
    { iApply (pki_244 with "Htext"). }
    iIntros (CID6 Hst6). iNext. iIntros "Hcg Hpc".
    assert (Htgth : add_vec (mword_of_int (KernelSyms.printk + 0x244) : mword 64) (sign_extend' 64 (sign_extend' 21 (concat_vec (mword_of_int 2035 : mword 11) ('b"0")))) = mword_of_int (KernelSyms.printk + 0x22a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgth) in "Hpc".
    iApply (wp_printk_str_loop γd γv K pv pkv dqm dqm2 DfracDiscarded "(null)"%string
              (mword_of_int pk_null_str : mword 64) b pcur
              HK Hpv Hpkv ltac:(vm_compute; reflexivity)
              6%nat 0%nat CID6 N4 l
              ((pa_stk sp0 23) ↦₈ (pk_ap s0v (S k)) ∗ pk_va sp0 m ∗ Rest)%I
              ltac:(vm_compute; lia) ltac:(vm_compute; lia) HN4s4
              with "Hcg Htext Hpc Hnull Hpanicking Hpanicked Hdev Htx Hdlab [$Hap $Hva $HR] [-]").
    iIntros (CID7 Hst7 mf bs) "%Hkept2 Hcg Hpc _ Hpanicking Hpanicked Htx Hsent (Hap & Hva & HR)".
    iSpecialize ("Hcont" $! CID7 with "[%]"); [wp_next_chain|].
    iApply ("Hcont" $! mf bs with "[%] Hcg Hpc Hap Hva Hpanicking Hpanicked Htx Hsent HR").
    intros c Hc N20. rewrite (Hkept2 c Hc N20). exact (Hkept c Hc N20).
  Qed.

  (* ================================================================== *)
  (*  THE [%p] ARM (0x1b4..0x1f8).                                       *)
  (*                                                                     *)
  (*  gcc does NOT call printint for a pointer: it inlines a fixed        *)
  (*  sixteen-iteration loop that peels one nibble off the top of the     *)
  (*  value each time and indexes the same [digits] table printint uses.  *)
  (*  Fixed trip count, so the induction is on the COUNTER and there is   *)
  (*  no value bound to carry -- the contrast with printint's do-while,   *)
  (*  where the buffer bound is the whole difficulty.                     *)
  (*                                                                     *)
  (*  It is also the only arm that needs a frame slot of its own: s9 is   *)
  (*  the table pointer, so it is saved into slot 19 at 0x1b4 and         *)
  (*  restored at 0x1f6.  s4 (the counter) and s5 (the value) are left    *)
  (*  clobbered -- 0x78 reloads s4 from s1, and the dispatch recomputes   *)
  (*  s5 before the next arm reads it. *)
  (* ================================================================== *)

  (* the sixteen persistent image bytes the nibble may index; their VALUES
     are irrelevant, exactly as in printint's [digits_tbl]. *)
  Definition pk_digits (dg : mword 64) : iProp Σ :=
    ([∗ list] j ∈ seq 0 16, ∃ b : bv 8, (pa_add dg j) ↦ₘ□ b)%I.

  Definition pk_digits_addr : Z := 0x80007730.

  Lemma pk_digits_data :
    kernel_data -∗ pk_digits (mword_of_int pk_digits_addr : mword 64).
  Proof.
    iIntros "#Hd".
    assert (Hbytes : forall j b, cstring_bytes "0123456789abcdef"%string !! j = Some b ->
                     KernelData.kernel_data !! (pk_digits_addr + Z.of_nat j)%Z = Some b).
    { intros j b Hj.
      do 17 (destruct j as [|j];
             [vm_compute in Hj; injection Hj as <-; vm_compute; reflexivity |]).
      vm_compute in Hj; discriminate. }
    iPoseProof (kernel_data_string pk_digits_addr "0123456789abcdef"%string _ eq_refl
                  ltac:(unfold text_end, pk_digits_addr; lia) Hbytes with "Hd") as "#Hs".
    rewrite /pk_digits. iApply big_sepL_intro. iIntros "!>" (u j Hu).
    apply lookup_seq in Hu. destruct Hu as [-> Hlt].
    iExists (pk_fbyte "0123456789abcdef"%string u).
    iApply (big_sepL_lookup _ _ u (pk_fbyte "0123456789abcdef"%string u) with "Hs").
    rewrite /pk_fbyte. apply list_lookup_lookup_total_lt.
    rewrite cstring_bytes_length. cbn [String.length]. lia.
  Qed.

  (* a small nonnegative literal is zero exactly when its index is: the
     counter's back-edge test. *)
  Lemma moi_small_nz (j : nat) :
    (j < 16)%nat -> neq_vec (mword_of_int (Z.of_nat j) : mword 64) zero_reg = negb (Nat.eqb j 0).
  Proof.
    intro Hj. do 16 (destruct j as [|j]; [vm_compute; reflexivity | ]). lia.
  Qed.

  (* ---- one pass of the nibble loop, 0x1e0 .. 0x1f2 ---- *)
  Lemma wp_printk_hex_loop (γd : uart_names) (γv : disk_names)
      (K : nat) (pv pkv : mword 32) (dqm dqm2 : dfrac) (dg : mword 64) (b : bool) (pcur : mword 64) :
    (30 <= K)%nat ->
    eq_vec (sign_extend' 64 pv) zero_reg = false ->
    neq_vec (sign_extend' 64 pkv) zero_reg = false ->
    forall (n : nat) `(CID0 : CpuId) (mc : regfile) (l : list (bv 8)) (Rest : iProp Σ),
    (1 <= n <= 16)%nat ->
    mc !!! Regidx (mword_of_int 20 : mword 5) = mword_of_int (Z.of_nat n) ->
    mc !!! Regidx (mword_of_int 25 : mword 5) = dg ->
    sie_cap_gpr mc (K - 24)%nat b pcur -∗
    kernel_text -∗ pk_digits dg -∗
    pc_is (mword_of_int (KernelSyms.printk + 0x1e0) : mword 64) -∗
    (mword_of_int KernelSyms.panicking : mword 64) ↦₄{ dqm } pv -∗
    (mword_of_int KernelSyms.panicked : mword 64) ↦₄{ dqm2 } pkv -∗
    dev_inv γd γv -∗ uart_tx_own γd l -∗ uart_dlab_off γd -∗
    Rest -∗
    wp_next (CID0 := CID0) b pcur (fun (CID : CpuId) =>
      ∀ (mf : regfile) (bs : list (bv 8)),
      ⌜ forall c : mword 5, is_cs_idx c = true ->
          c <> mword_of_int 20 -> c <> mword_of_int 21 ->
          mf !!! Regidx c = mc !!! Regidx c ⌝ -∗
      sie_cap_gpr mf (K - 24)%nat b pcur -∗
      pc_is (mword_of_int (KernelSyms.printk + 0x1f6) : mword 64) -∗
      (mword_of_int KernelSyms.panicking : mword 64) ↦₄{ dqm } pv -∗
      (mword_of_int KernelSyms.panicked : mword 64) ↦₄{ dqm2 } pkv -∗
      uart_tx_own γd (l ++ bs) -∗ uart_sent γd (l ++ bs) -∗
      Rest -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros HK Hpv Hpkv.
    assert (HK6 : (6 <= K - 24)%nat) by lia.
    induction n as [|n IH]; intros CID0 mc l Rest Hn Hs4 Hs9; [lia | ].
    iIntros "Hcg #Htext #Hdig Hpc Hpanicking Hpanicked #Hdev Htx #Hdlab HR Hcont".
    (* +0x1e0 srli a5,s5,0x3c : the top nibble *)
    iApply (wp_srli4_s_sconf (mword_of_int (KernelSyms.printk + 0x1e0)) a5_idx (mword_of_int 21 : mword 5)
              (mword_of_int 60 : mword 6) mc (K - 24)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc [] [-]").
    { iApply (pki_1e0 with "Htext"). }
    iIntros (CID1 Hst1) "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (nib := shift_bits_right (mc !!! Regidx (mword_of_int 21 : mword 5))
                  (subrange_vec_dec (mword_of_int 60 : mword 6) (Z.sub log2_xlen 1) 0)).
    set (P1 := <[Regidx a5_idx := regval_into_reg nib]> mc).
    assert (Hnib : uint nib < 16) by apply srli60_lt16.
    assert (Hnib0 : 0 <= uint nib) by apply pi_uint_nonneg.
    assert (HP1a5 : P1 !!! Regidx a5_idx = nib) by (rewrite /P1 upd_eq; reflexivity).
    assert (HP1s9 : P1 !!! Regidx (mword_of_int 25 : mword 5) = dg)
      by (rewrite /P1 upd_ne; [exact Hs9 | reg_neq]).
    assert (Hp1e4 : add_vec_int (mword_of_int (KernelSyms.printk + 0x1e0) : mword 64) 4 = mword_of_int (KernelSyms.printk + 0x1e4)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp1e4) in "Hpc".
    (* +0x1e4 c.add a5,a5,s9 : &digits[nibble] *)
    iApply (wp_cadd_s_sconf (mword_of_int (KernelSyms.printk + 0x1e4)) a5_idx (mword_of_int 25 : mword 5)
              P1 (K - 24)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc [] [-]").
    { iApply (pki_1e4 with "Htext"). }
    iIntros (CID2 Hst2) "Hcg Hpc".
    iEval (rgne; rgne) in "Hcg".
    set (P2 := <[Regidx a5_idx := regval_into_reg (add_vec (P1 !!! Regidx a5_idx) (P1 !!! Regidx (mword_of_int 25 : mword 5)))]> P1).
    assert (HP2a5 : P2 !!! Regidx a5_idx = pa_add dg (Z.to_nat (uint nib))).
    { rewrite /P2 upd_eq. unfold regval_into_reg. rewrite HP1a5 HP1s9.
      apply add_vec_pa_add. }
    assert (Hp1e6 : add_vec_int (mword_of_int (KernelSyms.printk + 0x1e4) : mword 64) 2 = mword_of_int (KernelSyms.printk + 0x1e6)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp1e6) in "Hpc".
    (* +0x1e6 lbu a0,0(a5) : the digit character, out of the image *)
    iDestruct (big_sepL_lookup _ _ (Z.to_nat (uint nib)) (Z.to_nat (uint nib)) with "Hdig")
      as (dbyte) "Hdb".
    { rewrite lookup_seq_lt; [reflexivity | lia]. }
    assert (Hlba : add_vec (rget P2 a5_idx) (sign_extend' 64 (mword_of_int 0 : mword 12))
                   = pa_add dg (Z.to_nat (uint nib))).
    { rgne. rewrite HP2a5.
      replace (sign_extend' 64 (mword_of_int 0 : mword 12)) with (mword_of_int 0 : mword 64)
        by (apply bv_eq; vm_compute; reflexivity).
      apply kv_addv_zero. }
    iEval (rewrite -Hlba) in "Hdb".
    iApply (wp_lbu_s_sconf (mword_of_int (KernelSyms.printk + 0x1e6)) a0_idx a5_idx
              (mword_of_int 0 : mword 12) P2 (K - 24)%nat (dbyte : mword 8) b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc [] Hdb [-]").
    { iApply (pki_1e6 with "Htext"). }
    iIntros (CID3 Hst3) "Hcg Hpc _".
    set (P3 := <[Regidx a0_idx := regval_into_reg (zero_extend' 64 (dbyte : mword 8))]> P2).
    assert (Hp1ea : add_vec_int (mword_of_int (KernelSyms.printk + 0x1e6) : mword 64) 4 = mword_of_int (KernelSyms.printk + 0x1ea)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp1ea) in "Hpc".
    (* +0x1ea jal consputc *)
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.printk + 0x1ea)) ra_idx (mword_of_int 2096022 : mword 21)
              P3 (K - 24)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(vm_compute; reflexivity)
              with "Hcg Hpc [] [-]").
    { iApply (pki_1ea with "Htext"). }
    iIntros (CID4 Hst4) "Hcg Hpc".
    set (P4 := <[Regidx ra_idx := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.printk + 0x1ea) : mword 64) 4)]> P3).
    assert (Htgtc : add_vec (mword_of_int (KernelSyms.printk + 0x1ea) : mword 64) (sign_extend' 64 (mword_of_int 2096022 : mword 21)) = mword_of_int KernelSyms.consputc) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgtc) in "Hpc".
    iApply (wp_consputc (CID0 := CID4) γd γv P4 (K - 24)%nat l pv pkv dqm dqm2 b pcur HK6 Hpv Hpkv
              with "Hcg Htext Hpc Hpanicking Hpanicked Hdev Htx Hdlab [-]").
    iIntros (CID5 Hst5 m1 bs) "Hcg Hpc %Hcs Hpanicking Hpanicked Htx #Hsent".
    destruct Hcs as [Hcs Hra].
    assert (Hret : ret_pc (P4 !!! Regidx ra_idx) = mword_of_int (KernelSyms.printk + 0x1ee))
      by (rewrite /P4 upd_eq; unfold ret_pc; apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hret) in "Hpc".
    (* the two registers the body still needs survived the call *)
    assert (Hm1s4 : m1 !!! Regidx (mword_of_int 20 : mword 5) = mword_of_int (Z.of_nat (S n))).
    { rewrite (callee_saved_lookup Hcs (mword_of_int 20 : mword 5) ltac:(vm_compute; reflexivity)).
      rewrite /P4 upd_ne; [| reg_neq]. rewrite /P3 upd_ne; [| reg_neq].
      rewrite /P2 upd_ne; [| reg_neq]. rewrite /P1 upd_ne; [exact Hs4 | reg_neq]. }
    assert (Hm1s9 : m1 !!! Regidx (mword_of_int 25 : mword 5) = dg).
    { rewrite (callee_saved_lookup Hcs (mword_of_int 25 : mword 5) ltac:(vm_compute; reflexivity)).
      rewrite /P4 upd_ne; [| reg_neq]. rewrite /P3 upd_ne; [| reg_neq].
      rewrite /P2 upd_ne; [| reg_neq]. rewrite /P1 upd_ne; [exact Hs9 | reg_neq]. }
    (* +0x1ee c.slli s5,s5,0x4 : peel the nibble off *)
    iApply (wp_cslli_s_sconf (mword_of_int (KernelSyms.printk + 0x1ee)) (Regidx (mword_of_int 21 : mword 5))
              (mword_of_int 21 : mword 5) (mword_of_int 4 : mword 6) m1 (K - 24)%nat b
              eq_refl ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc [] [-]").
    { iApply (pki_1ee with "Htext"). }
    iIntros (CID6 Hst6) "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (P5 := <[Regidx (mword_of_int 21 : mword 5) := regval_into_reg
                   (shift_bits_left (m1 !!! Regidx (mword_of_int 21 : mword 5))
                      (subrange_vec_dec (mword_of_int 4 : mword 6) (Z.sub log2_xlen 1) 0))]> m1).
    assert (HP5s4 : P5 !!! Regidx (mword_of_int 20 : mword 5) = mword_of_int (Z.of_nat (S n)))
      by (rewrite /P5 upd_ne; [exact Hm1s4 | reg_neq]).
    assert (HP5s9 : P5 !!! Regidx (mword_of_int 25 : mword 5) = dg)
      by (rewrite /P5 upd_ne; [exact Hm1s9 | reg_neq]).
    assert (Hp1f0 : add_vec_int (mword_of_int (KernelSyms.printk + 0x1ee) : mword 64) 2 = mword_of_int (KernelSyms.printk + 0x1f0)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp1f0) in "Hpc".
    (* +0x1f0 c.addiw s4,s4,-1 *)
    iApply (wp_caddiw_s_sconf (mword_of_int (KernelSyms.printk + 0x1f0)) (mword_of_int 20 : mword 5)
              (mword_of_int 63 : mword 6) P5 (K - 24)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc [] [-]").
    { iApply (pki_1f0 with "Htext"). }
    iIntros (CID7 Hst7) "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (P6 := <[Regidx (mword_of_int 20 : mword 5) := regval_into_reg
                   (sign_extend' 64 (subrange_vec_dec
                      (add_vec (P5 !!! Regidx (mword_of_int 20 : mword 5))
                         (sign_extend' 64 (sign_extend' 12 (mword_of_int 63 : mword 6)))) 31 0))]> P5).
    assert (HP6s4 : P6 !!! Regidx (mword_of_int 20 : mword 5) = mword_of_int (Z.of_nat n)).
    { rewrite /P6 upd_eq. unfold regval_into_reg. rewrite HP5s4.
      rewrite (addiw_lit (Z.of_nat (S n)) (-1)
                 (sign_extend' 64 (sign_extend' 12 (mword_of_int 63 : mword 6)))
                 ltac:(apply bv_eq; vm_compute; reflexivity)
                 ltac:(change (2^31) with 2147483648; lia)).
      f_equal. lia. }
    assert (HP6s9 : P6 !!! Regidx (mword_of_int 25 : mword 5) = dg)
      by (rewrite /P6 upd_ne; [exact HP5s9 | reg_neq]).
    (* what this pass kept, for either exit *)
    assert (Hkept : forall c : mword 5, is_cs_idx c = true ->
                      c <> mword_of_int 20 -> c <> mword_of_int 21 ->
                      P6 !!! Regidx c = mc !!! Regidx c).
    { intros c Hc N20 N21.
      pose proof (is_cs_idx_true_neq ra_idx c ltac:(vm_compute; reflexivity) Hc) as N1.
      pose proof (is_cs_idx_true_neq a0_idx c ltac:(vm_compute; reflexivity) Hc) as N10.
      pose proof (is_cs_idx_true_neq a5_idx c ltac:(vm_compute; reflexivity) Hc) as N15.
      rewrite /P6 upd_ne; [| congruence]. rewrite /P5 upd_ne; [| congruence].
      rewrite (callee_saved_lookup Hcs c Hc).
      rewrite /P4 upd_ne; [| congruence]. rewrite /P3 upd_ne; [| congruence].
      rewrite /P2 upd_ne; [| congruence]. rewrite /P1 upd_ne; [reflexivity | congruence]. }
    assert (Hp1f2 : add_vec_int (mword_of_int (KernelSyms.printk + 0x1f0) : mword 64) 2 = mword_of_int (KernelSyms.printk + 0x1f2)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp1f2) in "Hpc".
    (* +0x1f2 bnez s4 : sixteen nibbles or done *)
    destruct n as [|n'].
    - (* the sixteenth: fall through to the s9 restore *)
      assert (Hz : neq_vec (P6 !!! Regidx (mword_of_int 20 : mword 5)) zero_reg = false).
      { rewrite HP6s4. rewrite (moi_small_nz 0 ltac:(lia)). reflexivity. }
      iApply (wp_bnez_x0_fall_s_sconf (mword_of_int (KernelSyms.printk + 0x1f2)) (mword_of_int 8174 : mword 13)
                (mword_of_int 20 : mword 5) P6 (K - 24)%nat b
                ltac:(vm_compute; discriminate) ltac:(rgne; exact Hz)
                with "Hcg Hpc [] [-]").
      { iApply (pki_1f2 with "Htext"). }
      iIntros (CID8 Hst8) "Hcg Hpc".
      assert (Hp1f6 : add_vec_int (mword_of_int (KernelSyms.printk + 0x1f2) : mword 64) 4 = mword_of_int (KernelSyms.printk + 0x1f6)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hp1f6) in "Hpc".
      iSpecialize ("Hcont" $! CID8 with "[%]"); [wp_next_chain|].
      iApply ("Hcont" $! P6 bs with "[%] Hcg Hpc Hpanicking Hpanicked Htx Hsent HR").
      exact Hkept.
    - (* another nibble: back to 0x1e0 with the counter one lower *)
      assert (Hne : neq_vec (P6 !!! Regidx (mword_of_int 20 : mword 5)) zero_reg = true).
      { rewrite HP6s4. rewrite (moi_small_nz (S n') ltac:(lia)). reflexivity. }
      iApply (wp_bnez_x0_taken_s_sconf (mword_of_int (KernelSyms.printk + 0x1f2)) (mword_of_int 8174 : mword 13)
                (mword_of_int 20 : mword 5) P6 (K - 24)%nat b
                ltac:(vm_compute; discriminate) ltac:(rgne; exact Hne)
                ltac:(vm_compute; reflexivity)
                with "Hcg Hpc [] [-]").
      { iApply (pki_1f2 with "Htext"). }
      iIntros (CID8b Hst8b). iNext. iIntros "Hcg Hpc".
      assert (Htgth : add_vec (mword_of_int (KernelSyms.printk + 0x1f2) : mword 64) (sign_extend' 64 (mword_of_int 8174 : mword 13)) = mword_of_int (KernelSyms.printk + 0x1e0)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Htgth) in "Hpc".
      assert (Hshift : b = false \/ pcur = zero_reg -> (CID8b : CPU) = (CID0 : CPU)) by wp_next_chain.
      iDestruct (wp_next_shift Hshift with "Hcont") as "Hcont".
      iApply (IH CID8b P6 (l ++ bs)%list Rest ltac:(lia) HP6s4 HP6s9
                with "Hcg Htext Hdig Hpc Hpanicking Hpanicked Hdev Htx Hdlab HR [-]").
      iIntros (CID9 Hst9 mf bs2) "%Hkept2 Hcg Hpc Hpanicking Hpanicked Htx Hsent2 HR".
      iEval (rewrite -app_assoc) in "Htx".
      iEval (rewrite -app_assoc) in "Hsent2".
      iSpecialize ("Hcont" $! CID9 with "[%]"); [wp_next_chain|].
      iApply ("Hcont" $! mf (bs ++ bs2)%list with "[%] Hcg Hpc Hpanicking Hpanicked Htx Hsent2 HR").
      intros c Hc N20 N21. rewrite (Hkept2 c Hc N20 N21). exact (Hkept c Hc N20 N21).
  Qed.

  (* ---- the arm around it, 0x1b4 .. 0x1f8 ---- *)
  Lemma wp_printk_arm_p `{CID0 : CpuId} (γd : uart_names) (γv : disk_names)
      (m mc : regfile) (K : nat) (k : nat) (l : list (bv 8)) (pv pkv : mword 32)
      (dqm dqm2 : dfrac) (Rest : iProp Σ) (b : bool) (pcur : mword 64) :
    let sp0 := m !!! Regidx csp_rs1 in
    let spd := add_vec sp0 (sign_extend' 64 (caddi16sp_imm (mword_of_int 52 : mword 6))) in
    let s0v := add_vec sp0 (sign_extend' 64 (mword_of_int (-64) : mword 12)) in
    (30 <= K)%nat ->
    (k < 7)%nat ->
    eq_vec (sign_extend' 64 pv) zero_reg = false ->
    neq_vec (sign_extend' 64 pkv) zero_reg = false ->
    mc !!! Regidx csp_rs1 = spd ->
    mc !!! Regidx s0_idx = s0v ->
    sie_cap_gpr mc (K - 24)%nat b pcur -∗
    kernel_text -∗ kernel_data -∗
    pc_is (mword_of_int (KernelSyms.printk + 0x1b4) : mword 64) -∗
    (∃ w : mword 64, (pa_stk sp0 19) ↦₈ w) -∗
    (pa_stk sp0 23) ↦₈ (pk_ap s0v k) -∗
    pk_va sp0 m -∗
    (mword_of_int KernelSyms.panicking : mword 64) ↦₄{ dqm } pv -∗
    (mword_of_int KernelSyms.panicked : mword 64) ↦₄{ dqm2 } pkv -∗
    dev_inv γd γv -∗ uart_tx_own γd l -∗ uart_dlab_off γd -∗
    Rest -∗
    wp_next (CID0 := CID0) b pcur (fun (CID : CpuId) =>
      ∀ (mf : regfile) (bs : list (bv 8)),
      ⌜ forall c : mword 5, is_cs_idx c = true ->
          c <> mword_of_int 20 -> c <> mword_of_int 21 ->
          mf !!! Regidx c = mc !!! Regidx c ⌝ -∗
      sie_cap_gpr mf (K - 24)%nat b pcur -∗
      pc_is (mword_of_int (KernelSyms.printk + 0x78) : mword 64) -∗
      (∃ w : mword 64, (pa_stk sp0 19) ↦₈ w) -∗
      (pa_stk sp0 23) ↦₈ (pk_ap s0v (S k)) -∗
      pk_va sp0 m -∗
      (mword_of_int KernelSyms.panicking : mword 64) ↦₄{ dqm } pv -∗
      (mword_of_int KernelSyms.panicked : mword 64) ↦₄{ dqm2 } pkv -∗
      uart_tx_own γd (l ++ bs) -∗ uart_sent γd (l ++ bs) -∗
      Rest -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros sp0 spd s0v HK Hk Hpv Hpkv Hsp Hs0.
    assert (HK6 : (6 <= K - 24)%nat) by lia.
    iIntros "Hcg #Htext #Hdata Hpc S19 Hap Hva Hpanicking Hpanicked #Hdev Htx #Hdlab HR Hcont".
    iPoseProof (pk_digits_data with "Hdata") as "#Hdig".
    iDestruct "S19" as (w19) "S19".
    assert (Hb19 : add_vec spd (zero_extend' 64 (concat_vec (mword_of_int 5 : mword 6) ('b"000"))) = pa_stk sp0 19).
    { unfold spd, pa_stk, add_vec_int. rewrite pa_stk_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    (* +0x1b4 sd s9,40(sp) : the one lazy save this arm makes *)
    iEval (rewrite -Hb19 -Hsp) in "S19".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.printk + 0x1b4)) (mword_of_int 5 : mword 6)
              (mword_of_int 25 : mword 5) mc (K - 24)%nat w19 b
              with "Hcg Hpc [] S19 [-]").
    { iApply (pki_1b4 with "Htext"). }
    iIntros (CID1 Hst1) "Hcg Hpc S19". iEval (rewrite Hsp Hb19) in "S19". iEval (rgne) in "S19".
    assert (Hp1b6 : add_vec_int (mword_of_int (KernelSyms.printk + 0x1b4) : mword 64) 2 = mword_of_int (KernelSyms.printk + 0x1b6 + 0)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp1b6) in "Hpc".
    iApply (wp_printk_vaarg mc K 0x1b6 sp0 s0v k b pcur Hs0 eq_refl
              with "Hcg [] Hpc Hap [-]").
    { rewrite /pk_vaarg_instrs.
      iSplitR; [iApply (pki_1b6 with "Htext") | ].
      iSplitR; [iApply (pki_1ba with "Htext") | ].
      iApply (pki_1be with "Htext"). }
    iIntros (CIDv Hstv V) "%Hv Hcg Hpc Hap".
    destruct Hv as (Hva5 & Hvs0 & Hvk).
    assert (Hp1c2 : (mword_of_int (KernelSyms.printk + 0x1b6 + 12) : mword 64) = mword_of_int (KernelSyms.printk + 0x1c2))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp1c2) in "Hpc".
    (* +0x1c2 ld s5,0(a5) : the pointer *)
    iDestruct (pk_va_acc sp0 m k Hk with "Hva") as "[Hslot Hvacl]".
    assert (Hlda : add_vec (rget V a5_idx) (sign_extend' 64 (mword_of_int 0 : mword 12)) = pa_stk sp0 (7 - k)).
    { rgne. rewrite Hva5.
      replace (sign_extend' 64 (mword_of_int 0 : mword 12)) with (mword_of_int 0 : mword 64)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite kv_addv_zero. apply pk_ap_slot. exact Hk. }
    iEval (rewrite -Hlda) in "Hslot".
    iApply (wp_ld_s_sconf (mword_of_int (KernelSyms.printk + 0x1c2)) (mword_of_int 21 : mword 5) a5_idx
              (mword_of_int 0 : mword 12) V (K - 24)%nat (pk_vararg m k) b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc [] Hslot [-]").
    { iApply (pki_1c2 with "Htext"). }
    iIntros (CID2 Hst2) "Hcg Hpc Hslot". iEval (rewrite Hlda) in "Hslot".
    iDestruct ("Hvacl" with "Hslot") as "Hva".
    set (Q1 := <[Regidx (mword_of_int 21 : mword 5) := regval_into_reg (pk_vararg m k)]> V).
    assert (Hp1c6 : add_vec_int (mword_of_int (KernelSyms.printk + 0x1c2) : mword 64) 4 = mword_of_int (KernelSyms.printk + 0x1c6)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp1c6) in "Hpc".
    (* +0x1c6 li a0,'0' ; +0x1ca jal consputc *)
    iApply (wp_li4_s_sconf (mword_of_int (KernelSyms.printk + 0x1c6)) a0_idx (mword_of_int 48 : mword 12)
              (mword_of_int 48 : mword 64) Q1 (K - 24)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc [] [-]").
    { iApply (pki_1c6 with "Htext"). }
    iIntros (CID3 Hst3) "Hcg Hpc".
    set (Q2 := <[Regidx a0_idx := regval_into_reg (mword_of_int 48 : mword 64)]> Q1).
    assert (Hp1ca : add_vec_int (mword_of_int (KernelSyms.printk + 0x1c6) : mword 64) 4 = mword_of_int (KernelSyms.printk + 0x1ca)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp1ca) in "Hpc".
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.printk + 0x1ca)) ra_idx (mword_of_int 2096054 : mword 21)
              Q2 (K - 24)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(vm_compute; reflexivity)
              with "Hcg Hpc [] [-]").
    { iApply (pki_1ca with "Htext"). }
    iIntros (CID4 Hst4) "Hcg Hpc".
    set (Q3 := <[Regidx ra_idx := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.printk + 0x1ca) : mword 64) 4)]> Q2).
    assert (Htgtc1 : add_vec (mword_of_int (KernelSyms.printk + 0x1ca) : mword 64) (sign_extend' 64 (mword_of_int 2096054 : mword 21)) = mword_of_int KernelSyms.consputc) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgtc1) in "Hpc".
    iApply (wp_consputc (CID0 := CID4) γd γv Q3 (K - 24)%nat l pv pkv dqm dqm2 b pcur HK6 Hpv Hpkv
              with "Hcg Htext Hpc Hpanicking Hpanicked Hdev Htx Hdlab [-]").
    iIntros (CID5 Hst5 m1 bs1) "Hcg Hpc %Hcs1 Hpanicking Hpanicked Htx #Hsent1".
    destruct Hcs1 as [Hcs1 Hra1].
    assert (Hret1 : ret_pc (Q3 !!! Regidx ra_idx) = mword_of_int (KernelSyms.printk + 0x1ce))
      by (rewrite /Q3 upd_eq; unfold ret_pc; apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hret1) in "Hpc".
    (* +0x1ce li a0,'x' ; +0x1d2 jal consputc *)
    iApply (wp_li4_s_sconf (mword_of_int (KernelSyms.printk + 0x1ce)) a0_idx (mword_of_int 120 : mword 12)
              (mword_of_int 120 : mword 64) m1 (K - 24)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc [] [-]").
    { iApply (pki_1ce with "Htext"). }
    iIntros (CID6 Hst6) "Hcg Hpc".
    set (Q4 := <[Regidx a0_idx := regval_into_reg (mword_of_int 120 : mword 64)]> m1).
    assert (Hp1d2 : add_vec_int (mword_of_int (KernelSyms.printk + 0x1ce) : mword 64) 4 = mword_of_int (KernelSyms.printk + 0x1d2)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp1d2) in "Hpc".
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.printk + 0x1d2)) ra_idx (mword_of_int 2096046 : mword 21)
              Q4 (K - 24)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(vm_compute; reflexivity)
              with "Hcg Hpc [] [-]").
    { iApply (pki_1d2 with "Htext"). }
    iIntros (CID7 Hst7) "Hcg Hpc".
    set (Q5 := <[Regidx ra_idx := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.printk + 0x1d2) : mword 64) 4)]> Q4).
    assert (Htgtc2 : add_vec (mword_of_int (KernelSyms.printk + 0x1d2) : mword 64) (sign_extend' 64 (mword_of_int 2096046 : mword 21)) = mword_of_int KernelSyms.consputc) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgtc2) in "Hpc".
    iApply (wp_consputc (CID0 := CID7) γd γv Q5 (K - 24)%nat (l ++ bs1)%list pv pkv dqm dqm2 b pcur HK6 Hpv Hpkv
              with "Hcg Htext Hpc Hpanicking Hpanicked Hdev Htx Hdlab [-]").
    iIntros (CID8 Hst8 m2 bs2) "Hcg Hpc %Hcs2 Hpanicking Hpanicked Htx #Hsent2".
    destruct Hcs2 as [Hcs2 Hra2].
    assert (Hret2 : ret_pc (Q5 !!! Regidx ra_idx) = mword_of_int (KernelSyms.printk + 0x1d6))
      by (rewrite /Q5 upd_eq; unfold ret_pc; apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hret2) in "Hpc".
    (* +0x1d6 c.li s4,16 : the trip count *)
    iApply (wp_cli_s_sconf (mword_of_int (KernelSyms.printk + 0x1d6)) (mword_of_int 20 : mword 5)
              (mword_of_int 16 : mword 6) (mword_of_int 16 : mword 64) m2 (K - 24)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc [] [-]").
    { iApply (pki_1d6 with "Htext"). }
    iIntros (CID9 Hst9) "Hcg Hpc".
    set (Q6 := <[Regidx (mword_of_int 20 : mword 5) := regval_into_reg (mword_of_int 16 : mword 64)]> m2).
    assert (HQ6s4 : Q6 !!! Regidx (mword_of_int 20 : mword 5) = mword_of_int (Z.of_nat 16))
      by (rewrite /Q6 upd_eq; reflexivity).
    assert (Hp1d8 : add_vec_int (mword_of_int (KernelSyms.printk + 0x1d6) : mword 64) 2 = mword_of_int (KernelSyms.printk + 0x1d8)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp1d8) in "Hpc".
    (* +0x1d8 auipc s9,0x7 ; +0x1dc addi s9,s9,60 : &digits *)
    iApply (wp_auipc_s_sconf (mword_of_int (KernelSyms.printk + 0x1d8)) (mword_of_int 25 : mword 5)
              (mword_of_int 7 : mword 20) Q6 (K - 24)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc [] [-]").
    { iApply (pki_1d8 with "Htext"). }
    iIntros (CID10 Hst10) "Hcg Hpc".
    set (Q7 := <[Regidx (mword_of_int 25 : mword 5) := regval_into_reg
                   (add_vec (mword_of_int (KernelSyms.printk + 0x1d8) : mword 64) (auipc_off (mword_of_int 7 : mword 20)))]> Q6).
    assert (Hp1dc : add_vec_int (mword_of_int (KernelSyms.printk + 0x1d8) : mword 64) 4 = mword_of_int (KernelSyms.printk + 0x1dc)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp1dc) in "Hpc".
    iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.printk + 0x1dc)) (mword_of_int 25 : mword 5)
              (mword_of_int 25 : mword 5) (mword_of_int 78 : mword 12) Q7 (K - 24)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc [] [-]").
    { iApply (pki_1dc with "Htext"). }
    iIntros (CID11 Hst11) "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (Q8 := <[Regidx (mword_of_int 25 : mword 5) := regval_into_reg
                   (add_vec (Q7 !!! Regidx (mword_of_int 25 : mword 5))
                      (sign_extend' 64 (mword_of_int 78 : mword 12)))]> Q7).
    assert (HQ8s9 : Q8 !!! Regidx (mword_of_int 25 : mword 5) = (mword_of_int pk_digits_addr : mword 64)).
    { rewrite /Q8 upd_eq. unfold regval_into_reg. rewrite /Q7 upd_eq. unfold regval_into_reg.
      apply bv_eq; vm_compute; reflexivity. }
    assert (HQ8s4 : Q8 !!! Regidx (mword_of_int 20 : mword 5) = mword_of_int (Z.of_nat 16)).
    { rewrite /Q8 upd_ne; [| reg_neq]. rewrite /Q7 upd_ne; [exact HQ6s4 | reg_neq]. }
    assert (Hp1e0 : add_vec_int (mword_of_int (KernelSyms.printk + 0x1dc) : mword 64) 4 = mword_of_int (KernelSyms.printk + 0x1e0)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp1e0) in "Hpc".
    (* the sixteen nibbles *)
    iApply (wp_printk_hex_loop γd γv K pv pkv dqm dqm2 (mword_of_int pk_digits_addr : mword 64) b pcur
              HK Hpv Hpkv 16%nat CID11 Q8 (l ++ bs1 ++ bs2)%list
              ((pa_stk sp0 19) ↦₈ (mc !!! Regidx (mword_of_int 25 : mword 5)) ∗
               (pa_stk sp0 23) ↦₈ (pk_ap s0v (S k)) ∗ pk_va sp0 m ∗ Rest)%I
              ltac:(lia) HQ8s4 HQ8s9
              with "Hcg Htext Hdig Hpc Hpanicking Hpanicked Hdev [Htx] Hdlab [$S19 $Hap $Hva $HR] [-]").
    { iEval (rewrite app_assoc). iExact "Htx". }
    iIntros (CID12 Hst12 m3 bs3) "%Hkept3 Hcg Hpc Hpanicking Hpanicked Htx #Hsent3 (S19 & Hap & Hva & HR)".
    (* +0x1f6 ld s9,40(sp) : put s9 back *)
    assert (Hm3sp : m3 !!! Regidx csp_rs1 = spd).
    { rewrite (Hkept3 csp_rs1 ltac:(vm_compute; reflexivity)
                 ltac:(reg_neq) ltac:(reg_neq)).
      rewrite /Q8 upd_ne; [| reg_neq]. rewrite /Q7 upd_ne; [| reg_neq].
      rewrite /Q6 upd_ne; [| reg_neq].
      rewrite (callee_saved_lookup Hcs2 csp_rs1 ltac:(vm_compute; reflexivity)).
      rewrite /Q5 upd_ne; [| reg_neq]. rewrite /Q4 upd_ne; [| reg_neq].
      rewrite (callee_saved_lookup Hcs1 csp_rs1 ltac:(vm_compute; reflexivity)).
      rewrite /Q3 upd_ne; [| reg_neq]. rewrite /Q2 upd_ne; [| reg_neq].
      rewrite /Q1 upd_ne; [| reg_neq].
      rewrite (Hvk csp_rs1 ltac:(reg_neq) ltac:(reg_neq)). exact Hsp. }
    iEval (rewrite -Hb19 -Hm3sp) in "S19".
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.printk + 0x1f6)) (mword_of_int 5 : mword 6)
              (mword_of_int 25 : mword 5) m3 (K - 24)%nat
              (mc !!! Regidx (mword_of_int 25 : mword 5)) b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc [] S19 [-]").
    { iApply (pki_1f6 with "Htext"). }
    iIntros (CID13 Hst13) "Hcg Hpc S19". iEval (rewrite Hm3sp Hb19) in "S19".
    set (Q9 := <[Regidx (mword_of_int 25 : mword 5) := regval_into_reg (mc !!! Regidx (mword_of_int 25 : mword 5))]> m3).
    assert (Hp1f8 : add_vec_int (mword_of_int (KernelSyms.printk + 0x1f6) : mword 64) 2 = mword_of_int (KernelSyms.printk + 0x1f8)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp1f8) in "Hpc".
    (* +0x1f8 j 0x78 *)
    iApply (wp_cj_s_sconf (mword_of_int (KernelSyms.printk + 0x1f8)) (sign_extend' 21 (concat_vec (mword_of_int 1856 : mword 11) ('b"0")))
              Q9 (K - 24)%nat b ltac:(vm_compute; reflexivity)
              with "Hcg Hpc [] [-]").
    { iApply (pki_1f8 with "Htext"). }
    iIntros (CID14 Hst14). iNext. iIntros "Hcg Hpc".
    assert (Htgt78 : add_vec (mword_of_int (KernelSyms.printk + 0x1f8) : mword 64) (sign_extend' 64 (sign_extend' 21 (concat_vec (mword_of_int 1856 : mword 11) ('b"0")))) = mword_of_int (KernelSyms.printk + 0x78)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgt78) in "Hpc".
    iEval (rewrite -!app_assoc) in "Htx".
    iEval (rewrite -!app_assoc) in "Hsent3".
    iSpecialize ("Hcont" $! CID14 with "[%]"); [wp_next_chain|].
    iApply ("Hcont" $! Q9 (bs1 ++ bs2 ++ bs3)%list
              with "[%] Hcg Hpc [S19] Hap Hva Hpanicking Hpanicked Htx Hsent3 HR").
    - intros c Hc N20 N21.
      pose proof (is_cs_idx_true_neq ra_idx c ltac:(vm_compute; reflexivity) Hc) as N1.
      pose proof (is_cs_idx_true_neq a0_idx c ltac:(vm_compute; reflexivity) Hc) as N10.
      pose proof (is_cs_idx_true_neq (mword_of_int 14 : mword 5) c ltac:(vm_compute; reflexivity) Hc) as N14.
      pose proof (is_cs_idx_true_neq a5_idx c ltac:(vm_compute; reflexivity) Hc) as N15.
      destruct (decide (c = (mword_of_int 25 : mword 5))) as [-> | N25].
      { rewrite /Q9 upd_eq. reflexivity. }
      rewrite /Q9 upd_ne; [| congruence].
      rewrite (Hkept3 c Hc N20 N21).
      rewrite /Q8 upd_ne; [| congruence]. rewrite /Q7 upd_ne; [| congruence].
      rewrite /Q6 upd_ne; [| congruence].
      rewrite (callee_saved_lookup Hcs2 c Hc).
      rewrite /Q5 upd_ne; [| congruence]. rewrite /Q4 upd_ne; [| congruence].
      rewrite (callee_saved_lookup Hcs1 c Hc).
      rewrite /Q3 upd_ne; [| congruence]. rewrite /Q2 upd_ne; [| congruence].
      rewrite /Q1 upd_ne; [| congruence].
      apply Hvk; congruence.
    - iExists (mc !!! Regidx (mword_of_int 25 : mword 5)). iExact "S19".
  Qed.


  (* ------------------------------------------------------------------ *)
  (*  From the machine's BYTES to [pk_dir]'s CHARACTERS.                  *)
  (*                                                                     *)
  (*  Every test in the chain is either [beq s5, <const reg>] or an       *)
  (*  [addi rd, s5, -k] followed by [seqz].  Both reduce, once the byte   *)
  (*  is known to be a character's, to [Ascii.eqb] -- which is what       *)
  (*  [pk_dir] speaks.  Doing that once here is what keeps the chain a    *)
  (*  single linear walk instead of fifteen copies.                       *)
  (* ------------------------------------------------------------------ *)

  Definition pk_byte (c : Ascii.ascii) : mword 8 := Z_to_bv 8 (Z.of_N (Ascii.N_of_ascii c)).

  Lemma cstring_bytes_cons (c : Ascii.ascii) (f : string) :
    cstring_bytes (String.String c f) = pk_byte c :: cstring_bytes f.
  Proof. reflexivity. Qed.

  Lemma pk_fbyte_ch (f : string) (j : nat) :
    (j <= String.length f)%nat -> pk_fbyte f j = pk_byte (pk_ch f j).
  Proof.
    revert j. induction f as [|c f IH]; intros j Hj.
    - destruct j as [|j]; [ | cbn in Hj; lia ].
      rewrite /pk_fbyte /pk_byte /cstring_bytes /=. apply bv_eq; vm_compute; reflexivity.
    - destruct j as [|j].
      + rewrite /pk_fbyte cstring_bytes_cons. reflexivity.
      + rewrite /pk_fbyte cstring_bytes_cons.
        change ((pk_byte c :: cstring_bytes f) !!! S j) with (cstring_bytes f !!! j).
        rewrite -/(pk_fbyte f j). cbn [pk_ch]. apply IH. cbn in Hj. lia.
  Qed.

  (* [mword_of_int] is injective on the signed range: two literals a chain
     test compares are equal only if the integers are. *)
  Lemma moi64_inj_small (x y : Z) :
    -9223372036854775808 <= x < 9223372036854775808 ->
    -9223372036854775808 <= y < 9223372036854775808 ->
    (mword_of_int x : mword 64) = mword_of_int y -> x = y.
  Proof.
    intros Hx Hy H. apply (f_equal bv_unsigned) in H.
    rewrite !moi64_mod in H.
    assert (Hd : (x - y) `mod` 18446744073709551616 = 0).
    { rewrite Zminus_mod H Z.sub_diag. reflexivity. }
    apply Z.mod_divide in Hd; [| lia].
    destruct Hd as [q Hq]. lia.
  Qed.

  Lemma moi64_eqb_small (x y : Z) :
    -9223372036854775808 <= x < 9223372036854775808 ->
    -9223372036854775808 <= y < 9223372036854775808 ->
    eq_vec (mword_of_int x : mword 64) (mword_of_int y) = Z.eqb x y.
  Proof.
    intros Hx Hy.
    destruct (eq_vec (mword_of_int x : mword 64) (mword_of_int y)) eqn:E.
    - apply eq_vec_true_iff in E. symmetry. apply Z.eqb_eq.
      apply moi64_inj_small; assumption.
    - symmetry. apply Z.eqb_neq. intro Hc. subst y.
      assert (eq_vec (mword_of_int x : mword 64) (mword_of_int x) = true)
        by (apply eq_vec_true_iff; reflexivity).
      congruence.
  Qed.

  (* the character's code, as a plain [Z] bound -- stated separately because
     [lia] cannot cross [N] to [Z] under the bitvector zify hook. *)
  Lemma pk_N_bound (c : Ascii.ascii) : 0 <= Z.of_N (Ascii.N_of_ascii c) < 256.
  Proof.
    pose proof (Ascii.N_ascii_bounded c) as Hb.
    apply N2Z.inj_lt in Hb. change (Z.of_N 256) with 256 in Hb.
    split; [apply N2Z.is_nonneg | exact Hb].
  Qed.

  Lemma zext_pk_byte (c : Ascii.ascii) :
    (zero_extend' 64 (pk_byte c) : mword 64) = mword_of_int (Z.of_N (Ascii.N_of_ascii c)).
  Proof.
    destruct (pk_N_bound c) as [Hnn Hb].
    apply bv_eq. rewrite /pk_byte.
    unfold zero_extend', Operators_mwords.zero_extend, Operators_mwords.extz_vec,
      SailStdpp.Values.to_word, to_word, get_word, MachineWord.MachineWord.zero_extend.
    rewrite bv_zero_extend_unsigned; [ | vm_compute; intro Hc; discriminate Hc ].
    rewrite Z_to_bv_unsigned moi64_mod.
    unfold bv_wrap. change (bv_modulus 8) with 256.
    rewrite (Z.mod_small _ 256 (conj Hnn Hb)).
    rewrite Z.mod_small; [ reflexivity | ].
    split; [ exact Hnn | apply (Z.lt_trans _ 256); [exact Hb | reflexivity] ].
  Qed.

  (* the two shapes, as [Ascii.eqb] *)
  Lemma pk_eq_ascii (c d : Ascii.ascii) (x : mword 64) :
    x = mword_of_int (Z.of_N (Ascii.N_of_ascii d)) ->
    eq_vec (zero_extend' 64 (pk_byte c) : mword 64) x = Ascii.eqb c d.
  Proof.
    intros ->. rewrite zext_pk_byte.
    pose proof (pk_N_bound c); pose proof (pk_N_bound d).
    rewrite moi64_eqb_small; [| lia | lia].
    case_eq (Ascii.eqb c d); intro Hcd.
    - apply Ascii.eqb_eq in Hcd; subst. apply Z.eqb_refl.
    - apply Z.eqb_neq. intro Hz. apply N2Z.inj in Hz.
      apply not_true_iff_false in Hcd. apply Hcd. apply Ascii.eqb_eq.
      rewrite <- (Ascii.ascii_N_embedding c), <- (Ascii.ascii_N_embedding d), Hz. reflexivity.
  Qed.

  Lemma pk_sub_ascii (c d : Ascii.ascii) (y : mword 64) :
    y = mword_of_int (- Z.of_N (Ascii.N_of_ascii d)) ->
    eq_vec (add_vec (zero_extend' 64 (pk_byte c)) y) (zero_reg : mword 64) = Ascii.eqb c d.
  Proof.
    intros ->. rewrite zext_pk_byte moi_add.
    replace (zero_reg : mword 64) with (mword_of_int 0 : mword 64)
      by (apply bv_eq; vm_compute; reflexivity).
    pose proof (pk_N_bound c); pose proof (pk_N_bound d).
    rewrite moi64_eqb_small; [| lia | lia].
    case_eq (Ascii.eqb c d); intro Hcd.
    - apply Ascii.eqb_eq in Hcd; subst. apply Z.eqb_eq. lia.
    - apply Z.eqb_neq. intro Hz.
      assert (Hz' : Z.of_N (Ascii.N_of_ascii c) = Z.of_N (Ascii.N_of_ascii d)) by lia.
      apply N2Z.inj in Hz'.
      apply not_true_iff_false in Hcd. apply Hcd. apply Ascii.eqb_eq.
      rewrite <- (Ascii.ascii_N_embedding c), <- (Ascii.ascii_N_embedding d), Hz'. reflexivity.
  Qed.

  (* [seqz]: the model's [x <u 1] IS "x is zero" *)
  Lemma ltu1_eqz (x y : mword 64) :
    y = mword_of_int 1 -> zopz0zI_u x y = eq_vec x (zero_reg : mword 64).
  Proof.
    intros ->. unfold zopz0zI_u.
    assert (Hu1 : uint (mword_of_int 1 : mword 64) = 1) by (vm_compute; reflexivity).
    rewrite Hu1.
    destruct (eq_vec x (zero_reg : mword 64)) eqn:E.
    - apply eq_vec_true_iff in E. subst x. vm_compute. reflexivity.
    - apply Z.ltb_ge. pose proof (pi_uint_nonneg x) as Hx0.
      destruct (Z.eq_dec (uint x) 0) as [Hz | Hnz]; [ | lia ].
      exfalso.
      assert (Hxz : x = (zero_reg : mword 64)).
      { apply bv_eq. rewrite <- !uint_unsigned, Hz. vm_compute. reflexivity. }
      subst x.
      assert (eq_vec (zero_reg : mword 64) zero_reg = true)
        by (apply eq_vec_true_iff; reflexivity).
      congruence.
  Qed.

  (* a comparison's outcome, as it sits in a register between the [seqz] that
     produced it and the [bnez] that consumes it *)
  Definition pk_bit (b : bool) : mword 64 := zero_extend' 64 (bool_to_bit b).

  Lemma pk_bit_nz (b : bool) : neq_vec (pk_bit b) (zero_reg : mword 64) = b.
  Proof. destruct b; vm_compute; reflexivity. Qed.

  Lemma pk_bit_and (b1 b0 : bool) : and_vec (pk_bit b1) (pk_bit b0) = pk_bit (b1 && b0).
  Proof. destruct b1, b0; apply bv_eq; vm_compute; reflexivity. Qed.

  (* ================================================================== *)
  (*  THE DISPATCH (0x8a .. 0x328): which arm a directive selects.       *)
  (*                                                                     *)
  (*  gcc did not compile printk's if/else chain in source order.  It    *)
  (*  hoisted the three lookahead characters into s5 / a3 / (later) a3'  *)
  (*  and turned the "%l.." tests into two BOOLEAN FLAGS -- a4 for       *)
  (*  [c0 == 'l'] and a5 for [c0 == 'l' && c1 == 'l'] -- so a single     *)
  (*  comparison chain decides all fifteen arms.  [pk_dir] (PrintkFmt.v) *)
  (*  is the source-order reading; the two agree because the arms are    *)
  (*  pairwise disjoint on (c0,c1,c2), which is what the chain's proof   *)
  (*  has to establish case by case.                                     *)
  (*                                                                     *)
  (*  This is the SHARED HEAD: read c0, and c1 if there is one.  Three   *)
  (*  exits, corresponding to the three shapes [pk_kinds] distinguishes  *)
  (*  -- the string ends after '%' (c0 = 0), it ends one character later *)
  (*  (c1 = 0), or all three characters are there.                       *)
  (* ================================================================== *)

  (* the head leaves the two lookahead bytes in s5 and a3, [i+1] in s1 and
     a5, and [&f[i+1]] in a4 -- the last is what the THIRD byte is read
     through, at 0xf0, so it has to be named. *)
  Definition pk_disp_kept (mf mc : regfile) : Prop :=
    forall c : mword 5, c <> mword_of_int 9 -> c <> mword_of_int 21 ->
      c <> mword_of_int 13 -> c <> mword_of_int 14 -> c <> mword_of_int 15 ->
      mf !!! Regidx c = mc !!! Regidx c.

  Lemma wp_printk_disp_head `{CID0 : CpuId}
      (mc : regfile) (K : nat) (fmt : mword 64) (dqf : dfrac) (f : string) (i : nat)
      (Rest : iProp Σ) (b : bool) (pcur : mword 64) :
    (S i < length (cstring_bytes f))%nat ->
    (Z.of_nat i + 1 < 2^31) ->
    mc !!! Regidx (mword_of_int 20 : mword 5) = mword_of_int (Z.of_nat i) ->
    mc !!! Regidx s2_idx = fmt ->
    sie_cap_gpr mc (K - 24)%nat b pcur -∗
    kernel_text -∗
    pc_is (mword_of_int (KernelSyms.printk + 0x8a) : mword 64) -∗
    fmt ↦ₛ{ dqf } f -∗
    Rest -∗
    (* (a) c0 = 0: the format string ends right after the '%' *)
    wp_next (CID0 := CID0) b pcur (fun (CID : CpuId) =>
      ∀ mf : regfile,
      ⌜ pk_disp_kept mf mc
        /\ mf !!! Regidx (mword_of_int 9 : mword 5) = mword_of_int (Z.of_nat (S i))
        /\ mf !!! Regidx (mword_of_int 21 : mword 5) = zero_reg
        /\ pk_fbyte f (S i) = (mword_of_int 0 : mword 8) ⌝ -∗
      sie_cap_gpr mf (K - 24)%nat b pcur -∗
      pc_is (mword_of_int (KernelSyms.printk + 0x2aa) : mword 64) -∗
      fmt ↦ₛ{ dqf } f -∗ Rest -∗
      WP (Loop : expr riscv_lang)) -∗
    (* (b) c0 <> 0, c1 = 0: one character of directive and no more *)
    wp_next (CID0 := CID0) b pcur (fun (CID : CpuId) =>
      ∀ mf : regfile,
      ⌜ pk_disp_kept mf mc
        /\ mf !!! Regidx (mword_of_int 9 : mword 5) = mword_of_int (Z.of_nat (S i))
        /\ mf !!! Regidx (mword_of_int 21 : mword 5) = zero_extend' 64 (pk_fbyte f (S i))
        /\ mf !!! Regidx (mword_of_int 13 : mword 5) = zero_reg
        /\ pk_fbyte f (S i) <> (mword_of_int 0 : mword 8)
        /\ pk_fbyte f (S (S i)) = (mword_of_int 0 : mword 8) ⌝ -∗
      sie_cap_gpr mf (K - 24)%nat b pcur -∗
      pc_is (mword_of_int (KernelSyms.printk + 0x298) : mword 64) -∗
      fmt ↦ₛ{ dqf } f -∗ Rest -∗
      WP (Loop : expr riscv_lang)) -∗
    (* (c) both there: on into the comparison chain at 0xa4 *)
    wp_next (CID0 := CID0) b pcur (fun (CID : CpuId) =>
      ∀ mf : regfile,
      ⌜ pk_disp_kept mf mc
        /\ mf !!! Regidx (mword_of_int 9 : mword 5) = mword_of_int (Z.of_nat (S i))
        /\ mf !!! Regidx (mword_of_int 15 : mword 5) = mword_of_int (Z.of_nat (S i))
        /\ mf !!! Regidx (mword_of_int 14 : mword 5) = pa_add fmt (S i)
        /\ mf !!! Regidx (mword_of_int 21 : mword 5) = zero_extend' 64 (pk_fbyte f (S i))
        /\ mf !!! Regidx (mword_of_int 13 : mword 5) = zero_extend' 64 (pk_fbyte f (S (S i)))
        /\ pk_fbyte f (S i) <> (mword_of_int 0 : mword 8)
        /\ pk_fbyte f (S (S i)) <> (mword_of_int 0 : mword 8) ⌝ -∗
      sie_cap_gpr mf (K - 24)%nat b pcur -∗
      pc_is (mword_of_int (KernelSyms.printk + 0xa4) : mword 64) -∗
      fmt ↦ₛ{ dqf } f -∗ Rest -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hlen Hi31 Hs4 Hs2.
    iIntros "Hcg #Htext Hpc Hfmt HR K0 K1 Kgo".
    (* +0x8a addiw a5,s4,1 : the index of c0 *)
    iApply (wp_addiw_s_sconf (mword_of_int (KernelSyms.printk + 0x8a)) a5_idx (mword_of_int 20 : mword 5)
              (mword_of_int 1 : mword 12) mc (K - 24)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc [] [-]").
    { iApply (pki_8a with "Htext"). }
    iIntros (CID1 Hst1) "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (D1 := <[Regidx a5_idx := regval_into_reg
                   (sign_extend' 64 (subrange_vec_dec
                      (add_vec (mc !!! Regidx (mword_of_int 20 : mword 5))
                         (sign_extend' 64 (mword_of_int 1 : mword 12))) 31 0))]> mc).
    assert (HD1a5 : D1 !!! Regidx a5_idx = mword_of_int (Z.of_nat (S i))).
    { rewrite /D1 upd_eq. unfold regval_into_reg. rewrite Hs4.
      rewrite (addiw_lit (Z.of_nat i) 1 (sign_extend' 64 (mword_of_int 1 : mword 12))
                 ltac:(apply bv_eq; vm_compute; reflexivity)
                 ltac:(change (2^31) with 2147483648; lia)).
      f_equal. lia. }
    assert (HD1s2 : D1 !!! Regidx s2_idx = fmt) by (rewrite /D1 upd_ne; [exact Hs2 | reg_neq]).
    assert (Hp8e : add_vec_int (mword_of_int (KernelSyms.printk + 0x8a) : mword 64) 4 = mword_of_int (KernelSyms.printk + 0x8e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp8e) in "Hpc".
    (* +0x8e c.mv s1,a5 : the arm calling convention -- s1 is (next index) - 1 *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.printk + 0x8e)) (mword_of_int 9 : mword 5) a5_idx
              D1 (K - 24)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc [] [-]").
    { iApply (pki_8e with "Htext"). }
    iIntros (CID2 Hst2) "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (D2 := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg (add_vec zero_reg (D1 !!! Regidx a5_idx))]> D1).
    assert (HD2s1 : D2 !!! Regidx (mword_of_int 9 : mword 5) = mword_of_int (Z.of_nat (S i))).
    { rewrite /D2 upd_eq. unfold regval_into_reg. rewrite HD1a5. apply add_vec_zero_l. }
    assert (HD2a5 : D2 !!! Regidx a5_idx = mword_of_int (Z.of_nat (S i)))
      by (rewrite /D2 upd_ne; [exact HD1a5 | reg_neq]).
    assert (HD2s2 : D2 !!! Regidx s2_idx = fmt)
      by (rewrite /D2 upd_ne; [exact HD1s2 | reg_neq]).
    assert (Hp90 : add_vec_int (mword_of_int (KernelSyms.printk + 0x8e) : mword 64) 2 = mword_of_int (KernelSyms.printk + 0x90)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp90) in "Hpc".
    (* +0x90 add a4,s2,a5 : &f[i+1] *)
    iApply (wp_add_s_sconf (mword_of_int (KernelSyms.printk + 0x90)) (mword_of_int 14 : mword 5)
              s2_idx a5_idx (pa_add fmt (S i)) D2 (K - 24)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(rgne; rgne; rewrite HD2s2 HD2a5; unfold pa_add, add_vec_int; reflexivity)
              with "Hcg Hpc [] [-]").
    { iApply (pki_90 with "Htext"). }
    iIntros (CID3 Hst3) "Hcg Hpc".
    set (D3 := <[Regidx (mword_of_int 14 : mword 5) := regval_into_reg (pa_add fmt (S i))]> D2).
    assert (HD3a4 : D3 !!! Regidx (mword_of_int 14 : mword 5) = pa_add fmt (S i))
      by (rewrite /D3 upd_eq; reflexivity).
    assert (Hp94 : add_vec_int (mword_of_int (KernelSyms.printk + 0x90) : mword 64) 4 = mword_of_int (KernelSyms.printk + 0x94)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp94) in "Hpc".
    (* +0x94 lbu s5,0(a4) : c0 *)
    iDestruct (pk_str_byte fmt dqf f (S i) Hlen with "Hfmt") as "[Hb0 Hcl0]".
    assert (Hla0 : add_vec (rget D3 (mword_of_int 14 : mword 5))
                     (sign_extend' 64 (mword_of_int 0 : mword 12)) = pa_add fmt (S i)).
    { rgne. rewrite HD3a4.
      replace (sign_extend' 64 (mword_of_int 0 : mword 12)) with (mword_of_int 0 : mword 64)
        by (apply bv_eq; vm_compute; reflexivity).
      apply kv_addv_zero. }
    iEval (rewrite -Hla0) in "Hb0".
    iApply (wp_lbu_s_sconf (mword_of_int (KernelSyms.printk + 0x94)) (mword_of_int 21 : mword 5)
              (mword_of_int 14 : mword 5) (mword_of_int 0 : mword 12) D3 (K - 24)%nat
              (pk_fbyte f (S i)) b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc [] Hb0 [-]").
    { iApply (pki_94 with "Htext"). }
    iIntros (CID4 Hst4) "Hcg Hpc Hb0". iEval (rewrite Hla0) in "Hb0".
    iDestruct ("Hcl0" with "Hb0") as "Hfmt".
    set (D4 := <[Regidx (mword_of_int 21 : mword 5) := regval_into_reg (zero_extend' 64 (pk_fbyte f (S i)))]> D3).
    assert (HD4s5 : D4 !!! Regidx (mword_of_int 21 : mword 5) = zero_extend' 64 (pk_fbyte f (S i)))
      by (rewrite /D4 upd_eq; reflexivity).
    assert (HD4a4 : D4 !!! Regidx (mword_of_int 14 : mword 5) = pa_add fmt (S i))
      by (rewrite /D4 upd_ne; [exact HD3a4 | reg_neq]).
    assert (HD4s1 : D4 !!! Regidx (mword_of_int 9 : mword 5) = mword_of_int (Z.of_nat (S i))).
    { rewrite /D4 upd_ne; [| reg_neq]. rewrite /D3 upd_ne; [exact HD2s1 | reg_neq]. }
    assert (HD4a5 : D4 !!! Regidx a5_idx = mword_of_int (Z.of_nat (S i))).
    { rewrite /D4 upd_ne; [| reg_neq]. rewrite /D3 upd_ne; [exact HD2a5 | reg_neq]. }
    (* what the head has kept so far -- the same at all three exits *)
    assert (Hkept4 : pk_disp_kept D4 mc).
    { intros c N9 N21 N13 N14 N15.
      rewrite /D4 upd_ne; [| congruence]. rewrite /D3 upd_ne; [| congruence].
      rewrite /D2 upd_ne; [| congruence]. rewrite /D1 upd_ne; [reflexivity | congruence]. }
    assert (Hp98 : add_vec_int (mword_of_int (KernelSyms.printk + 0x94) : mword 64) 4 = mword_of_int (KernelSyms.printk + 0x98)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp98) in "Hpc".
    (* +0x98 beqz s5 : nothing after the '%' *)
    destruct (decide (pk_fbyte f (S i) = (mword_of_int 0 : mword 8))) as [Hc0 | Hc0].
    { iApply (wp_beqz_x0_taken_s_sconf (mword_of_int (KernelSyms.printk + 0x98)) (mword_of_int 530 : mword 13)
                (mword_of_int 21 : mword 5) D4 (K - 24)%nat b
                ltac:(vm_compute; discriminate)
                ltac:(rgne; rewrite HD4s5 Hc0; vm_compute; reflexivity)
                ltac:(vm_compute; reflexivity)
                with "Hcg Hpc [] [-]").
      { iApply (pki_98 with "Htext"). }
      iIntros (CID5 Hst5). iNext. iIntros "Hcg Hpc".
      assert (Htgt : add_vec (mword_of_int (KernelSyms.printk + 0x98) : mword 64) (sign_extend' 64 (mword_of_int 530 : mword 13)) = mword_of_int (KernelSyms.printk + 0x2aa)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Htgt) in "Hpc".
      iSpecialize ("K0" $! CID5 with "[%]"); [wp_next_chain|].
      iApply ("K0" $! D4 with "[%] Hcg Hpc Hfmt HR").
      split_and!; [exact Hkept4 | exact HD4s1 | rewrite HD4s5 Hc0; apply bv_eq; vm_compute; reflexivity | exact Hc0]. }
    iApply (wp_beqz_x0_fall_s_sconf (mword_of_int (KernelSyms.printk + 0x98)) (mword_of_int 530 : mword 13)
              (mword_of_int 21 : mword 5) D4 (K - 24)%nat b
              ltac:(vm_compute; discriminate)
              ltac:(rgne; rewrite HD4s5; apply zext8_nonzero; exact Hc0)
              with "Hcg Hpc [] [-]").
    { iApply (pki_98 with "Htext"). }
    iIntros (CID6 Hst6) "Hcg Hpc".
    assert (Hp9c : add_vec_int (mword_of_int (KernelSyms.printk + 0x98) : mword 64) 4 = mword_of_int (KernelSyms.printk + 0x9c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp9c) in "Hpc".
    (* c0 <> 0 means [i+1] is a character, so [i+2] is still inside the string *)
    assert (Hlen2 : (S (S i) < length (cstring_bytes f))%nat).
    { rewrite cstring_bytes_length. rewrite cstring_bytes_length in Hlen.
      destruct (decide (S i = String.length f)) as [He | He].
      - exfalso. apply Hc0. rewrite -(string_bytes_length f) in He.
        rewrite He. apply pk_fbyte_nul.
      - lia. }
    (* +0x9c lbu a3,1(a4) : c1 *)
    iDestruct (pk_str_byte fmt dqf f (S (S i)) Hlen2 with "Hfmt") as "[Hb1 Hcl1]".
    assert (Hla1 : add_vec (rget D4 (mword_of_int 14 : mword 5))
                     (sign_extend' 64 (mword_of_int 1 : mword 12)) = pa_add fmt (S (S i))).
    { rgne. rewrite HD4a4.
      replace (sign_extend' 64 (mword_of_int 1 : mword 12)) with (mword_of_int 1 : mword 64)
        by (apply bv_eq; vm_compute; reflexivity).
      apply pa_add_S. }
    iEval (rewrite -Hla1) in "Hb1".
    iApply (wp_lbu_s_sconf (mword_of_int (KernelSyms.printk + 0x9c)) (mword_of_int 13 : mword 5)
              (mword_of_int 14 : mword 5) (mword_of_int 1 : mword 12) D4 (K - 24)%nat
              (pk_fbyte f (S (S i))) b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc [] Hb1 [-]").
    { iApply (pki_9c with "Htext"). }
    iIntros (CID7 Hst7) "Hcg Hpc Hb1". iEval (rewrite Hla1) in "Hb1".
    iDestruct ("Hcl1" with "Hb1") as "Hfmt".
    set (D5 := <[Regidx (mword_of_int 13 : mword 5) := regval_into_reg (zero_extend' 64 (pk_fbyte f (S (S i))))]> D4).
    assert (HD5a3 : D5 !!! Regidx (mword_of_int 13 : mword 5) = zero_extend' 64 (pk_fbyte f (S (S i))))
      by (rewrite /D5 upd_eq; reflexivity).
    assert (HD5s5 : D5 !!! Regidx (mword_of_int 21 : mword 5) = zero_extend' 64 (pk_fbyte f (S i)))
      by (rewrite /D5 upd_ne; [exact HD4s5 | reg_neq]).
    assert (HD5s1 : D5 !!! Regidx (mword_of_int 9 : mword 5) = mword_of_int (Z.of_nat (S i)))
      by (rewrite /D5 upd_ne; [exact HD4s1 | reg_neq]).
    assert (HD5a5 : D5 !!! Regidx a5_idx = mword_of_int (Z.of_nat (S i)))
      by (rewrite /D5 upd_ne; [exact HD4a5 | reg_neq]).
    assert (HD5a4 : D5 !!! Regidx (mword_of_int 14 : mword 5) = pa_add fmt (S i))
      by (rewrite /D5 upd_ne; [exact HD4a4 | reg_neq]).
    assert (Hkept5 : pk_disp_kept D5 mc).
    { intros c N9 N21 N13 N14 N15.
      rewrite /D5 upd_ne; [| congruence]. apply Hkept4; assumption. }
    assert (Hpa0 : add_vec_int (mword_of_int (KernelSyms.printk + 0x9c) : mword 64) 4 = mword_of_int (KernelSyms.printk + 0xa0)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpa0) in "Hpc".
    (* +0xa0 beqz a3 : one character of directive and no more *)
    destruct (decide (pk_fbyte f (S (S i)) = (mword_of_int 0 : mword 8))) as [Hc1 | Hc1].
    - iApply (wp_beqz_x0_taken_s_sconf (mword_of_int (KernelSyms.printk + 0xa0)) (mword_of_int 504 : mword 13)
                (mword_of_int 13 : mword 5) D5 (K - 24)%nat b
                ltac:(vm_compute; discriminate)
                ltac:(rgne; rewrite HD5a3 Hc1; vm_compute; reflexivity)
                ltac:(vm_compute; reflexivity)
                with "Hcg Hpc [] [-]").
      { iApply (pki_a0 with "Htext"). }
      iIntros (CID8 Hst8). iNext. iIntros "Hcg Hpc".
      assert (Htgt : add_vec (mword_of_int (KernelSyms.printk + 0xa0) : mword 64) (sign_extend' 64 (mword_of_int 504 : mword 13)) = mword_of_int (KernelSyms.printk + 0x298)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Htgt) in "Hpc".
      iSpecialize ("K1" $! CID8 with "[%]"); [wp_next_chain|].
      iApply ("K1" $! D5 with "[%] Hcg Hpc Hfmt HR").
      split_and!; [exact Hkept5 | exact HD5s1 | exact HD5s5
                  | rewrite HD5a3 Hc1; apply bv_eq; vm_compute; reflexivity
                  | exact Hc0 | exact Hc1].
    - iApply (wp_beqz_x0_fall_s_sconf (mword_of_int (KernelSyms.printk + 0xa0)) (mword_of_int 504 : mword 13)
                (mword_of_int 13 : mword 5) D5 (K - 24)%nat b
                ltac:(vm_compute; discriminate)
                ltac:(rgne; rewrite HD5a3; apply zext8_nonzero; exact Hc1)
                with "Hcg Hpc [] [-]").
      { iApply (pki_a0 with "Htext"). }
      iIntros (CID9 Hst9) "Hcg Hpc".
      assert (Hpa4 : add_vec_int (mword_of_int (KernelSyms.printk + 0xa0) : mword 64) 4 = mword_of_int (KernelSyms.printk + 0xa4)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpa4) in "Hpc".
      iSpecialize ("Kgo" $! CID9 with "[%]"); [wp_next_chain|].
      iApply ("Kgo" $! D5 with "[%] Hcg Hpc Hfmt HR").
      split_and!; [exact Hkept5 | exact HD5s1 | exact HD5a5 | exact HD5a4
                  | exact HD5s5 | exact HD5a3 | exact Hc0 | exact Hc1].
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  [pk_entry]: which arm the chain selects, as a function of the three *)
  (*  lookahead characters.  Written in the MACHINE's test order, not     *)
  (*  [pk_dir]'s source order -- that is what lets each segment below      *)
  (*  discharge its conclusion by rewriting the tests it has already       *)
  (*  ruled out.  (The two orders agree because the arms are pairwise      *)
  (*  disjoint on (c0,c1,c2); the loop body is where that is cashed in.)   *)
  (* ------------------------------------------------------------------ *)
  Definition pk_entry (c0 c1 c2 : Ascii.ascii) : Z :=
    if Ascii.eqb c0 "d"%char then 0xd4
    else if (Ascii.eqb c0 "l"%char && Ascii.eqb c1 "d"%char)%bool then 0xb8
    else if (Ascii.eqb c0 "l"%char && (Ascii.eqb c1 "l"%char && Ascii.eqb c2 "d"%char))%bool then 0xf6
    else if Ascii.eqb c0 "u"%char then 0x112
    else if (Ascii.eqb c0 "l"%char && Ascii.eqb c1 "u"%char)%bool then 0x12c
    else if (Ascii.eqb c0 "l"%char && (Ascii.eqb c1 "l"%char && Ascii.eqb c2 "u"%char))%bool then 0x148
    else if Ascii.eqb c0 "x"%char then 0x164
    else if (Ascii.eqb c0 "l"%char && Ascii.eqb c1 "x"%char)%bool then 0x17e
    else if (Ascii.eqb c0 "l"%char && (Ascii.eqb c1 "l"%char && Ascii.eqb c2 "x"%char))%bool then 0x198
    else if Ascii.eqb c0 "p"%char then 0x1b4
    else if Ascii.eqb c0 "c"%char then 0x1fa
    else if Ascii.eqb c0 "s"%char then 0x20e
    else if Ascii.eqb c0 "%"%char then 0x246
    else if Ascii.eqb c0 pk_nul then 0x276
    else 0x31a.

  (* the chain writes only a1..a5 *)
  Definition pk_chain_kept (mf mq : regfile) : Prop :=
    forall c : mword 5, c <> mword_of_int 11 -> c <> mword_of_int 12 ->
      c <> mword_of_int 13 -> c <> mword_of_int 14 -> c <> mword_of_int 15 ->
      mf !!! Regidx c = mq !!! Regidx c.

  Lemma pk_chain_kept_trans (m1 m2 m3 : regfile) :
    pk_chain_kept m1 m2 -> pk_chain_kept m2 m3 -> pk_chain_kept m1 m3.
  Proof. intros H1 H2 c A B C D E. rewrite (H1 c A B C D E). apply H2; assumption. Qed.

  (* ---- 0x2fa .. 0x31a: the six single-character tests and the fall-out -- *)
  Lemma wp_printk_chain_2fa `{CID0 : CpuId}
      (mq : regfile) (K : nat) (c0 c1 c2 : Ascii.ascii) (Rest : iProp Σ) (b : bool) (pcur : mword 64) :
    Ascii.eqb c0 "d"%char = false ->
    (Ascii.eqb c0 "l"%char && Ascii.eqb c1 "d"%char)%bool = false ->
    (Ascii.eqb c0 "l"%char && (Ascii.eqb c1 "l"%char && Ascii.eqb c2 "d"%char))%bool = false ->
    Ascii.eqb c0 "u"%char = false ->
    (Ascii.eqb c0 "l"%char && Ascii.eqb c1 "u"%char)%bool = false ->
    (Ascii.eqb c0 "l"%char && (Ascii.eqb c1 "l"%char && Ascii.eqb c2 "u"%char))%bool = false ->
    Ascii.eqb c0 "x"%char = false ->
    (Ascii.eqb c0 "l"%char && Ascii.eqb c1 "x"%char)%bool = false ->
    (Ascii.eqb c0 "l"%char && (Ascii.eqb c1 "l"%char && Ascii.eqb c2 "x"%char))%bool = false ->
    mq !!! Regidx (mword_of_int 21 : mword 5) = zero_extend' 64 (pk_byte c0) ->
    mq !!! Regidx (mword_of_int 27 : mword 5) = (mword_of_int 112 : mword 64) ->
    sie_cap_gpr mq (K - 24)%nat b pcur -∗
    kernel_text -∗
    pc_is (mword_of_int (KernelSyms.printk + 0x2fa) : mword 64) -∗
    Rest -∗
    wp_next (CID0 := CID0) b pcur (fun (CID : CpuId) =>
      ∀ mf : regfile,
      ⌜ pk_chain_kept mf mq ⌝ -∗
      sie_cap_gpr mf (K - 24)%nat b pcur -∗
      pc_is (mword_of_int (KernelSyms.printk + pk_entry c0 c1 c2) : mword 64) -∗
      Rest -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros E1 E2 E3 E4 E5 E6 E7 E8 E9 Hs5 Hs11.
    iIntros "Hcg #Htext Hpc HR Hcont".
    assert (Hid : pk_chain_kept mq mq) by (intros c ????; reflexivity).
    (* +0x2fa beq s5,s11 : '%p' *)
    case_eq (Ascii.eqb c0 "p"%char); intro Hp0.
    { iApply (wp_beq_taken_s_sconf (mword_of_int (KernelSyms.printk + 0x2fa)) (mword_of_int 7866 : mword 13)
                (mword_of_int 27 : mword 5) (mword_of_int 21 : mword 5) mq (K - 24)%nat b
                ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                ltac:(rgne; rgne; rewrite Hs5 Hs11 (pk_eq_ascii c0 "p"%char (mword_of_int 112)
                        ltac:(apply bv_eq; vm_compute; reflexivity)); exact Hp0)
                ltac:(vm_compute; reflexivity)
                with "Hcg Hpc [] [-]").
      { iApply (pki_2fa with "Htext"). }
      iIntros (CID1 Hst1). iNext. iIntros "Hcg Hpc".
      assert (Ht : add_vec (mword_of_int (KernelSyms.printk + 0x2fa) : mword 64) (sign_extend' 64 (mword_of_int 7866 : mword 13)) = mword_of_int (KernelSyms.printk + pk_entry c0 c1 c2)).
      { unfold pk_entry. rewrite E1 E2 E3 E4 E5 E6 E7 E8 E9 Hp0.
        apply bv_eq; vm_compute; reflexivity. }
      iEval (rewrite Ht) in "Hpc".
      iSpecialize ("Hcont" $! CID1 with "[%]"); [wp_next_chain|].
      iApply ("Hcont" $! mq with "[%] Hcg Hpc HR"). exact Hid. }
    iApply (wp_beq_fall_s_sconf (mword_of_int (KernelSyms.printk + 0x2fa)) (mword_of_int 7866 : mword 13)
              (mword_of_int 27 : mword 5) (mword_of_int 21 : mword 5) mq (K - 24)%nat b
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              ltac:(rgne; rgne; rewrite Hs5 Hs11 (pk_eq_ascii c0 "p"%char (mword_of_int 112)
                      ltac:(apply bv_eq; vm_compute; reflexivity)); exact Hp0)
              with "Hcg Hpc [] [-]").
    { iApply (pki_2fa with "Htext"). }
    iIntros (CID2 Hst2) "Hcg Hpc".
    assert (Hp2fe : add_vec_int (mword_of_int (KernelSyms.printk + 0x2fa) : mword 64) 4 = mword_of_int (KernelSyms.printk + 0x2fe)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp2fe) in "Hpc".
    (* the three remaining characters are compared through a5 *)
    iApply (wp_li4_s_sconf (mword_of_int (KernelSyms.printk + 0x2fe)) a5_idx (mword_of_int 99 : mword 12)
              (mword_of_int 99 : mword 64) mq (K - 24)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc [] [-]").
    { iApply (pki_2fe with "Htext"). }
    iIntros (CID3 Hst3) "Hcg Hpc".
    set (C1 := <[Regidx a5_idx := regval_into_reg (mword_of_int 99 : mword 64)]> mq).
    assert (HC1k : pk_chain_kept C1 mq)
      by (intros c ? ? ? ? N; rewrite /C1 upd_ne; [reflexivity | congruence]).
    assert (HC1s5 : C1 !!! Regidx (mword_of_int 21 : mword 5) = zero_extend' 64 (pk_byte c0))
      by (rewrite /C1 upd_ne; [exact Hs5 | reg_neq]).
    assert (HC1a5 : C1 !!! Regidx a5_idx = (mword_of_int 99 : mword 64))
      by (rewrite /C1 upd_eq; reflexivity).
    assert (Hp302 : add_vec_int (mword_of_int (KernelSyms.printk + 0x2fe) : mword 64) 4 = mword_of_int (KernelSyms.printk + 0x302)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp302) in "Hpc".
    (* +0x302 beq s5,a5 : '%c' *)
    case_eq (Ascii.eqb c0 "c"%char); intro Hc0.
    { iApply (wp_beq_taken_s_sconf (mword_of_int (KernelSyms.printk + 0x302)) (mword_of_int 7928 : mword 13)
                a5_idx (mword_of_int 21 : mword 5) C1 (K - 24)%nat b
                ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                ltac:(rgne; rgne; rewrite HC1s5 HC1a5 (pk_eq_ascii c0 "c"%char (mword_of_int 99)
                        ltac:(apply bv_eq; vm_compute; reflexivity)); exact Hc0)
                ltac:(vm_compute; reflexivity)
                with "Hcg Hpc [] [-]").
      { iApply (pki_302 with "Htext"). }
      iIntros (CID4 Hst4). iNext. iIntros "Hcg Hpc".
      assert (Ht : add_vec (mword_of_int (KernelSyms.printk + 0x302) : mword 64) (sign_extend' 64 (mword_of_int 7928 : mword 13)) = mword_of_int (KernelSyms.printk + pk_entry c0 c1 c2)).
      { unfold pk_entry. rewrite E1 E2 E3 E4 E5 E6 E7 E8 E9 Hp0 Hc0.
        apply bv_eq; vm_compute; reflexivity. }
      iEval (rewrite Ht) in "Hpc".
      iSpecialize ("Hcont" $! CID4 with "[%]"); [wp_next_chain|].
      iApply ("Hcont" $! C1 with "[%] Hcg Hpc HR"). exact HC1k. }
    iApply (wp_beq_fall_s_sconf (mword_of_int (KernelSyms.printk + 0x302)) (mword_of_int 7928 : mword 13)
              a5_idx (mword_of_int 21 : mword 5) C1 (K - 24)%nat b
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              ltac:(rgne; rgne; rewrite HC1s5 HC1a5 (pk_eq_ascii c0 "c"%char (mword_of_int 99)
                      ltac:(apply bv_eq; vm_compute; reflexivity)); exact Hc0)
              with "Hcg Hpc [] [-]").
    { iApply (pki_302 with "Htext"). }
    iIntros (CID5 Hst5) "Hcg Hpc".
    assert (Hp306 : add_vec_int (mword_of_int (KernelSyms.printk + 0x302) : mword 64) 4 = mword_of_int (KernelSyms.printk + 0x306)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp306) in "Hpc".
    iApply (wp_li4_s_sconf (mword_of_int (KernelSyms.printk + 0x306)) a5_idx (mword_of_int 115 : mword 12)
              (mword_of_int 115 : mword 64) C1 (K - 24)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc [] [-]").
    { iApply (pki_306 with "Htext"). }
    iIntros (CID6 Hst6) "Hcg Hpc".
    set (C2 := <[Regidx a5_idx := regval_into_reg (mword_of_int 115 : mword 64)]> C1).
    assert (HC2k : pk_chain_kept C2 mq).
    { intros c A B C D N. rewrite /C2 upd_ne; [| congruence]. apply HC1k; assumption. }
    assert (HC2s5 : C2 !!! Regidx (mword_of_int 21 : mword 5) = zero_extend' 64 (pk_byte c0))
      by (rewrite /C2 upd_ne; [exact HC1s5 | reg_neq]).
    assert (HC2a5 : C2 !!! Regidx a5_idx = (mword_of_int 115 : mword 64))
      by (rewrite /C2 upd_eq; reflexivity).
    assert (Hp30a : add_vec_int (mword_of_int (KernelSyms.printk + 0x306) : mword 64) 4 = mword_of_int (KernelSyms.printk + 0x30a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp30a) in "Hpc".
    (* +0x30a beq s5,a5 : '%s' *)
    case_eq (Ascii.eqb c0 "s"%char); intro Hs0.
    { iApply (wp_beq_taken_s_sconf (mword_of_int (KernelSyms.printk + 0x30a)) (mword_of_int 7940 : mword 13)
                a5_idx (mword_of_int 21 : mword 5) C2 (K - 24)%nat b
                ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                ltac:(rgne; rgne; rewrite HC2s5 HC2a5 (pk_eq_ascii c0 "s"%char (mword_of_int 115)
                        ltac:(apply bv_eq; vm_compute; reflexivity)); exact Hs0)
                ltac:(vm_compute; reflexivity)
                with "Hcg Hpc [] [-]").
      { iApply (pki_30a with "Htext"). }
      iIntros (CID7 Hst7). iNext. iIntros "Hcg Hpc".
      assert (Ht : add_vec (mword_of_int (KernelSyms.printk + 0x30a) : mword 64) (sign_extend' 64 (mword_of_int 7940 : mword 13)) = mword_of_int (KernelSyms.printk + pk_entry c0 c1 c2)).
      { unfold pk_entry. rewrite E1 E2 E3 E4 E5 E6 E7 E8 E9 Hp0 Hc0 Hs0.
        apply bv_eq; vm_compute; reflexivity. }
      iEval (rewrite Ht) in "Hpc".
      iSpecialize ("Hcont" $! CID7 with "[%]"); [wp_next_chain|].
      iApply ("Hcont" $! C2 with "[%] Hcg Hpc HR"). exact HC2k. }
    iApply (wp_beq_fall_s_sconf (mword_of_int (KernelSyms.printk + 0x30a)) (mword_of_int 7940 : mword 13)
              a5_idx (mword_of_int 21 : mword 5) C2 (K - 24)%nat b
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              ltac:(rgne; rgne; rewrite HC2s5 HC2a5 (pk_eq_ascii c0 "s"%char (mword_of_int 115)
                      ltac:(apply bv_eq; vm_compute; reflexivity)); exact Hs0)
              with "Hcg Hpc [] [-]").
    { iApply (pki_30a with "Htext"). }
    iIntros (CID8 Hst8) "Hcg Hpc".
    assert (Hp30e : add_vec_int (mword_of_int (KernelSyms.printk + 0x30a) : mword 64) 4 = mword_of_int (KernelSyms.printk + 0x30e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp30e) in "Hpc".
    iApply (wp_li4_s_sconf (mword_of_int (KernelSyms.printk + 0x30e)) a5_idx (mword_of_int 37 : mword 12)
              (mword_of_int 37 : mword 64) C2 (K - 24)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc [] [-]").
    { iApply (pki_30e with "Htext"). }
    iIntros (CID9 Hst9) "Hcg Hpc".
    set (C3 := <[Regidx a5_idx := regval_into_reg (mword_of_int 37 : mword 64)]> C2).
    assert (HC3k : pk_chain_kept C3 mq).
    { intros c A B C D N. rewrite /C3 upd_ne; [| congruence]. apply HC2k; assumption. }
    assert (HC3s5 : C3 !!! Regidx (mword_of_int 21 : mword 5) = zero_extend' 64 (pk_byte c0))
      by (rewrite /C3 upd_ne; [exact HC2s5 | reg_neq]).
    assert (HC3a5 : C3 !!! Regidx a5_idx = (mword_of_int 37 : mword 64))
      by (rewrite /C3 upd_eq; reflexivity).
    assert (Hp312 : add_vec_int (mword_of_int (KernelSyms.printk + 0x30e) : mword 64) 4 = mword_of_int (KernelSyms.printk + 0x312)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp312) in "Hpc".
    (* +0x312 beq s5,a5 : '%%' *)
    case_eq (Ascii.eqb c0 "%"%char); intro Hm0.
    { iApply (wp_beq_taken_s_sconf (mword_of_int (KernelSyms.printk + 0x312)) (mword_of_int 7988 : mword 13)
                a5_idx (mword_of_int 21 : mword 5) C3 (K - 24)%nat b
                ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                ltac:(rgne; rgne; rewrite HC3s5 HC3a5 (pk_eq_ascii c0 "%"%char (mword_of_int 37)
                        ltac:(apply bv_eq; vm_compute; reflexivity)); exact Hm0)
                ltac:(vm_compute; reflexivity)
                with "Hcg Hpc [] [-]").
      { iApply (pki_312 with "Htext"). }
      iIntros (CID10 Hst10). iNext. iIntros "Hcg Hpc".
      assert (Ht : add_vec (mword_of_int (KernelSyms.printk + 0x312) : mword 64) (sign_extend' 64 (mword_of_int 7988 : mword 13)) = mword_of_int (KernelSyms.printk + pk_entry c0 c1 c2)).
      { unfold pk_entry. rewrite E1 E2 E3 E4 E5 E6 E7 E8 E9 Hp0 Hc0 Hs0 Hm0.
        apply bv_eq; vm_compute; reflexivity. }
      iEval (rewrite Ht) in "Hpc".
      iSpecialize ("Hcont" $! CID10 with "[%]"); [wp_next_chain|].
      iApply ("Hcont" $! C3 with "[%] Hcg Hpc HR"). exact HC3k. }
    iApply (wp_beq_fall_s_sconf (mword_of_int (KernelSyms.printk + 0x312)) (mword_of_int 7988 : mword 13)
              a5_idx (mword_of_int 21 : mword 5) C3 (K - 24)%nat b
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              ltac:(rgne; rgne; rewrite HC3s5 HC3a5 (pk_eq_ascii c0 "%"%char (mword_of_int 37)
                      ltac:(apply bv_eq; vm_compute; reflexivity)); exact Hm0)
              with "Hcg Hpc [] [-]").
    { iApply (pki_312 with "Htext"). }
    iIntros (CID11 Hst11) "Hcg Hpc".
    assert (Hp316 : add_vec_int (mword_of_int (KernelSyms.printk + 0x312) : mword 64) 4 = mword_of_int (KernelSyms.printk + 0x316)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp316) in "Hpc".
    (* +0x316 beqz s5 : the format string ended right after the '%' *)
    case_eq (Ascii.eqb c0 pk_nul); intro Hn0.
    - iApply (wp_beqz_x0_taken_s_sconf (mword_of_int (KernelSyms.printk + 0x316)) (mword_of_int 8032 : mword 13)
                (mword_of_int 21 : mword 5) C3 (K - 24)%nat b
                ltac:(vm_compute; discriminate)
                ltac:(rgne; rewrite HC3s5 (pk_eq_ascii c0 pk_nul (zero_reg : mword 64)
                        ltac:(apply bv_eq; vm_compute; reflexivity)); exact Hn0)
                ltac:(vm_compute; reflexivity)
                with "Hcg Hpc [] [-]").
      { iApply (pki_316 with "Htext"). }
      iIntros (CID12 Hst12). iNext. iIntros "Hcg Hpc".
      assert (Ht : add_vec (mword_of_int (KernelSyms.printk + 0x316) : mword 64) (sign_extend' 64 (mword_of_int 8032 : mword 13)) = mword_of_int (KernelSyms.printk + pk_entry c0 c1 c2)).
      { unfold pk_entry. rewrite E1 E2 E3 E4 E5 E6 E7 E8 E9 Hp0 Hc0 Hs0 Hm0 Hn0.
        apply bv_eq; vm_compute; reflexivity. }
      iEval (rewrite Ht) in "Hpc".
      iSpecialize ("Hcont" $! CID12 with "[%]"); [wp_next_chain|].
      iApply ("Hcont" $! C3 with "[%] Hcg Hpc HR"). exact HC3k.
    - iApply (wp_beqz_x0_fall_s_sconf (mword_of_int (KernelSyms.printk + 0x316)) (mword_of_int 8032 : mword 13)
                (mword_of_int 21 : mword 5) C3 (K - 24)%nat b
                ltac:(vm_compute; discriminate)
                ltac:(rgne; rewrite HC3s5 (pk_eq_ascii c0 pk_nul (zero_reg : mword 64)
                        ltac:(apply bv_eq; vm_compute; reflexivity)); exact Hn0)
                with "Hcg Hpc [] [-]").
      { iApply (pki_316 with "Htext"). }
      iIntros (CID13 Hst13) "Hcg Hpc".
      assert (Ht : add_vec_int (mword_of_int (KernelSyms.printk + 0x316) : mword 64) 4 = mword_of_int (KernelSyms.printk + pk_entry c0 c1 c2)).
      { unfold pk_entry. rewrite E1 E2 E3 E4 E5 E6 E7 E8 E9 Hp0 Hc0 Hs0 Hm0 Hn0.
        apply bv_eq; vm_compute; reflexivity. }
      iEval (rewrite Ht) in "Hpc".
      iSpecialize ("Hcont" $! CID13 with "[%]"); [wp_next_chain|].
      iApply ("Hcont" $! C3 with "[%] Hcg Hpc HR"). exact HC3k.
  Qed.

  (* ---- 0x2f0 .. 0x2f6: the "%llx" test, then on to 0x2fa ---- *)
  Lemma wp_printk_chain_2f0 `{CID0 : CpuId}
      (mq : regfile) (K : nat) (c0 c1 c2 : Ascii.ascii) (Rest : iProp Σ) (b : bool) (pcur : mword 64) :
    Ascii.eqb c0 "d"%char = false ->
    (Ascii.eqb c0 "l"%char && Ascii.eqb c1 "d"%char)%bool = false ->
    (Ascii.eqb c0 "l"%char && (Ascii.eqb c1 "l"%char && Ascii.eqb c2 "d"%char))%bool = false ->
    Ascii.eqb c0 "u"%char = false ->
    (Ascii.eqb c0 "l"%char && Ascii.eqb c1 "u"%char)%bool = false ->
    (Ascii.eqb c0 "l"%char && (Ascii.eqb c1 "l"%char && Ascii.eqb c2 "u"%char))%bool = false ->
    Ascii.eqb c0 "x"%char = false ->
    (Ascii.eqb c0 "l"%char && Ascii.eqb c1 "x"%char)%bool = false ->
    mq !!! Regidx (mword_of_int 21 : mword 5) = zero_extend' 64 (pk_byte c0) ->
    mq !!! Regidx (mword_of_int 27 : mword 5) = (mword_of_int 112 : mword 64) ->
    mq !!! Regidx (mword_of_int 13 : mword 5) = zero_extend' 64 (pk_byte c2) ->
    mq !!! Regidx a5_idx = pk_bit (Ascii.eqb c1 "l"%char && Ascii.eqb c0 "l"%char) ->
    sie_cap_gpr mq (K - 24)%nat b pcur -∗
    kernel_text -∗
    pc_is (mword_of_int (KernelSyms.printk + 0x2f0) : mword 64) -∗
    Rest -∗
    wp_next (CID0 := CID0) b pcur (fun (CID : CpuId) =>
      ∀ mf : regfile,
      ⌜ pk_chain_kept mf mq ⌝ -∗
      sie_cap_gpr mf (K - 24)%nat b pcur -∗
      pc_is (mword_of_int (KernelSyms.printk + pk_entry c0 c1 c2) : mword 64) -∗
      Rest -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros E1 E2 E3 E4 E5 E6 E7 E8 Hs5 Hs11 Ha3 Ha5.
    iIntros "Hcg #Htext Hpc HR Hcont".
    (* +0x2f0 addi a3,a3,-120 *)
    iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.printk + 0x2f0)) (mword_of_int 13 : mword 5)
              (mword_of_int 13 : mword 5) (mword_of_int 3976 : mword 12) mq (K - 24)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc [] [-]").
    { iApply (pki_2f0 with "Htext"). }
    iIntros (CID1 Hst1) "Hcg Hpc".
    set (D1 := <[Regidx (mword_of_int 13 : mword 5) := regval_into_reg
                   (add_vec (mq !!! Regidx (mword_of_int 13 : mword 5))
                      (sign_extend' 64 (mword_of_int 3976 : mword 12)))]> mq).
    assert (HD1k : pk_chain_kept D1 mq)
      by (intros c ? ? N ? ?; rewrite /D1 upd_ne; [reflexivity | congruence]).
    assert (HD1a3 : eq_vec (D1 !!! Regidx (mword_of_int 13 : mword 5)) (zero_reg : mword 64)
                    = Ascii.eqb c2 "x"%char).
    { rewrite /D1 upd_eq. unfold regval_into_reg. rewrite Ha3.
      apply (pk_sub_ascii c2 "x"%char). apply bv_eq; vm_compute; reflexivity. }
    assert (HD1a5 : D1 !!! Regidx a5_idx = pk_bit (Ascii.eqb c1 "l"%char && Ascii.eqb c0 "l"%char))
      by (rewrite /D1 upd_ne; [exact Ha5 | reg_neq]).
    assert (HD1s5 : D1 !!! Regidx (mword_of_int 21 : mword 5) = zero_extend' 64 (pk_byte c0))
      by (rewrite /D1 upd_ne; [exact Hs5 | reg_neq]).
    assert (HD1s11 : D1 !!! Regidx (mword_of_int 27 : mword 5) = (mword_of_int 112 : mword 64))
      by (rewrite /D1 upd_ne; [exact Hs11 | reg_neq]).
    assert (Hp2f4 : add_vec_int (mword_of_int (KernelSyms.printk + 0x2f0) : mword 64) 4 = mword_of_int (KernelSyms.printk + 0x2f4)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp2f4) in "Hpc".
    (* +0x2f4 bnez a3 : c2 is not 'x', so no %llx *)
    case_eq (Ascii.eqb c2 "x"%char); intro Hx2.
    - (* c2 = 'x': fall through to the ll test *)
      iApply (wp_cbnez_fall_s_sconf (mword_of_int (KernelSyms.printk + 0x2f4)) (mword_of_int 3 : mword 8)
                (Cregidx (mword_of_int 5)) (mword_of_int 13 : mword 5) D1 (K - 24)%nat b
                ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
                ltac:(rgne; unfold neq_vec; rewrite HD1a3 Hx2; reflexivity)
                with "Hcg Hpc [] [-]").
      { iApply (pki_2f4 with "Htext"). }
      iIntros (CID2 Hst2) "Hcg Hpc".
      assert (Hp2f6 : add_vec_int (mword_of_int (KernelSyms.printk + 0x2f4) : mword 64) 2 = mword_of_int (KernelSyms.printk + 0x2f6)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hp2f6) in "Hpc".
      case_eq (Ascii.eqb c1 "l"%char && Ascii.eqb c0 "l"%char)%bool; intro Hll.
      + iApply (wp_bnez_x0_taken_s_sconf (mword_of_int (KernelSyms.printk + 0x2f6)) (mword_of_int 7842 : mword 13)
                  a5_idx D1 (K - 24)%nat b ltac:(vm_compute; discriminate)
                  ltac:(rgne; rewrite HD1a5 pk_bit_nz; exact Hll)
                  ltac:(vm_compute; reflexivity)
                  with "Hcg Hpc [] [-]").
        { iApply (pki_2f6 with "Htext"). }
        iIntros (CID3 Hst3). iNext. iIntros "Hcg Hpc".
        assert (Ht : add_vec (mword_of_int (KernelSyms.printk + 0x2f6) : mword 64) (sign_extend' 64 (mword_of_int 7842 : mword 13)) = mword_of_int (KernelSyms.printk + pk_entry c0 c1 c2)).
        { unfold pk_entry. rewrite E1 E2 E3 E4 E5 E6 E7 E8.
          apply andb_true_iff in Hll as [Hl1 Hl0]. rewrite Hl0 Hl1 Hx2.
          apply bv_eq; vm_compute; reflexivity. }
        iEval (rewrite Ht) in "Hpc".
        iSpecialize ("Hcont" $! CID3 with "[%]"); [wp_next_chain|].
        iApply ("Hcont" $! D1 with "[%] Hcg Hpc HR"). exact HD1k.
      + iApply (wp_bnez_x0_fall_s_sconf (mword_of_int (KernelSyms.printk + 0x2f6)) (mword_of_int 7842 : mword 13)
                  a5_idx D1 (K - 24)%nat b ltac:(vm_compute; discriminate)
                  ltac:(rgne; rewrite HD1a5 pk_bit_nz; exact Hll)
                  with "Hcg Hpc [] [-]").
        { iApply (pki_2f6 with "Htext"). }
        iIntros (CID4 Hst4) "Hcg Hpc".
        assert (Hp2fa : add_vec_int (mword_of_int (KernelSyms.printk + 0x2f6) : mword 64) 4 = mword_of_int (KernelSyms.printk + 0x2fa)) by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hp2fa) in "Hpc".
        iApply (wp_printk_chain_2fa D1 K c0 c1 c2 Rest b pcur E1 E2 E3 E4 E5 E6 E7 E8
                  ltac:(rewrite Hx2; repeat rewrite andb_true_r; rewrite andb_comm; exact Hll) HD1s5 HD1s11
                  with "Hcg Htext Hpc HR [-]").
        iIntros (CID5 Hst5 mf) "%Hk Hcg Hpc HR".
        iSpecialize ("Hcont" $! CID5 with "[%]"); [wp_next_chain|].
        iApply ("Hcont" $! mf with "[%] Hcg Hpc HR").
        exact (pk_chain_kept_trans mf D1 mq Hk HD1k).
    - (* c2 <> 'x': straight on to 0x2fa *)
      iApply (wp_cbnez_taken_s_sconf (mword_of_int (KernelSyms.printk + 0x2f4)) (mword_of_int 3 : mword 8)
                (Cregidx (mword_of_int 5)) (mword_of_int 13 : mword 5) D1 (K - 24)%nat b
                ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
                ltac:(rgne; unfold neq_vec; rewrite HD1a3 Hx2; reflexivity)
                ltac:(vm_compute; reflexivity)
                with "Hcg Hpc [] [-]").
      { iApply (pki_2f4 with "Htext"). }
      iIntros (CID6 Hst6). iNext. iIntros "Hcg Hpc".
      assert (Ht : add_vec (mword_of_int (KernelSyms.printk + 0x2f4) : mword 64) (sign_extend' 64 (sign_extend' 13 (concat_vec (mword_of_int 3 : mword 8) ('b"0")))) = mword_of_int (KernelSyms.printk + 0x2fa)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Ht) in "Hpc".
      iApply (wp_printk_chain_2fa D1 K c0 c1 c2 Rest b pcur E1 E2 E3 E4 E5 E6 E7 E8
                ltac:(rewrite Hx2; repeat rewrite andb_false_r; reflexivity) HD1s5 HD1s11
                with "Hcg Htext Hpc HR [-]").
      iIntros (CID7 Hst7 mf) "%Hk Hcg Hpc HR".
      iSpecialize ("Hcont" $! CID7 with "[%]"); [wp_next_chain|].
      iApply ("Hcont" $! mf with "[%] Hcg Hpc HR").
      exact (pk_chain_kept_trans mf D1 mq Hk HD1k).
  Qed.

  (* ---- 0x2e2 .. 0x2ec: "%x" and "%lx", then on to 0x2f0 ---- *)
  Lemma wp_printk_chain_2e2 `{CID0 : CpuId}
      (mq : regfile) (K : nat) (c0 c1 c2 : Ascii.ascii) (Rest : iProp Σ) (b : bool) (pcur : mword 64) :
    Ascii.eqb c0 "d"%char = false ->
    (Ascii.eqb c0 "l"%char && Ascii.eqb c1 "d"%char)%bool = false ->
    (Ascii.eqb c0 "l"%char && (Ascii.eqb c1 "l"%char && Ascii.eqb c2 "d"%char))%bool = false ->
    Ascii.eqb c0 "u"%char = false ->
    (Ascii.eqb c0 "l"%char && Ascii.eqb c1 "u"%char)%bool = false ->
    (Ascii.eqb c0 "l"%char && (Ascii.eqb c1 "l"%char && Ascii.eqb c2 "u"%char))%bool = false ->
    mq !!! Regidx (mword_of_int 21 : mword 5) = zero_extend' 64 (pk_byte c0) ->
    mq !!! Regidx (mword_of_int 26 : mword 5) = (mword_of_int 120 : mword 64) ->
    mq !!! Regidx (mword_of_int 27 : mword 5) = (mword_of_int 112 : mword 64) ->
    mq !!! Regidx (mword_of_int 12 : mword 5) = zero_extend' 64 (pk_byte c1) ->
    mq !!! Regidx (mword_of_int 13 : mword 5) = zero_extend' 64 (pk_byte c2) ->
    mq !!! Regidx (mword_of_int 14 : mword 5) = pk_bit (Ascii.eqb c0 "l"%char) ->
    mq !!! Regidx a5_idx = pk_bit (Ascii.eqb c1 "l"%char && Ascii.eqb c0 "l"%char) ->
    sie_cap_gpr mq (K - 24)%nat b pcur -∗
    kernel_text -∗
    pc_is (mword_of_int (KernelSyms.printk + 0x2e2) : mword 64) -∗
    Rest -∗
    wp_next (CID0 := CID0) b pcur (fun (CID : CpuId) =>
      ∀ mf : regfile,
      ⌜ pk_chain_kept mf mq ⌝ -∗
      sie_cap_gpr mf (K - 24)%nat b pcur -∗
      pc_is (mword_of_int (KernelSyms.printk + pk_entry c0 c1 c2) : mword 64) -∗
      Rest -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros E1 E2 E3 E4 E5 E6 Hs5 Hs10 Hs11 Ha2 Ha3 Ha4 Ha5.
    iIntros "Hcg #Htext Hpc HR Hcont".
    assert (Hid : pk_chain_kept mq mq) by (intros c ????; reflexivity).
    (* +0x2e2 beq s5,s10 : '%x' *)
    case_eq (Ascii.eqb c0 "x"%char); intro Hx0.
    { iApply (wp_beq_taken_s_sconf (mword_of_int (KernelSyms.printk + 0x2e2)) (mword_of_int 7810 : mword 13)
                (mword_of_int 26 : mword 5) (mword_of_int 21 : mword 5) mq (K - 24)%nat b
                ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                ltac:(rgne; rgne; rewrite Hs5 Hs10 (pk_eq_ascii c0 "x"%char (mword_of_int 120)
                        ltac:(apply bv_eq; vm_compute; reflexivity)); exact Hx0)
                ltac:(vm_compute; reflexivity)
                with "Hcg Hpc [] [-]").
      { iApply (pki_2e2 with "Htext"). }
      iIntros (CID1 Hst1). iNext. iIntros "Hcg Hpc".
      assert (Ht : add_vec (mword_of_int (KernelSyms.printk + 0x2e2) : mword 64) (sign_extend' 64 (mword_of_int 7810 : mword 13)) = mword_of_int (KernelSyms.printk + pk_entry c0 c1 c2)).
      { unfold pk_entry. rewrite E1 E2 E3 E4 E5 E6 Hx0.
        apply bv_eq; vm_compute; reflexivity. }
      iEval (rewrite Ht) in "Hpc".
      iSpecialize ("Hcont" $! CID1 with "[%]"); [wp_next_chain|].
      iApply ("Hcont" $! mq with "[%] Hcg Hpc HR"). exact Hid. }
    iApply (wp_beq_fall_s_sconf (mword_of_int (KernelSyms.printk + 0x2e2)) (mword_of_int 7810 : mword 13)
              (mword_of_int 26 : mword 5) (mword_of_int 21 : mword 5) mq (K - 24)%nat b
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              ltac:(rgne; rgne; rewrite Hs5 Hs10 (pk_eq_ascii c0 "x"%char (mword_of_int 120)
                      ltac:(apply bv_eq; vm_compute; reflexivity)); exact Hx0)
              with "Hcg Hpc [] [-]").
    { iApply (pki_2e2 with "Htext"). }
    iIntros (CID2 Hst2) "Hcg Hpc".
    assert (Hp2e6 : add_vec_int (mword_of_int (KernelSyms.printk + 0x2e2) : mword 64) 4 = mword_of_int (KernelSyms.printk + 0x2e6)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp2e6) in "Hpc".
    (* +0x2e6 addi a2,a2,-120 *)
    iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.printk + 0x2e6)) (mword_of_int 12 : mword 5)
              (mword_of_int 12 : mword 5) (mword_of_int 3976 : mword 12) mq (K - 24)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc [] [-]").
    { iApply (pki_2e6 with "Htext"). }
    iIntros (CID3 Hst3) "Hcg Hpc".
    set (D1 := <[Regidx (mword_of_int 12 : mword 5) := regval_into_reg
                   (add_vec (mq !!! Regidx (mword_of_int 12 : mword 5))
                      (sign_extend' 64 (mword_of_int 3976 : mword 12)))]> mq).
    assert (HD1k : pk_chain_kept D1 mq)
      by (intros c ? N ? ? ?; rewrite /D1 upd_ne; [reflexivity | congruence]).
    assert (HD1a2 : eq_vec (D1 !!! Regidx (mword_of_int 12 : mword 5)) (zero_reg : mword 64)
                    = Ascii.eqb c1 "x"%char).
    { rewrite /D1 upd_eq. unfold regval_into_reg. rewrite Ha2.
      apply (pk_sub_ascii c1 "x"%char). apply bv_eq; vm_compute; reflexivity. }
    assert (HD1a4 : D1 !!! Regidx (mword_of_int 14 : mword 5) = pk_bit (Ascii.eqb c0 "l"%char))
      by (rewrite /D1 upd_ne; [exact Ha4 | reg_neq]).
    assert (HD1a5 : D1 !!! Regidx a5_idx = pk_bit (Ascii.eqb c1 "l"%char && Ascii.eqb c0 "l"%char))
      by (rewrite /D1 upd_ne; [exact Ha5 | reg_neq]).
    assert (HD1a3 : D1 !!! Regidx (mword_of_int 13 : mword 5) = zero_extend' 64 (pk_byte c2))
      by (rewrite /D1 upd_ne; [exact Ha3 | reg_neq]).
    assert (HD1s5 : D1 !!! Regidx (mword_of_int 21 : mword 5) = zero_extend' 64 (pk_byte c0))
      by (rewrite /D1 upd_ne; [exact Hs5 | reg_neq]).
    assert (HD1s11 : D1 !!! Regidx (mword_of_int 27 : mword 5) = (mword_of_int 112 : mword 64))
      by (rewrite /D1 upd_ne; [exact Hs11 | reg_neq]).
    assert (Hp2ea : add_vec_int (mword_of_int (KernelSyms.printk + 0x2e6) : mword 64) 4 = mword_of_int (KernelSyms.printk + 0x2ea)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp2ea) in "Hpc".
    (* +0x2ea bnez a2 ; +0x2ec bnez a4 : "%lx" *)
    case_eq (Ascii.eqb c1 "x"%char); intro Hx1.
    - iApply (wp_cbnez_fall_s_sconf (mword_of_int (KernelSyms.printk + 0x2ea)) (mword_of_int 3 : mword 8)
                (Cregidx (mword_of_int 4)) (mword_of_int 12 : mword 5) D1 (K - 24)%nat b
                ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
                ltac:(rgne; unfold neq_vec; rewrite HD1a2 Hx1; reflexivity)
                with "Hcg Hpc [] [-]").
      { iApply (pki_2ea with "Htext"). }
      iIntros (CID4 Hst4) "Hcg Hpc".
      assert (Hp2ec : add_vec_int (mword_of_int (KernelSyms.printk + 0x2ea) : mword 64) 2 = mword_of_int (KernelSyms.printk + 0x2ec)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hp2ec) in "Hpc".
      case_eq (Ascii.eqb c0 "l"%char); intro Hl0.
      + iApply (wp_bnez_x0_taken_s_sconf (mword_of_int (KernelSyms.printk + 0x2ec)) (mword_of_int 7826 : mword 13)
                  (mword_of_int 14 : mword 5) D1 (K - 24)%nat b ltac:(vm_compute; discriminate)
                  ltac:(rgne; rewrite HD1a4 pk_bit_nz; exact Hl0)
                  ltac:(vm_compute; reflexivity)
                  with "Hcg Hpc [] [-]").
        { iApply (pki_2ec with "Htext"). }
        iIntros (CID5 Hst5). iNext. iIntros "Hcg Hpc".
        assert (Ht : add_vec (mword_of_int (KernelSyms.printk + 0x2ec) : mword 64) (sign_extend' 64 (mword_of_int 7826 : mword 13)) = mword_of_int (KernelSyms.printk + pk_entry c0 c1 c2)).
        { unfold pk_entry. rewrite E1 E2 E3 E4 E5 E6 Hx0 Hl0 Hx1.
          apply bv_eq; vm_compute; reflexivity. }
        iEval (rewrite Ht) in "Hpc".
        iSpecialize ("Hcont" $! CID5 with "[%]"); [wp_next_chain|].
        iApply ("Hcont" $! D1 with "[%] Hcg Hpc HR"). exact HD1k.
      + iApply (wp_bnez_x0_fall_s_sconf (mword_of_int (KernelSyms.printk + 0x2ec)) (mword_of_int 7826 : mword 13)
                  (mword_of_int 14 : mword 5) D1 (K - 24)%nat b ltac:(vm_compute; discriminate)
                  ltac:(rgne; rewrite HD1a4 pk_bit_nz; exact Hl0)
                  with "Hcg Hpc [] [-]").
        { iApply (pki_2ec with "Htext"). }
        iIntros (CID6 Hst6) "Hcg Hpc".
        assert (Hp2f0 : add_vec_int (mword_of_int (KernelSyms.printk + 0x2ec) : mword 64) 4 = mword_of_int (KernelSyms.printk + 0x2f0)) by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hp2f0) in "Hpc".
        iApply (wp_printk_chain_2f0 D1 K c0 c1 c2 Rest b pcur E1 E2 E3 E4 E5 E6 Hx0
                  ltac:(rewrite Hl0; reflexivity) HD1s5 HD1s11 HD1a3 HD1a5
                  with "Hcg Htext Hpc HR [-]").
        iIntros (CID7 Hst7 mf) "%Hk Hcg Hpc HR".
        iSpecialize ("Hcont" $! CID7 with "[%]"); [wp_next_chain|].
        iApply ("Hcont" $! mf with "[%] Hcg Hpc HR").
        exact (pk_chain_kept_trans mf D1 mq Hk HD1k).
    - iApply (wp_cbnez_taken_s_sconf (mword_of_int (KernelSyms.printk + 0x2ea)) (mword_of_int 3 : mword 8)
                (Cregidx (mword_of_int 4)) (mword_of_int 12 : mword 5) D1 (K - 24)%nat b
                ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
                ltac:(rgne; unfold neq_vec; rewrite HD1a2 Hx1; reflexivity)
                ltac:(vm_compute; reflexivity)
                with "Hcg Hpc [] [-]").
      { iApply (pki_2ea with "Htext"). }
      iIntros (CID8 Hst8). iNext. iIntros "Hcg Hpc".
      assert (Ht : add_vec (mword_of_int (KernelSyms.printk + 0x2ea) : mword 64) (sign_extend' 64 (sign_extend' 13 (concat_vec (mword_of_int 3 : mword 8) ('b"0")))) = mword_of_int (KernelSyms.printk + 0x2f0)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Ht) in "Hpc".
      iApply (wp_printk_chain_2f0 D1 K c0 c1 c2 Rest b pcur E1 E2 E3 E4 E5 E6 Hx0
                ltac:(rewrite Hx1; repeat rewrite andb_false_r; reflexivity) HD1s5 HD1s11 HD1a3 HD1a5
                with "Hcg Htext Hpc HR [-]").
      iIntros (CID9 Hst9 mf) "%Hk Hcg Hpc HR".
      iSpecialize ("Hcont" $! CID9 with "[%]"); [wp_next_chain|].
      iApply ("Hcont" $! mf with "[%] Hcg Hpc HR").
      exact (pk_chain_kept_trans mf D1 mq Hk HD1k).
  Qed.

  (* ---- 0x2d8 .. 0x2de: the "%llu" test, then on to 0x2e2 ---- *)
  Lemma wp_printk_chain_2d8 `{CID0 : CpuId}
      (mq : regfile) (K : nat) (c0 c1 c2 : Ascii.ascii) (Rest : iProp Σ) (b : bool) (pcur : mword 64) :
    Ascii.eqb c0 "d"%char = false ->
    (Ascii.eqb c0 "l"%char && Ascii.eqb c1 "d"%char)%bool = false ->
    (Ascii.eqb c0 "l"%char && (Ascii.eqb c1 "l"%char && Ascii.eqb c2 "d"%char))%bool = false ->
    Ascii.eqb c0 "u"%char = false ->
    (Ascii.eqb c0 "l"%char && Ascii.eqb c1 "u"%char)%bool = false ->
    mq !!! Regidx (mword_of_int 21 : mword 5) = zero_extend' 64 (pk_byte c0) ->
    mq !!! Regidx (mword_of_int 26 : mword 5) = (mword_of_int 120 : mword 64) ->
    mq !!! Regidx (mword_of_int 27 : mword 5) = (mword_of_int 112 : mword 64) ->
    mq !!! Regidx (mword_of_int 12 : mword 5) = zero_extend' 64 (pk_byte c1) ->
    mq !!! Regidx (mword_of_int 13 : mword 5) = zero_extend' 64 (pk_byte c2) ->
    mq !!! Regidx (mword_of_int 14 : mword 5) = pk_bit (Ascii.eqb c0 "l"%char) ->
    mq !!! Regidx a5_idx = pk_bit (Ascii.eqb c1 "l"%char && Ascii.eqb c0 "l"%char) ->
    sie_cap_gpr mq (K - 24)%nat b pcur -∗
    kernel_text -∗
    pc_is (mword_of_int (KernelSyms.printk + 0x2d8) : mword 64) -∗
    Rest -∗
    wp_next (CID0 := CID0) b pcur (fun (CID : CpuId) =>
      ∀ mf : regfile,
      ⌜ pk_chain_kept mf mq ⌝ -∗
      sie_cap_gpr mf (K - 24)%nat b pcur -∗
      pc_is (mword_of_int (KernelSyms.printk + pk_entry c0 c1 c2) : mword 64) -∗
      Rest -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros E1 E2 E3 E4 E5 Hs5 Hs10 Hs11 Ha2 Ha3 Ha4 Ha5.
    iIntros "Hcg #Htext Hpc HR Hcont".
    (* +0x2d8 addi a1,a3,-117 *)
    iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.printk + 0x2d8)) (mword_of_int 11 : mword 5)
              (mword_of_int 13 : mword 5) (mword_of_int 3979 : mword 12) mq (K - 24)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc [] [-]").
    { iApply (pki_2d8 with "Htext"). }
    iIntros (CID1 Hst1) "Hcg Hpc".
    set (D1 := <[Regidx (mword_of_int 11 : mword 5) := regval_into_reg
                   (add_vec (mq !!! Regidx (mword_of_int 13 : mword 5))
                      (sign_extend' 64 (mword_of_int 3979 : mword 12)))]> mq).
    assert (HD1k : pk_chain_kept D1 mq)
      by (intros c N ? ? ? ?; rewrite /D1 upd_ne; [reflexivity | congruence]).
    assert (HD1a1 : eq_vec (D1 !!! Regidx (mword_of_int 11 : mword 5)) (zero_reg : mword 64)
                    = Ascii.eqb c2 "u"%char).
    { rewrite /D1 upd_eq. unfold regval_into_reg. rewrite Ha3.
      apply (pk_sub_ascii c2 "u"%char). apply bv_eq; vm_compute; reflexivity. }
    assert (HD1a5 : D1 !!! Regidx a5_idx = pk_bit (Ascii.eqb c1 "l"%char && Ascii.eqb c0 "l"%char))
      by (rewrite /D1 upd_ne; [exact Ha5 | reg_neq]).
    assert (HD1a4 : D1 !!! Regidx (mword_of_int 14 : mword 5) = pk_bit (Ascii.eqb c0 "l"%char))
      by (rewrite /D1 upd_ne; [exact Ha4 | reg_neq]).
    assert (HD1a2 : D1 !!! Regidx (mword_of_int 12 : mword 5) = zero_extend' 64 (pk_byte c1))
      by (rewrite /D1 upd_ne; [exact Ha2 | reg_neq]).
    assert (HD1a3 : D1 !!! Regidx (mword_of_int 13 : mword 5) = zero_extend' 64 (pk_byte c2))
      by (rewrite /D1 upd_ne; [exact Ha3 | reg_neq]).
    assert (HD1s5 : D1 !!! Regidx (mword_of_int 21 : mword 5) = zero_extend' 64 (pk_byte c0))
      by (rewrite /D1 upd_ne; [exact Hs5 | reg_neq]).
    assert (HD1s10 : D1 !!! Regidx (mword_of_int 26 : mword 5) = (mword_of_int 120 : mword 64))
      by (rewrite /D1 upd_ne; [exact Hs10 | reg_neq]).
    assert (HD1s11 : D1 !!! Regidx (mword_of_int 27 : mword 5) = (mword_of_int 112 : mword 64))
      by (rewrite /D1 upd_ne; [exact Hs11 | reg_neq]).
    assert (Hp2dc : add_vec_int (mword_of_int (KernelSyms.printk + 0x2d8) : mword 64) 4 = mword_of_int (KernelSyms.printk + 0x2dc)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp2dc) in "Hpc".
    case_eq (Ascii.eqb c2 "u"%char); intro Hu2.
    - iApply (wp_cbnez_fall_s_sconf (mword_of_int (KernelSyms.printk + 0x2dc)) (mword_of_int 3 : mword 8)
                (Cregidx (mword_of_int 3)) (mword_of_int 11 : mword 5) D1 (K - 24)%nat b
                ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
                ltac:(rgne; unfold neq_vec; rewrite HD1a1 Hu2; reflexivity)
                with "Hcg Hpc [] [-]").
      { iApply (pki_2dc with "Htext"). }
      iIntros (CID2 Hst2) "Hcg Hpc".
      assert (Hp2de : add_vec_int (mword_of_int (KernelSyms.printk + 0x2dc) : mword 64) 2 = mword_of_int (KernelSyms.printk + 0x2de)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hp2de) in "Hpc".
      case_eq (Ascii.eqb c1 "l"%char && Ascii.eqb c0 "l"%char)%bool; intro Hll.
      + iApply (wp_bnez_x0_taken_s_sconf (mword_of_int (KernelSyms.printk + 0x2de)) (mword_of_int 7786 : mword 13)
                  a5_idx D1 (K - 24)%nat b ltac:(vm_compute; discriminate)
                  ltac:(rgne; rewrite HD1a5 pk_bit_nz; exact Hll)
                  ltac:(vm_compute; reflexivity)
                  with "Hcg Hpc [] [-]").
        { iApply (pki_2de with "Htext"). }
        iIntros (CID3 Hst3). iNext. iIntros "Hcg Hpc".
        assert (Ht : add_vec (mword_of_int (KernelSyms.printk + 0x2de) : mword 64) (sign_extend' 64 (mword_of_int 7786 : mword 13)) = mword_of_int (KernelSyms.printk + pk_entry c0 c1 c2)).
        { unfold pk_entry. rewrite E1 E2 E3 E4 E5.
          apply andb_true_iff in Hll as [Hl1 Hl0]. rewrite Hl0 Hl1 Hu2.
          apply bv_eq; vm_compute; reflexivity. }
        iEval (rewrite Ht) in "Hpc".
        iSpecialize ("Hcont" $! CID3 with "[%]"); [wp_next_chain|].
        iApply ("Hcont" $! D1 with "[%] Hcg Hpc HR"). exact HD1k.
      + iApply (wp_bnez_x0_fall_s_sconf (mword_of_int (KernelSyms.printk + 0x2de)) (mword_of_int 7786 : mword 13)
                  a5_idx D1 (K - 24)%nat b ltac:(vm_compute; discriminate)
                  ltac:(rgne; rewrite HD1a5 pk_bit_nz; exact Hll)
                  with "Hcg Hpc [] [-]").
        { iApply (pki_2de with "Htext"). }
        iIntros (CID4 Hst4) "Hcg Hpc".
        assert (Hp2e2 : add_vec_int (mword_of_int (KernelSyms.printk + 0x2de) : mword 64) 4 = mword_of_int (KernelSyms.printk + 0x2e2)) by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hp2e2) in "Hpc".
        iApply (wp_printk_chain_2e2 D1 K c0 c1 c2 Rest b pcur E1 E2 E3 E4 E5
                  ltac:(rewrite Hu2; repeat rewrite andb_true_r; rewrite andb_comm; exact Hll)
                  HD1s5 HD1s10 HD1s11 HD1a2 HD1a3 HD1a4 HD1a5
                  with "Hcg Htext Hpc HR [-]").
        iIntros (CID5 Hst5 mf) "%Hk Hcg Hpc HR".
        iSpecialize ("Hcont" $! CID5 with "[%]"); [wp_next_chain|].
        iApply ("Hcont" $! mf with "[%] Hcg Hpc HR").
        exact (pk_chain_kept_trans mf D1 mq Hk HD1k).
    - iApply (wp_cbnez_taken_s_sconf (mword_of_int (KernelSyms.printk + 0x2dc)) (mword_of_int 3 : mword 8)
                (Cregidx (mword_of_int 3)) (mword_of_int 11 : mword 5) D1 (K - 24)%nat b
                ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
                ltac:(rgne; unfold neq_vec; rewrite HD1a1 Hu2; reflexivity)
                ltac:(vm_compute; reflexivity)
                with "Hcg Hpc [] [-]").
      { iApply (pki_2dc with "Htext"). }
      iIntros (CID6 Hst6). iNext. iIntros "Hcg Hpc".
      assert (Ht : add_vec (mword_of_int (KernelSyms.printk + 0x2dc) : mword 64) (sign_extend' 64 (sign_extend' 13 (concat_vec (mword_of_int 3 : mword 8) ('b"0")))) = mword_of_int (KernelSyms.printk + 0x2e2)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Ht) in "Hpc".
      iApply (wp_printk_chain_2e2 D1 K c0 c1 c2 Rest b pcur E1 E2 E3 E4 E5
                ltac:(rewrite Hu2; repeat rewrite andb_false_r; reflexivity)
                HD1s5 HD1s10 HD1s11 HD1a2 HD1a3 HD1a4 HD1a5
                with "Hcg Htext Hpc HR [-]").
      iIntros (CID7 Hst7 mf) "%Hk Hcg Hpc HR".
      iSpecialize ("Hcont" $! CID7 with "[%]"); [wp_next_chain|].
      iApply ("Hcont" $! mf with "[%] Hcg Hpc HR").
      exact (pk_chain_kept_trans mf D1 mq Hk HD1k).
  Qed.

  (* ---- 0x2ca .. 0x2d4: "%u" and "%lu", then on to 0x2d8.  This is where
     the two SHORT-string entries rejoin the chain (0x2a8 jumps here). ---- *)
  Lemma wp_printk_chain_2ca `{CID0 : CpuId}
      (mq : regfile) (K : nat) (c0 c1 c2 : Ascii.ascii) (Rest : iProp Σ) (b : bool) (pcur : mword 64) :
    Ascii.eqb c0 "d"%char = false ->
    (Ascii.eqb c0 "l"%char && Ascii.eqb c1 "d"%char)%bool = false ->
    (Ascii.eqb c0 "l"%char && (Ascii.eqb c1 "l"%char && Ascii.eqb c2 "d"%char))%bool = false ->
    mq !!! Regidx (mword_of_int 21 : mword 5) = zero_extend' 64 (pk_byte c0) ->
    mq !!! Regidx (mword_of_int 24 : mword 5) = (mword_of_int 117 : mword 64) ->
    mq !!! Regidx (mword_of_int 26 : mword 5) = (mword_of_int 120 : mword 64) ->
    mq !!! Regidx (mword_of_int 27 : mword 5) = (mword_of_int 112 : mword 64) ->
    mq !!! Regidx (mword_of_int 12 : mword 5) = zero_extend' 64 (pk_byte c1) ->
    mq !!! Regidx (mword_of_int 13 : mword 5) = zero_extend' 64 (pk_byte c2) ->
    mq !!! Regidx (mword_of_int 14 : mword 5) = pk_bit (Ascii.eqb c0 "l"%char) ->
    mq !!! Regidx a5_idx = pk_bit (Ascii.eqb c1 "l"%char && Ascii.eqb c0 "l"%char) ->
    sie_cap_gpr mq (K - 24)%nat b pcur -∗
    kernel_text -∗
    pc_is (mword_of_int (KernelSyms.printk + 0x2ca) : mword 64) -∗
    Rest -∗
    wp_next (CID0 := CID0) b pcur (fun (CID : CpuId) =>
      ∀ mf : regfile,
      ⌜ pk_chain_kept mf mq ⌝ -∗
      sie_cap_gpr mf (K - 24)%nat b pcur -∗
      pc_is (mword_of_int (KernelSyms.printk + pk_entry c0 c1 c2) : mword 64) -∗
      Rest -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros E1 E2 E3 Hs5 Hs8 Hs10 Hs11 Ha2 Ha3 Ha4 Ha5.
    iIntros "Hcg #Htext Hpc HR Hcont".
    assert (Hid : pk_chain_kept mq mq) by (intros c ????; reflexivity).
    (* +0x2ca beq s5,s8 : '%u' *)
    case_eq (Ascii.eqb c0 "u"%char); intro Hu0.
    { iApply (wp_beq_taken_s_sconf (mword_of_int (KernelSyms.printk + 0x2ca)) (mword_of_int 7752 : mword 13)
                (mword_of_int 24 : mword 5) (mword_of_int 21 : mword 5) mq (K - 24)%nat b
                ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                ltac:(rgne; rgne; rewrite Hs5 Hs8 (pk_eq_ascii c0 "u"%char (mword_of_int 117)
                        ltac:(apply bv_eq; vm_compute; reflexivity)); exact Hu0)
                ltac:(vm_compute; reflexivity)
                with "Hcg Hpc [] [-]").
      { iApply (pki_2ca with "Htext"). }
      iIntros (CID1 Hst1). iNext. iIntros "Hcg Hpc".
      assert (Ht : add_vec (mword_of_int (KernelSyms.printk + 0x2ca) : mword 64) (sign_extend' 64 (mword_of_int 7752 : mword 13)) = mword_of_int (KernelSyms.printk + pk_entry c0 c1 c2)).
      { unfold pk_entry. rewrite E1 E2 E3 Hu0. apply bv_eq; vm_compute; reflexivity. }
      iEval (rewrite Ht) in "Hpc".
      iSpecialize ("Hcont" $! CID1 with "[%]"); [wp_next_chain|].
      iApply ("Hcont" $! mq with "[%] Hcg Hpc HR"). exact Hid. }
    iApply (wp_beq_fall_s_sconf (mword_of_int (KernelSyms.printk + 0x2ca)) (mword_of_int 7752 : mword 13)
              (mword_of_int 24 : mword 5) (mword_of_int 21 : mword 5) mq (K - 24)%nat b
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              ltac:(rgne; rgne; rewrite Hs5 Hs8 (pk_eq_ascii c0 "u"%char (mword_of_int 117)
                      ltac:(apply bv_eq; vm_compute; reflexivity)); exact Hu0)
              with "Hcg Hpc [] [-]").
    { iApply (pki_2ca with "Htext"). }
    iIntros (CID2 Hst2) "Hcg Hpc".
    assert (Hp2ce : add_vec_int (mword_of_int (KernelSyms.printk + 0x2ca) : mword 64) 4 = mword_of_int (KernelSyms.printk + 0x2ce)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp2ce) in "Hpc".
    (* +0x2ce addi a1,a2,-117 *)
    iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.printk + 0x2ce)) (mword_of_int 11 : mword 5)
              (mword_of_int 12 : mword 5) (mword_of_int 3979 : mword 12) mq (K - 24)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc [] [-]").
    { iApply (pki_2ce with "Htext"). }
    iIntros (CID3 Hst3) "Hcg Hpc".
    set (D1 := <[Regidx (mword_of_int 11 : mword 5) := regval_into_reg
                   (add_vec (mq !!! Regidx (mword_of_int 12 : mword 5))
                      (sign_extend' 64 (mword_of_int 3979 : mword 12)))]> mq).
    assert (HD1k : pk_chain_kept D1 mq)
      by (intros c N ? ? ? ?; rewrite /D1 upd_ne; [reflexivity | congruence]).
    assert (HD1a1 : eq_vec (D1 !!! Regidx (mword_of_int 11 : mword 5)) (zero_reg : mword 64)
                    = Ascii.eqb c1 "u"%char).
    { rewrite /D1 upd_eq. unfold regval_into_reg. rewrite Ha2.
      apply (pk_sub_ascii c1 "u"%char). apply bv_eq; vm_compute; reflexivity. }
    assert (HD1a5 : D1 !!! Regidx a5_idx = pk_bit (Ascii.eqb c1 "l"%char && Ascii.eqb c0 "l"%char))
      by (rewrite /D1 upd_ne; [exact Ha5 | reg_neq]).
    assert (HD1a4 : D1 !!! Regidx (mword_of_int 14 : mword 5) = pk_bit (Ascii.eqb c0 "l"%char))
      by (rewrite /D1 upd_ne; [exact Ha4 | reg_neq]).
    assert (HD1a2 : D1 !!! Regidx (mword_of_int 12 : mword 5) = zero_extend' 64 (pk_byte c1))
      by (rewrite /D1 upd_ne; [exact Ha2 | reg_neq]).
    assert (HD1a3 : D1 !!! Regidx (mword_of_int 13 : mword 5) = zero_extend' 64 (pk_byte c2))
      by (rewrite /D1 upd_ne; [exact Ha3 | reg_neq]).
    assert (HD1s5 : D1 !!! Regidx (mword_of_int 21 : mword 5) = zero_extend' 64 (pk_byte c0))
      by (rewrite /D1 upd_ne; [exact Hs5 | reg_neq]).
    assert (HD1s10 : D1 !!! Regidx (mword_of_int 26 : mword 5) = (mword_of_int 120 : mword 64))
      by (rewrite /D1 upd_ne; [exact Hs10 | reg_neq]).
    assert (HD1s11 : D1 !!! Regidx (mword_of_int 27 : mword 5) = (mword_of_int 112 : mword 64))
      by (rewrite /D1 upd_ne; [exact Hs11 | reg_neq]).
    assert (Hp2d2 : add_vec_int (mword_of_int (KernelSyms.printk + 0x2ce) : mword 64) 4 = mword_of_int (KernelSyms.printk + 0x2d2)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp2d2) in "Hpc".
    case_eq (Ascii.eqb c1 "u"%char); intro Hu1.
    - iApply (wp_cbnez_fall_s_sconf (mword_of_int (KernelSyms.printk + 0x2d2)) (mword_of_int 3 : mword 8)
                (Cregidx (mword_of_int 3)) (mword_of_int 11 : mword 5) D1 (K - 24)%nat b
                ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
                ltac:(rgne; unfold neq_vec; rewrite HD1a1 Hu1; reflexivity)
                with "Hcg Hpc [] [-]").
      { iApply (pki_2d2 with "Htext"). }
      iIntros (CID4 Hst4) "Hcg Hpc".
      assert (Hp2d4 : add_vec_int (mword_of_int (KernelSyms.printk + 0x2d2) : mword 64) 2 = mword_of_int (KernelSyms.printk + 0x2d4)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hp2d4) in "Hpc".
      case_eq (Ascii.eqb c0 "l"%char); intro Hl0.
      + iApply (wp_bnez_x0_taken_s_sconf (mword_of_int (KernelSyms.printk + 0x2d4)) (mword_of_int 7768 : mword 13)
                  (mword_of_int 14 : mword 5) D1 (K - 24)%nat b ltac:(vm_compute; discriminate)
                  ltac:(rgne; rewrite HD1a4 pk_bit_nz; exact Hl0)
                  ltac:(vm_compute; reflexivity)
                  with "Hcg Hpc [] [-]").
        { iApply (pki_2d4 with "Htext"). }
        iIntros (CID5 Hst5). iNext. iIntros "Hcg Hpc".
        assert (Ht : add_vec (mword_of_int (KernelSyms.printk + 0x2d4) : mword 64) (sign_extend' 64 (mword_of_int 7768 : mword 13)) = mword_of_int (KernelSyms.printk + pk_entry c0 c1 c2)).
        { unfold pk_entry. rewrite E1 E2 E3 Hu0 Hl0 Hu1. apply bv_eq; vm_compute; reflexivity. }
        iEval (rewrite Ht) in "Hpc".
        iSpecialize ("Hcont" $! CID5 with "[%]"); [wp_next_chain|].
        iApply ("Hcont" $! D1 with "[%] Hcg Hpc HR"). exact HD1k.
      + iApply (wp_bnez_x0_fall_s_sconf (mword_of_int (KernelSyms.printk + 0x2d4)) (mword_of_int 7768 : mword 13)
                  (mword_of_int 14 : mword 5) D1 (K - 24)%nat b ltac:(vm_compute; discriminate)
                  ltac:(rgne; rewrite HD1a4 pk_bit_nz; exact Hl0)
                  with "Hcg Hpc [] [-]").
        { iApply (pki_2d4 with "Htext"). }
        iIntros (CID6 Hst6) "Hcg Hpc".
        assert (Hp2d8 : add_vec_int (mword_of_int (KernelSyms.printk + 0x2d4) : mword 64) 4 = mword_of_int (KernelSyms.printk + 0x2d8)) by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hp2d8) in "Hpc".
        iApply (wp_printk_chain_2d8 D1 K c0 c1 c2 Rest b pcur E1 E2 E3 Hu0
                  ltac:(rewrite Hl0; reflexivity)
                  HD1s5 HD1s10 HD1s11 HD1a2 HD1a3 HD1a4 HD1a5
                  with "Hcg Htext Hpc HR [-]").
        iIntros (CID7 Hst7 mf) "%Hk Hcg Hpc HR".
        iSpecialize ("Hcont" $! CID7 with "[%]"); [wp_next_chain|].
        iApply ("Hcont" $! mf with "[%] Hcg Hpc HR").
        exact (pk_chain_kept_trans mf D1 mq Hk HD1k).
    - iApply (wp_cbnez_taken_s_sconf (mword_of_int (KernelSyms.printk + 0x2d2)) (mword_of_int 3 : mword 8)
                (Cregidx (mword_of_int 3)) (mword_of_int 11 : mword 5) D1 (K - 24)%nat b
                ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
                ltac:(rgne; unfold neq_vec; rewrite HD1a1 Hu1; reflexivity)
                ltac:(vm_compute; reflexivity)
                with "Hcg Hpc [] [-]").
      { iApply (pki_2d2 with "Htext"). }
      iIntros (CID8 Hst8). iNext. iIntros "Hcg Hpc".
      assert (Ht : add_vec (mword_of_int (KernelSyms.printk + 0x2d2) : mword 64) (sign_extend' 64 (sign_extend' 13 (concat_vec (mword_of_int 3 : mword 8) ('b"0")))) = mword_of_int (KernelSyms.printk + 0x2d8)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Ht) in "Hpc".
      iApply (wp_printk_chain_2d8 D1 K c0 c1 c2 Rest b pcur E1 E2 E3 Hu0
                ltac:(rewrite Hu1; repeat rewrite andb_false_r; reflexivity)
                HD1s5 HD1s10 HD1s11 HD1a2 HD1a3 HD1a4 HD1a5
                with "Hcg Htext Hpc HR [-]").
      iIntros (CID9 Hst9 mf) "%Hk Hcg Hpc HR".
      iSpecialize ("Hcont" $! CID9 with "[%]"); [wp_next_chain|].
      iApply ("Hcont" $! mf with "[%] Hcg Hpc HR").
      exact (pk_chain_kept_trans mf D1 mq Hk HD1k).
  Qed.

  (* ---- 0x2b6 .. 0x2c6: build the "ll" flag, test "%lld", then on to 0x2ca.
     Entered from 0xf4 (all three characters present) and by falling out of
     the c0 = 0 preamble at 0x2b4. ---- *)
  Lemma wp_printk_chain_2b6 `{CID0 : CpuId}
      (mq : regfile) (K : nat) (c0 c1 c2 : Ascii.ascii) (Rest : iProp Σ) (b : bool) (pcur : mword 64) :
    Ascii.eqb c0 "d"%char = false ->
    (Ascii.eqb c0 "l"%char && Ascii.eqb c1 "d"%char)%bool = false ->
    mq !!! Regidx (mword_of_int 21 : mword 5) = zero_extend' 64 (pk_byte c0) ->
    mq !!! Regidx (mword_of_int 24 : mword 5) = (mword_of_int 117 : mword 64) ->
    mq !!! Regidx (mword_of_int 26 : mword 5) = (mword_of_int 120 : mword 64) ->
    mq !!! Regidx (mword_of_int 27 : mword 5) = (mword_of_int 112 : mword 64) ->
    mq !!! Regidx (mword_of_int 12 : mword 5) = zero_extend' 64 (pk_byte c1) ->
    mq !!! Regidx (mword_of_int 13 : mword 5) = zero_extend' 64 (pk_byte c2) ->
    mq !!! Regidx (mword_of_int 14 : mword 5) = pk_bit (Ascii.eqb c0 "l"%char) ->
    sie_cap_gpr mq (K - 24)%nat b pcur -∗
    kernel_text -∗
    pc_is (mword_of_int (KernelSyms.printk + 0x2b6) : mword 64) -∗
    Rest -∗
    wp_next (CID0 := CID0) b pcur (fun (CID : CpuId) =>
      ∀ mf : regfile,
      ⌜ pk_chain_kept mf mq ⌝ -∗
      sie_cap_gpr mf (K - 24)%nat b pcur -∗
      pc_is (mword_of_int (KernelSyms.printk + pk_entry c0 c1 c2) : mword 64) -∗
      Rest -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros E1 E2 Hs5 Hs8 Hs10 Hs11 Ha2 Ha3 Ha4.
    iIntros "Hcg #Htext Hpc HR Hcont".
    (* +0x2b6 addi a5,a2,-108 ; +0x2ba seqz a5,a5 : c1 == 'l' *)
    iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.printk + 0x2b6)) a5_idx
              (mword_of_int 12 : mword 5) (mword_of_int 3988 : mword 12) mq (K - 24)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc [] [-]").
    { iApply (pki_2b6 with "Htext"). }
    iIntros (CID1 Hst1) "Hcg Hpc".
    set (D1 := <[Regidx a5_idx := regval_into_reg
                   (add_vec (mq !!! Regidx (mword_of_int 12 : mword 5))
                      (sign_extend' 64 (mword_of_int 3988 : mword 12)))]> mq).
    assert (HD1a5 : eq_vec (D1 !!! Regidx a5_idx) (zero_reg : mword 64) = Ascii.eqb c1 "l"%char).
    { rewrite /D1 upd_eq. unfold regval_into_reg. rewrite Ha2.
      apply (pk_sub_ascii c1 "l"%char). apply bv_eq; vm_compute; reflexivity. }
    assert (Hp2ba : add_vec_int (mword_of_int (KernelSyms.printk + 0x2b6) : mword 64) 4 = mword_of_int (KernelSyms.printk + 0x2ba)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp2ba) in "Hpc".
    iApply (wp_sltiu_s_sconf (mword_of_int (KernelSyms.printk + 0x2ba)) a5_idx a5_idx
              (mword_of_int 1 : mword 12) (pk_bit (Ascii.eqb c1 "l"%char)) D1 (K - 24)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(rgne; rewrite /pk_bit (ltu1_eqz (D1 !!! Regidx a5_idx)
                      (sign_extend' 64 (mword_of_int 1 : mword 12))
                      ltac:(apply bv_eq; vm_compute; reflexivity)) HD1a5; reflexivity)
              with "Hcg Hpc [] [-]").
    { iApply (pki_2ba with "Htext"). }
    iIntros (CID2 Hst2) "Hcg Hpc".
    set (D2 := <[Regidx a5_idx := regval_into_reg (pk_bit (Ascii.eqb c1 "l"%char))]> D1).
    assert (HD2a5 : D2 !!! Regidx a5_idx = pk_bit (Ascii.eqb c1 "l"%char))
      by (rewrite /D2 upd_eq; reflexivity).
    assert (HD2a4 : D2 !!! Regidx (mword_of_int 14 : mword 5) = pk_bit (Ascii.eqb c0 "l"%char)).
    { rewrite /D2 upd_ne; [| reg_neq]. rewrite /D1 upd_ne; [exact Ha4 | reg_neq]. }
    assert (Hp2be : add_vec_int (mword_of_int (KernelSyms.printk + 0x2ba) : mword 64) 4 = mword_of_int (KernelSyms.printk + 0x2be)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp2be) in "Hpc".
    (* +0x2be and a5,a5,a4 : the "ll" flag *)
    iApply (wp_cand_s_sconf (mword_of_int (KernelSyms.printk + 0x2be)) a5_idx (mword_of_int 14 : mword 5)
              D2 (K - 24)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc [] [-]").
    { iApply (pki_2be with "Htext"). }
    iIntros (CID3 Hst3) "Hcg Hpc".
    iEval (rgne; rgne) in "Hcg".
    set (D3 := <[Regidx a5_idx := regval_into_reg
                   (and_vec (D2 !!! Regidx a5_idx) (D2 !!! Regidx (mword_of_int 14 : mword 5)))]> D2).
    assert (HD3a5 : D3 !!! Regidx a5_idx = pk_bit (Ascii.eqb c1 "l"%char && Ascii.eqb c0 "l"%char)).
    { rewrite /D3 upd_eq. unfold regval_into_reg. rewrite HD2a5 HD2a4. apply pk_bit_and. }
    assert (Hp2c0 : add_vec_int (mword_of_int (KernelSyms.printk + 0x2be) : mword 64) 2 = mword_of_int (KernelSyms.printk + 0x2c0)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp2c0) in "Hpc".
    (* +0x2c0 addi a1,a3,-100 *)
    iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.printk + 0x2c0)) (mword_of_int 11 : mword 5)
              (mword_of_int 13 : mword 5) (mword_of_int 3996 : mword 12) D3 (K - 24)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc [] [-]").
    { iApply (pki_2c0 with "Htext"). }
    iIntros (CID4 Hst4) "Hcg Hpc".
    set (D4 := <[Regidx (mword_of_int 11 : mword 5) := regval_into_reg
                   (add_vec (D3 !!! Regidx (mword_of_int 13 : mword 5))
                      (sign_extend' 64 (mword_of_int 3996 : mword 12)))]> D3).
    assert (HD3a3 : D3 !!! Regidx (mword_of_int 13 : mword 5) = zero_extend' 64 (pk_byte c2)).
    { rewrite /D3 upd_ne; [| reg_neq]. rewrite /D2 upd_ne; [| reg_neq].
      rewrite /D1 upd_ne; [exact Ha3 | reg_neq]. }
    assert (HD4a1 : eq_vec (D4 !!! Regidx (mword_of_int 11 : mword 5)) (zero_reg : mword 64)
                    = Ascii.eqb c2 "d"%char).
    { rewrite /D4 upd_eq. unfold regval_into_reg. rewrite HD3a3.
      apply (pk_sub_ascii c2 "d"%char). apply bv_eq; vm_compute; reflexivity. }
    assert (HD4k : pk_chain_kept D4 mq).
    { intros c N1 N2 N3 N4 N5.
      rewrite /D4 upd_ne; [| congruence]. rewrite /D3 upd_ne; [| congruence].
      rewrite /D2 upd_ne; [| congruence]. rewrite /D1 upd_ne; [reflexivity | congruence]. }
    assert (HD4a5 : D4 !!! Regidx a5_idx = pk_bit (Ascii.eqb c1 "l"%char && Ascii.eqb c0 "l"%char))
      by (rewrite /D4 upd_ne; [exact HD3a5 | reg_neq]).
    assert (HD4a4 : D4 !!! Regidx (mword_of_int 14 : mword 5) = pk_bit (Ascii.eqb c0 "l"%char))
      by (rewrite /D4 upd_ne; [exact HD2a4 | reg_neq]).
    assert (HD4a2 : D4 !!! Regidx (mword_of_int 12 : mword 5) = zero_extend' 64 (pk_byte c1)).
    { rewrite /D4 upd_ne; [| reg_neq]. rewrite /D3 upd_ne; [| reg_neq].
      rewrite /D2 upd_ne; [| reg_neq]. rewrite /D1 upd_ne; [exact Ha2 | reg_neq]. }
    assert (HD4a3 : D4 !!! Regidx (mword_of_int 13 : mword 5) = zero_extend' 64 (pk_byte c2))
      by (rewrite /D4 upd_ne; [exact HD3a3 | reg_neq]).
    assert (HD4s5 : D4 !!! Regidx (mword_of_int 21 : mword 5) = zero_extend' 64 (pk_byte c0)).
    { rewrite (HD4k (mword_of_int 21 : mword 5)); [exact Hs5 | reg_neq | reg_neq | reg_neq | reg_neq | reg_neq]. }
    assert (HD4s8 : D4 !!! Regidx (mword_of_int 24 : mword 5) = (mword_of_int 117 : mword 64)).
    { rewrite (HD4k (mword_of_int 24 : mword 5)); [exact Hs8 | reg_neq | reg_neq | reg_neq | reg_neq | reg_neq]. }
    assert (HD4s10 : D4 !!! Regidx (mword_of_int 26 : mword 5) = (mword_of_int 120 : mword 64)).
    { rewrite (HD4k (mword_of_int 26 : mword 5)); [exact Hs10 | reg_neq | reg_neq | reg_neq | reg_neq | reg_neq]. }
    assert (HD4s11 : D4 !!! Regidx (mword_of_int 27 : mword 5) = (mword_of_int 112 : mword 64)).
    { rewrite (HD4k (mword_of_int 27 : mword 5)); [exact Hs11 | reg_neq | reg_neq | reg_neq | reg_neq | reg_neq]. }
    assert (Hp2c4 : add_vec_int (mword_of_int (KernelSyms.printk + 0x2c0) : mword 64) 4 = mword_of_int (KernelSyms.printk + 0x2c4)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp2c4) in "Hpc".
    (* +0x2c4 bnez a1 ; +0x2c6 bnez a5 : "%lld" *)
    case_eq (Ascii.eqb c2 "d"%char); intro Hd2.
    - iApply (wp_cbnez_fall_s_sconf (mword_of_int (KernelSyms.printk + 0x2c4)) (mword_of_int 3 : mword 8)
                (Cregidx (mword_of_int 3)) (mword_of_int 11 : mword 5) D4 (K - 24)%nat b
                ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
                ltac:(rgne; unfold neq_vec; rewrite HD4a1 Hd2; reflexivity)
                with "Hcg Hpc [] [-]").
      { iApply (pki_2c4 with "Htext"). }
      iIntros (CID5 Hst5) "Hcg Hpc".
      assert (Hp2c6 : add_vec_int (mword_of_int (KernelSyms.printk + 0x2c4) : mword 64) 2 = mword_of_int (KernelSyms.printk + 0x2c6)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hp2c6) in "Hpc".
      case_eq (Ascii.eqb c1 "l"%char && Ascii.eqb c0 "l"%char)%bool; intro Hll.
      + iApply (wp_bnez_x0_taken_s_sconf (mword_of_int (KernelSyms.printk + 0x2c6)) (mword_of_int 7728 : mword 13)
                  a5_idx D4 (K - 24)%nat b ltac:(vm_compute; discriminate)
                  ltac:(rgne; rewrite HD4a5 pk_bit_nz; exact Hll)
                  ltac:(vm_compute; reflexivity)
                  with "Hcg Hpc [] [-]").
        { iApply (pki_2c6 with "Htext"). }
        iIntros (CID6 Hst6). iNext. iIntros "Hcg Hpc".
        assert (Ht : add_vec (mword_of_int (KernelSyms.printk + 0x2c6) : mword 64) (sign_extend' 64 (mword_of_int 7728 : mword 13)) = mword_of_int (KernelSyms.printk + pk_entry c0 c1 c2)).
        { unfold pk_entry. rewrite E1 E2.
          apply andb_true_iff in Hll as [Hl1 Hl0]. rewrite Hl0 Hl1 Hd2.
          apply bv_eq; vm_compute; reflexivity. }
        iEval (rewrite Ht) in "Hpc".
        iSpecialize ("Hcont" $! CID6 with "[%]"); [wp_next_chain|].
        iApply ("Hcont" $! D4 with "[%] Hcg Hpc HR"). exact HD4k.
      + iApply (wp_bnez_x0_fall_s_sconf (mword_of_int (KernelSyms.printk + 0x2c6)) (mword_of_int 7728 : mword 13)
                  a5_idx D4 (K - 24)%nat b ltac:(vm_compute; discriminate)
                  ltac:(rgne; rewrite HD4a5 pk_bit_nz; exact Hll)
                  with "Hcg Hpc [] [-]").
        { iApply (pki_2c6 with "Htext"). }
        iIntros (CID7 Hst7) "Hcg Hpc".
        assert (Hp2ca : add_vec_int (mword_of_int (KernelSyms.printk + 0x2c6) : mword 64) 4 = mword_of_int (KernelSyms.printk + 0x2ca)) by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hp2ca) in "Hpc".
        iApply (wp_printk_chain_2ca D4 K c0 c1 c2 Rest b pcur E1 E2
                  ltac:(rewrite Hd2; repeat rewrite andb_true_r; rewrite andb_comm; exact Hll)
                  HD4s5 HD4s8 HD4s10 HD4s11 HD4a2 HD4a3 HD4a4 HD4a5
                  with "Hcg Htext Hpc HR [-]").
        iIntros (CID8 Hst8 mf) "%Hk Hcg Hpc HR".
        iSpecialize ("Hcont" $! CID8 with "[%]"); [wp_next_chain|].
        iApply ("Hcont" $! mf with "[%] Hcg Hpc HR").
        exact (pk_chain_kept_trans mf D4 mq Hk HD4k).
    - iApply (wp_cbnez_taken_s_sconf (mword_of_int (KernelSyms.printk + 0x2c4)) (mword_of_int 3 : mword 8)
                (Cregidx (mword_of_int 3)) (mword_of_int 11 : mword 5) D4 (K - 24)%nat b
                ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
                ltac:(rgne; unfold neq_vec; rewrite HD4a1 Hd2; reflexivity)
                ltac:(vm_compute; reflexivity)
                with "Hcg Hpc [] [-]").
      { iApply (pki_2c4 with "Htext"). }
      iIntros (CID9 Hst9). iNext. iIntros "Hcg Hpc".
      assert (Ht : add_vec (mword_of_int (KernelSyms.printk + 0x2c4) : mword 64) (sign_extend' 64 (sign_extend' 13 (concat_vec (mword_of_int 3 : mword 8) ('b"0")))) = mword_of_int (KernelSyms.printk + 0x2ca)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Ht) in "Hpc".
      iApply (wp_printk_chain_2ca D4 K c0 c1 c2 Rest b pcur E1 E2
                ltac:(rewrite Hd2; repeat rewrite andb_false_r; reflexivity)
                HD4s5 HD4s8 HD4s10 HD4s11 HD4a2 HD4a3 HD4a4 HD4a5
                with "Hcg Htext Hpc HR [-]").
      iIntros (CID10 Hst10 mf) "%Hk Hcg Hpc HR".
      iSpecialize ("Hcont" $! CID10 with "[%]"); [wp_next_chain|].
      iApply ("Hcont" $! mf with "[%] Hcg Hpc HR").
      exact (pk_chain_kept_trans mf D4 mq Hk HD4k).
  Qed.

  (* the character at or past the end is the NUL [pk_dir] is applied to *)
  Lemma pk_ch_nul (f : string) (j : nat) :
    (String.length f <= j)%nat -> pk_ch f j = pk_nul.
  Proof.
    revert j. induction f as [|c f IH]; intros j Hj; [destruct j; reflexivity | ].
    destruct j as [|j]; [cbn in Hj; lia | ]. cbn. apply IH. cbn in Hj. lia.
  Qed.

  (* a zero byte inside the bound can only be the terminator *)
  Lemma pk_fbyte_zero_end (f : string) (j : nat) :
    nonul f = true -> (j <= String.length f)%nat ->
    pk_fbyte f j = (mword_of_int 0 : mword 8) -> j = String.length f.
  Proof.
    intros Hn Hj Hz.
    destruct (Nat.eq_dec j (String.length f)) as [He | He]; [exact He | ].
    exfalso. apply (pk_fbyte_nonzero f j Hn); [ rewrite string_bytes_length; lia | exact Hz ].
  Qed.

  (* ---- 0x2aa .. 0x2b4: the c0 = 0 preamble, which falls into 0x2b6 ---- *)
  Lemma wp_printk_chain_2aa `{CID0 : CpuId}
      (mq : regfile) (K : nat) (c0 c1 c2 : Ascii.ascii) (Rest : iProp Σ) (b : bool) (pcur : mword 64) :
    c0 = pk_nul -> c1 = pk_nul -> c2 = pk_nul ->
    mq !!! Regidx (mword_of_int 21 : mword 5) = zero_extend' 64 (pk_byte c0) ->
    mq !!! Regidx (mword_of_int 24 : mword 5) = (mword_of_int 117 : mword 64) ->
    mq !!! Regidx (mword_of_int 26 : mword 5) = (mword_of_int 120 : mword 64) ->
    mq !!! Regidx (mword_of_int 27 : mword 5) = (mword_of_int 112 : mword 64) ->
    sie_cap_gpr mq (K - 24)%nat b pcur -∗
    kernel_text -∗
    pc_is (mword_of_int (KernelSyms.printk + 0x2aa) : mword 64) -∗
    Rest -∗
    wp_next (CID0 := CID0) b pcur (fun (CID : CpuId) =>
      ∀ mf : regfile,
      ⌜ pk_chain_kept mf mq ⌝ -∗
      sie_cap_gpr mf (K - 24)%nat b pcur -∗
      pc_is (mword_of_int (KernelSyms.printk + pk_entry c0 c1 c2) : mword 64) -∗
      Rest -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hn0 Hn1 Hn2 Hs5 Hs8 Hs10 Hs11.
    iIntros "Hcg #Htext Hpc HR Hcont".
    (* +0x2aa addi a4,s5,-108 ; +0x2ae seqz a4,a4 *)
    iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.printk + 0x2aa)) (mword_of_int 14 : mword 5)
              (mword_of_int 21 : mword 5) (mword_of_int 3988 : mword 12) mq (K - 24)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc [] [-]").
    { iApply (pki_2aa with "Htext"). }
    iIntros (CID1 Hst1) "Hcg Hpc".
    set (D1 := <[Regidx (mword_of_int 14 : mword 5) := regval_into_reg
                   (add_vec (mq !!! Regidx (mword_of_int 21 : mword 5))
                      (sign_extend' 64 (mword_of_int 3988 : mword 12)))]> mq).
    assert (HD1a4 : eq_vec (D1 !!! Regidx (mword_of_int 14 : mword 5)) (zero_reg : mword 64)
                    = Ascii.eqb c0 "l"%char).
    { rewrite /D1 upd_eq. unfold regval_into_reg. rewrite Hs5.
      apply (pk_sub_ascii c0 "l"%char). apply bv_eq; vm_compute; reflexivity. }
    assert (Hp2ae : add_vec_int (mword_of_int (KernelSyms.printk + 0x2aa) : mword 64) 4 = mword_of_int (KernelSyms.printk + 0x2ae)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp2ae) in "Hpc".
    iApply (wp_sltiu_s_sconf (mword_of_int (KernelSyms.printk + 0x2ae)) (mword_of_int 14 : mword 5)
              (mword_of_int 14 : mword 5) (mword_of_int 1 : mword 12)
              (pk_bit (Ascii.eqb c0 "l"%char)) D1 (K - 24)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(rgne; rewrite /pk_bit (ltu1_eqz (D1 !!! Regidx (mword_of_int 14 : mword 5))
                      (sign_extend' 64 (mword_of_int 1 : mword 12))
                      ltac:(apply bv_eq; vm_compute; reflexivity)) HD1a4; reflexivity)
              with "Hcg Hpc [] [-]").
    { iApply (pki_2ae with "Htext"). }
    iIntros (CID2 Hst2) "Hcg Hpc".
    set (D2 := <[Regidx (mword_of_int 14 : mword 5) := regval_into_reg (pk_bit (Ascii.eqb c0 "l"%char))]> D1).
    assert (Hp2b2 : add_vec_int (mword_of_int (KernelSyms.printk + 0x2ae) : mword 64) 4 = mword_of_int (KernelSyms.printk + 0x2b2)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp2b2) in "Hpc".
    (* +0x2b2 mv a2,s5 ; +0x2b4 mv a3,s5 : both lookaheads are the NUL *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.printk + 0x2b2)) (mword_of_int 12 : mword 5)
              (mword_of_int 21 : mword 5) D2 (K - 24)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc [] [-]").
    { iApply (pki_2b2 with "Htext"). }
    iIntros (CID3 Hst3) "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (D3 := <[Regidx (mword_of_int 12 : mword 5) := regval_into_reg
                   (add_vec zero_reg (D2 !!! Regidx (mword_of_int 21 : mword 5)))]> D2).
    assert (Hp2b4 : add_vec_int (mword_of_int (KernelSyms.printk + 0x2b2) : mword 64) 2 = mword_of_int (KernelSyms.printk + 0x2b4)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp2b4) in "Hpc".
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.printk + 0x2b4)) (mword_of_int 13 : mword 5)
              (mword_of_int 21 : mword 5) D3 (K - 24)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc [] [-]").
    { iApply (pki_2b4 with "Htext"). }
    iIntros (CID4 Hst4) "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (D4 := <[Regidx (mword_of_int 13 : mword 5) := regval_into_reg
                   (add_vec zero_reg (D3 !!! Regidx (mword_of_int 21 : mword 5)))]> D3).
    assert (HD4k : pk_chain_kept D4 mq).
    { intros c N1 N2 N3 N4 N5.
      rewrite /D4 upd_ne; [| congruence]. rewrite /D3 upd_ne; [| congruence].
      rewrite /D2 upd_ne; [| congruence]. rewrite /D1 upd_ne; [reflexivity | congruence]. }
    assert (HD2s5 : D2 !!! Regidx (mword_of_int 21 : mword 5) = zero_extend' 64 (pk_byte c0)).
    { rewrite /D2 upd_ne; [| reg_neq]. rewrite /D1 upd_ne; [exact Hs5 | reg_neq]. }
    assert (HD3s5 : D3 !!! Regidx (mword_of_int 21 : mword 5) = zero_extend' 64 (pk_byte c0))
      by (rewrite /D3 upd_ne; [exact HD2s5 | reg_neq]).
    assert (HD4a2 : D4 !!! Regidx (mword_of_int 12 : mword 5) = zero_extend' 64 (pk_byte c1)).
    { rewrite /D4 upd_ne; [| reg_neq]. rewrite /D3 upd_eq. unfold regval_into_reg.
      rewrite HD2s5 add_vec_zero_l Hn0 Hn1. reflexivity. }
    assert (HD4a3 : D4 !!! Regidx (mword_of_int 13 : mword 5) = zero_extend' 64 (pk_byte c2)).
    { rewrite /D4 upd_eq. unfold regval_into_reg.
      rewrite HD3s5 add_vec_zero_l Hn0 Hn2. reflexivity. }
    assert (HD4a4 : D4 !!! Regidx (mword_of_int 14 : mword 5) = pk_bit (Ascii.eqb c0 "l"%char)).
    { rewrite /D4 upd_ne; [| reg_neq]. rewrite /D3 upd_ne; [| reg_neq].
      rewrite /D2 upd_eq; reflexivity. }
    assert (HD4s5 : D4 !!! Regidx (mword_of_int 21 : mword 5) = zero_extend' 64 (pk_byte c0)).
    { rewrite (HD4k (mword_of_int 21 : mword 5)); [exact Hs5 | reg_neq | reg_neq | reg_neq | reg_neq | reg_neq]. }
    assert (HD4s8 : D4 !!! Regidx (mword_of_int 24 : mword 5) = (mword_of_int 117 : mword 64)).
    { rewrite (HD4k (mword_of_int 24 : mword 5)); [exact Hs8 | reg_neq | reg_neq | reg_neq | reg_neq | reg_neq]. }
    assert (HD4s10 : D4 !!! Regidx (mword_of_int 26 : mword 5) = (mword_of_int 120 : mword 64)).
    { rewrite (HD4k (mword_of_int 26 : mword 5)); [exact Hs10 | reg_neq | reg_neq | reg_neq | reg_neq | reg_neq]. }
    assert (HD4s11 : D4 !!! Regidx (mword_of_int 27 : mword 5) = (mword_of_int 112 : mword 64)).
    { rewrite (HD4k (mword_of_int 27 : mword 5)); [exact Hs11 | reg_neq | reg_neq | reg_neq | reg_neq | reg_neq]. }
    assert (Hp2b6 : add_vec_int (mword_of_int (KernelSyms.printk + 0x2b4) : mword 64) 2 = mword_of_int (KernelSyms.printk + 0x2b6)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp2b6) in "Hpc".
    iApply (wp_printk_chain_2b6 D4 K c0 c1 c2 Rest b pcur
              ltac:(rewrite Hn0; reflexivity)
              ltac:(rewrite Hn1; repeat rewrite andb_false_r; reflexivity)
              HD4s5 HD4s8 HD4s10 HD4s11 HD4a2 HD4a3 HD4a4
              with "Hcg Htext Hpc HR [-]").
    iIntros (CID5 Hst5 mf) "%Hk Hcg Hpc HR".
    iSpecialize ("Hcont" $! CID5 with "[%]"); [wp_next_chain|].
    iApply ("Hcont" $! mf with "[%] Hcg Hpc HR").
    exact (pk_chain_kept_trans mf D4 mq Hk HD4k).
  Qed.

  (* ---- 0x298 .. 0x2a8: the c1 = 0 preamble, which jumps to 0x2ca ---- *)
  Lemma wp_printk_chain_298 `{CID0 : CpuId}
      (mq : regfile) (K : nat) (c0 c1 c2 : Ascii.ascii) (Rest : iProp Σ) (b : bool) (pcur : mword 64) :
    c1 = pk_nul -> c2 = pk_nul ->
    mq !!! Regidx (mword_of_int 21 : mword 5) = zero_extend' 64 (pk_byte c0) ->
    mq !!! Regidx (mword_of_int 13 : mword 5) = zero_extend' 64 (pk_byte c1) ->
    mq !!! Regidx (mword_of_int 23 : mword 5) = (mword_of_int 100 : mword 64) ->
    mq !!! Regidx (mword_of_int 24 : mword 5) = (mword_of_int 117 : mword 64) ->
    mq !!! Regidx (mword_of_int 26 : mword 5) = (mword_of_int 120 : mword 64) ->
    mq !!! Regidx (mword_of_int 27 : mword 5) = (mword_of_int 112 : mword 64) ->
    sie_cap_gpr mq (K - 24)%nat b pcur -∗
    kernel_text -∗
    pc_is (mword_of_int (KernelSyms.printk + 0x298) : mword 64) -∗
    Rest -∗
    wp_next (CID0 := CID0) b pcur (fun (CID : CpuId) =>
      ∀ mf : regfile,
      ⌜ pk_chain_kept mf mq ⌝ -∗
      sie_cap_gpr mf (K - 24)%nat b pcur -∗
      pc_is (mword_of_int (KernelSyms.printk + pk_entry c0 c1 c2) : mword 64) -∗
      Rest -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hn1 Hn2 Hs5 Ha3 Hs7 Hs8 Hs10 Hs11.
    iIntros "Hcg #Htext Hpc HR Hcont".
    assert (Hid : pk_chain_kept mq mq) by (intros c ????; reflexivity).
    (* +0x298 beq s5,s7 : '%d' *)
    case_eq (Ascii.eqb c0 "d"%char); intro Hd0.
    { iApply (wp_beq_taken_s_sconf (mword_of_int (KernelSyms.printk + 0x298)) (mword_of_int 7740 : mword 13)
                (mword_of_int 23 : mword 5) (mword_of_int 21 : mword 5) mq (K - 24)%nat b
                ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                ltac:(rgne; rgne; rewrite Hs5 Hs7 (pk_eq_ascii c0 "d"%char (mword_of_int 100)
                        ltac:(apply bv_eq; vm_compute; reflexivity)); exact Hd0)
                ltac:(vm_compute; reflexivity)
                with "Hcg Hpc [] [-]").
      { iApply (pki_298 with "Htext"). }
      iIntros (CID1 Hst1). iNext. iIntros "Hcg Hpc".
      assert (Ht : add_vec (mword_of_int (KernelSyms.printk + 0x298) : mword 64) (sign_extend' 64 (mword_of_int 7740 : mword 13)) = mword_of_int (KernelSyms.printk + pk_entry c0 c1 c2)).
      { unfold pk_entry. rewrite Hd0. apply bv_eq; vm_compute; reflexivity. }
      iEval (rewrite Ht) in "Hpc".
      iSpecialize ("Hcont" $! CID1 with "[%]"); [wp_next_chain|].
      iApply ("Hcont" $! mq with "[%] Hcg Hpc HR"). exact Hid. }
    iApply (wp_beq_fall_s_sconf (mword_of_int (KernelSyms.printk + 0x298)) (mword_of_int 7740 : mword 13)
              (mword_of_int 23 : mword 5) (mword_of_int 21 : mword 5) mq (K - 24)%nat b
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              ltac:(rgne; rgne; rewrite Hs5 Hs7 (pk_eq_ascii c0 "d"%char (mword_of_int 100)
                      ltac:(apply bv_eq; vm_compute; reflexivity)); exact Hd0)
              with "Hcg Hpc [] [-]").
    { iApply (pki_298 with "Htext"). }
    iIntros (CID2 Hst2) "Hcg Hpc".
    assert (Hp29c : add_vec_int (mword_of_int (KernelSyms.printk + 0x298) : mword 64) 4 = mword_of_int (KernelSyms.printk + 0x29c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp29c) in "Hpc".
    (* +0x29c addi a4,s5,-108 ; +0x2a0 seqz a4,a4 *)
    iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.printk + 0x29c)) (mword_of_int 14 : mword 5)
              (mword_of_int 21 : mword 5) (mword_of_int 3988 : mword 12) mq (K - 24)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc [] [-]").
    { iApply (pki_29c with "Htext"). }
    iIntros (CID3 Hst3) "Hcg Hpc".
    set (D1 := <[Regidx (mword_of_int 14 : mword 5) := regval_into_reg
                   (add_vec (mq !!! Regidx (mword_of_int 21 : mword 5))
                      (sign_extend' 64 (mword_of_int 3988 : mword 12)))]> mq).
    assert (HD1a4 : eq_vec (D1 !!! Regidx (mword_of_int 14 : mword 5)) (zero_reg : mword 64)
                    = Ascii.eqb c0 "l"%char).
    { rewrite /D1 upd_eq. unfold regval_into_reg. rewrite Hs5.
      apply (pk_sub_ascii c0 "l"%char). apply bv_eq; vm_compute; reflexivity. }
    assert (Hp2a0 : add_vec_int (mword_of_int (KernelSyms.printk + 0x29c) : mword 64) 4 = mword_of_int (KernelSyms.printk + 0x2a0)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp2a0) in "Hpc".
    iApply (wp_sltiu_s_sconf (mword_of_int (KernelSyms.printk + 0x2a0)) (mword_of_int 14 : mword 5)
              (mword_of_int 14 : mword 5) (mword_of_int 1 : mword 12)
              (pk_bit (Ascii.eqb c0 "l"%char)) D1 (K - 24)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(rgne; rewrite /pk_bit (ltu1_eqz (D1 !!! Regidx (mword_of_int 14 : mword 5))
                      (sign_extend' 64 (mword_of_int 1 : mword 12))
                      ltac:(apply bv_eq; vm_compute; reflexivity)) HD1a4; reflexivity)
              with "Hcg Hpc [] [-]").
    { iApply (pki_2a0 with "Htext"). }
    iIntros (CID4 Hst4) "Hcg Hpc".
    set (D2 := <[Regidx (mword_of_int 14 : mword 5) := regval_into_reg (pk_bit (Ascii.eqb c0 "l"%char))]> D1).
    assert (Hp2a4 : add_vec_int (mword_of_int (KernelSyms.printk + 0x2a0) : mword 64) 4 = mword_of_int (KernelSyms.printk + 0x2a4)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp2a4) in "Hpc".
    (* +0x2a4 mv a2,a3 *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.printk + 0x2a4)) (mword_of_int 12 : mword 5)
              (mword_of_int 13 : mword 5) D2 (K - 24)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc [] [-]").
    { iApply (pki_2a4 with "Htext"). }
    iIntros (CID5 Hst5) "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (D3 := <[Regidx (mword_of_int 12 : mword 5) := regval_into_reg
                   (add_vec zero_reg (D2 !!! Regidx (mword_of_int 13 : mword 5)))]> D2).
    assert (Hp2a6 : add_vec_int (mword_of_int (KernelSyms.printk + 0x2a4) : mword 64) 2 = mword_of_int (KernelSyms.printk + 0x2a6)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp2a6) in "Hpc".
    (* +0x2a6 li a5,0 : the "ll" flag, which cannot be set with c1 = 0 *)
    iApply (wp_cli_s_sconf (mword_of_int (KernelSyms.printk + 0x2a6)) a5_idx (mword_of_int 0 : mword 6)
              (pk_bit (Ascii.eqb c1 "l"%char && Ascii.eqb c0 "l"%char)) D3 (K - 24)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(rewrite Hn1; apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc [] [-]").
    { iApply (pki_2a6 with "Htext"). }
    iIntros (CID6 Hst6) "Hcg Hpc".
    set (D4 := <[Regidx a5_idx := regval_into_reg (pk_bit (Ascii.eqb c1 "l"%char && Ascii.eqb c0 "l"%char))]> D3).
    assert (HD4k : pk_chain_kept D4 mq).
    { intros c N1 N2 N3 N4 N5.
      rewrite /D4 upd_ne; [| congruence]. rewrite /D3 upd_ne; [| congruence].
      rewrite /D2 upd_ne; [| congruence]. rewrite /D1 upd_ne; [reflexivity | congruence]. }
    assert (HD2a3 : D2 !!! Regidx (mword_of_int 13 : mword 5) = zero_extend' 64 (pk_byte c1)).
    { rewrite /D2 upd_ne; [| reg_neq]. rewrite /D1 upd_ne; [exact Ha3 | reg_neq]. }
    assert (HD4a2 : D4 !!! Regidx (mword_of_int 12 : mword 5) = zero_extend' 64 (pk_byte c1)).
    { rewrite /D4 upd_ne; [| reg_neq]. rewrite /D3 upd_eq. unfold regval_into_reg.
      rewrite HD2a3 add_vec_zero_l. reflexivity. }
    assert (HD4a3 : D4 !!! Regidx (mword_of_int 13 : mword 5) = zero_extend' 64 (pk_byte c2)).
    { rewrite /D4 upd_ne; [| reg_neq]. rewrite /D3 upd_ne; [| reg_neq].
      rewrite HD2a3 Hn1 Hn2. reflexivity. }
    assert (HD4a4 : D4 !!! Regidx (mword_of_int 14 : mword 5) = pk_bit (Ascii.eqb c0 "l"%char)).
    { rewrite /D4 upd_ne; [| reg_neq]. rewrite /D3 upd_ne; [| reg_neq].
      rewrite /D2 upd_eq; reflexivity. }
    assert (HD4a5 : D4 !!! Regidx a5_idx = pk_bit (Ascii.eqb c1 "l"%char && Ascii.eqb c0 "l"%char))
      by (rewrite /D4 upd_eq; reflexivity).
    assert (HD4s5 : D4 !!! Regidx (mword_of_int 21 : mword 5) = zero_extend' 64 (pk_byte c0)).
    { rewrite (HD4k (mword_of_int 21 : mword 5)); [exact Hs5 | reg_neq | reg_neq | reg_neq | reg_neq | reg_neq]. }
    assert (HD4s8 : D4 !!! Regidx (mword_of_int 24 : mword 5) = (mword_of_int 117 : mword 64)).
    { rewrite (HD4k (mword_of_int 24 : mword 5)); [exact Hs8 | reg_neq | reg_neq | reg_neq | reg_neq | reg_neq]. }
    assert (HD4s10 : D4 !!! Regidx (mword_of_int 26 : mword 5) = (mword_of_int 120 : mword 64)).
    { rewrite (HD4k (mword_of_int 26 : mword 5)); [exact Hs10 | reg_neq | reg_neq | reg_neq | reg_neq | reg_neq]. }
    assert (HD4s11 : D4 !!! Regidx (mword_of_int 27 : mword 5) = (mword_of_int 112 : mword 64)).
    { rewrite (HD4k (mword_of_int 27 : mword 5)); [exact Hs11 | reg_neq | reg_neq | reg_neq | reg_neq | reg_neq]. }
    assert (Hp2a8 : add_vec_int (mword_of_int (KernelSyms.printk + 0x2a6) : mword 64) 2 = mword_of_int (KernelSyms.printk + 0x2a8)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp2a8) in "Hpc".
    (* +0x2a8 j 0x2ca : straight past the "ll" tests *)
    iApply (wp_cj_s_sconf (mword_of_int (KernelSyms.printk + 0x2a8)) (sign_extend' 21 (concat_vec (mword_of_int 17 : mword 11) ('b"0")))
              D4 (K - 24)%nat b ltac:(vm_compute; reflexivity)
              with "Hcg Hpc [] [-]").
    { iApply (pki_2a8 with "Htext"). }
    iIntros (CID7 Hst7). iNext. iIntros "Hcg Hpc".
    assert (Ht : add_vec (mword_of_int (KernelSyms.printk + 0x2a8) : mword 64) (sign_extend' 64 (sign_extend' 21 (concat_vec (mword_of_int 17 : mword 11) ('b"0")))) = mword_of_int (KernelSyms.printk + 0x2ca)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Ht) in "Hpc".
    iApply (wp_printk_chain_2ca D4 K c0 c1 c2 Rest b pcur Hd0
              ltac:(rewrite Hn1; repeat rewrite andb_false_r; reflexivity)
              ltac:(rewrite Hn1; repeat rewrite andb_false_r; reflexivity)
              HD4s5 HD4s8 HD4s10 HD4s11 HD4a2 HD4a3 HD4a4 HD4a5
              with "Hcg Htext Hpc HR [-]").
    iIntros (CID8 Hst8 mf) "%Hk Hcg Hpc HR".
    iSpecialize ("Hcont" $! CID8 with "[%]"); [wp_next_chain|].
    iApply ("Hcont" $! mf with "[%] Hcg Hpc HR").
    exact (pk_chain_kept_trans mf D4 mq Hk HD4k).
  Qed.

  (* ---- 0xec .. 0xf4: the join both "not this arm" exits take.  It is the
     only segment that reads memory -- the THIRD character, at 0xf0, through
     the [&f[i+1]] recomputed from a5.  A separate lemma rather than an
     [iAssert] inside 0xa4's proof: the later [case_eq]s abstract their
     scrutinee throughout the GOAL, and an iris hypothesis lives in the goal,
     so an [iAssert] stated before them comes out specialised. ---- *)
  Lemma wp_printk_chain_ec `{CID0 : CpuId}
      (mq : regfile) (K : nat) (fmt : mword 64) (dqf : dfrac) (f : string) (i : nat)
      (c0 c1 c2 : Ascii.ascii) (Rest : iProp Σ) (b : bool) (pcur : mword 64) :
    (S (S (S i)) < length (cstring_bytes f))%nat ->
    (Z.of_nat i + 1 < 2^31) ->
    c2 = pk_ch f (S (S (S i))) ->
    Ascii.eqb c0 "d"%char = false ->
    (Ascii.eqb c0 "l"%char && Ascii.eqb c1 "d"%char)%bool = false ->
    mq !!! Regidx (mword_of_int 21 : mword 5) = zero_extend' 64 (pk_byte c0) ->
    mq !!! Regidx (mword_of_int 13 : mword 5) = zero_extend' 64 (pk_byte c1) ->
    mq !!! Regidx (mword_of_int 14 : mword 5) = pk_bit (Ascii.eqb c0 "l"%char) ->
    mq !!! Regidx a5_idx = mword_of_int (Z.of_nat (S i)) ->
    mq !!! Regidx s2_idx = fmt ->
    mq !!! Regidx (mword_of_int 24 : mword 5) = (mword_of_int 117 : mword 64) ->
    mq !!! Regidx (mword_of_int 26 : mword 5) = (mword_of_int 120 : mword 64) ->
    mq !!! Regidx (mword_of_int 27 : mword 5) = (mword_of_int 112 : mword 64) ->
    sie_cap_gpr mq (K - 24)%nat b pcur -∗
    kernel_text -∗
    pc_is (mword_of_int (KernelSyms.printk + 0xec) : mword 64) -∗
    fmt ↦ₛ{ dqf } f -∗ Rest -∗
    wp_next (CID0 := CID0) b pcur (fun (CID : CpuId) =>
      ∀ mf : regfile,
      ⌜ pk_chain_kept mf mq ⌝ -∗
      sie_cap_gpr mf (K - 24)%nat b pcur -∗
      pc_is (mword_of_int (KernelSyms.printk + pk_entry c0 c1 c2) : mword 64) -∗
      fmt ↦ₛ{ dqf } f -∗ Rest -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hlen Hi31 Hc2 E1 E2 Hmqs5 Hmqa3 Hmqa4 Hmqa5 Hmqs2 Hmqs8 Hmqs10 Hmqs11.
    iIntros "Hcg #Htext Hpc Hfmt HR Hout".

    (* +0xec add a5,a5,s2 : &f[i+1] again *)
    iApply (wp_cadd_s_sconf (mword_of_int (KernelSyms.printk + 0xec)) a5_idx s2_idx mq (K - 24)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc [] [-]").
    { iApply (pki_ec with "Htext"). }
    iIntros (CID1 Hst1) "Hcg Hpc".
    iEval (rgne; rgne) in "Hcg".
    set (J1 := <[Regidx a5_idx := regval_into_reg
                   (add_vec (mq !!! Regidx a5_idx) (mq !!! Regidx s2_idx))]> mq).
    assert (HJ1a5 : J1 !!! Regidx a5_idx = pa_add fmt (S i)).
    { rewrite /J1 upd_eq. unfold regval_into_reg. rewrite Hmqa5 Hmqs2 add_vec_pa_add.
      f_equal.
      rewrite (uint_moi_small (Z.of_nat (S i))
                 ltac:(change (2^64) with 18446744073709551616; lia)).
      apply Nat2Z.id. }
    assert (HJ1a3 : J1 !!! Regidx (mword_of_int 13 : mword 5) = zero_extend' 64 (pk_byte c1))
      by (rewrite /J1 upd_ne; [exact Hmqa3 | reg_neq]).
    assert (Hpee : add_vec_int (mword_of_int (KernelSyms.printk + 0xec) : mword 64) 2 = mword_of_int (KernelSyms.printk + 0xee)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpee) in "Hpc".
    (* +0xee mv a2,a3 : c1 moves to where the tail chain reads it *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.printk + 0xee)) (mword_of_int 12 : mword 5)
              (mword_of_int 13 : mword 5) J1 (K - 24)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc [] [-]").
    { iApply (pki_ee with "Htext"). }
    iIntros (CID2 Hst2) "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (J2 := <[Regidx (mword_of_int 12 : mword 5) := regval_into_reg
                   (add_vec zero_reg (J1 !!! Regidx (mword_of_int 13 : mword 5)))]> J1).
    assert (HJ2a2 : J2 !!! Regidx (mword_of_int 12 : mword 5) = zero_extend' 64 (pk_byte c1)).
    { rewrite /J2 upd_eq. unfold regval_into_reg. rewrite HJ1a3. apply add_vec_zero_l. }
    assert (HJ2a5 : J2 !!! Regidx a5_idx = pa_add fmt (S i))
      by (rewrite /J2 upd_ne; [exact HJ1a5 | reg_neq]).
    assert (Hpf0 : add_vec_int (mword_of_int (KernelSyms.printk + 0xee) : mword 64) 2 = mword_of_int (KernelSyms.printk + 0xf0)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpf0) in "Hpc".
    (* +0xf0 lbu a3,2(a5) : the THIRD character *)
    iDestruct (pk_str_byte fmt dqf f (S (S (S i))) Hlen with "Hfmt") as "[Hb2 Hcl2]".
    assert (Hla2 : add_vec (rget J2 a5_idx) (sign_extend' 64 (mword_of_int 2 : mword 12))
                   = pa_add fmt (S (S (S i)))).
    { rgne. rewrite HJ2a5.
      replace (sign_extend' 64 (mword_of_int 2 : mword 12)) with (mword_of_int 2 : mword 64)
        by (apply bv_eq; vm_compute; reflexivity).
      change (add_vec (pa_add fmt (S i)) (mword_of_int 2 : mword 64))
        with (pa_add (pa_add fmt (S i)) 2).
      rewrite pa_add_add. f_equal. lia. }
    iEval (rewrite -Hla2) in "Hb2".
    iApply (wp_lbu_s_sconf (mword_of_int (KernelSyms.printk + 0xf0)) (mword_of_int 13 : mword 5)
              a5_idx (mword_of_int 2 : mword 12) J2 (K - 24)%nat (pk_fbyte f (S (S (S i)))) b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc [] Hb2 [-]").
    { iApply (pki_f0 with "Htext"). }
    iIntros (CID3 Hst3) "Hcg Hpc Hb2". iEval (rewrite Hla2) in "Hb2".
    iDestruct ("Hcl2" with "Hb2") as "Hfmt".
    set (J3 := <[Regidx (mword_of_int 13 : mword 5) := regval_into_reg (zero_extend' 64 (pk_fbyte f (S (S (S i)))))]> J2).
    assert (HJ3a3 : J3 !!! Regidx (mword_of_int 13 : mword 5) = zero_extend' 64 (pk_byte c2)).
    { rewrite /J3 upd_eq. unfold regval_into_reg. rewrite Hc2.
      rewrite pk_fbyte_ch; [reflexivity | ].
      rewrite cstring_bytes_length in Hlen. lia. }
    assert (HJ3a2 : J3 !!! Regidx (mword_of_int 12 : mword 5) = zero_extend' 64 (pk_byte c1))
      by (rewrite /J3 upd_ne; [exact HJ2a2 | reg_neq]).
    assert (HJ3k : pk_chain_kept J3 mq).
    { intros c N1 N2 N3 N4 N5.
      rewrite /J3 upd_ne; [| congruence]. rewrite /J2 upd_ne; [| congruence].
      rewrite /J1 upd_ne; [reflexivity | congruence]. }
    assert (HJ3a4 : J3 !!! Regidx (mword_of_int 14 : mword 5) = pk_bit (Ascii.eqb c0 "l"%char)).
    { rewrite /J3 upd_ne; [| reg_neq]. rewrite /J2 upd_ne; [| reg_neq].
      rewrite /J1 upd_ne; [exact Hmqa4 | reg_neq]. }
    assert (HJ3s5 : J3 !!! Regidx (mword_of_int 21 : mword 5) = zero_extend' 64 (pk_byte c0)).
    { rewrite (HJ3k (mword_of_int 21 : mword 5)); [exact Hmqs5 | reg_neq | reg_neq | reg_neq | reg_neq | reg_neq]. }
    assert (HJ3s8 : J3 !!! Regidx (mword_of_int 24 : mword 5) = (mword_of_int 117 : mword 64)).
    { rewrite (HJ3k (mword_of_int 24 : mword 5)); [exact Hmqs8 | reg_neq | reg_neq | reg_neq | reg_neq | reg_neq]. }
    assert (HJ3s10 : J3 !!! Regidx (mword_of_int 26 : mword 5) = (mword_of_int 120 : mword 64)).
    { rewrite (HJ3k (mword_of_int 26 : mword 5)); [exact Hmqs10 | reg_neq | reg_neq | reg_neq | reg_neq | reg_neq]. }
    assert (HJ3s11 : J3 !!! Regidx (mword_of_int 27 : mword 5) = (mword_of_int 112 : mword 64)).
    { rewrite (HJ3k (mword_of_int 27 : mword 5)); [exact Hmqs11 | reg_neq | reg_neq | reg_neq | reg_neq | reg_neq]. }
    assert (Hpf4 : add_vec_int (mword_of_int (KernelSyms.printk + 0xf0) : mword 64) 4 = mword_of_int (KernelSyms.printk + 0xf4)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpf4) in "Hpc".
    iApply (wp_cj_s_sconf (mword_of_int (KernelSyms.printk + 0xf4)) (sign_extend' 21 (concat_vec (mword_of_int 225 : mword 11) ('b"0")))
              J3 (K - 24)%nat b ltac:(vm_compute; reflexivity)
              with "Hcg Hpc [] [-]").
    { iApply (pki_f4 with "Htext"). }
    iIntros (CID4 Hst4). iNext. iIntros "Hcg Hpc".
    assert (Ht : add_vec (mword_of_int (KernelSyms.printk + 0xf4) : mword 64) (sign_extend' 64 (sign_extend' 21 (concat_vec (mword_of_int 225 : mword 11) ('b"0")))) = mword_of_int (KernelSyms.printk + 0x2b6)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Ht) in "Hpc".
    iApply (wp_printk_chain_2b6 J3 K c0 c1 c2 (fmt ↦ₛ{ dqf } f ∗ Rest)%I b pcur E1 E2
              HJ3s5 HJ3s8 HJ3s10 HJ3s11 HJ3a2 HJ3a3 HJ3a4
              with "Hcg Htext Hpc [$Hfmt $HR] [-]").
    iIntros (CID5 Hst5 mf) "%Hkk Hcg Hpc (Hfmt & HR)".
    iSpecialize ("Hout" $! CID5 with "[%]"); [wp_next_chain|].
    iApply ("Hout" $! mf with "[%] Hcg Hpc Hfmt HR").
    exact (pk_chain_kept_trans mf J3 mq Hkk HJ3k).
  Qed.


  (* ---- 0xa4 .. 0xb6, and the 0xec join: the full-lookahead entry.  This is
     the only segment that reads memory -- the THIRD character, at 0xf0,
     through the [&f[i+1]] the head left in a5. ---- *)
  Lemma wp_printk_chain_a4 `{CID0 : CpuId}
      (mq : regfile) (K : nat) (fmt : mword 64) (dqf : dfrac) (f : string) (i : nat)
      (c0 c1 c2 : Ascii.ascii) (Rest : iProp Σ) (b : bool) (pcur : mword 64) :
    (S (S (S i)) < length (cstring_bytes f))%nat ->
    (Z.of_nat i + 1 < 2^31) ->
    c2 = pk_ch f (S (S (S i))) ->
    mq !!! Regidx (mword_of_int 21 : mword 5) = zero_extend' 64 (pk_byte c0) ->
    mq !!! Regidx (mword_of_int 13 : mword 5) = zero_extend' 64 (pk_byte c1) ->
    mq !!! Regidx a5_idx = mword_of_int (Z.of_nat (S i)) ->
    mq !!! Regidx s2_idx = fmt ->
    mq !!! Regidx (mword_of_int 23 : mword 5) = (mword_of_int 100 : mword 64) ->
    mq !!! Regidx (mword_of_int 24 : mword 5) = (mword_of_int 117 : mword 64) ->
    mq !!! Regidx (mword_of_int 26 : mword 5) = (mword_of_int 120 : mword 64) ->
    mq !!! Regidx (mword_of_int 27 : mword 5) = (mword_of_int 112 : mword 64) ->
    sie_cap_gpr mq (K - 24)%nat b pcur -∗
    kernel_text -∗
    pc_is (mword_of_int (KernelSyms.printk + 0xa4) : mword 64) -∗
    fmt ↦ₛ{ dqf } f -∗
    Rest -∗
    wp_next (CID0 := CID0) b pcur (fun (CID : CpuId) =>
      ∀ mf : regfile,
      ⌜ pk_chain_kept mf mq ⌝ -∗
      sie_cap_gpr mf (K - 24)%nat b pcur -∗
      pc_is (mword_of_int (KernelSyms.printk + pk_entry c0 c1 c2) : mword 64) -∗
      fmt ↦ₛ{ dqf } f -∗ Rest -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hlen Hi31 Hc2 Hs5 Ha3 Ha5 Hs2 Hs7 Hs8 Hs10 Hs11.
    iIntros "Hcg #Htext Hpc Hfmt HR Hcont".
    assert (Hid : pk_chain_kept mq mq) by (intros c ????; reflexivity).
    (* +0xa4 beq s5,s7 : '%d' *)
    case_eq (Ascii.eqb c0 "d"%char); intro Hd0.
    { iApply (wp_beq_taken_s_sconf (mword_of_int (KernelSyms.printk + 0xa4)) (mword_of_int 48 : mword 13)
                (mword_of_int 23 : mword 5) (mword_of_int 21 : mword 5) mq (K - 24)%nat b
                ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                ltac:(rgne; rgne; rewrite Hs5 Hs7 (pk_eq_ascii c0 "d"%char (mword_of_int 100)
                        ltac:(apply bv_eq; vm_compute; reflexivity)); exact Hd0)
                ltac:(vm_compute; reflexivity)
                with "Hcg Hpc [] [-]").
      { iApply (pki_a4 with "Htext"). }
      iIntros (CID1 Hst1). iNext. iIntros "Hcg Hpc".
      assert (Ht : add_vec (mword_of_int (KernelSyms.printk + 0xa4) : mword 64) (sign_extend' 64 (mword_of_int 48 : mword 13)) = mword_of_int (KernelSyms.printk + pk_entry c0 c1 c2)).
      { unfold pk_entry. rewrite Hd0. apply bv_eq; vm_compute; reflexivity. }
      iEval (rewrite Ht) in "Hpc".
      iSpecialize ("Hcont" $! CID1 with "[%]"); [wp_next_chain|].
      iApply ("Hcont" $! mq with "[%] Hcg Hpc Hfmt HR"). exact Hid. }
    iApply (wp_beq_fall_s_sconf (mword_of_int (KernelSyms.printk + 0xa4)) (mword_of_int 48 : mword 13)
              (mword_of_int 23 : mword 5) (mword_of_int 21 : mword 5) mq (K - 24)%nat b
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              ltac:(rgne; rgne; rewrite Hs5 Hs7 (pk_eq_ascii c0 "d"%char (mword_of_int 100)
                      ltac:(apply bv_eq; vm_compute; reflexivity)); exact Hd0)
              with "Hcg Hpc [] [-]").
    { iApply (pki_a4 with "Htext"). }
    iIntros (CID2 Hst2) "Hcg Hpc".
    assert (Hpa8 : add_vec_int (mword_of_int (KernelSyms.printk + 0xa4) : mword 64) 4 = mword_of_int (KernelSyms.printk + 0xa8)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpa8) in "Hpc".
    (* +0xa8 addi a4,s5,-108 ; +0xac seqz a4,a4 : c0 == 'l'.  This overwrites
       the [&f[i+1]] the head left in a4 -- 0xec recomputes it from a5. *)
    iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.printk + 0xa8)) (mword_of_int 14 : mword 5)
              (mword_of_int 21 : mword 5) (mword_of_int 3988 : mword 12) mq (K - 24)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc [] [-]").
    { iApply (pki_a8 with "Htext"). }
    iIntros (CID3 Hst3) "Hcg Hpc".
    set (D1 := <[Regidx (mword_of_int 14 : mword 5) := regval_into_reg
                   (add_vec (mq !!! Regidx (mword_of_int 21 : mword 5))
                      (sign_extend' 64 (mword_of_int 3988 : mword 12)))]> mq).
    assert (HD1a4 : eq_vec (D1 !!! Regidx (mword_of_int 14 : mword 5)) (zero_reg : mword 64)
                    = Ascii.eqb c0 "l"%char).
    { rewrite /D1 upd_eq. unfold regval_into_reg. rewrite Hs5.
      apply (pk_sub_ascii c0 "l"%char). apply bv_eq; vm_compute; reflexivity. }
    assert (Hpac : add_vec_int (mword_of_int (KernelSyms.printk + 0xa8) : mword 64) 4 = mword_of_int (KernelSyms.printk + 0xac)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpac) in "Hpc".
    iApply (wp_sltiu_s_sconf (mword_of_int (KernelSyms.printk + 0xac)) (mword_of_int 14 : mword 5)
              (mword_of_int 14 : mword 5) (mword_of_int 1 : mword 12)
              (pk_bit (Ascii.eqb c0 "l"%char)) D1 (K - 24)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(rgne; rewrite /pk_bit (ltu1_eqz (D1 !!! Regidx (mword_of_int 14 : mword 5))
                      (sign_extend' 64 (mword_of_int 1 : mword 12))
                      ltac:(apply bv_eq; vm_compute; reflexivity)) HD1a4; reflexivity)
              with "Hcg Hpc [] [-]").
    { iApply (pki_ac with "Htext"). }
    iIntros (CID4 Hst4) "Hcg Hpc".
    set (D2 := <[Regidx (mword_of_int 14 : mword 5) := regval_into_reg (pk_bit (Ascii.eqb c0 "l"%char))]> D1).
    assert (HD2a4 : D2 !!! Regidx (mword_of_int 14 : mword 5) = pk_bit (Ascii.eqb c0 "l"%char))
      by (rewrite /D2 upd_eq; reflexivity).
    assert (HD2a3 : D2 !!! Regidx (mword_of_int 13 : mword 5) = zero_extend' 64 (pk_byte c1)).
    { rewrite /D2 upd_ne; [| reg_neq]. rewrite /D1 upd_ne; [exact Ha3 | reg_neq]. }
    assert (Hpb0 : add_vec_int (mword_of_int (KernelSyms.printk + 0xac) : mword 64) 4 = mword_of_int (KernelSyms.printk + 0xb0)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpb0) in "Hpc".
    (* +0xb0 addi a2,a3,-100 : c1 == 'd' *)
    iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.printk + 0xb0)) (mword_of_int 12 : mword 5)
              (mword_of_int 13 : mword 5) (mword_of_int 3996 : mword 12) D2 (K - 24)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc [] [-]").
    { iApply (pki_b0 with "Htext"). }
    iIntros (CID5 Hst5) "Hcg Hpc".
    set (D3 := <[Regidx (mword_of_int 12 : mword 5) := regval_into_reg
                   (add_vec (D2 !!! Regidx (mword_of_int 13 : mword 5))
                      (sign_extend' 64 (mword_of_int 3996 : mword 12)))]> D2).
    assert (HD3a2 : eq_vec (D3 !!! Regidx (mword_of_int 12 : mword 5)) (zero_reg : mword 64)
                    = Ascii.eqb c1 "d"%char).
    { rewrite /D3 upd_eq. unfold regval_into_reg. rewrite HD2a3.
      apply (pk_sub_ascii c1 "d"%char). apply bv_eq; vm_compute; reflexivity. }
    assert (HD3a4 : D3 !!! Regidx (mword_of_int 14 : mword 5) = pk_bit (Ascii.eqb c0 "l"%char))
      by (rewrite /D3 upd_ne; [exact HD2a4 | reg_neq]).
    assert (HD3k : pk_chain_kept D3 mq).
    { intros c N1 N2 N3 N4 N5.
      rewrite /D3 upd_ne; [| congruence]. rewrite /D2 upd_ne; [| congruence].
      rewrite /D1 upd_ne; [reflexivity | congruence]. }
    assert (HD3a3 : D3 !!! Regidx (mword_of_int 13 : mword 5) = zero_extend' 64 (pk_byte c1))
      by (rewrite /D3 upd_ne; [exact HD2a3 | reg_neq]).
    assert (HD3a5 : D3 !!! Regidx a5_idx = mword_of_int (Z.of_nat (S i))).
    { rewrite /D3 upd_ne; [| reg_neq]. rewrite /D2 upd_ne; [| reg_neq].
      rewrite /D1 upd_ne; [exact Ha5 | reg_neq]. }
    assert (HD3s2 : D3 !!! Regidx s2_idx = fmt).
    { rewrite (HD3k s2_idx); [exact Hs2 | reg_neq | reg_neq | reg_neq | reg_neq | reg_neq]. }
    assert (HD3s5 : D3 !!! Regidx (mword_of_int 21 : mword 5) = zero_extend' 64 (pk_byte c0)).
    { rewrite (HD3k (mword_of_int 21 : mword 5)); [exact Hs5 | reg_neq | reg_neq | reg_neq | reg_neq | reg_neq]. }
    assert (HD3s8 : D3 !!! Regidx (mword_of_int 24 : mword 5) = (mword_of_int 117 : mword 64)).
    { rewrite (HD3k (mword_of_int 24 : mword 5)); [exact Hs8 | reg_neq | reg_neq | reg_neq | reg_neq | reg_neq]. }
    assert (HD3s10 : D3 !!! Regidx (mword_of_int 26 : mword 5) = (mword_of_int 120 : mword 64)).
    { rewrite (HD3k (mword_of_int 26 : mword 5)); [exact Hs10 | reg_neq | reg_neq | reg_neq | reg_neq | reg_neq]. }
    assert (HD3s11 : D3 !!! Regidx (mword_of_int 27 : mword 5) = (mword_of_int 112 : mword 64)).
    { rewrite (HD3k (mword_of_int 27 : mword 5)); [exact Hs11 | reg_neq | reg_neq | reg_neq | reg_neq | reg_neq]. }
    assert (Hpb4 : add_vec_int (mword_of_int (KernelSyms.printk + 0xb0) : mword 64) 4 = mword_of_int (KernelSyms.printk + 0xb4)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpb4) in "Hpc".
    (* +0xb4 bnez a2 : c1 is not 'd' *)
    case_eq (Ascii.eqb c1 "d"%char); intro Hd1.
    - iApply (wp_cbnez_fall_s_sconf (mword_of_int (KernelSyms.printk + 0xb4)) (mword_of_int 28 : mword 8)
                (Cregidx (mword_of_int 4)) (mword_of_int 12 : mword 5) D3 (K - 24)%nat b
                ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
                ltac:(rgne; unfold neq_vec; rewrite HD3a2 Hd1; reflexivity)
                with "Hcg Hpc [] [-]").
      { iApply (pki_b4 with "Htext"). }
      iIntros (CID6 Hst6) "Hcg Hpc".
      assert (Hpb6 : add_vec_int (mword_of_int (KernelSyms.printk + 0xb4) : mword 64) 2 = mword_of_int (KernelSyms.printk + 0xb6)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpb6) in "Hpc".
      (* +0xb6 beqz a4 : and c0 is not 'l' either *)
      case_eq (Ascii.eqb c0 "l"%char); intro Hl0.
      + iApply (wp_cbeqz_fall_s_sconf (mword_of_int (KernelSyms.printk + 0xb6)) (mword_of_int 27 : mword 8)
                  (Cregidx (mword_of_int 6)) (mword_of_int 14 : mword 5) D3 (K - 24)%nat b
                  ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
                  ltac:(rgne; rewrite HD3a4 Hl0; vm_compute; reflexivity)
                  with "Hcg Hpc [] [-]").
        { iApply (pki_b6 with "Htext"). }
        iIntros (CID7 Hst7) "Hcg Hpc".
        assert (Ht : add_vec_int (mword_of_int (KernelSyms.printk + 0xb6) : mword 64) 2 = mword_of_int (KernelSyms.printk + pk_entry c0 c1 c2)).
        { unfold pk_entry. rewrite Hd0 Hl0 Hd1. apply bv_eq; vm_compute; reflexivity. }
        iEval (rewrite Ht) in "Hpc".
        iSpecialize ("Hcont" $! CID7 with "[%]"); [wp_next_chain|].
        iApply ("Hcont" $! D3 with "[%] Hcg Hpc Hfmt HR"). exact HD3k.
      + iApply (wp_cbeqz_taken_s_sconf (mword_of_int (KernelSyms.printk + 0xb6)) (mword_of_int 27 : mword 8)
                  (Cregidx (mword_of_int 6)) (mword_of_int 14 : mword 5) D3 (K - 24)%nat b
                  ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
                  ltac:(rgne; rewrite HD3a4 Hl0; vm_compute; reflexivity)
                  ltac:(vm_compute; reflexivity)
                  with "Hcg Hpc [] [-]").
        { iApply (pki_b6 with "Htext"). }
        iIntros (CID8 Hst8). iNext. iIntros "Hcg Hpc".
        assert (Ht : add_vec (mword_of_int (KernelSyms.printk + 0xb6) : mword 64) (sign_extend' 64 (sign_extend' 13 (concat_vec (mword_of_int 27 : mword 8) ('b"0")))) = mword_of_int (KernelSyms.printk + 0xec)) by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Ht) in "Hpc".
        iApply (wp_printk_chain_ec D3 K fmt dqf f i c0 c1 c2 Rest b pcur Hlen Hi31 Hc2 Hd0
                  ltac:(rewrite Hl0; reflexivity)
                  HD3s5 HD3a3 HD3a4 HD3a5 HD3s2 HD3s8 HD3s10 HD3s11
                  with "Hcg Htext Hpc Hfmt HR [-]").
        iIntros (CID9 Hst9 mf) "%Hkk Hcg Hpc Hfmt HR".
        iSpecialize ("Hcont" $! CID9 with "[%]"); [wp_next_chain|].
        iApply ("Hcont" $! mf with "[%] Hcg Hpc Hfmt HR").
        exact (pk_chain_kept_trans mf D3 mq Hkk HD3k).
    - iApply (wp_cbnez_taken_s_sconf (mword_of_int (KernelSyms.printk + 0xb4)) (mword_of_int 28 : mword 8)
                (Cregidx (mword_of_int 4)) (mword_of_int 12 : mword 5) D3 (K - 24)%nat b
                ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
                ltac:(rgne; unfold neq_vec; rewrite HD3a2 Hd1; reflexivity)
                ltac:(vm_compute; reflexivity)
                with "Hcg Hpc [] [-]").
      { iApply (pki_b4 with "Htext"). }
      iIntros (CID10 Hst10). iNext. iIntros "Hcg Hpc".
      assert (Ht : add_vec (mword_of_int (KernelSyms.printk + 0xb4) : mword 64) (sign_extend' 64 (sign_extend' 13 (concat_vec (mword_of_int 28 : mword 8) ('b"0")))) = mword_of_int (KernelSyms.printk + 0xec)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Ht) in "Hpc".
      iApply (wp_printk_chain_ec D3 K fmt dqf f i c0 c1 c2 Rest b pcur Hlen Hi31 Hc2 Hd0
                ltac:(rewrite Hd1; repeat rewrite andb_false_r; reflexivity)
                HD3s5 HD3a3 HD3a4 HD3a5 HD3s2 HD3s8 HD3s10 HD3s11
                with "Hcg Htext Hpc Hfmt HR [-]").
      iIntros (CID11 Hst11 mf) "%Hkk Hcg Hpc Hfmt HR".
      iSpecialize ("Hcont" $! CID11 with "[%]"); [wp_next_chain|].
      iApply ("Hcont" $! mf with "[%] Hcg Hpc Hfmt HR").
      exact (pk_chain_kept_trans mf D3 mq Hkk HD3k).
  Qed.



  (* a nonzero byte inside the bound is a real character *)
  Lemma pk_fbyte_nz_lt (f : string) (j : nat) :
    (j < length (cstring_bytes f))%nat -> pk_fbyte f j <> (mword_of_int 0 : mword 8) ->
    (j < String.length f)%nat.
  Proof.
    intros Hj Hnz. rewrite cstring_bytes_length in Hj.
    destruct (Nat.eq_dec j (String.length f)) as [He | He]; [ | lia ].
    exfalso. apply Hnz. rewrite He -(string_bytes_length f). apply pk_fbyte_nul.
  Qed.

  Lemma zext_pk_byte_nul : (zero_extend' 64 (pk_byte pk_nul) : mword 64) = zero_reg.
  Proof. apply bv_eq; vm_compute; reflexivity. Qed.

  (* the whole dispatch, 0x8a to whichever arm the directive selects.  The
     three shapes [pk_kinds] distinguishes are exactly the head's three exits,
     and all three end in the same statement because [pk_ch] already returns
     the NUL past the end of the string. *)
  Definition pk_disp_all (mf mc : regfile) : Prop :=
    forall c : mword 5, c <> mword_of_int 9 -> c <> mword_of_int 11 ->
      c <> mword_of_int 12 -> c <> mword_of_int 13 -> c <> mword_of_int 14 ->
      c <> mword_of_int 15 -> c <> mword_of_int 21 ->
      mf !!! Regidx c = mc !!! Regidx c.

  Lemma wp_printk_dispatch `{CID0 : CpuId}
      (mc : regfile) (K : nat) (fmt : mword 64) (dqf : dfrac) (f : string) (i : nat)
      (Rest : iProp Σ) (b : bool) (pcur : mword 64) :
    (S i < length (cstring_bytes f))%nat ->
    (Z.of_nat i + 1 < 2^31) ->
    nonul f = true ->
    mc !!! Regidx (mword_of_int 20 : mword 5) = mword_of_int (Z.of_nat i) ->
    mc !!! Regidx s2_idx = fmt ->
    pk_consts mc ->
    sie_cap_gpr mc (K - 24)%nat b pcur -∗
    kernel_text -∗
    pc_is (mword_of_int (KernelSyms.printk + 0x8a) : mword 64) -∗
    fmt ↦ₛ{ dqf } f -∗
    Rest -∗
    wp_next (CID0 := CID0) b pcur (fun (CID : CpuId) =>
      ∀ mf : regfile,
      ⌜ pk_disp_all mf mc
        /\ mf !!! Regidx (mword_of_int 9 : mword 5) = mword_of_int (Z.of_nat (S i)) ⌝ -∗
      sie_cap_gpr mf (K - 24)%nat b pcur -∗
      pc_is (mword_of_int (KernelSyms.printk + pk_entry (pk_ch f (S i)) (pk_ch f (S (S i)))
                                         (pk_ch f (S (S (S i))))) : mword 64) -∗
      fmt ↦ₛ{ dqf } f -∗ Rest -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hlen Hi31 Hnn Hs4 Hs2 Hconsts.
    destruct Hconsts as (Hs3 & Hs6 & Hs7 & Hs8 & Hs10 & Hs11).
    iIntros "Hcg #Htext Hpc Hfmt HR Hcont".
    (* [wp_printk_disp_head] has three continuations and only one copy of
       [Hcont] to give them, so decide which exit is live FIRST -- the other
       two are then discharged from their own pure premise. *)
    destruct (decide (pk_fbyte f (S i) = (mword_of_int 0 : mword 8))) as [Hz0 | Hnz0].
    { iApply (wp_printk_disp_head mc K fmt dqf f i Rest b pcur Hlen Hi31 Hs4 Hs2
                with "Hcg Htext Hpc Hfmt HR [-] [] []").
      2: { iIntros (CIDd1 Hstd1 mf) "%Hv Hcg Hpc Hfmt HR". exfalso.
           destruct Hv as (_ & _ & _ & _ & Hn & _). exact (Hn Hz0). }
      2: { iIntros (CIDd2 Hstd2 mf) "%Hv Hcg Hpc Hfmt HR". exfalso.
           destruct Hv as (_ & _ & _ & _ & _ & _ & Hn & _). exact (Hn Hz0). }
      (* (a) c0 = 0 -- the string ends right after the '%' *)
      iIntros (CIDd3 Hstd3 mf) "%Hv Hcg Hpc Hfmt HR".
      destruct Hv as (Hkept & Hs1 & Hs5 & Hzz).
      assert (Hend : S i = String.length f)
        by (apply (pk_fbyte_zero_end f (S i) Hnn); [ rewrite cstring_bytes_length in Hlen; lia | exact Hzz ]).
      assert (Hc0 : pk_ch f (S i) = pk_nul) by (apply pk_ch_nul; lia).
      assert (Hc1 : pk_ch f (S (S i)) = pk_nul) by (apply pk_ch_nul; lia).
      assert (Hc2 : pk_ch f (S (S (S i))) = pk_nul) by (apply pk_ch_nul; lia).
      iApply (wp_printk_chain_2aa mf K (pk_ch f (S i)) (pk_ch f (S (S i)))
                (pk_ch f (S (S (S i)))) (fmt ↦ₛ{ dqf } f ∗ Rest)%I b pcur Hc0 Hc1 Hc2
                ltac:(rewrite Hs5 Hc0 zext_pk_byte_nul; reflexivity)
                ltac:(rewrite (Hkept (mword_of_int 24 : mword 5)); [exact Hs8 | reg_neq | reg_neq | reg_neq | reg_neq | reg_neq])
                ltac:(rewrite (Hkept (mword_of_int 26 : mword 5)); [exact Hs10 | reg_neq | reg_neq | reg_neq | reg_neq | reg_neq])
                ltac:(rewrite (Hkept (mword_of_int 27 : mword 5)); [exact Hs11 | reg_neq | reg_neq | reg_neq | reg_neq | reg_neq])
                with "Hcg Htext Hpc [$Hfmt $HR] [-]").
      iIntros (CIDd4 Hstd4 mg) "%Hk Hcg Hpc (Hfmt & HR)".
      iSpecialize ("Hcont" $! CIDd4 with "[%]"); [wp_next_chain|].
      iApply ("Hcont" $! mg with "[%] Hcg Hpc Hfmt HR").
      split.
      + intros c N9 N11 N12 N13 N14 N15 N21.
        rewrite (Hk c N11 N12 N13 N14 N15). apply Hkept; assumption.
      + rewrite (Hk (mword_of_int 9 : mword 5)); [exact Hs1 | reg_neq | reg_neq | reg_neq | reg_neq | reg_neq]. }
    destruct (decide (pk_fbyte f (S (S i)) = (mword_of_int 0 : mword 8))) as [Hz1 | Hnz1].
    { iApply (wp_printk_disp_head mc K fmt dqf f i Rest b pcur Hlen Hi31 Hs4 Hs2
                with "Hcg Htext Hpc Hfmt HR [] [-] []").
      1: { iIntros (CIDd5 Hstd5 mf) "%Hv Hcg Hpc Hfmt HR". exfalso.
           destruct Hv as (_ & _ & _ & Hn). exact (Hnz0 Hn). }
      2: { iIntros (CIDd6 Hstd6 mf) "%Hv Hcg Hpc Hfmt HR". exfalso.
           destruct Hv as (_ & _ & _ & _ & _ & _ & _ & Hn). exact (Hn Hz1). }
      (* (b) c0 <> 0, c1 = 0 -- one character of directive and no more *)
      iIntros (CIDd7 Hstd7 mf) "%Hv Hcg Hpc Hfmt HR".
      destruct Hv as (Hkept & Hs1 & Hs5 & Ha3 & Hnzz & Hzz).
      assert (Hlt0 : (S i < String.length f)%nat) by (apply (pk_fbyte_nz_lt f (S i) Hlen Hnzz)).
      assert (Hend : S (S i) = String.length f)
        by (apply (pk_fbyte_zero_end f (S (S i)) Hnn); [ lia | exact Hzz ]).
      assert (Hc1 : pk_ch f (S (S i)) = pk_nul) by (apply pk_ch_nul; lia).
      assert (Hc2 : pk_ch f (S (S (S i))) = pk_nul) by (apply pk_ch_nul; lia).
      iApply (wp_printk_chain_298 mf K (pk_ch f (S i)) (pk_ch f (S (S i)))
                (pk_ch f (S (S (S i)))) (fmt ↦ₛ{ dqf } f ∗ Rest)%I b pcur Hc1 Hc2
                ltac:(rewrite Hs5 (pk_fbyte_ch f (S i) ltac:(lia)); reflexivity)
                ltac:(rewrite Ha3 Hc1 zext_pk_byte_nul; reflexivity)
                ltac:(rewrite (Hkept (mword_of_int 23 : mword 5)); [exact Hs7 | reg_neq | reg_neq | reg_neq | reg_neq | reg_neq])
                ltac:(rewrite (Hkept (mword_of_int 24 : mword 5)); [exact Hs8 | reg_neq | reg_neq | reg_neq | reg_neq | reg_neq])
                ltac:(rewrite (Hkept (mword_of_int 26 : mword 5)); [exact Hs10 | reg_neq | reg_neq | reg_neq | reg_neq | reg_neq])
                ltac:(rewrite (Hkept (mword_of_int 27 : mword 5)); [exact Hs11 | reg_neq | reg_neq | reg_neq | reg_neq | reg_neq])
                with "Hcg Htext Hpc [$Hfmt $HR] [-]").
      iIntros (CIDd8 Hstd8 mg) "%Hk Hcg Hpc (Hfmt & HR)".
      iSpecialize ("Hcont" $! CIDd8 with "[%]"); [wp_next_chain|].
      iApply ("Hcont" $! mg with "[%] Hcg Hpc Hfmt HR").
      split.
      + intros c N9 N11 N12 N13 N14 N15 N21.
        rewrite (Hk c N11 N12 N13 N14 N15). apply Hkept; assumption.
      + rewrite (Hk (mword_of_int 9 : mword 5)); [exact Hs1 | reg_neq | reg_neq | reg_neq | reg_neq | reg_neq]. }
    iApply (wp_printk_disp_head mc K fmt dqf f i Rest b pcur Hlen Hi31 Hs4 Hs2
              with "Hcg Htext Hpc Hfmt HR [] [] [-]").
    1: { iIntros (CIDd9 Hstd9 mf) "%Hv Hcg Hpc Hfmt HR". exfalso.
         destruct Hv as (_ & _ & _ & Hn). exact (Hnz0 Hn). }
    1: { iIntros (CIDd10 Hstd10 mf) "%Hv Hcg Hpc Hfmt HR". exfalso.
         destruct Hv as (_ & _ & _ & _ & _ & Hn). exact (Hnz1 Hn). }
    (* (c) all three characters are there *)
    iIntros (CIDd11 Hstd11 mf) "%Hv Hcg Hpc Hfmt HR".
    destruct Hv as (Hkept & Hs1 & Ha5 & Ha4 & Hs5 & Ha3 & Hnzz0 & Hnzz1).
    assert (Hlt1 : (S (S i) < String.length f)%nat).
    { apply (pk_fbyte_nz_lt f (S (S i))); [ | exact Hnzz1 ].
      rewrite cstring_bytes_length.
      assert (S i < String.length f)%nat by (apply (pk_fbyte_nz_lt f (S i) Hlen Hnzz0)).
      lia. }
    assert (Hlen3 : (S (S (S i)) < length (cstring_bytes f))%nat)
      by (rewrite cstring_bytes_length; lia).
    iApply (wp_printk_chain_a4 mf K fmt dqf f i (pk_ch f (S i)) (pk_ch f (S (S i)))
              (pk_ch f (S (S (S i)))) Rest b pcur Hlen3 Hi31 eq_refl
              ltac:(rewrite Hs5 (pk_fbyte_ch f (S i) ltac:(lia)); reflexivity)
              ltac:(rewrite Ha3 (pk_fbyte_ch f (S (S i)) ltac:(lia)); reflexivity)
              Ha5
              ltac:(rewrite (Hkept s2_idx); [exact Hs2 | reg_neq | reg_neq | reg_neq | reg_neq | reg_neq])
              ltac:(rewrite (Hkept (mword_of_int 23 : mword 5)); [exact Hs7 | reg_neq | reg_neq | reg_neq | reg_neq | reg_neq])
              ltac:(rewrite (Hkept (mword_of_int 24 : mword 5)); [exact Hs8 | reg_neq | reg_neq | reg_neq | reg_neq | reg_neq])
              ltac:(rewrite (Hkept (mword_of_int 26 : mword 5)); [exact Hs10 | reg_neq | reg_neq | reg_neq | reg_neq | reg_neq])
              ltac:(rewrite (Hkept (mword_of_int 27 : mword 5)); [exact Hs11 | reg_neq | reg_neq | reg_neq | reg_neq | reg_neq])
              with "Hcg Htext Hpc Hfmt HR [-]").
    iIntros (CIDd12 Hstd12 mg) "%Hk Hcg Hpc Hfmt HR".
    iSpecialize ("Hcont" $! CIDd12 with "[%]"); [wp_next_chain|].
    iApply ("Hcont" $! mg with "[%] Hcg Hpc Hfmt HR").
    split.
    + intros c N9 N11 N12 N13 N14 N15 N21.
      rewrite (Hk c N11 N12 N13 N14 N15). apply Hkept; assumption.
    + rewrite (Hk (mword_of_int 9 : mword 5)); [exact Hs1 | reg_neq | reg_neq | reg_neq | reg_neq | reg_neq].
  Qed.



  (* ================================================================== *)
  (*  FROM [pk_entry] TO THE ARM.                                        *)
  (*                                                                     *)
  (*  The chain says where the pc lands; this says what happens there.    *)
  (*  Three lemmas, split by what the directive CONSUMES, because that    *)
  (*  is what the loop has to account for: a number (eleven entries, no   *)
  (*  descriptor resource -- [PkANum]'s is [True]), a string (one entry,  *)
  (*  which needs the caller's [PkAStr]/[PkANull]), or nothing at all.    *)
  (* ================================================================== *)

  Lemma ascii_eqb_neq (c d e : Ascii.ascii) :
    Ascii.eqb c d = true -> Ascii.eqb d e = false -> Ascii.eqb c e = false.
  Proof. intros H1 H2. apply Ascii.eqb_eq in H1. subst c. exact H2. Qed.

  Lemma wp_printk_arm_num `{CID0 : CpuId} (γd : uart_names) (γv : disk_names)
      (m mc : regfile) (K : nat) (k i : nat) (l : list (bv 8)) (pv pkv : mword 32)
      (dqm dqm2 : dfrac) (c0 c1 c2 : Ascii.ascii) (Rest : iProp Σ) (b : bool) (pcur : mword 64) :
    let sp0 := m !!! Regidx csp_rs1 in
    let spd := add_vec sp0 (sign_extend' 64 (caddi16sp_imm (mword_of_int 52 : mword 6))) in
    let s0v := add_vec sp0 (sign_extend' 64 (mword_of_int (-64) : mword 12)) in
    (38 <= K)%nat ->
    (k < 7)%nat ->
    (Z.of_nat i + 3 < 2^31) ->
    eq_vec (sign_extend' 64 pv) zero_reg = false ->
    neq_vec (sign_extend' 64 pkv) zero_reg = false ->
    fst (pk_dir c0 c1 c2) = Some PkNum ->
    mc !!! Regidx csp_rs1 = spd ->
    mc !!! Regidx s0_idx = s0v ->
    mc !!! Regidx (mword_of_int 22 : mword 5) = (mword_of_int 10 : mword 64) ->
    mc !!! Regidx (mword_of_int 20 : mword 5) = mword_of_int (Z.of_nat i) ->
    mc !!! Regidx (mword_of_int 9 : mword 5) = mword_of_int (Z.of_nat i + 1) ->
    sie_cap_gpr mc (K - 24)%nat b pcur -∗
    kernel_text -∗ kernel_data -∗
    pc_is (mword_of_int (KernelSyms.printk + pk_entry c0 c1 c2) : mword 64) -∗
    (∃ w : mword 64, (pa_stk sp0 19) ↦₈ w) -∗
    (pa_stk sp0 23) ↦₈ (pk_ap s0v k) -∗
    pk_va sp0 m -∗
    (mword_of_int KernelSyms.panicking : mword 64) ↦₄{ dqm } pv -∗
    (mword_of_int KernelSyms.panicked : mword 64) ↦₄{ dqm2 } pkv -∗
    dev_inv γd γv -∗ uart_tx_own γd l -∗ uart_dlab_off γd -∗
    Rest -∗
    wp_next (CID0 := CID0) b pcur (fun (CID : CpuId) =>
      ∀ (mf : regfile) (bs : list (bv 8)),
      ⌜ (forall c : mword 5, is_cs_idx c = true -> c <> mword_of_int 9 ->
           c <> mword_of_int 20 -> c <> mword_of_int 21 ->
           mf !!! Regidx c = mc !!! Regidx c)
        /\ mf !!! Regidx (mword_of_int 9 : mword 5)
           = mword_of_int (Z.of_nat (S i + snd (pk_dir c0 c1 c2))) ⌝ -∗
      sie_cap_gpr mf (K - 24)%nat b pcur -∗
      pc_is (mword_of_int (KernelSyms.printk + 0x78) : mword 64) -∗
      (∃ w : mword 64, (pa_stk sp0 19) ↦₈ w) -∗
      (pa_stk sp0 23) ↦₈ (pk_ap s0v (S k)) -∗
      pk_va sp0 m -∗
      (mword_of_int KernelSyms.panicking : mword 64) ↦₄{ dqm } pv -∗
      (mword_of_int KernelSyms.panicked : mword 64) ↦₄{ dqm2 } pkv -∗
      uart_tx_own γd (l ++ bs) -∗ uart_sent γd (l ++ bs) -∗
      Rest -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros sp0 spd s0v HK Hk Hi31 Hpv Hpkv Hnum Hsp Hs0 Hs6 Hs4 Hs1.
    assert (HK30 : (30 <= K)%nat) by lia.
    iIntros "Hcg #Htext #Hkdata Hpc S19 Hap Hva Hpanicking Hpanicked #Hdev Htx #Hdlab HR Hcont".
    (* the case order is [pk_entry]'s own: d, l, then u, x, p, c *)
    case_eq (Ascii.eqb c0 "d"%char); intro Hd0.
    { assert (Hent : pk_entry c0 c1 c2 = 0xd4) by (unfold pk_entry; rewrite ?Hd0 ?Hu0 ?Hx0 ?Hp0 ?Hc0 ?Hs0c ?Hl0 ?Hd1 ?Hu1 ?Hx1 ?Hl1 ?Hd2 ?Hu2 ?Hx2; reflexivity).
      assert (Hsnd : snd (pk_dir c0 c1 c2) = 0%nat) by (unfold pk_dir; rewrite ?Hd0 ?Hu0 ?Hx0 ?Hp0 ?Hc0 ?Hs0c ?Hl0 ?Hd1 ?Hu1 ?Hx1 ?Hl1 ?Hd2 ?Hu2 ?Hx2; reflexivity).
      iEval (rewrite Hent) in "Hpc".
      iApply (wp_printk_arm_d γd γv m mc K k l pv pkv dqm dqm2
                ((∃ w : mword 64, (pa_stk sp0 19) ↦₈ w) ∗ Rest)%I b pcur HK Hk Hpv Hpkv Hs0 Hs6
                with "Hcg Htext Hkdata Hpc Hap Hva Hpanicking Hpanicked Hdev Htx Hdlab [$S19 $HR] [-]").
      iIntros (CIDn1 Hstn1 mf bs) "%Hcs Hcg Hpc Hap Hva Hpanicking Hpanicked Htx Hsent (S19 & HR)".
      iSpecialize ("Hcont" $! CIDn1 with "[%]"); [wp_next_chain|].
      iApply ("Hcont" $! mf bs with "[%] Hcg Hpc S19 Hap Hva Hpanicking Hpanicked Htx Hsent HR").
      rewrite Hsnd. split; [ intros c Hc _ _ _; apply Hcs; assumption | ].
      replace (Z.of_nat (S i + 0)) with (Z.of_nat i + 1) by lia.
      rewrite (Hcs (mword_of_int 9 : mword 5) ltac:(vm_compute; reflexivity)). exact Hs1. }
    case_eq (Ascii.eqb c0 "l"%char); intro Hl0.
    { (* the long forms: one more character, maybe two.  [pk_dir] tests c0
         against d,u,x,p,c,s BEFORE l, so those have to be ruled out here --
         the machine's order rules them out later. *)
      assert (Hu0 : Ascii.eqb c0 "u"%char = false)
        by (apply (ascii_eqb_neq c0 "l"%char "u"%char Hl0); vm_compute; reflexivity).
      assert (Hx0 : Ascii.eqb c0 "x"%char = false)
        by (apply (ascii_eqb_neq c0 "l"%char "x"%char Hl0); vm_compute; reflexivity).
      assert (Hp0 : Ascii.eqb c0 "p"%char = false)
        by (apply (ascii_eqb_neq c0 "l"%char "p"%char Hl0); vm_compute; reflexivity).
      assert (Hc0 : Ascii.eqb c0 "c"%char = false)
        by (apply (ascii_eqb_neq c0 "l"%char "c"%char Hl0); vm_compute; reflexivity).
      assert (Hs0c : Ascii.eqb c0 "s"%char = false)
        by (apply (ascii_eqb_neq c0 "l"%char "s"%char Hl0); vm_compute; reflexivity).
      case_eq (Ascii.eqb c1 "d"%char); intro Hd1.
      { assert (Hent : pk_entry c0 c1 c2 = 0xb8)
          by (unfold pk_entry; rewrite ?Hd0 ?Hu0 ?Hx0 ?Hp0 ?Hc0 ?Hs0c ?Hl0 ?Hd1 ?Hu1 ?Hx1 ?Hl1 ?Hd2 ?Hu2 ?Hx2; reflexivity).
        assert (Hsnd : snd (pk_dir c0 c1 c2) = 1%nat)
          by (unfold pk_dir; rewrite ?Hd0 ?Hu0 ?Hx0 ?Hp0 ?Hc0 ?Hs0c ?Hl0 ?Hd1 ?Hu1 ?Hx1 ?Hl1 ?Hd2 ?Hu2 ?Hx2; reflexivity).
        iEval (rewrite Hent) in "Hpc".
        iApply (wp_printk_arm_ld γd γv m mc K k i l pv pkv dqm dqm2
                  ((∃ w : mword 64, (pa_stk sp0 19) ↦₈ w) ∗ Rest)%I b pcur
                  HK Hk ltac:(lia) Hpv Hpkv Hs0 Hs6 Hs4
                  with "Hcg Htext Hkdata Hpc Hap Hva Hpanicking Hpanicked Hdev Htx Hdlab [$S19 $HR] [-]").
        iIntros (CIDn2 Hstn2 mf bs) "%Hcs Hcg Hpc Hap Hva Hpanicking Hpanicked Htx Hsent (S19 & HR)".
        iSpecialize ("Hcont" $! CIDn2 with "[%]"); [wp_next_chain|].
        iApply ("Hcont" $! mf bs with "[%] Hcg Hpc S19 Hap Hva Hpanicking Hpanicked Htx Hsent HR").
        rewrite Hsnd. split; [ intros c Hc N9 _ _; exact (proj1 Hcs c Hc N9) | ].
        replace (Z.of_nat (S i + 1)) with (Z.of_nat i + 2) by lia. exact (proj2 Hcs). }
      case_eq (Ascii.eqb c1 "l"%char); intro Hl1.
      { assert (Hu1 : Ascii.eqb c1 "u"%char = false)
          by (apply (ascii_eqb_neq c1 "l"%char "u"%char Hl1); vm_compute; reflexivity).
        assert (Hx1 : Ascii.eqb c1 "x"%char = false)
          by (apply (ascii_eqb_neq c1 "l"%char "x"%char Hl1); vm_compute; reflexivity).
        case_eq (Ascii.eqb c2 "d"%char); intro Hd2.
        { assert (Hent : pk_entry c0 c1 c2 = 0xf6)
            by (unfold pk_entry; rewrite ?Hd0 ?Hu0 ?Hx0 ?Hp0 ?Hc0 ?Hs0c ?Hl0 ?Hd1 ?Hu1 ?Hx1 ?Hl1 ?Hd2 ?Hu2 ?Hx2; reflexivity).
          assert (Hsnd : snd (pk_dir c0 c1 c2) = 2%nat)
            by (unfold pk_dir; rewrite ?Hd0 ?Hu0 ?Hx0 ?Hp0 ?Hc0 ?Hs0c ?Hl0 ?Hd1 ?Hu1 ?Hx1 ?Hl1 ?Hd2 ?Hu2 ?Hx2; reflexivity).
          iEval (rewrite Hent) in "Hpc".
          iApply (wp_printk_arm_lld γd γv m mc K k i l pv pkv dqm dqm2
                    ((∃ w : mword 64, (pa_stk sp0 19) ↦₈ w) ∗ Rest)%I b pcur
                    HK Hk ltac:(lia) Hpv Hpkv Hs0 Hs6 Hs4
                    with "Hcg Htext Hkdata Hpc Hap Hva Hpanicking Hpanicked Hdev Htx Hdlab [$S19 $HR] [-]").
          iIntros (CIDn3 Hstn3 mf bs) "%Hcs Hcg Hpc Hap Hva Hpanicking Hpanicked Htx Hsent (S19 & HR)".
          iSpecialize ("Hcont" $! CIDn3 with "[%]"); [wp_next_chain|].
          iApply ("Hcont" $! mf bs with "[%] Hcg Hpc S19 Hap Hva Hpanicking Hpanicked Htx Hsent HR").
          rewrite Hsnd. split; [ intros c Hc N9 _ _; exact (proj1 Hcs c Hc N9) | ].
          replace (Z.of_nat (S i + 2)) with (Z.of_nat i + 3) by lia. exact (proj2 Hcs). }
        case_eq (Ascii.eqb c2 "u"%char); intro Hu2.
        { assert (Hent : pk_entry c0 c1 c2 = 0x148)
            by (unfold pk_entry; rewrite ?Hd0 ?Hu0 ?Hx0 ?Hp0 ?Hc0 ?Hs0c ?Hl0 ?Hd1 ?Hu1 ?Hx1 ?Hl1 ?Hd2 ?Hu2 ?Hx2; reflexivity).
          assert (Hsnd : snd (pk_dir c0 c1 c2) = 2%nat)
            by (unfold pk_dir; rewrite ?Hd0 ?Hu0 ?Hx0 ?Hp0 ?Hc0 ?Hs0c ?Hl0 ?Hd1 ?Hu1 ?Hx1 ?Hl1 ?Hd2 ?Hu2 ?Hx2; reflexivity).
          iEval (rewrite Hent) in "Hpc".
          iApply (wp_printk_arm_llu γd γv m mc K k i l pv pkv dqm dqm2
                    ((∃ w : mword 64, (pa_stk sp0 19) ↦₈ w) ∗ Rest)%I b pcur
                    HK Hk ltac:(lia) Hpv Hpkv Hs0 Hs6 Hs4
                    with "Hcg Htext Hkdata Hpc Hap Hva Hpanicking Hpanicked Hdev Htx Hdlab [$S19 $HR] [-]").
          iIntros (CIDn4 Hstn4 mf bs) "%Hcs Hcg Hpc Hap Hva Hpanicking Hpanicked Htx Hsent (S19 & HR)".
          iSpecialize ("Hcont" $! CIDn4 with "[%]"); [wp_next_chain|].
          iApply ("Hcont" $! mf bs with "[%] Hcg Hpc S19 Hap Hva Hpanicking Hpanicked Htx Hsent HR").
          rewrite Hsnd. split; [ intros c Hc N9 _ _; exact (proj1 Hcs c Hc N9) | ].
          replace (Z.of_nat (S i + 2)) with (Z.of_nat i + 3) by lia. exact (proj2 Hcs). }
        case_eq (Ascii.eqb c2 "x"%char); intro Hx2.
        { assert (Hent : pk_entry c0 c1 c2 = 0x198)
            by (unfold pk_entry; rewrite ?Hd0 ?Hu0 ?Hx0 ?Hp0 ?Hc0 ?Hs0c ?Hl0 ?Hd1 ?Hu1 ?Hx1 ?Hl1 ?Hd2 ?Hu2 ?Hx2; reflexivity).
          assert (Hsnd : snd (pk_dir c0 c1 c2) = 2%nat)
            by (unfold pk_dir; rewrite ?Hd0 ?Hu0 ?Hx0 ?Hp0 ?Hc0 ?Hs0c ?Hl0 ?Hd1 ?Hu1 ?Hx1 ?Hl1 ?Hd2 ?Hu2 ?Hx2; reflexivity).
          iEval (rewrite Hent) in "Hpc".
          iApply (wp_printk_arm_llx γd γv m mc K k i l pv pkv dqm dqm2
                    ((∃ w : mword 64, (pa_stk sp0 19) ↦₈ w) ∗ Rest)%I b pcur
                    HK Hk ltac:(lia) Hpv Hpkv Hs0 Hs6 Hs4
                    with "Hcg Htext Hkdata Hpc Hap Hva Hpanicking Hpanicked Hdev Htx Hdlab [$S19 $HR] [-]").
          iIntros (CIDn5 Hstn5 mf bs) "%Hcs Hcg Hpc Hap Hva Hpanicking Hpanicked Htx Hsent (S19 & HR)".
          iSpecialize ("Hcont" $! CIDn5 with "[%]"); [wp_next_chain|].
          iApply ("Hcont" $! mf bs with "[%] Hcg Hpc S19 Hap Hva Hpanicking Hpanicked Htx Hsent HR").
          rewrite Hsnd. split; [ intros c Hc N9 _ _; exact (proj1 Hcs c Hc N9) | ].
          replace (Z.of_nat (S i + 2)) with (Z.of_nat i + 3) by lia. exact (proj2 Hcs). }
        (* "%ll" followed by none of d/u/x consumes nothing *)
        exfalso. unfold pk_dir in Hnum. rewrite ?Hd0 ?Hu0 ?Hx0 ?Hp0 ?Hc0 ?Hs0c ?Hl0 ?Hd1 ?Hu1 ?Hx1 ?Hl1 ?Hd2 ?Hu2 ?Hx2 in Hnum.
        cbn in Hnum. discriminate Hnum. }
      case_eq (Ascii.eqb c1 "u"%char); intro Hu1.
      { assert (Hent : pk_entry c0 c1 c2 = 0x12c)
          by (unfold pk_entry; rewrite ?Hd0 ?Hu0 ?Hx0 ?Hp0 ?Hc0 ?Hs0c ?Hl0 ?Hd1 ?Hu1 ?Hx1 ?Hl1 ?Hd2 ?Hu2 ?Hx2; reflexivity).
        assert (Hsnd : snd (pk_dir c0 c1 c2) = 1%nat)
          by (unfold pk_dir; rewrite ?Hd0 ?Hu0 ?Hx0 ?Hp0 ?Hc0 ?Hs0c ?Hl0 ?Hd1 ?Hu1 ?Hx1 ?Hl1 ?Hd2 ?Hu2 ?Hx2; reflexivity).
        iEval (rewrite Hent) in "Hpc".
        iApply (wp_printk_arm_lu γd γv m mc K k i l pv pkv dqm dqm2
                  ((∃ w : mword 64, (pa_stk sp0 19) ↦₈ w) ∗ Rest)%I b pcur
                  HK Hk ltac:(lia) Hpv Hpkv Hs0 Hs6 Hs4
                  with "Hcg Htext Hkdata Hpc Hap Hva Hpanicking Hpanicked Hdev Htx Hdlab [$S19 $HR] [-]").
        iIntros (CIDn6 Hstn6 mf bs) "%Hcs Hcg Hpc Hap Hva Hpanicking Hpanicked Htx Hsent (S19 & HR)".
        iSpecialize ("Hcont" $! CIDn6 with "[%]"); [wp_next_chain|].
        iApply ("Hcont" $! mf bs with "[%] Hcg Hpc S19 Hap Hva Hpanicking Hpanicked Htx Hsent HR").
        rewrite Hsnd. split; [ intros c Hc N9 _ _; exact (proj1 Hcs c Hc N9) | ].
        replace (Z.of_nat (S i + 1)) with (Z.of_nat i + 2) by lia. exact (proj2 Hcs). }
      case_eq (Ascii.eqb c1 "x"%char); intro Hx1.
      { assert (Hent : pk_entry c0 c1 c2 = 0x17e)
          by (unfold pk_entry; rewrite ?Hd0 ?Hu0 ?Hx0 ?Hp0 ?Hc0 ?Hs0c ?Hl0 ?Hd1 ?Hu1 ?Hx1 ?Hl1 ?Hd2 ?Hu2 ?Hx2; reflexivity).
        assert (Hsnd : snd (pk_dir c0 c1 c2) = 1%nat)
          by (unfold pk_dir; rewrite ?Hd0 ?Hu0 ?Hx0 ?Hp0 ?Hc0 ?Hs0c ?Hl0 ?Hd1 ?Hu1 ?Hx1 ?Hl1 ?Hd2 ?Hu2 ?Hx2; reflexivity).
        iEval (rewrite Hent) in "Hpc".
        iApply (wp_printk_arm_lx γd γv m mc K k i l pv pkv dqm dqm2
                  ((∃ w : mword 64, (pa_stk sp0 19) ↦₈ w) ∗ Rest)%I b pcur
                  HK Hk ltac:(lia) Hpv Hpkv Hs0 Hs6 Hs4
                  with "Hcg Htext Hkdata Hpc Hap Hva Hpanicking Hpanicked Hdev Htx Hdlab [$S19 $HR] [-]").
        iIntros (CIDn7 Hstn7 mf bs) "%Hcs Hcg Hpc Hap Hva Hpanicking Hpanicked Htx Hsent (S19 & HR)".
        iSpecialize ("Hcont" $! CIDn7 with "[%]"); [wp_next_chain|].
        iApply ("Hcont" $! mf bs with "[%] Hcg Hpc S19 Hap Hva Hpanicking Hpanicked Htx Hsent HR").
        rewrite Hsnd. split; [ intros c Hc N9 _ _; exact (proj1 Hcs c Hc N9) | ].
        replace (Z.of_nat (S i + 1)) with (Z.of_nat i + 2) by lia. exact (proj2 Hcs). }
      exfalso. unfold pk_dir in Hnum. rewrite ?Hd0 ?Hu0 ?Hx0 ?Hp0 ?Hc0 ?Hs0c ?Hl0 ?Hd1 ?Hu1 ?Hx1 ?Hl1 ?Hd2 ?Hu2 ?Hx2 in Hnum.
      cbn in Hnum. discriminate Hnum. }
    (* the single-character forms *)
    case_eq (Ascii.eqb c0 "u"%char); intro Hu0.
    { assert (Hent : pk_entry c0 c1 c2 = 0x112)
        by (unfold pk_entry; rewrite ?Hd0 ?Hu0 ?Hx0 ?Hp0 ?Hc0 ?Hs0c ?Hl0 ?Hd1 ?Hu1 ?Hx1 ?Hl1 ?Hd2 ?Hu2 ?Hx2; reflexivity).
      assert (Hsnd : snd (pk_dir c0 c1 c2) = 0%nat)
        by (unfold pk_dir; rewrite ?Hd0 ?Hu0 ?Hx0 ?Hp0 ?Hc0 ?Hs0c ?Hl0 ?Hd1 ?Hu1 ?Hx1 ?Hl1 ?Hd2 ?Hu2 ?Hx2; reflexivity).
      iEval (rewrite Hent) in "Hpc".
      iApply (wp_printk_arm_u γd γv m mc K k l pv pkv dqm dqm2
                ((∃ w : mword 64, (pa_stk sp0 19) ↦₈ w) ∗ Rest)%I b pcur HK Hk Hpv Hpkv Hs0 Hs6
                with "Hcg Htext Hkdata Hpc Hap Hva Hpanicking Hpanicked Hdev Htx Hdlab [$S19 $HR] [-]").
      iIntros (CIDn8 Hstn8 mf bs) "%Hcs Hcg Hpc Hap Hva Hpanicking Hpanicked Htx Hsent (S19 & HR)".
      iSpecialize ("Hcont" $! CIDn8 with "[%]"); [wp_next_chain|].
      iApply ("Hcont" $! mf bs with "[%] Hcg Hpc S19 Hap Hva Hpanicking Hpanicked Htx Hsent HR").
      rewrite Hsnd. split; [ intros c Hc _ _ _; apply Hcs; assumption | ].
      replace (Z.of_nat (S i + 0)) with (Z.of_nat i + 1) by lia.
      rewrite (Hcs (mword_of_int 9 : mword 5) ltac:(vm_compute; reflexivity)). exact Hs1. }
    case_eq (Ascii.eqb c0 "x"%char); intro Hx0.
    { assert (Hent : pk_entry c0 c1 c2 = 0x164)
        by (unfold pk_entry; rewrite ?Hd0 ?Hu0 ?Hx0 ?Hp0 ?Hc0 ?Hs0c ?Hl0 ?Hd1 ?Hu1 ?Hx1 ?Hl1 ?Hd2 ?Hu2 ?Hx2; reflexivity).
      assert (Hsnd : snd (pk_dir c0 c1 c2) = 0%nat)
        by (unfold pk_dir; rewrite ?Hd0 ?Hu0 ?Hx0 ?Hp0 ?Hc0 ?Hs0c ?Hl0 ?Hd1 ?Hu1 ?Hx1 ?Hl1 ?Hd2 ?Hu2 ?Hx2; reflexivity).
      iEval (rewrite Hent) in "Hpc".
      iApply (wp_printk_arm_x γd γv m mc K k l pv pkv dqm dqm2
                ((∃ w : mword 64, (pa_stk sp0 19) ↦₈ w) ∗ Rest)%I b pcur HK Hk Hpv Hpkv Hs0 Hs6
                with "Hcg Htext Hkdata Hpc Hap Hva Hpanicking Hpanicked Hdev Htx Hdlab [$S19 $HR] [-]").
      iIntros (CIDn9 Hstn9 mf bs) "%Hcs Hcg Hpc Hap Hva Hpanicking Hpanicked Htx Hsent (S19 & HR)".
      iSpecialize ("Hcont" $! CIDn9 with "[%]"); [wp_next_chain|].
      iApply ("Hcont" $! mf bs with "[%] Hcg Hpc S19 Hap Hva Hpanicking Hpanicked Htx Hsent HR").
      rewrite Hsnd. split; [ intros c Hc _ _ _; apply Hcs; assumption | ].
      replace (Z.of_nat (S i + 0)) with (Z.of_nat i + 1) by lia.
      rewrite (Hcs (mword_of_int 9 : mword 5) ltac:(vm_compute; reflexivity)). exact Hs1. }
    case_eq (Ascii.eqb c0 "p"%char); intro Hp0.
    { assert (Hent : pk_entry c0 c1 c2 = 0x1b4)
        by (unfold pk_entry; rewrite ?Hd0 ?Hu0 ?Hx0 ?Hp0 ?Hc0 ?Hs0c ?Hl0 ?Hd1 ?Hu1 ?Hx1 ?Hl1 ?Hd2 ?Hu2 ?Hx2; reflexivity).
      assert (Hsnd : snd (pk_dir c0 c1 c2) = 0%nat)
        by (unfold pk_dir; rewrite ?Hd0 ?Hu0 ?Hx0 ?Hp0 ?Hc0 ?Hs0c ?Hl0 ?Hd1 ?Hu1 ?Hx1 ?Hl1 ?Hd2 ?Hu2 ?Hx2; reflexivity).
      iEval (rewrite Hent) in "Hpc".
      iApply (wp_printk_arm_p γd γv m mc K k l pv pkv dqm dqm2 Rest b pcur
                HK30 Hk Hpv Hpkv Hsp Hs0
                with "Hcg Htext Hkdata Hpc S19 Hap Hva Hpanicking Hpanicked Hdev Htx Hdlab HR [-]").
      iIntros (CIDn10 Hstn10 mf bs) "%Hcs Hcg Hpc S19 Hap Hva Hpanicking Hpanicked Htx Hsent HR".
      iSpecialize ("Hcont" $! CIDn10 with "[%]"); [wp_next_chain|].
      iApply ("Hcont" $! mf bs with "[%] Hcg Hpc S19 Hap Hva Hpanicking Hpanicked Htx Hsent HR").
      rewrite Hsnd. split; [ intros c Hc _ N20 N21; apply Hcs; assumption | ].
      replace (Z.of_nat (S i + 0)) with (Z.of_nat i + 1) by lia.
      rewrite (Hcs (mword_of_int 9 : mword 5) ltac:(vm_compute; reflexivity)
                 ltac:(reg_neq) ltac:(reg_neq)). exact Hs1. }
    case_eq (Ascii.eqb c0 "c"%char); intro Hc0.
    { assert (Hent : pk_entry c0 c1 c2 = 0x1fa)
        by (unfold pk_entry; rewrite ?Hd0 ?Hu0 ?Hx0 ?Hp0 ?Hc0 ?Hs0c ?Hl0 ?Hd1 ?Hu1 ?Hx1 ?Hl1 ?Hd2 ?Hu2 ?Hx2; reflexivity).
      assert (Hsnd : snd (pk_dir c0 c1 c2) = 0%nat)
        by (unfold pk_dir; rewrite ?Hd0 ?Hu0 ?Hx0 ?Hp0 ?Hc0 ?Hs0c ?Hl0 ?Hd1 ?Hu1 ?Hx1 ?Hl1 ?Hd2 ?Hu2 ?Hx2; reflexivity).
      iEval (rewrite Hent) in "Hpc".
      iApply (wp_printk_arm_c γd γv m mc K k l pv pkv dqm dqm2
                ((∃ w : mword 64, (pa_stk sp0 19) ↦₈ w) ∗ Rest)%I b pcur HK30 Hk Hpv Hpkv Hs0
                with "Hcg Htext Hpc Hap Hva Hpanicking Hpanicked Hdev Htx Hdlab [$S19 $HR] [-]").
      iIntros (CIDn11 Hstn11 mf bs) "%Hcs Hcg Hpc Hap Hva Hpanicking Hpanicked Htx Hsent (S19 & HR)".
      iSpecialize ("Hcont" $! CIDn11 with "[%]"); [wp_next_chain|].
      iApply ("Hcont" $! mf bs with "[%] Hcg Hpc S19 Hap Hva Hpanicking Hpanicked Htx Hsent HR").
      rewrite Hsnd. split; [ intros c Hc _ _ _; apply Hcs; assumption | ].
      replace (Z.of_nat (S i + 0)) with (Z.of_nat i + 1) by lia.
      rewrite (Hcs (mword_of_int 9 : mword 5) ltac:(vm_compute; reflexivity)). exact Hs1. }
    (* '%s' consumes a STRING, and anything else consumes nothing *)
    exfalso. case_eq (Ascii.eqb c0 "s"%char); intro Hs0c;
      unfold pk_dir in Hnum; rewrite ?Hd0 ?Hu0 ?Hx0 ?Hp0 ?Hc0 ?Hs0c ?Hl0 ?Hd1 ?Hu1 ?Hx1 ?Hl1 ?Hd2 ?Hu2 ?Hx2 in Hnum;
      cbn in Hnum; discriminate Hnum.
  Qed.


  (* the '%s' entry: the one directive that consumes a STRING, so the one
     that needs the caller's descriptor.  Which of the two string arms runs
     is decided by the descriptor, not by the machine -- [PkANull] is a null
     char* and takes the "(null)" path. *)
  Lemma wp_printk_arm_str `{CID0 : CpuId} (γd : uart_names) (γv : disk_names)
      (m mc : regfile) (K : nat) (k i : nat) (l : list (bv 8)) (pv pkv : mword 32)
      (dqm dqm2 : dfrac) (c0 c1 c2 : Ascii.ascii) (d : pk_arg_desc) (Rest : iProp Σ)
      (b : bool) (pcur : mword 64) :
    let sp0 := m !!! Regidx csp_rs1 in
    let s0v := add_vec sp0 (sign_extend' 64 (mword_of_int (-64) : mword 12)) in
    (30 <= K)%nat ->
    (k < 7)%nat ->
    eq_vec (sign_extend' 64 pv) zero_reg = false ->
    neq_vec (sign_extend' 64 pkv) zero_reg = false ->
    fst (pk_dir c0 c1 c2) = Some PkStr ->
    pk_desc_kind d = PkStr ->
    mc !!! Regidx s0_idx = s0v ->
    mc !!! Regidx (mword_of_int 9 : mword 5) = mword_of_int (Z.of_nat i + 1) ->
    sie_cap_gpr mc (K - 24)%nat b pcur -∗
    kernel_text -∗ kernel_data -∗
    pc_is (mword_of_int (KernelSyms.printk + pk_entry c0 c1 c2) : mword 64) -∗
    (∃ w : mword 64, (pa_stk sp0 19) ↦₈ w) -∗
    (pa_stk sp0 23) ↦₈ (pk_ap s0v k) -∗
    pk_va sp0 m -∗
    pk_desc_res (pk_vararg m k) d -∗
    (mword_of_int KernelSyms.panicking : mword 64) ↦₄{ dqm } pv -∗
    (mword_of_int KernelSyms.panicked : mword 64) ↦₄{ dqm2 } pkv -∗
    dev_inv γd γv -∗ uart_tx_own γd l -∗ uart_sent γd l -∗ uart_dlab_off γd -∗
    Rest -∗
    wp_next (CID0 := CID0) b pcur (fun (CID : CpuId) =>
      ∀ (mf : regfile) (bs : list (bv 8)),
      ⌜ (forall c : mword 5, is_cs_idx c = true -> c <> mword_of_int 9 ->
           c <> mword_of_int 20 -> c <> mword_of_int 21 ->
           mf !!! Regidx c = mc !!! Regidx c)
        /\ mf !!! Regidx (mword_of_int 9 : mword 5)
           = mword_of_int (Z.of_nat (S i + snd (pk_dir c0 c1 c2))) ⌝ -∗
      sie_cap_gpr mf (K - 24)%nat b pcur -∗
      pc_is (mword_of_int (KernelSyms.printk + 0x78) : mword 64) -∗
      (∃ w : mword 64, (pa_stk sp0 19) ↦₈ w) -∗
      (pa_stk sp0 23) ↦₈ (pk_ap s0v (S k)) -∗
      pk_va sp0 m -∗
      pk_desc_res (pk_vararg m k) d -∗
      (mword_of_int KernelSyms.panicking : mword 64) ↦₄{ dqm } pv -∗
      (mword_of_int KernelSyms.panicked : mword 64) ↦₄{ dqm2 } pkv -∗
      uart_tx_own γd (l ++ bs) -∗ uart_sent γd (l ++ bs) -∗
      Rest -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros sp0 s0v HK Hk Hpv Hpkv Hstr Hkind Hs0 Hs1.
    (* only c0 = 's' yields PkStr *)
    assert (Hs0c : Ascii.eqb c0 "s"%char = true).
    { case_eq (Ascii.eqb c0 "s"%char); [reflexivity | intro Hn].
      exfalso. unfold pk_dir in Hstr.
      case_eq (Ascii.eqb c0 "d"%char); intro E1; rewrite E1 in Hstr; [cbn in Hstr; discriminate | ].
      case_eq (Ascii.eqb c0 "u"%char); intro E2; rewrite E2 in Hstr; [cbn in Hstr; discriminate | ].
      case_eq (Ascii.eqb c0 "x"%char); intro E3; rewrite E3 in Hstr; [cbn in Hstr; discriminate | ].
      case_eq (Ascii.eqb c0 "p"%char); intro E4; rewrite E4 in Hstr; [cbn in Hstr; discriminate | ].
      case_eq (Ascii.eqb c0 "c"%char); intro E5; rewrite E5 in Hstr; [cbn in Hstr; discriminate | ].
      rewrite Hn in Hstr.
      case_eq (Ascii.eqb c0 "l"%char); intro E6; rewrite E6 in Hstr; cbn in Hstr;
        [ | discriminate ].
      repeat (match type of Hstr with context [if ?b then _ else _] => destruct b end);
        cbn in Hstr; discriminate. }
    assert (Hd0 : Ascii.eqb c0 "d"%char = false)
      by (apply (ascii_eqb_neq c0 "s"%char "d"%char Hs0c); vm_compute; reflexivity).
    assert (Hl0 : Ascii.eqb c0 "l"%char = false)
      by (apply (ascii_eqb_neq c0 "s"%char "l"%char Hs0c); vm_compute; reflexivity).
    assert (Hu0 : Ascii.eqb c0 "u"%char = false)
      by (apply (ascii_eqb_neq c0 "s"%char "u"%char Hs0c); vm_compute; reflexivity).
    assert (Hx0 : Ascii.eqb c0 "x"%char = false)
      by (apply (ascii_eqb_neq c0 "s"%char "x"%char Hs0c); vm_compute; reflexivity).
    assert (Hp0 : Ascii.eqb c0 "p"%char = false)
      by (apply (ascii_eqb_neq c0 "s"%char "p"%char Hs0c); vm_compute; reflexivity).
    assert (Hc0 : Ascii.eqb c0 "c"%char = false)
      by (apply (ascii_eqb_neq c0 "s"%char "c"%char Hs0c); vm_compute; reflexivity).
    assert (Hent : pk_entry c0 c1 c2 = 0x20e)
      by (unfold pk_entry; rewrite ?Hd0 ?Hu0 ?Hx0 ?Hp0 ?Hc0 ?Hs0c ?Hl0; reflexivity).
    assert (Hsnd : snd (pk_dir c0 c1 c2) = 0%nat)
      by (unfold pk_dir; rewrite ?Hd0 ?Hu0 ?Hx0 ?Hp0 ?Hc0 ?Hs0c ?Hl0; reflexivity).
    iIntros "Hcg #Htext #Hkdata Hpc S19 Hap Hva Hdesc Hpanicking Hpanicked #Hdev Htx #Hsl #Hdlab HR Hcont".
    iEval (rewrite Hent) in "Hpc".
    destruct d as [ | | dq str]; [ discriminate Hkind | | ].
    - (* PkANull: the "(null)" literal *)
      iDestruct "Hdesc" as "%Hnull".
      iApply (wp_printk_arm_s_null γd γv m mc K k l pv pkv dqm dqm2
                ((∃ w : mword 64, (pa_stk sp0 19) ↦₈ w) ∗ Rest)%I b pcur
                HK Hk Hpv Hpkv Hnull Hs0
                with "Hcg Htext Hkdata Hpc Hap Hva Hpanicking Hpanicked Hdev Htx Hdlab [$S19 $HR] [-]").
      iIntros (CIDs1 Hsts1 mf bs) "%Hcs Hcg Hpc Hap Hva Hpanicking Hpanicked Htx Hsent (S19 & HR)".
      iSpecialize ("Hcont" $! CIDs1 with "[%]"); [wp_next_chain|].
      iApply ("Hcont" $! mf bs with "[%] Hcg Hpc S19 Hap Hva [%] Hpanicking Hpanicked Htx Hsent HR").
      + rewrite Hsnd. split; [ intros c Hc _ N20 _; apply Hcs; assumption | ].
        replace (Z.of_nat (S i + 0)) with (Z.of_nat i + 1) by lia.
        rewrite (Hcs (mword_of_int 9 : mword 5) ltac:(vm_compute; reflexivity) ltac:(reg_neq)).
        exact Hs1.
      + exact Hnull.
    - (* PkAStr: a real string *)
      iDestruct "Hdesc" as "(%Hnn & %Hnz & Hstrp)".
      iApply (wp_printk_arm_s γd γv m mc K k l pv pkv dqm dqm2 dq str
                ((∃ w : mword 64, (pa_stk sp0 19) ↦₈ w) ∗ Rest)%I b pcur
                HK Hk Hpv Hpkv Hnn Hnz Hs0
                with "Hcg Htext Hpc Hap Hva Hstrp Hpanicking Hpanicked Hdev Htx Hsl Hdlab [$S19 $HR] [-]").
      iIntros (CIDs2 Hsts2 mf bs) "%Hcs Hcg Hpc Hap Hva Hstrp Hpanicking Hpanicked Htx Hsent (S19 & HR)".
      iSpecialize ("Hcont" $! CIDs2 with "[%]"); [wp_next_chain|].
      iApply ("Hcont" $! mf bs with "[%] Hcg Hpc S19 Hap Hva [$Hstrp] Hpanicking Hpanicked Htx Hsent HR").
      + rewrite Hsnd. split; [ intros c Hc _ N20 _; apply Hcs; assumption | ].
        replace (Z.of_nat (S i + 0)) with (Z.of_nat i + 1) by lia.
        rewrite (Hcs (mword_of_int 9 : mword 5) ltac:(vm_compute; reflexivity) ltac:(reg_neq)).
        exact Hs1.
      + iPureIntro. split; assumption.
  Qed.

  (* '%%' and an unrecognised directive: two characters out, no vararg. *)
  Lemma wp_printk_arm_none `{CID0 : CpuId} (γd : uart_names) (γv : disk_names)
      (mc : regfile) (K : nat) (i : nat) (l : list (bv 8)) (pv pkv : mword 32)
      (dqm dqm2 : dfrac) (c0 c1 c2 : Ascii.ascii) (Rest : iProp Σ) (b : bool) (pcur : mword 64) :
    (30 <= K)%nat ->
    eq_vec (sign_extend' 64 pv) zero_reg = false ->
    neq_vec (sign_extend' 64 pkv) zero_reg = false ->
    fst (pk_dir c0 c1 c2) = None ->
    Ascii.eqb c0 pk_nul = false ->
    mc !!! Regidx (mword_of_int 9 : mword 5) = mword_of_int (Z.of_nat i + 1) ->
    sie_cap_gpr mc (K - 24)%nat b pcur -∗
    kernel_text -∗
    pc_is (mword_of_int (KernelSyms.printk + pk_entry c0 c1 c2) : mword 64) -∗
    (mword_of_int KernelSyms.panicking : mword 64) ↦₄{ dqm } pv -∗
    (mword_of_int KernelSyms.panicked : mword 64) ↦₄{ dqm2 } pkv -∗
    dev_inv γd γv -∗ uart_tx_own γd l -∗ uart_dlab_off γd -∗
    Rest -∗
    wp_next (CID0 := CID0) b pcur (fun (CID : CpuId) =>
      ∀ (mf : regfile) (bs : list (bv 8)),
      ⌜ (forall c : mword 5, is_cs_idx c = true -> c <> mword_of_int 9 ->
           c <> mword_of_int 20 -> c <> mword_of_int 21 ->
           mf !!! Regidx c = mc !!! Regidx c)
        /\ mf !!! Regidx (mword_of_int 9 : mword 5)
           = mword_of_int (Z.of_nat (S i + snd (pk_dir c0 c1 c2))) ⌝ -∗
      sie_cap_gpr mf (K - 24)%nat b pcur -∗
      pc_is (mword_of_int (KernelSyms.printk + 0x78) : mword 64) -∗
      (mword_of_int KernelSyms.panicking : mword 64) ↦₄{ dqm } pv -∗
      (mword_of_int KernelSyms.panicked : mword 64) ↦₄{ dqm2 } pkv -∗
      uart_tx_own γd (l ++ bs) -∗ uart_sent γd (l ++ bs) -∗
      Rest -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros HK Hpv Hpkv Hnone Hnn Hs1.
    iIntros "Hcg #Htext Hpc Hpanicking Hpanicked #Hdev Htx #Hdlab HR Hcont".
    (* [fst = None] rules out every consuming form, so [pk_entry] is either
       the '%%' arm or the unknown-directive arm. *)
    assert (Hsnd : snd (pk_dir c0 c1 c2) = 0%nat).
    { unfold pk_dir in Hnone |- *.
      repeat (match goal with |- context [if ?b then _ else _] => destruct b end);
        cbn in Hnone |- *; try reflexivity; discriminate Hnone. }
    assert (Hd0 : Ascii.eqb c0 "d"%char = false)
      by (case_eq (Ascii.eqb c0 "d"%char); intro E; [ exfalso; unfold pk_dir in Hnone;
            rewrite E in Hnone; cbn in Hnone; discriminate | reflexivity ]).
    assert (Hu0 : Ascii.eqb c0 "u"%char = false)
      by (case_eq (Ascii.eqb c0 "u"%char); intro E; [ exfalso; unfold pk_dir in Hnone;
            rewrite Hd0 E in Hnone; cbn in Hnone; discriminate | reflexivity ]).
    assert (Hx0 : Ascii.eqb c0 "x"%char = false)
      by (case_eq (Ascii.eqb c0 "x"%char); intro E; [ exfalso; unfold pk_dir in Hnone;
            rewrite Hd0 Hu0 E in Hnone; cbn in Hnone; discriminate | reflexivity ]).
    assert (Hp0 : Ascii.eqb c0 "p"%char = false)
      by (case_eq (Ascii.eqb c0 "p"%char); intro E; [ exfalso; unfold pk_dir in Hnone;
            rewrite Hd0 Hu0 Hx0 E in Hnone; cbn in Hnone; discriminate | reflexivity ]).
    assert (Hc0 : Ascii.eqb c0 "c"%char = false)
      by (case_eq (Ascii.eqb c0 "c"%char); intro E; [ exfalso; unfold pk_dir in Hnone;
            rewrite Hd0 Hu0 Hx0 Hp0 E in Hnone; cbn in Hnone; discriminate | reflexivity ]).
    assert (Hs0c : Ascii.eqb c0 "s"%char = false)
      by (case_eq (Ascii.eqb c0 "s"%char); intro E; [ exfalso; unfold pk_dir in Hnone;
            rewrite Hd0 Hu0 Hx0 Hp0 Hc0 E in Hnone; cbn in Hnone; discriminate | reflexivity ]).
    (* the long forms are out too, one test at a time *)
    assert (Hlk : (Ascii.eqb c0 "l"%char && Ascii.eqb c1 "d"%char)%bool = false
               /\ (Ascii.eqb c0 "l"%char && (Ascii.eqb c1 "l"%char && Ascii.eqb c2 "d"%char))%bool = false
               /\ (Ascii.eqb c0 "l"%char && Ascii.eqb c1 "u"%char)%bool = false
               /\ (Ascii.eqb c0 "l"%char && (Ascii.eqb c1 "l"%char && Ascii.eqb c2 "u"%char))%bool = false
               /\ (Ascii.eqb c0 "l"%char && Ascii.eqb c1 "x"%char)%bool = false
               /\ (Ascii.eqb c0 "l"%char && (Ascii.eqb c1 "l"%char && Ascii.eqb c2 "x"%char))%bool = false).
    { unfold pk_dir in Hnone. rewrite Hd0 Hu0 Hx0 Hp0 Hc0 Hs0c in Hnone.
      (* here [destruct]'s generalisation is what we WANT: it rewrites the
         scrutinee in the goal as well, so each conjunct collapses. *)
      destruct (Ascii.eqb c0 "l"%char) eqn:El; [ | split_and!; reflexivity ].
      destruct (Ascii.eqb c1 "d"%char) eqn:Ed1; [ cbn in Hnone; discriminate | ].
      destruct (Ascii.eqb c1 "u"%char) eqn:Eu1; [ cbn in Hnone; discriminate | ].
      destruct (Ascii.eqb c1 "x"%char) eqn:Ex1; [ cbn in Hnone; discriminate | ].
      destruct (Ascii.eqb c1 "l"%char) eqn:El1; [ | split_and!; reflexivity ].
      destruct (Ascii.eqb c2 "d"%char) eqn:Ed2; [ cbn in Hnone; discriminate | ].
      destruct (Ascii.eqb c2 "u"%char) eqn:Eu2; [ cbn in Hnone; discriminate | ].
      destruct (Ascii.eqb c2 "x"%char) eqn:Ex2; [ cbn in Hnone; discriminate | ].
      split_and!; reflexivity. }
    destruct Hlk as (L1 & L2 & L3 & L4 & L5 & L6).
    case_eq (Ascii.eqb c0 "%"%char); intro Hm0.
    - assert (Hent : pk_entry c0 c1 c2 = 0x246)
        by (unfold pk_entry; rewrite Hd0 L1 L2 Hu0 L3 L4 Hx0 L5 L6 Hp0 Hc0 Hs0c Hm0; reflexivity).
      iEval (rewrite Hent) in "Hpc".
      iApply (wp_printk_arm_pct γd γv mc K l pv pkv dqm dqm2 Rest b pcur HK Hpv Hpkv
                with "Hcg Htext Hpc Hpanicking Hpanicked Hdev Htx Hdlab HR [-]").
      iIntros (CIDn1 Hstn1 mf bs) "%Hcs Hcg Hpc Hpanicking Hpanicked Htx Hsent HR".
      iSpecialize ("Hcont" $! CIDn1 with "[%]"); [wp_next_chain|].
      iApply ("Hcont" $! mf bs with "[%] Hcg Hpc Hpanicking Hpanicked Htx Hsent HR").
      rewrite Hsnd. split; [ intros c Hc _ _ _; apply Hcs; assumption | ].
      replace (Z.of_nat (S i + 0)) with (Z.of_nat i + 1) by lia.
      rewrite (Hcs (mword_of_int 9 : mword 5) ltac:(vm_compute; reflexivity)). exact Hs1.
    - assert (Hent : pk_entry c0 c1 c2 = 0x31a)
        by (unfold pk_entry; rewrite Hd0 L1 L2 Hu0 L3 L4 Hx0 L5 L6 Hp0 Hc0 Hs0c Hm0 Hnn; reflexivity).
      iEval (rewrite Hent) in "Hpc".
      iApply (wp_printk_arm_unknown γd γv mc K l pv pkv dqm dqm2 Rest b pcur HK Hpv Hpkv
                with "Hcg Htext Hpc Hpanicking Hpanicked Hdev Htx Hdlab HR [-]").
      iIntros (CIDn2 Hstn2 mf bs) "%Hcs Hcg Hpc Hpanicking Hpanicked Htx Hsent HR".
      iSpecialize ("Hcont" $! CIDn2 with "[%]"); [wp_next_chain|].
      iApply ("Hcont" $! mf bs with "[%] Hcg Hpc Hpanicking Hpanicked Htx Hsent HR").
      rewrite Hsnd. split; [ intros c Hc _ _ _; apply Hcs; assumption | ].
      replace (Z.of_nat (S i + 0)) with (Z.of_nat i + 1) by lia.
      rewrite (Hcs (mword_of_int 9 : mword 5) ltac:(vm_compute; reflexivity)). exact Hs1.
  Qed.

  (* ================================================================== *)
  (*  THE FORMAT LOOP.                                                   *)
  (*                                                                     *)
  (*  Everything below only ASSEMBLES proven pieces -- advance, char,    *)
  (*  dispatch, the fifteen arms, the two exits.  The loop state is two  *)
  (*  numbers: [p], the index of the last format character consumed, and *)
  (*  [k], the varargs consumed so far; the invariant ties them together *)
  (*  by [pk_kinds] on the remaining SUFFIX of the format string, and    *)
  (*  [pk_kinds_step] is the equation one turn rewrites it by.           *)
  (*                                                                     *)
  (*  The fuel induction runs at the increment point 0x78                *)
  (*  ([wp_printk_loop78]); one turn from the '%' test at 0x86 is its    *)
  (*  own lemma ([wp_printk_body86]) so that the ENTRY from the setup    *)
  (*  (which lands at 0x86, not 0x78) is the same proof as a turn from   *)
  (*  inside the loop.  [wp_printk_body86] takes its two futures as ONE  *)
  (*  [∧]-conjunction -- go round again, or exit through 0x276 -- since  *)
  (*  which one runs is decided by the machine inside the lemma, while   *)
  (*  the caller has only one copy of the final continuation to give     *)
  (*  out; [∧] hands the same context to both.                           *)
  (* ================================================================== *)

  (* a character strictly inside the string, from its byte being nonzero *)
  Lemma pk_ch_lt (g : string) (j : nat) :
    pk_ch g j <> pk_nul -> (j < String.length g)%nat.
  Proof.
    intro Hnz. destruct (decide (String.length g <= j)%nat) as [Hle | Hgt].
    - exfalso. apply Hnz. apply pk_ch_nul. exact Hle.
    - lia.
  Qed.

  Lemma pk_ch_nonzero (g : string) (j : nat) :
    nonul g = true -> (j < String.length g)%nat -> pk_ch g j <> pk_nul.
  Proof.
    intros Hn Hj He.
    apply (pk_fbyte_nonzero g j Hn).
    - rewrite string_bytes_length. exact Hj.
    - rewrite (pk_fbyte_ch g j ltac:(lia)) He.
      apply bv_eq; vm_compute; reflexivity.
  Qed.

  Section PrintkLoop.
    Variables (γd : uart_names) (γv : disk_names).
    Variables (m : regfile) (K : nat).
    Variables (pv pkv : mword 32) (dqm dqm2 dqf : dfrac).
    Variables (f : string) (descs : list pk_arg_desc).
    Variables (b : bool) (pcur : mword 64).

    Let sp0 : mword 64 := m !!! Regidx csp_rs1.
    Let spd : mword 64 := add_vec sp0 (sign_extend' 64 (caddi16sp_imm (mword_of_int 52 : mword 6))).
    Let s0v : mword 64 := add_vec sp0 (sign_extend' 64 (mword_of_int (-64) : mword 12)).
    Let fmtv : mword 64 := m !!! Regidx a0_idx.

    Hypothesis HK : (38 <= K)%nat.
    Hypothesis Hflen : (Z.of_nat (String.length f) < 2147483645)%Z.
    Hypothesis Hnn : nonul f = true.
    Hypothesis Hdlen : (length descs <= 7)%nat.
    Hypothesis Hpv : eq_vec (sign_extend' 64 pv) zero_reg = false.
    Hypothesis Hpkv : neq_vec (sign_extend' 64 pkv) zero_reg = false.

    (* the frame as the loop carries it: everything the prologue and setup
       built, with the va_list cursor at [k] arguments consumed *)
    Definition pk_loop_frame (k : nat) : iProp Σ :=
      ((pa_stk sp0 9) ↦₈ (m !!! Regidx ra_idx) ∗
       (pa_stk sp0 10) ↦₈ (m !!! Regidx s0_idx) ∗
       (pa_stk sp0 12) ↦₈ (m !!! Regidx s2_idx) ∗
       pk_va sp0 m ∗
       pk_saved sp0 (m !!! Regidx (mword_of_int 9 : mword 5)) (m !!! Regidx (mword_of_int 19 : mword 5)) (m !!! Regidx (mword_of_int 20 : mword 5)) (m !!! Regidx (mword_of_int 21 : mword 5)) (m !!! Regidx (mword_of_int 22 : mword 5)) (m !!! Regidx (mword_of_int 23 : mword 5)) (m !!! Regidx (mword_of_int 24 : mword 5)) (m !!! Regidx (mword_of_int 26 : mword 5)) (m !!! Regidx (mword_of_int 27 : mword 5)) ∗
       (∃ w : mword 64, (pa_stk sp0 8) ↦₈ w) ∗
       (∃ w : mword 64, (pa_stk sp0 19) ↦₈ w) ∗
       (∃ w : mword 64, (pa_stk sp0 22) ↦₈ w) ∗
       (pa_stk sp0 23) ↦₈ (pk_ap s0v k) ∗
       (∃ w : mword 64, (pa_stk sp0 24) ↦₈ w))%I.

    (* what the whole loop owes at the end: the spec's continuation, relative
       to the byte list [l] the UART held when the loop was entered *)
    Definition pk_loop_post `{CID0 : CpuId} (l : list (bv 8)) : iProp Σ :=
      wp_next (CID0 := CID0) b pcur (fun (CID : CpuId) =>
        ∀ (mf : regfile) (bs : list (bv 8)),
        sie_cap_gpr mf K b pcur -∗
        pc_is (ret_pc (m !!! Regidx ra_idx)) -∗
        ⌜ callee_saved m mf /\ mf !!! Regidx ra_idx = m !!! Regidx ra_idx
          /\ mf !!! Regidx a0_idx = zero_reg ⌝ -∗
        fmtv ↦ₛ{ dqf } f -∗
        ([∗ list] j ↦ d ∈ descs, pk_desc_res (pk_vararg m j) d) -∗
        (mword_of_int KernelSyms.panicking : mword 64) ↦₄{ dqm } pv -∗
        (mword_of_int KernelSyms.panicked : mword 64) ↦₄{ dqm2 } pkv -∗
        uart_tx_own γd (l ++ bs) -∗ uart_sent γd (l ++ bs) -∗
        WP (Loop : expr riscv_lang))%I.

    (* "go round again": what one turn from index [i] hands back to the loop
       head at 0x78.  [p'] is the new last-consumed index, [k'] the new
       vararg count, [bs] what the turn printed. *)
    Definition pk_loop_head `{CID0 : CpuId} (i : nat) (l : list (bv 8)) : iProp Σ :=
      wp_next (CID0 := CID0) b pcur (fun (CID : CpuId) =>
        ∀ (mk : regfile) (k' p' : nat) (bs : list (bv 8)),
        ⌜ (i <= p')%nat /\ (p' < String.length f)%nat
          /\ pk_kinds (str_drop (S p') f) = map pk_desc_kind (drop k' descs)
          /\ mk !!! Regidx csp_rs1 = spd
          /\ mk !!! Regidx s0_idx = s0v
          /\ mk !!! Regidx s2_idx = fmtv
          /\ mk !!! Regidx (mword_of_int 9 : mword 5) = mword_of_int (Z.of_nat p')
          /\ mk !!! Regidx (mword_of_int 25 : mword 5) = m !!! Regidx (mword_of_int 25 : mword 5)
          /\ pk_consts mk ⌝ -∗
        sie_cap_gpr mk (K - 24)%nat b pcur -∗
        pc_is (mword_of_int (KernelSyms.printk + 0x78) : mword 64) -∗
        fmtv ↦ₛ{ dqf } f -∗
        ([∗ list] j ↦ d ∈ descs, pk_desc_res (pk_vararg m j) d) -∗
        (mword_of_int KernelSyms.panicking : mword 64) ↦₄{ dqm } pv -∗
        (mword_of_int KernelSyms.panicked : mword 64) ↦₄{ dqm2 } pkv -∗
        uart_tx_own γd (l ++ bs) -∗ uart_sent γd (l ++ bs) -∗
        pk_loop_frame k' -∗
        WP (Loop : expr riscv_lang))%I.

    (* the unused frame slots, in the exit lemmas' shape *)
    Lemma pk_slots_rest_of (w23 : mword 64) :
      pk_va sp0 m -∗
      (∃ w : mword 64, (pa_stk sp0 8) ↦₈ w) -∗
      (∃ w : mword 64, (pa_stk sp0 19) ↦₈ w) -∗
      (∃ w : mword 64, (pa_stk sp0 22) ↦₈ w) -∗
      (pa_stk sp0 23) ↦₈ w23 -∗
      (∃ w : mword 64, (pa_stk sp0 24) ↦₈ w) -∗
      pk_slots_rest sp0.
    Proof.
      iIntros "(V7 & V6 & V5 & V4 & V3 & V2 & V1) S8 S19 S22 Hap S24".
      rewrite /pk_slots_rest. cbn [big_opL].
      iSplitL "V1". { iExists (m !!! Regidx (mword_of_int 17 : mword 5)). iExact "V1". }
      iSplitL "V2". { iExists (m !!! Regidx (mword_of_int 16 : mword 5)). iExact "V2". }
      iSplitL "V3". { iExists (m !!! Regidx (mword_of_int 15 : mword 5)). iExact "V3". }
      iSplitL "V4". { iExists (m !!! Regidx (mword_of_int 14 : mword 5)). iExact "V4". }
      iSplitL "V5". { iExists (m !!! Regidx (mword_of_int 13 : mword 5)). iExact "V5". }
      iSplitL "V6". { iExists (m !!! Regidx (mword_of_int 12 : mword 5)). iExact "V6". }
      iSplitL "V7". { iExists (m !!! Regidx (mword_of_int 11 : mword 5)). iExact "V7". }
      iFrame "S8 S19 S22 S24".
      iExists w23. iExact "Hap".
    Qed.

    (* thread the loop's fixed registers through a turn: [Hgq] is whichever
       "kept every callee-saved register except s1/s4/s5" fact the turn's
       lemmas produced. *)
    Lemma pk_head_regs (mq mg : regfile)
        (Hgq : forall c : mword 5, is_cs_idx c = true ->
                 c <> mword_of_int 9 -> c <> mword_of_int 20 -> c <> mword_of_int 21 ->
                 mg !!! Regidx c = mq !!! Regidx c)
        (Hsp : mq !!! Regidx csp_rs1 = spd)
        (Hs0 : mq !!! Regidx s0_idx = s0v)
        (Hs2 : mq !!! Regidx s2_idx = fmtv)
        (Hs9 : mq !!! Regidx (mword_of_int 25 : mword 5) = m !!! Regidx (mword_of_int 25 : mword 5))
        (Hcn : pk_consts mq) :
      mg !!! Regidx csp_rs1 = spd /\ mg !!! Regidx s0_idx = s0v /\ mg !!! Regidx s2_idx = fmtv
      /\ mg !!! Regidx (mword_of_int 25 : mword 5) = m !!! Regidx (mword_of_int 25 : mword 5)
      /\ pk_consts mg.
    Proof.
      destruct Hcn as (A1 & A2 & A3 & A4 & A5 & A6).
      refine (conj _ (conj _ (conj _ (conj _ _)))).
      - rewrite (Hgq csp_rs1 ltac:(vm_compute; reflexivity) ltac:(mw_neq) ltac:(mw_neq) ltac:(mw_neq)). exact Hsp.
      - rewrite (Hgq s0_idx ltac:(vm_compute; reflexivity) ltac:(mw_neq) ltac:(mw_neq) ltac:(mw_neq)). exact Hs0.
      - rewrite (Hgq s2_idx ltac:(vm_compute; reflexivity) ltac:(mw_neq) ltac:(mw_neq) ltac:(mw_neq)). exact Hs2.
      - rewrite (Hgq (mword_of_int 25 : mword 5) ltac:(vm_compute; reflexivity) ltac:(mw_neq) ltac:(mw_neq) ltac:(mw_neq)). exact Hs9.
      - unfold pk_consts. split_and!.
        + rewrite (Hgq (mword_of_int 19 : mword 5) ltac:(vm_compute; reflexivity) ltac:(mw_neq) ltac:(mw_neq) ltac:(mw_neq)). exact A1.
        + rewrite (Hgq (mword_of_int 22 : mword 5) ltac:(vm_compute; reflexivity) ltac:(mw_neq) ltac:(mw_neq) ltac:(mw_neq)). exact A2.
        + rewrite (Hgq (mword_of_int 23 : mword 5) ltac:(vm_compute; reflexivity) ltac:(mw_neq) ltac:(mw_neq) ltac:(mw_neq)). exact A3.
        + rewrite (Hgq (mword_of_int 24 : mword 5) ltac:(vm_compute; reflexivity) ltac:(mw_neq) ltac:(mw_neq) ltac:(mw_neq)). exact A4.
        + rewrite (Hgq (mword_of_int 26 : mword 5) ltac:(vm_compute; reflexivity) ltac:(mw_neq) ltac:(mw_neq) ltac:(mw_neq)). exact A5.
        + rewrite (Hgq (mword_of_int 27 : mword 5) ltac:(vm_compute; reflexivity) ltac:(mw_neq) ltac:(mw_neq) ltac:(mw_neq)). exact A6.
    Qed.

    (* the dispatch's kept-set, weakened to the shape [pk_head_regs] takes *)
    Lemma pk_disp_regs (mq mf : regfile) (Hkept : pk_disp_all mf mq) :
      forall c : mword 5, is_cs_idx c = true ->
        c <> mword_of_int 9 -> c <> mword_of_int 20 -> c <> mword_of_int 21 ->
        mf !!! Regidx c = mq !!! Regidx c.
    Proof.
      intros c Hc N9 _ N21.
      assert (N11 : c <> (mword_of_int 11 : mword 5)) by (intro He; subst c; vm_compute in Hc; discriminate).
      assert (N12 : c <> (mword_of_int 12 : mword 5)) by (intro He; subst c; vm_compute in Hc; discriminate).
      assert (N13 : c <> (mword_of_int 13 : mword 5)) by (intro He; subst c; vm_compute in Hc; discriminate).
      assert (N14 : c <> (mword_of_int 14 : mword 5)) by (intro He; subst c; vm_compute in Hc; discriminate).
      assert (N15 : c <> (mword_of_int 15 : mword 5)) by (intro He; subst c; vm_compute in Hc; discriminate).
      exact (Hkept c N9 N11 N12 N13 N14 N15 N21).
    Qed.

    (* the advance block's kept-set, ditto *)
    Lemma pk_adv_regs (mq mf : regfile) (Hkept : pk_adv_kept mf mq) :
      forall c : mword 5, is_cs_idx c = true ->
        c <> mword_of_int 9 -> c <> mword_of_int 20 -> c <> mword_of_int 21 ->
        mf !!! Regidx c = mq !!! Regidx c.
    Proof.
      intros c Hc N9 N20 _.
      assert (N10 : c <> (mword_of_int 10 : mword 5)) by (intro He; subst c; vm_compute in Hc; discriminate).
      exact (Hkept c N9 N20 N10).
    Qed.

    (* ---------------------------------------------------------------- *)
    (*  ONE TURN, from the '%' test at 0x86.                             *)
    (* ---------------------------------------------------------------- *)

    Lemma wp_printk_body86 `{CID0 : CpuId} (mq : regfile) (k i : nat) (l : list (bv 8)) :
      (i < String.length f)%nat ->
      pk_kinds (str_drop i f) = map pk_desc_kind (drop k descs) ->
      mq !!! Regidx csp_rs1 = spd ->
      mq !!! Regidx s0_idx = s0v ->
      mq !!! Regidx s2_idx = fmtv ->
      mq !!! Regidx (mword_of_int 20 : mword 5) = mword_of_int (Z.of_nat i) ->
      mq !!! Regidx a0_idx = zero_extend' 64 (pk_fbyte f i) ->
      mq !!! Regidx (mword_of_int 25 : mword 5) = m !!! Regidx (mword_of_int 25 : mword 5) ->
      pk_consts mq ->
      sie_cap_gpr mq (K - 24)%nat b pcur -∗
      kernel_text -∗ kernel_data -∗
      pc_is (mword_of_int (KernelSyms.printk + 0x86) : mword 64) -∗
      fmtv ↦ₛ{ dqf } f -∗
      ([∗ list] j ↦ d ∈ descs, pk_desc_res (pk_vararg m j) d) -∗
      (mword_of_int KernelSyms.panicking : mword 64) ↦₄{ dqm } pv -∗
      (mword_of_int KernelSyms.panicked : mword 64) ↦₄{ dqm2 } pkv -∗
      dev_inv γd γv -∗ uart_tx_own γd l -∗ uart_sent γd l -∗ uart_dlab_off γd -∗
      pk_loop_frame k -∗
      (pk_loop_head i l ∧ pk_loop_post l) -∗
      WP (Loop : expr riscv_lang).
    Proof using All.
      intros Hilen Hinv Hsp Hs0 Hs2 Hs4 Ha0 Hs9r Hconsts.
      assert (HK24 : (24 <= K)%nat) by lia.
      assert (HK30 : (30 <= K)%nat) by lia.
      assert (Hc19 : mq !!! Regidx (mword_of_int 19 : mword 5) = (mword_of_int 37 : mword 64))
        by (destruct Hconsts as (X & _); exact X).
      iIntros "Hcg #Htext #Hkdata Hpc Hfmt Hdescs Hpanicking Hpanicked #Hdev Htx #Hsent #Hdlab Hfr Hcont".
      assert (Hfch : pk_fbyte f i = pk_byte (pk_ch f i)) by (apply pk_fbyte_ch; lia).
      pose proof (pk_kinds_step f i Hnn Hilen) as Hstep.
      case_eq (Ascii.eqb (pk_ch f i) "%"%char); intro Hpct.
      - (* '%': the bne falls through into the dispatch *)
        rewrite Hpct in Hstep. cbn [negb] in Hstep.
        assert (Hne : neq_vec (mq !!! Regidx a0_idx) (mq !!! Regidx (mword_of_int 19 : mword 5)) = false).
        { rewrite Ha0 Hc19 Hfch. unfold neq_vec.
          rewrite (pk_eq_ascii (pk_ch f i) "%"%char (mword_of_int 37)
                     ltac:(apply bv_eq; vm_compute; reflexivity)).
          rewrite Hpct. reflexivity. }
        iPoseProof (pki_86 with "Htext") as "Hi86".
        iApply (wp_bne_fall_s_sconf (mword_of_int (KernelSyms.printk + 0x86)) (mword_of_int 8172 : mword 13)
                  (mword_of_int 19 : mword 5) a0_idx mq (K - 24)%nat b
                  ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) ltac:(rgne; rgne; exact Hne)
                  with "Hcg Hpc Hi86 [-]").
        iIntros (CIDbne Hstbne) "Hcg Hpc".
        assert (Hp8a : add_vec_int (mword_of_int (KernelSyms.printk + 0x86) : mword 64) 4 = mword_of_int (KernelSyms.printk + 0x8a)) by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hp8a) in "Hpc".
        assert (Hlen1 : (S i < length (cstring_bytes f))%nat) by (rewrite cstring_bytes_length; lia).
        assert (Hi31 : Z.of_nat i + 1 < 2^31) by (change (2^31) with 2147483648; lia).
        iApply (wp_printk_dispatch (CID0 := CIDbne) mq K fmtv dqf f i
                  (([∗ list] j ↦ d ∈ descs, pk_desc_res (pk_vararg m j) d) ∗
                   (mword_of_int KernelSyms.panicking : mword 64) ↦₄{ dqm } pv ∗
                   (mword_of_int KernelSyms.panicked : mword 64) ↦₄{ dqm2 } pkv ∗
                   uart_tx_own γd l ∗ pk_loop_frame k ∗
                   (pk_loop_head (CID0 := CID0) i l ∧ pk_loop_post (CID0 := CID0) l))%I b pcur
                  Hlen1 Hi31 Hnn Hs4 Hs2 Hconsts
                  with "Hcg Htext Hpc Hfmt [$Hdescs $Hpanicking $Hpanicked $Htx $Hfr $Hcont] [-]").
        iIntros (CIDdisp Hstdisp mf) "%Hd Hcg Hpc Hfmt (Hdescs & Hpanicking & Hpanicked & Htx & Hfr & Hcont)".
        destruct Hd as [Hkept Hs1f].
        set (c0 := pk_ch f (S i)) in *.
        set (c1 := pk_ch f (S (S i))) in *.
        set (c2 := pk_ch f (S (S (S i)))) in *.
        pose proof (pk_head_regs mq mf (pk_disp_regs mq mf Hkept) Hsp Hs0 Hs2 Hs9r Hconsts)
          as (Hfsp & Hfs0 & Hfs2 & Hfs9 & Hfconsts).
        destruct (decide (String.length f <= S i)%nat) as [Hend | Hnend].
        + (* c0 = NUL: the format string is over -- leave through 0x276 *)
          assert (Hc0 : c0 = pk_nul) by (apply pk_ch_nul; exact Hend).
          assert (Hc1 : c1 = pk_nul) by (apply pk_ch_nul; lia).
          assert (Hc2 : c2 = pk_nul) by (apply pk_ch_nul; lia).
          assert (Hent : pk_entry c0 c1 c2 = 0x276)
            by (rewrite Hc0 Hc1 Hc2; vm_compute; reflexivity).
          iEval (rewrite Hent) in "Hpc".
          iDestruct "Hcont" as "[_ Hfin]".
          iEval (rewrite /pk_loop_frame) in "Hfr".
          iDestruct "Hfr" as "(H9 & H10 & H12 & Hva & Hsv & S8 & S19 & S22 & Hap & S24)".
          iDestruct (pk_slots_rest_of (pk_ap s0v k) with "Hva S8 S19 S22 Hap S24") as "Hrest".
          iApply (wp_printk_exit276 (CID0 := CIDdisp) m mf K pv dqm
                    (fmtv ↦ₛ{ dqf } f ∗
                     ([∗ list] j ↦ d ∈ descs, pk_desc_res (pk_vararg m j) d) ∗
                     (mword_of_int KernelSyms.panicked : mword 64) ↦₄{ dqm2 } pkv ∗
                     uart_tx_own γd l)%I b pcur
                    HK24 Hpv Hfsp Hfs9
                    with "Hcg Htext Hpc H9 H10 H12 Hsv Hrest Hpanicking [$Hfmt $Hdescs $Hpanicked $Htx] [-]").
          iIntros (CIDexit Hstexit mz) "Hcg Hpc %Hfin2 Hpanicking (Hfmt & Hdescs & Hpanicked & Htx)".
          iEval (rewrite /pk_loop_post) in "Hfin".
          iSpecialize ("Hfin" $! CIDexit with "[%]"); [wp_next_chain|].
          iSpecialize ("Hfin" $! mz []).
          iEval (rewrite (app_nil_r l)) in "Hfin".
          iApply ("Hfin" with "Hcg Hpc [%] Hfmt Hdescs Hpanicking Hpanicked Htx Hsent").
          exact Hfin2.
        + (* a real directive *)
          assert (Hlt1 : (S i < String.length f)%nat) by lia.
          assert (Hc0nz : c0 <> pk_nul) by (apply pk_ch_nonzero; [exact Hnn | exact Hlt1]).
          rewrite (proj2 (Ascii.eqb_neq c0 pk_nul) Hc0nz) in Hstep.
          cbn [negb] in Hstep.
          assert (Hplt : (S i + snd (pk_dir c0 c1 c2) < String.length f)%nat).
          { pose proof (pk_dir_snd_le c0 c1 c2) as Hsle.
            destruct (snd (pk_dir c0 c1 c2)) as [|[|[|n']]] eqn:Hsnd.
            - lia.
            - pose proof (pk_ch_lt f (S (S i)) (pk_dir_snd1_c1 c0 c1 c2 Hsnd)) as Hx. lia.
            - pose proof (pk_ch_lt f (S (S (S i))) (pk_dir_snd2_c2 c0 c1 c2 Hsnd)) as Hx. lia.
            - lia. }
          assert (HzS : Z.of_nat (S i) = Z.of_nat i + 1) by lia.
          rewrite HzS in Hs1f.
          assert (Hi33 : Z.of_nat i + 3 < 2^31) by (change (2^31) with 2147483648; lia).
          assert (Hf20 : mf !!! Regidx (mword_of_int 20 : mword 5) = mword_of_int (Z.of_nat i)).
          { rewrite (Hkept (mword_of_int 20 : mword 5) ltac:(mw_neq) ltac:(mw_neq) ltac:(mw_neq)
                       ltac:(mw_neq) ltac:(mw_neq) ltac:(mw_neq) ltac:(mw_neq)).
            exact Hs4. }
          assert (Hf22 : mf !!! Regidx (mword_of_int 22 : mword 5) = (mword_of_int 10 : mword 64))
            by (destruct Hfconsts as (_ & X & _); exact X).
          (* [case_eq], not [destruct eqn:]: the latter substitutes the
             scrutinee into [Hstep], and the rewrite below then finds
             nothing (the gotcha this file's dispatch chain recorded). *)
          case_eq (fst (pk_dir c0 c1 c2)); [ intros kd Hfst; destruct kd | intro Hfst ].
          * (* a NUMBER directive *)
            rewrite Hfst in Hstep. cbn [pk_cons] in Hstep.
               rewrite Hinv in Hstep.
               destruct (drop k descs) as [|d0 rest] eqn:Hdk; [ discriminate Hstep | ].
               cbn [List.map] in Hstep. injection Hstep as Hkd0 Htail.
               assert (Hk0 : descs !! k = Some d0).
               { rewrite -(Nat.add_0_r k) -lookup_drop Hdk. reflexivity. }
               pose proof (lookup_lt_Some descs k d0 Hk0) as Hklen.
               assert (Hk7 : (k < 7)%nat) by lia.
               assert (Hdrop : drop (S k) descs = rest).
               { pose proof (drop_S descs d0 k Hk0) as Hds. rewrite Hdk in Hds.
                 injection Hds as Hds. symmetry. exact Hds. }
               assert (Hinv' : pk_kinds (str_drop (S (S i) + snd (pk_dir c0 c1 c2)) f)
                               = map pk_desc_kind (drop (S k) descs))
                 by (rewrite Hdrop; symmetry; exact Htail).
               iEval (rewrite /pk_loop_frame) in "Hfr".
               iDestruct "Hfr" as "(H9 & H10 & H12 & Hva & Hsv & S8 & S19 & S22 & Hap & S24)".
               iDestruct "Hcont" as "[Hhead _]".
               iApply (wp_printk_arm_num (CID0 := CIDdisp) γd γv m mf K k i l pv pkv dqm dqm2 c0 c1 c2
                         (fmtv ↦ₛ{ dqf } f ∗
                          ([∗ list] j ↦ d ∈ descs, pk_desc_res (pk_vararg m j) d) ∗
                          (pa_stk sp0 9) ↦₈ (m !!! Regidx ra_idx) ∗
                          (pa_stk sp0 10) ↦₈ (m !!! Regidx s0_idx) ∗
                          (pa_stk sp0 12) ↦₈ (m !!! Regidx s2_idx) ∗
                          pk_saved sp0 (m !!! Regidx (mword_of_int 9 : mword 5)) (m !!! Regidx (mword_of_int 19 : mword 5)) (m !!! Regidx (mword_of_int 20 : mword 5)) (m !!! Regidx (mword_of_int 21 : mword 5)) (m !!! Regidx (mword_of_int 22 : mword 5)) (m !!! Regidx (mword_of_int 23 : mword 5)) (m !!! Regidx (mword_of_int 24 : mword 5)) (m !!! Regidx (mword_of_int 26 : mword 5)) (m !!! Regidx (mword_of_int 27 : mword 5)) ∗
                          (∃ w : mword 64, (pa_stk sp0 8) ↦₈ w) ∗
                          (∃ w : mword 64, (pa_stk sp0 22) ↦₈ w) ∗
                          (∃ w : mword 64, (pa_stk sp0 24) ↦₈ w) ∗
                          pk_loop_head (CID0 := CID0) i l)%I b pcur
                         HK Hk7 Hi33 Hpv Hpkv Hfst Hfsp Hfs0 Hf22 Hf20 Hs1f
                         with "Hcg Htext Hkdata Hpc S19 Hap Hva Hpanicking Hpanicked Hdev Htx Hdlab [$Hfmt $Hdescs $H9 $H10 $H12 $Hsv $S8 $S22 $S24 $Hhead] [-]").
               iIntros (CIDarm Hstarm mg bs) "%Hcs2 Hcg Hpc S19 Hap Hva Hpanicking Hpanicked Htx #Hsent2 (Hfmt & Hdescs & H9 & H10 & H12 & Hsv & S8 & S22 & S24 & Hhead)".
               destruct Hcs2 as [Hcs2 Hs1g].
               pose proof (pk_head_regs mf mg Hcs2 Hfsp Hfs0 Hfs2 Hfs9 Hfconsts)
                 as (Hgsp & Hgs0 & Hgs2 & Hgs9 & Hgconsts).
               iEval (rewrite /pk_loop_head) in "Hhead".
               iSpecialize ("Hhead" $! CIDarm with "[%]"); [wp_next_chain|].
               iApply ("Hhead" $! mg (S k) (S i + snd (pk_dir c0 c1 c2))%nat bs
                         with "[%] Hcg Hpc Hfmt Hdescs Hpanicking Hpanicked Htx Hsent2 [-]").
               { split_and!.
                 - lia.
                 - exact Hplt.
                 - replace (S (S i + snd (pk_dir c0 c1 c2)))%nat
                     with (S (S i) + snd (pk_dir c0 c1 c2))%nat by lia.
                   exact Hinv'.
                 - exact Hgsp.
                 - exact Hgs0.
                 - exact Hgs2.
                 - exact Hs1g.
                 - exact Hgs9.
                 - exact Hgconsts. }
               rewrite /pk_loop_frame.
               iFrame "H9 H10 H12 Hva Hsv S8 S19 S22 Hap S24".
          * (* the STRING directive *)
            rewrite Hfst in Hstep. cbn [pk_cons] in Hstep.
               rewrite Hinv in Hstep.
               destruct (drop k descs) as [|d0 rest] eqn:Hdk; [ discriminate Hstep | ].
               cbn [List.map] in Hstep. injection Hstep as Hkd0 Htail.
               assert (Hk0 : descs !! k = Some d0).
               { rewrite -(Nat.add_0_r k) -lookup_drop Hdk. reflexivity. }
               pose proof (lookup_lt_Some descs k d0 Hk0) as Hklen.
               assert (Hk7 : (k < 7)%nat) by lia.
               assert (Hdrop : drop (S k) descs = rest).
               { pose proof (drop_S descs d0 k Hk0) as Hds. rewrite Hdk in Hds.
                 injection Hds as Hds. symmetry. exact Hds. }
               assert (Hinv' : pk_kinds (str_drop (S (S i) + snd (pk_dir c0 c1 c2)) f)
                               = map pk_desc_kind (drop (S k) descs))
                 by (rewrite Hdrop; symmetry; exact Htail).
               iEval (rewrite /pk_loop_frame) in "Hfr".
               iDestruct "Hfr" as "(H9 & H10 & H12 & Hva & Hsv & S8 & S19 & S22 & Hap & S24)".
               iDestruct "Hcont" as "[Hhead _]".
               iDestruct (big_sepL_lookup_acc (fun j d => pk_desc_res (pk_vararg m j) d) descs k d0 Hk0
                            with "Hdescs") as "[Hdk0 Hdcl]".
               iApply (wp_printk_arm_str (CID0 := CIDdisp) γd γv m mf K k i l pv pkv dqm dqm2 c0 c1 c2 d0
                         (fmtv ↦ₛ{ dqf } f ∗
                          (pk_desc_res (pk_vararg m k) d0 -∗
                           ([∗ list] j ↦ d ∈ descs, pk_desc_res (pk_vararg m j) d)) ∗
                          (pa_stk sp0 9) ↦₈ (m !!! Regidx ra_idx) ∗
                          (pa_stk sp0 10) ↦₈ (m !!! Regidx s0_idx) ∗
                          (pa_stk sp0 12) ↦₈ (m !!! Regidx s2_idx) ∗
                          pk_saved sp0 (m !!! Regidx (mword_of_int 9 : mword 5)) (m !!! Regidx (mword_of_int 19 : mword 5)) (m !!! Regidx (mword_of_int 20 : mword 5)) (m !!! Regidx (mword_of_int 21 : mword 5)) (m !!! Regidx (mword_of_int 22 : mword 5)) (m !!! Regidx (mword_of_int 23 : mword 5)) (m !!! Regidx (mword_of_int 24 : mword 5)) (m !!! Regidx (mword_of_int 26 : mword 5)) (m !!! Regidx (mword_of_int 27 : mword 5)) ∗
                          (∃ w : mword 64, (pa_stk sp0 8) ↦₈ w) ∗
                          (∃ w : mword 64, (pa_stk sp0 22) ↦₈ w) ∗
                          (∃ w : mword 64, (pa_stk sp0 24) ↦₈ w) ∗
                          pk_loop_head (CID0 := CID0) i l)%I b pcur
                         HK30 Hk7 Hpv Hpkv Hfst Hkd0 Hfs0 Hs1f
                         with "Hcg Htext Hkdata Hpc S19 Hap Hva Hdk0 Hpanicking Hpanicked Hdev Htx Hsent Hdlab [$Hfmt $Hdcl $H9 $H10 $H12 $Hsv $S8 $S22 $S24 $Hhead] [-]").
               iIntros (CIDarm2 Hstarm2 mg bs) "%Hcs2 Hcg Hpc S19 Hap Hva Hdk0 Hpanicking Hpanicked Htx #Hsent2 (Hfmt & Hdcl & H9 & H10 & H12 & Hsv & S8 & S22 & S24 & Hhead)".
               destruct Hcs2 as [Hcs2 Hs1g].
               iDestruct ("Hdcl" with "Hdk0") as "Hdescs".
               pose proof (pk_head_regs mf mg Hcs2 Hfsp Hfs0 Hfs2 Hfs9 Hfconsts)
                 as (Hgsp & Hgs0 & Hgs2 & Hgs9 & Hgconsts).
               iEval (rewrite /pk_loop_head) in "Hhead".
               iSpecialize ("Hhead" $! CIDarm2 with "[%]"); [wp_next_chain|].
               iApply ("Hhead" $! mg (S k) (S i + snd (pk_dir c0 c1 c2))%nat bs
                         with "[%] Hcg Hpc Hfmt Hdescs Hpanicking Hpanicked Htx Hsent2 [-]").
               { split_and!.
                 - lia.
                 - exact Hplt.
                 - replace (S (S i + snd (pk_dir c0 c1 c2)))%nat
                     with (S (S i) + snd (pk_dir c0 c1 c2))%nat by lia.
                   exact Hinv'.
                 - exact Hgsp.
                 - exact Hgs0.
                 - exact Hgs2.
                 - exact Hs1g.
                 - exact Hgs9.
                 - exact Hgconsts. }
               rewrite /pk_loop_frame.
               iFrame "H9 H10 H12 Hva Hsv S8 S19 S22 Hap S24".
          * (* '%%' or an unknown directive: no vararg *)
            rewrite Hfst in Hstep. cbn [pk_cons] in Hstep.
            rewrite Hinv in Hstep.
            assert (Hinv' : pk_kinds (str_drop (S (S i) + snd (pk_dir c0 c1 c2)) f)
                            = map pk_desc_kind (drop k descs)) by (symmetry; exact Hstep).
            assert (Hc0f : Ascii.eqb c0 pk_nul = false)
              by (apply (proj2 (Ascii.eqb_neq c0 pk_nul)); exact Hc0nz).
            iDestruct "Hcont" as "[Hhead _]".
            iApply (wp_printk_arm_none (CID0 := CIDdisp) γd γv mf K i l pv pkv dqm dqm2 c0 c1 c2
                      (fmtv ↦ₛ{ dqf } f ∗
                       ([∗ list] j ↦ d ∈ descs, pk_desc_res (pk_vararg m j) d) ∗
                       pk_loop_frame k ∗ pk_loop_head (CID0 := CID0) i l)%I b pcur
                      HK30 Hpv Hpkv Hfst Hc0f Hs1f
                      with "Hcg Htext Hpc Hpanicking Hpanicked Hdev Htx Hdlab [$Hfmt $Hdescs $Hfr $Hhead] [-]").
            iIntros (CIDarm3 Hstarm3 mg bs) "%Hcs2 Hcg Hpc Hpanicking Hpanicked Htx #Hsent2 (Hfmt & Hdescs & Hfr & Hhead)".
            destruct Hcs2 as [Hcs2 Hs1g].
            pose proof (pk_head_regs mf mg Hcs2 Hfsp Hfs0 Hfs2 Hfs9 Hfconsts)
              as (Hgsp & Hgs0 & Hgs2 & Hgs9 & Hgconsts).
            iEval (rewrite /pk_loop_head) in "Hhead".
            iSpecialize ("Hhead" $! CIDarm3 with "[%]"); [wp_next_chain|].
            iApply ("Hhead" $! mg k (S i + snd (pk_dir c0 c1 c2))%nat bs
                      with "[%] Hcg Hpc Hfmt Hdescs Hpanicking Hpanicked Htx Hsent2 Hfr").
            split_and!.
            -- lia.
            -- exact Hplt.
            -- replace (S (S i + snd (pk_dir c0 c1 c2)))%nat
                 with (S (S i) + snd (pk_dir c0 c1 c2))%nat by lia.
               exact Hinv'.
            -- exact Hgsp.
            -- exact Hgs0.
            -- exact Hgs2.
            -- exact Hs1g.
            -- exact Hgs9.
            -- exact Hgconsts.
      - (* an ordinary character: print it and continue at i *)
        rewrite Hpct in Hstep. cbn [negb] in Hstep.
        rewrite Hstep in Hinv.
        assert (Hne : neq_vec (mq !!! Regidx a0_idx) (mq !!! Regidx (mword_of_int 19 : mword 5)) = true).
        { rewrite Ha0 Hc19 Hfch. unfold neq_vec.
          rewrite (pk_eq_ascii (pk_ch f i) "%"%char (mword_of_int 37)
                     ltac:(apply bv_eq; vm_compute; reflexivity)).
          rewrite Hpct. reflexivity. }
        iDestruct "Hcont" as "[Hhead _]".
        iApply (wp_printk_char γd γv mq K l pv pkv dqm dqm2
                  (fmtv ↦ₛ{ dqf } f ∗
                   ([∗ list] j ↦ d ∈ descs, pk_desc_res (pk_vararg m j) d) ∗
                   pk_loop_frame k ∗ pk_loop_head (CID0 := CID0) i l)%I b pcur
                  HK30 Hpv Hpkv Hne
                  with "Hcg Htext Hpc Hpanicking Hpanicked Hdev Htx Hdlab [$Hfmt $Hdescs $Hfr $Hhead] [-]").
        iIntros (CIDchar Hstchar mk bs) "%Hcs2 Hcg Hpc Hpanicking Hpanicked Htx #Hsent2 (Hfmt & Hdescs & Hfr & Hhead)".
        destruct Hcs2 as [Hcs2 Hs1k].
        pose proof (pk_head_regs mq mk (fun c Hc N9 _ _ => Hcs2 c Hc N9) Hsp Hs0 Hs2 Hs9r Hconsts)
          as (Hgsp & Hgs0 & Hgs2 & Hgs9 & Hgconsts).
        assert (Hs1k' : mk !!! Regidx (mword_of_int 9 : mword 5) = mword_of_int (Z.of_nat i))
          by (rewrite Hs1k; exact Hs4).
        iEval (rewrite /pk_loop_head) in "Hhead".
        iSpecialize ("Hhead" $! CIDchar with "[%]"); [wp_next_chain|].
        iApply ("Hhead" $! mk k i bs with "[%] Hcg Hpc Hfmt Hdescs Hpanicking Hpanicked Htx Hsent2 Hfr").
        split_and!.
        + lia.
        + exact Hilen.
        + exact Hinv.
        + exact Hgsp.
        + exact Hgs0.
        + exact Hgs2.
        + exact Hs1k'.
        + exact Hgs9.
        + exact Hgconsts.
    Qed.

    (* ---------------------------------------------------------------- *)
    (*  THE LOOP, by induction on the fuel [length f - p] at 0x78.       *)
    (* ---------------------------------------------------------------- *)

    Lemma wp_printk_loop78 (n : nat) `{CID0 : CpuId} (mq : regfile) (k p : nat) (l : list (bv 8)) :
      (String.length f - p <= n)%nat ->
      (p < String.length f)%nat ->
      pk_kinds (str_drop (S p) f) = map pk_desc_kind (drop k descs) ->
      mq !!! Regidx csp_rs1 = spd ->
      mq !!! Regidx s0_idx = s0v ->
      mq !!! Regidx s2_idx = fmtv ->
      mq !!! Regidx (mword_of_int 9 : mword 5) = mword_of_int (Z.of_nat p) ->
      mq !!! Regidx (mword_of_int 25 : mword 5) = m !!! Regidx (mword_of_int 25 : mword 5) ->
      pk_consts mq ->
      sie_cap_gpr mq (K - 24)%nat b pcur -∗
      kernel_text -∗ kernel_data -∗
      pc_is (mword_of_int (KernelSyms.printk + 0x78) : mword 64) -∗
      fmtv ↦ₛ{ dqf } f -∗
      ([∗ list] j ↦ d ∈ descs, pk_desc_res (pk_vararg m j) d) -∗
      (mword_of_int KernelSyms.panicking : mword 64) ↦₄{ dqm } pv -∗
      (mword_of_int KernelSyms.panicked : mword 64) ↦₄{ dqm2 } pkv -∗
      dev_inv γd γv -∗ uart_tx_own γd l -∗ uart_sent γd l -∗ uart_dlab_off γd -∗
      pk_loop_frame k -∗
      pk_loop_post l -∗
      WP (Loop : expr riscv_lang).
    Proof using All.
      revert CID0 mq k p l.
      induction n as [|n IH]; intros CID0 mq k p l Hfuel Hplen Hinv Hsp Hs0 Hs2 Hs1 Hs9r Hconsts.
      { exfalso. lia. }
      assert (HK24 : (24 <= K)%nat) by lia.
      iIntros "Hcg #Htext #Hkdata Hpc Hfmt Hdescs Hpanicking Hpanicked #Hdev Htx #Hsent #Hdlab Hfr Hfin".
      assert (Hlen1 : (S p < length (cstring_bytes f))%nat) by (rewrite cstring_bytes_length; lia).
      assert (Hp31 : Z.of_nat p + 1 < 2^31) by (change (2^31) with 2147483648; lia).
      destruct (decide (pk_fbyte f (S p) = (mword_of_int 0 : mword 8))) as [Hz | Hnz].
      - (* the string ends here: 0x24e, restore, epilogue *)
        iApply (wp_printk_advance (CID0 := CID0) mq K fmtv dqf f p
                  (([∗ list] j ↦ d ∈ descs, pk_desc_res (pk_vararg m j) d) ∗
                   (mword_of_int KernelSyms.panicking : mword 64) ↦₄{ dqm } pv ∗
                   (mword_of_int KernelSyms.panicked : mword 64) ↦₄{ dqm2 } pkv ∗
                   uart_tx_own γd l ∗ pk_loop_frame k ∗ pk_loop_post (CID0 := CID0) l)%I b pcur
                  Hlen1 Hp31 Hs1 Hs2
                  with "Hcg Htext Hpc Hfmt [$Hdescs $Hpanicking $Hpanicked $Htx $Hfr $Hfin] [-] []").
        2: { iIntros (CIDd1 Hstd1 mfx) "%Hv Hcg Hpc Hfmt HR". exfalso.
             destruct Hv as (_ & _ & _ & Hnzx). exact (Hnzx Hz). }
        iIntros (CIDe1 Hste1 mfe) "%Hv Hcg Hpc Hfmt (Hdescs & Hpanicking & Hpanicked & Htx & Hfr & Hfin)".
        destruct Hv as [Hkept _].
        pose proof (pk_head_regs mq mfe (pk_adv_regs mq mfe Hkept) Hsp Hs0 Hs2 Hs9r Hconsts)
          as (Hesp & _ & _ & Hes9 & _).
        iEval (rewrite /pk_loop_frame) in "Hfr".
        iDestruct "Hfr" as "(H9 & H10 & H12 & Hva & Hsv & S8 & S19 & S22 & Hap & S24)".
        iDestruct (pk_slots_rest_of (pk_ap s0v k) with "Hva S8 S19 S22 Hap S24") as "Hrest".
        iPoseProof (pk_restore_at_24e with "Htext") as "Hres".
        assert (Hnext : mword_of_int (KernelSyms.printk + 0x24e + 18) = (mword_of_int (KernelSyms.printk + 0x260) : mword 64))
          by (apply bv_eq; vm_compute; reflexivity).
        iApply (wp_printk_exit (CID0 := CIDe1) m mfe K 0x24e pv dqm
                  (fmtv ↦ₛ{ dqf } f ∗
                   ([∗ list] j ↦ d ∈ descs, pk_desc_res (pk_vararg m j) d) ∗
                   (mword_of_int KernelSyms.panicked : mword 64) ↦₄{ dqm2 } pkv ∗
                   uart_tx_own γd l)%I b pcur
                  HK24 Hpv Hesp Hes9 Hnext
                  with "Hcg Htext Hres Hpc H9 H10 H12 Hsv Hrest Hpanicking [$Hfmt $Hdescs $Hpanicked $Htx] [-]").
        iIntros (CIDex Hstex mz) "Hcg Hpc %Hfin2 Hpanicking (Hfmt & Hdescs & Hpanicked & Htx)".
        iEval (rewrite /pk_loop_post) in "Hfin".
        iSpecialize ("Hfin" $! CIDex with "[%]"); [wp_next_chain|].
        iSpecialize ("Hfin" $! mz []).
        iEval (rewrite (app_nil_r l)) in "Hfin".
        iApply ("Hfin" with "Hcg Hpc [%] Hfmt Hdescs Hpanicking Hpanicked Htx Hsent").
        exact Hfin2.
      - (* another character: one turn of the body, then round again by IH *)
        iApply (wp_printk_advance (CID0 := CID0) mq K fmtv dqf f p
                  (([∗ list] j ↦ d ∈ descs, pk_desc_res (pk_vararg m j) d) ∗
                   (mword_of_int KernelSyms.panicking : mword 64) ↦₄{ dqm } pv ∗
                   (mword_of_int KernelSyms.panicked : mword 64) ↦₄{ dqm2 } pkv ∗
                   uart_tx_own γd l ∗ pk_loop_frame k ∗ pk_loop_post (CID0 := CID0) l)%I b pcur
                  Hlen1 Hp31 Hs1 Hs2
                  with "Hcg Htext Hpc Hfmt [$Hdescs $Hpanicking $Hpanicked $Htx $Hfr $Hfin] [] [-]").
        { iIntros (CIDd2 Hstd2 mfx) "%Hv Hcg Hpc Hfmt HR". exfalso.
          destruct Hv as (_ & Hzx). exact (Hnz Hzx). }
        iIntros (CIDadv Hstadv mfg) "%Hv Hcg Hpc Hfmt (Hdescs & Hpanicking & Hpanicked & Htx & Hfr & Hfin)".
        destruct Hv as (Hkept & Hs4g & Ha0g & Hnzg).
        assert (Hilen' : (S p < String.length f)%nat) by (exact (pk_fbyte_nz_lt f (S p) Hlen1 Hnzg)).
        pose proof (pk_head_regs mq mfg (pk_adv_regs mq mfg Hkept) Hsp Hs0 Hs2 Hs9r Hconsts)
          as (Hgsp & Hgs0 & Hgs2 & Hgs9 & Hgconsts).
        iApply (wp_printk_body86 (CID0 := CIDadv) mfg k (S p) l Hilen' Hinv Hgsp Hgs0 Hgs2 Hs4g Ha0g Hgs9 Hgconsts
                  with "Hcg Htext Hkdata Hpc Hfmt Hdescs Hpanicking Hpanicked Hdev Htx Hsent Hdlab Hfr [Hfin]").
        iSplit.
        + (* go round again: the induction hypothesis *)
          rewrite /pk_loop_head.
          iIntros (CIDh Hsth mk k' p' bs) "%Hh Hcg Hpc Hfmt Hdescs Hpanicking Hpanicked Htx #Hsent2 Hfr".
          destruct Hh as (Hip & Hplen' & Hinv' & Hksp & Hks0 & Hks2 & Hks1 & Hks9 & Hkconsts).
          iApply (@IH CIDh mk k' p' ((l ++ bs)%list) ltac:(lia) Hplen' Hinv' Hksp Hks0 Hks2 Hks1 Hks9 Hkconsts
                    with "Hcg Htext Hkdata Hpc Hfmt Hdescs Hpanicking Hpanicked Hdev Htx Hsent2 Hdlab Hfr [Hfin]").
          rewrite /pk_loop_post.
          iIntros (CIDp Hstp mz bs') "Hcg Hpc %Hfin2 Hfmt Hdescs Hpanicking Hpanicked Htx #Hsent3".
          iEval (rewrite /pk_loop_post) in "Hfin".
          iSpecialize ("Hfin" $! CIDp with "[%]"); [wp_next_chain|].
          iSpecialize ("Hfin" $! mz ((bs ++ bs')%list)).
          iEval (rewrite (app_assoc l bs bs')) in "Hfin".
          iApply ("Hfin" with "Hcg Hpc [%] Hfmt Hdescs Hpanicking Hpanicked Htx Hsent3").
          exact Hfin2.
        + iDestruct (wp_next_shift Hstadv with "Hfin") as "Hfin". iExact "Hfin".
    Qed.

  End PrintkLoop.

  (* ================================================================== *)
  (*  THE WHOLE FUNCTION: prologue, setup, loop, exit.                   *)
  (* ================================================================== *)

  Lemma wp_printk_sconf_gen (γd : uart_names) (γv : disk_names)
      (m0 : regfile) (K : nat) (l : list (bv 8)) (pv pkv : mword 32) (dqm dqm2 dqf : dfrac)
      (f : string) (descs : list pk_arg_desc) (b : bool) (p : mword 64)
    : wp_printk_sconf_body γd γv m0 K l pv pkv dqm dqm2 dqf f descs b p.
  Proof using All.
    cbv beta delta [wp_printk_sconf_body].
    intros rai a0i pcE0 ra00 rtgt fmtv0 HK Hflen Hnn Hkinds Hdlen Hpv0 Hpkv0.
    pose proof (pk_cap_bounds K HK) as [HK24 _].
    iIntros "Hcg #Htext #Hkdata Hpc Hfmt Hdescs Hpanicking Hpanicked #Hdev Htx #Hsent #Hdlab Hcont".
    iApply (wp_printk_prologue m0 K b p HK24 with "Hcg Htext Hpc [-]").
    iIntros (CIDpro Hstpro mp) "%Hpro Hcg Hpc H9 H10 H12 Hva Hrest".
    destruct Hpro as (Hpsp & Hps0 & Hps2 & Hpkept).
    destruct (decide (pk_fbyte f 0%nat = (mword_of_int 0 : mword 8))) as [Hf0z | Hf0nz].
    - (* the empty format string: no loop at all, and nothing was printed *)
      iApply (wp_printk_setup (CID0 := CIDpro) m0 mp K pv dqm dqf f
                (([∗ list] j ↦ d ∈ descs, pk_desc_res (pk_vararg m0 j) d) ∗
                 (mword_of_int KernelSyms.panicked : mword 64) ↦₄{ dqm2 } pkv ∗
                 uart_tx_own γd l)%I b p
                HK24 Hpv0 Hnn Hpsp Hps0 Hps2 Hpkept
                with "Hcg Htext Hpc Hpanicking Hfmt H9 H10 H12 Hva Hrest [$Hdescs $Hpanicked $Htx] [-] []").
      2: { iIntros (CIDd1 Hstd1 mq) "%Hb Hcg Hpc Hpanicking Hfmt H9b H10b H12b Hvab Hsvb S8b S19b S22b Hapb S24b HR".
           exfalso. destruct Hb as (_ & _ & _ & _ & _ & Hnzb & _). exact (Hnzb Hf0z). }
      iIntros (CIDse1 Hstse1 mf) "Hcg Hpc %Hz0 %Hfin Hpanicking Hfmt (Hdescs & Hpanicked & Htx)".
      iSpecialize ("Hcont" $! CIDse1 with "[%]"); [wp_next_chain|].
      iSpecialize ("Hcont" $! mf []).
      iEval (rewrite (app_nil_r l)) in "Hcont".
      iApply ("Hcont" with "Hcg Hpc [%] Hfmt Hdescs Hpanicking Hpanicked Htx Hsent").
      exact Hfin.
    - (* a nonempty one: setup, then the loop with the string length as fuel *)
      iApply (wp_printk_setup (CID0 := CIDpro) m0 mp K pv dqm dqf f
                (([∗ list] j ↦ d ∈ descs, pk_desc_res (pk_vararg m0 j) d) ∗
                 (mword_of_int KernelSyms.panicked : mword 64) ↦₄{ dqm2 } pkv ∗
                 uart_tx_own γd l)%I b p
                HK24 Hpv0 Hnn Hpsp Hps0 Hps2 Hpkept
                with "Hcg Htext Hpc Hpanicking Hfmt H9 H10 H12 Hva Hrest [$Hdescs $Hpanicked $Htx] [] [-]").
      { iIntros (CIDd2 Hstd2 mf) "Hcg Hpc %Hz0 %Hfin Hpanicking Hfmt HR". exfalso. exact (Hf0nz Hz0). }
      iIntros (CIDse2 Hstse2 mq) "%Hb Hcg Hpc Hpanicking Hfmt H9 H10 H12 Hva Hsv S8 S19 S22 Hap S24 (Hdescs & Hpanicked & Htx)".
      destruct Hb as (Hqsp & Hqs0 & Hqs2 & Hqs4 & Hqa0 & Hqnz & Hqconsts & Hqkept).
      assert (Hqs4' : mq !!! Regidx (mword_of_int 20 : mword 5) = mword_of_int (Z.of_nat 0)).
      { rewrite Hqs4. apply bv_eq; vm_compute; reflexivity. }
      assert (Hqs9 : mq !!! Regidx (mword_of_int 25 : mword 5) = m0 !!! Regidx (mword_of_int 25 : mword 5))
        by (apply Hqkept; mw_neq).
      assert (Hilen0 : (0 < String.length f)%nat).
      { apply (pk_fbyte_nz_lt f 0%nat); [ rewrite cstring_bytes_length; lia | exact Hqnz ]. }
      assert (Hinv0 : pk_kinds (str_drop 0%nat f) = map pk_desc_kind (drop 0%nat descs))
        by (exact Hkinds).
      assert (Hap0 : add_vec (add_vec (m0 !!! Regidx csp_rs1) (sign_extend' 64 (mword_of_int (-64) : mword 12))) (sign_extend' 64 (mword_of_int 8 : mword 12))
                     = pk_ap (add_vec (m0 !!! Regidx csp_rs1) (sign_extend' 64 (mword_of_int (-64) : mword 12))) 0%nat).
      { unfold pk_ap. apply f_equal. apply bv_eq; vm_compute; reflexivity. }
      iEval (rewrite Hap0) in "Hap".
      iApply (wp_printk_body86 (CID0 := CIDse2) γd γv m0 K pv pkv dqm dqm2 dqf f descs b p
                HK Hflen Hnn Hdlen Hpv0 Hpkv0
                mq 0%nat 0%nat l Hilen0 Hinv0 Hqsp Hqs0 Hqs2 Hqs4' Hqa0 Hqs9 Hqconsts
                with "Hcg Htext Hkdata Hpc Hfmt Hdescs Hpanicking Hpanicked Hdev Htx Hsent Hdlab [H9 H10 H12 Hva Hsv S8 S19 S22 Hap S24] [Hcont]").
      { rewrite /pk_loop_frame. iFrame "H9 H10 H12 Hva Hsv S8 S19 S22 Hap S24". }
      iSplit.
      + (* go round: the loop, with the whole string's length as fuel *)
        rewrite /pk_loop_head.
        iIntros (CIDlh Hstlh mk k' p' bs) "%Hh Hcg Hpc Hfmt Hdescs Hpanicking Hpanicked Htx #Hsent2 Hfr".
        destruct Hh as (_ & Hplen' & Hinv' & Hksp & Hks0 & Hks2 & Hks1 & Hks9 & Hkconsts).
        iApply (wp_printk_loop78 (CID0 := CIDlh) γd γv m0 K pv pkv dqm dqm2 dqf f descs b p
                  HK Hflen Hnn Hdlen Hpv0 Hpkv0
                  (String.length f) mk k' p' ((l ++ bs)%list)
                  ltac:(lia) Hplen' Hinv' Hksp Hks0 Hks2 Hks1 Hks9 Hkconsts
                  with "Hcg Htext Hkdata Hpc Hfmt Hdescs Hpanicking Hpanicked Hdev Htx Hsent2 Hdlab Hfr [Hcont]").
        rewrite /pk_loop_post.
        iIntros (CIDlp Hstlp mz bs') "Hcg Hpc %Hfin2 Hfmt Hdescs Hpanicking Hpanicked Htx #Hsent3".
        iEval (rewrite /pk_loop_post) in "Hcont".
        iSpecialize ("Hcont" $! CIDlp with "[%]"); [wp_next_chain|].
        iSpecialize ("Hcont" $! mz ((bs ++ bs')%list)).
        iEval (rewrite (app_assoc l bs bs')) in "Hcont".
        iApply ("Hcont" with "Hcg Hpc [%] Hfmt Hdescs Hpanicking Hpanicked Htx Hsent3").
        exact Hfin2.
      + (* the first directive already ended the string: e.g. f = "...%" *)
        rewrite /pk_loop_post.
        iIntros (CIDlp2 Hstlp2 mz bs) "Hcg Hpc %Hfin2 Hfmt Hdescs Hpanicking Hpanicked Htx #Hsent3".
        iEval (rewrite /pk_loop_post) in "Hcont".
        iSpecialize ("Hcont" $! CIDlp2 with "[%]"); [wp_next_chain|].
        iApply ("Hcont" $! mz bs with "Hcg Hpc [%] Hfmt Hdescs Hpanicking Hpanicked Htx Hsent3").
        exact Hfin2.
  Qed.

End ProofPrintk.

(* ===================================================================== *)
(* THE SEALED FUNCTOR: instantiate the callees' WP hypotheses with their  *)
(* proven specs, discharging the PRINTK Module Type.                      *)
(* ===================================================================== *)
  Definition wp_printk_sconf `{!riscvGS Σ, !sieG Σ} `{!uartGhostG Σ, !diskGhostG Σ} `{GEN : GenId} `{CID : CpuId}
      (γd : uart_names) (γv : disk_names) (m0 : regfile) (K : nat)
      (l : list (bv 8)) (pv pkv : mword 32) {dqm dqm2 dqf : dfrac}
      (f : string) (descs : list pk_arg_desc) (b : bool) (p : mword 64)
      : wp_printk_sconf_body γd γv m0 K l pv pkv dqm dqm2 dqf f descs b p :=
    wp_printk_sconf_gen
      (fun `{CID0 : CpuId} γd' γv' m' K' l' pv' pkv' dqm' dqm2' b' pcur' =>
         Consputc.wp_consputc_sconf (CID:=CID0) γd' γv' m' K' l' pv' pkv' (dqm:=dqm') (dqm2:=dqm2') b' pcur')
      (fun `{CID0 : CpuId} γd' γv' m' K' l' pv' pkv' dqm' dqm2' b' pcur' =>
         Printint.wp_printint_sconf (CID:=CID0) γd' γv' m' K' l' pv' pkv' (dqm:=dqm') (dqm2:=dqm2') b' pcur')
      γd γv m0 K l pv pkv dqm dqm2 dqf f descs b p.

End PrintkProof.
