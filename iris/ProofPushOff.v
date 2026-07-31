(* ProofPushOff.v: push_off over the SIE-agnostic v2 bundle (stage 8).
   This file holds the SUFFIX (PO+0x18: second mycpu call, the noff
   increment, the epilogue frame-trade and c.ret) -- the shared tail of
   both branch arms -- and (next) the main lemma with the prologue, the
   fused csrrci flip, and the intena arm. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExtras.
Require Import InstrBytes WpMmodeLeafBase.
Require Import RegFile.
Require Import SmodeCore.
Require Import StackOwn CalleeSaved KernelText.
Require Import HartTp WpNext.
Require Import IntrDefs.
Require Import VcGen WpSconfAlu WpSconfMem WpSconfCtl WpSconfBtype WpSconfCsr.
Require Import WpGprCsrwCommon WpIntenaBits KernelRvcDecode KernelBaseDecode WpPushOffCsr WpMycpu SpecMycpu WpPushOffTop WpPopOff.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import ProcGeom CpuOwn.
Require Import WpPushOffBridges.
Require Import SpecPushOff.
Import Defs.


(* +0x24  0x10016073  csrsi sstatus,2 (rd = x0) -- pop_off's intr_on.  Its
   decode is KernelBaseDecode.v's shared [bdec_10016073], stated with the csr
   field as [Ox"100"], which is (delta-)equal to the [csr_sstatus] the CSR
   leaves -- and the [instr] fact below -- are phrased with. *)

(* the epilogue +32 cancels a pa_stk 4 re-anchor (closed offsets). *)
Local Lemma po_up_cancel (X : mword 64) :
  pa_stk (add_vec X (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6)))) 4 = X.
Proof.
  unfold pa_stk, add_vec_int.
  rewrite pa_stk_off2.
  assert (Hz : bv_wrap 64 (uint (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6)) : mword 64)
                           + uint (mword_of_int (- (8 * Z.of_nat 4)) : mword 64)) = 0%Z)
    by (vm_compute; reflexivity).
  rewrite Hz.
  change (add_vec X (mword_of_int 0)) with (add_vec_int X 0).
  apply avi0.
Qed.


Local Lemma addv_zero_l (x : mword 64) : add_vec zero_reg x = x.
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

Local Lemma po_up_cancel16 (X : mword 64) :
  pa_stk (add_vec X (sign_extend' 64 (sign_extend' 12 (mword_of_int 16 : mword 6)))) 2 = X.
Proof.
  unfold pa_stk, add_vec_int.
  rewrite pa_stk_off2.
  assert (Hz : bv_wrap 64 (uint (sign_extend' 64 (sign_extend' 12 (mword_of_int 16 : mword 6)) : mword 64)
                           + uint (mword_of_int (- (8 * Z.of_nat 2)) : mword 64)) = 0%Z)
    by (vm_compute; reflexivity).
  rewrite Hz.
  change (add_vec X (mword_of_int 0)) with (add_vec_int X 0).
  apply avi0.
Qed.


Module PushOffProof (Mycpu : MYCPU) : PUSHOFF.

Section ProofPushOff.
  Context `{!riscvGS Σ, !sieG Σ}.

  Lemma ppi_24 : kernel_text -∗ instr (mword_of_int (PP + 0x24) : mword 64) false
      (CSRImm (csr_sstatus, mword_of_int 2, Regidx (mword_of_int 0), CSRRS)).
  Proof. mk_base (PP + 0x24)%Z (mword_of_int 0x10016073 : mword 32)
    (mword_of_int (PP + 0x24) : mword 64)
    (CSRImm (csr_sstatus, mword_of_int 2, Regidx (mword_of_int 0), CSRRS)) bdec_10016073. Qed.

  (* ------------------------------------------------------------------- *)
  (* pop_off's shared epilogue (PP+0x28..0x2e): restore ra/s0, trade the  *)
  (* 2-slot frame back through the capability, ret.  All three runtime    *)
  (* paths (early-noff, intena=0, post-restore) funnel here.  ORDINARY    *)
  (* b-GENERIC consumer template: threading function, entry b = exit b = *)
  (* the wp_next index b (it never touches sie_arm), but the actual value *)
  (* of b varies across pop_off's THREE call sites (false, false, true    *)
  (* -- the last one only after the restore has already flipped the       *)
  (* resource), so it needs a genuine per-lemma CID binder and the full   *)
  (* fresh-hart-per-leaf template, not the M-mode shortcut.               *)
  (* ------------------------------------------------------------------- *)
  Lemma wp_pop_off_epi_sconf `{CID : CpuId} (Φ : mval -> iProp Σ)
      (M : regfile) (av : nat) (ra0e s00e : mword 64) (b : bool) (p : mword 64) :
    let spd := M !!! Regidx csp_rs1 in
    let sp0up := add_vec spd (sign_extend' 64 (sign_extend' 12 (mword_of_int 16 : mword 6))) in
    let ret_tgt := ret_pc ra0e in
    sie_cap_gpr M av b p -∗
    kernel_text -∗ pc_is (mword_of_int (PP + 0x28) : mword 64) -∗
    add_vec spd (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000"))) ↦₈ ra0e -∗
    add_vec spd (zero_extend' 64 (concat_vec (mword_of_int 0 : mword 6) ('b"000"))) ↦₈ s00e -∗
    wp_next b (fun (CID : CpuId) =>
    ∀ mf,
      sie_cap_gpr mf (av + 2) b p -∗
      pc_is ret_tgt -∗
      ⌜ mf = <[Regidx csp_rs1 := regval_into_reg sp0up]>
             (<[Regidx (mword_of_int 8 : mword 5) := regval_into_reg s00e]>
              (<[Regidx (mword_of_int 1 : mword 5) := regval_into_reg ra0e]> M)) ⌝ -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    intros spd sp0up ret_tgt.
    set (M4 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg ra0e]> M).
    set (M5 := <[Regidx (mword_of_int 8 : mword 5) := regval_into_reg s00e]> M4).
    set (M6 := <[Regidx csp_rs1 := regval_into_reg
        (add_vec (M5 !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 16 : mword 6))))]> M5).
    iIntros "Hcg #Htext Hpc Hp8 Hp0 Hcont".
    iPoseProof (ppi_28 with "Htext") as "Hi28".
    iPoseProof (ppi_2a with "Htext") as "Hi2a".
    iPoseProof (ppi_2c with "Htext") as "Hi2c".
    iPoseProof (ppi_2e with "Htext") as "Hi2e".
    (* ---- 0x28: c.ldsp ra,8(sp) ---- *)
    iApply (wp_cldsp_s_sconf Φ (mword_of_int (PP + 0x28)) (mword_of_int 1 : mword 6) (mword_of_int 1 : mword 5)
              M av ra0e b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi28 Hp8 [-]").
    iIntros (CID1 Hs1) "Hcg Hpc Hp8".
    assert (Hpc2a : add_vec_int (mword_of_int (PP + 0x28) : mword 64) 2 = mword_of_int (PP + 0x2a))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc2a) in "Hpc".
    change (<[Regidx (mword_of_int 1 : mword 5) := regval_into_reg ra0e]> M) with M4.
    (* ---- 0x2a: c.ldsp s0,0(sp) ---- *)
    assert (Hsp4 : M4 !!! Regidx csp_rs1 = spd)
      by (rewrite /M4 upd_ne; [reflexivity | vm_compute; discriminate]).
    iApply (wp_cldsp_s_sconf Φ (mword_of_int (PP + 0x2a)) (mword_of_int 0 : mword 6) (mword_of_int 8 : mword 5)
              M4 av s00e b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi2a [Hp0] [-]").
    { iEval (rewrite Hsp4). iExact "Hp0". }
    iIntros (CID2 Hs2) "Hcg Hpc Hp0".
    assert (Hpc2c : add_vec_int (mword_of_int (PP + 0x2a) : mword 64) 2 = mword_of_int (PP + 0x2c))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc2c) in "Hpc".
    change (<[Regidx (mword_of_int 8 : mword 5) := regval_into_reg s00e]> M4) with M5.
    (* ---- 0x2c: c.addi sp,16 -- the frame trade back ---- *)
    assert (Hsp5 : M5 !!! Regidx csp_rs1 = spd)
      by (rewrite /M5 upd_ne; [exact Hsp4 | vm_compute; discriminate]).
    assert (HM6sp : M6 !!! Regidx csp_rs1 = sp0up).
    { rewrite /M6 upd_eq Hsp5. reflexivity. }
    assert (Hupc : pa_stk sp0up 2 = spd).
    { unfold sp0up. apply po_up_cancel16. }
    assert (Hwv : add_vec (M5 !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 16 : mword 6))) = sp0up).
    { rewrite Hsp5. reflexivity. }
    assert (Hpop : M5 !!! Regidx csp_rs1
                   = pa_stk (add_vec (M5 !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 16 : mword 6)))) 2).
    { rewrite Hwv Hsp5. symmetry. exact Hupc. }
    assert (Hb1u : pa_stk sp0up 1
                    = add_vec spd (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000")))).
    { unfold sp0up, pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb2u : pa_stk sp0up 2
                    = add_vec spd (zero_extend' 64 (concat_vec (mword_of_int 0 : mword 6) ('b"000")))).
    { unfold sp0up, pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    iAssert (stack_own sp0up 2) with "[Hp8 Hp0]" as "Hframe".
    { iApply (stack_own_2_intro with "[Hp8] [Hp0]").
      - iEval (rewrite Hb1u). iExact "Hp8".
      - iEval (rewrite Hb2u -Hsp4). iExact "Hp0". }
    iEval (rewrite -Hwv) in "Hframe".
    iApply (wp_caddi_sp_pop_s_sconf Φ (mword_of_int (PP + 0x2c)) (mword_of_int 16 : mword 6) M5 av 2 b Hpop
              with "Hcg Hpc Hi2c Hframe [-]").
    iIntros (CID3 Hs3) "Hcg Hpc".
    assert (Hpc2e : add_vec_int (mword_of_int (PP + 0x2c) : mword 64) 2 = mword_of_int (PP + 0x2e))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc2e) in "Hpc".
    change (<[Regidx csp_rs1 := regval_into_reg
        (add_vec (M5 !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 16 : mword 6))))]> M5) with M6.
    (* ---- 0x2e: c.ret ---- *)
    assert (HM6ra : M6 !!! Regidx (mword_of_int 1 : mword 5) = ra0e).
    { rewrite /M6 upd_ne; [| vm_compute; discriminate].
      rewrite /M5 upd_ne; [| vm_compute; discriminate].
      rewrite /M4. apply upd_eq. }
    iApply (wp_cret_s_sconf Φ (mword_of_int (PP + 0x2e)) (mword_of_int 1 : mword 5) M6 (av + 2)%nat b
              ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi2e [-]").
    iIntros (CID4 Hs4) "Hcg Hpc".
    iEval (rgne) in "Hpc".
    assert (Hra_final : ret_pc (M6 !!! Regidx (mword_of_int 1 : mword 5)) = ret_tgt)
      by (rewrite HM6ra; reflexivity).
    iEval (rewrite Hra_final) in "Hpc".
    iSpecialize ("Hcont" $! CID4 with "[%]"); [wp_next_chain|].
    iApply ("Hcont" $! M6 with "Hcg Hpc [%]").
    rewrite /M6 /M5 /M4 Hsp5. reflexivity.
  Qed.

  (* ------------------------------------------------------------------- *)
  (* push_off's shared suffix (PO+0x18..0x2a): the second mycpu() call,   *)
  (* the noff increment, the epilogue frame-trade and c.ret.  Runs        *)
  (* ENTIRELY after push_off's csrci has already flipped the resource to  *)
  (* [false], and never re-enables, so -- pop_off-style -- it is stated   *)
  (* at LITERAL [false] (no [b] binder, no [wp_next] wrapper: the         *)
  (* "M-mode / interrupts-off" convention).  [a0v] no longer threads a    *)
  (* caller-supplied [ms !!! Regidx 4 = cid_word] premise (the old        *)
  (* convention): [tp] is pinned, so [mycpu_ret cid_word] is what every   *)
  (* mycpu() call returns, by [rget_tp], with NO premise at all -- the    *)
  (* whole [Ha0cid]/tp-preservation chain the pre-port code carried       *)
  (* through N1..N8/M1..M7 is gone. *)
  Lemma wp_push_off_suffix_sconf `{CID : CpuId} (Φ : mval -> iProp Σ)
      (ms : regfile) (av : nat)
      (noff : mword 32) (ra0e s00e s10e vgap : mword 64) (p : mword 64)
      :
    let P : mword 64 := mword_of_int (PO + 0x18) in
    let spm := ms !!! Regidx csp_rs1 in
    let a0v := mycpu_ret cid_word in
    let a8_noff := add_vec a0v (sign_extend' 64 (mword_of_int 120 : mword 12)) in
    let a8_p24 := add_vec spm (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000"))) in
    let a8_p16 := add_vec spm (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000"))) in
    let a8_p8  := add_vec spm (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000"))) in
    let sp0up := add_vec spm (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))) in
    let noff_a5 := sign_extend' 64 (subrange_vec_dec
        (add_vec (sign_extend' 64 noff) (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6)))) 31 0) in
    let storeval := (autocast (T := mword)
        (subrange_vec_dec noff_a5 (Z.sub (Z.mul 4 8) 1) 0) : mword 32) in
    let cret_tgt := ret_pc ra0e in
    (2 <= av)%nat ->
    sie_cap_gpr ms av false p -∗
    kernel_text -∗ pc_is P -∗
    a8_noff ↦₄ noff -∗
    a8_p24 ↦₈ ra0e -∗
    a8_p16 ↦₈ s00e -∗
    a8_p8 ↦₈ s10e -∗
    spm ↦₈ vgap -∗
    ( pc_is cret_tgt -∗
      (∃ mfin, sie_cap_gpr mfin (av + 4) false p ∗ ⌜ mfin !!! Regidx (mword_of_int 1 : mword 5) = ra0e /\
                                 mfin !!! Regidx (mword_of_int 8 : mword 5) = s00e /\
                                 mfin !!! Regidx (mword_of_int 9 : mword 5) = s10e /\
                                 mfin !!! Regidx csp_rs1 = add_vec spm (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))) /\
                                 mfin !!! Regidx (mword_of_int 18 : mword 5) = ms !!! Regidx (mword_of_int 18 : mword 5) /\
                                 mfin !!! Regidx (mword_of_int 19 : mword 5) = ms !!! Regidx (mword_of_int 19 : mword 5) /\
                                 mfin !!! Regidx (mword_of_int 20 : mword 5) = ms !!! Regidx (mword_of_int 20 : mword 5) /\
                                 mfin !!! Regidx (mword_of_int 21 : mword 5) = ms !!! Regidx (mword_of_int 21 : mword 5) /\
                                 mfin !!! Regidx (mword_of_int 22 : mword 5) = ms !!! Regidx (mword_of_int 22 : mword 5) /\
                                 mfin !!! Regidx (mword_of_int 23 : mword 5) = ms !!! Regidx (mword_of_int 23 : mword 5) /\
                                 mfin !!! Regidx (mword_of_int 24 : mword 5) = ms !!! Regidx (mword_of_int 24 : mword 5) /\
                                 mfin !!! Regidx (mword_of_int 25 : mword 5) = ms !!! Regidx (mword_of_int 25 : mword 5) /\
                                 mfin !!! Regidx (mword_of_int 26 : mword 5) = ms !!! Regidx (mword_of_int 26 : mword 5) /\
                                 mfin !!! Regidx (mword_of_int 27 : mword 5) = ms !!! Regidx (mword_of_int 27 : mword 5) ⌝) -∗
      a8_noff ↦₄ storeval -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    intros P spm a0v a8_noff a8_p24 a8_p16 a8_p8 sp0up noff_a5 storeval cret_tgt Hav.
    set (s00 := ms !!! Regidx (mword_of_int 8 : mword 5)).
    assert (Hm0sp : (<[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int P 4)]> ms) !!! Regidx csp_rs1 = spm)
      by (rewrite upd_ne; [ reflexivity | vm_compute; discriminate ]).
    iIntros "Hcg #Htext Hpc Hnoff Hpp24 Hpp16 Hpp8 Hgap Hcont".
    iPoseProof (poi_18 with "Htext") as "Hi18".
    iApply (Mycpu.wp_call_mycpu_sconf_cs Φ P (mword_of_int 0xcfe : mword 21) ms av p
              ltac:(apply bv_eq; vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
              ltac:(lia)
              with "Hcg Htext Hpc Hi18 [-]").
    iIntros (mo) "Hcg Hpc %Hmo".
    destruct Hmo as [Hmo_cs Hmo_a0].
    destruct Hmo_cs as (Hcsp & Hs0 & Hs1 & Hs2 & Hs3 & Hs4 & Hs5 & Hs6 & Hs7 & Hs8 & Hs9 & Hs10 & Hs11).
    set (M1 := mo).
    set (M2 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (sign_extend' 64 noff)]> M1).
    set (M3 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg
        (sign_extend' 64 (subrange_vec_dec
           (add_vec (M2 !!! Regidx (mword_of_int 15 : mword 5))
              (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6)))) 31 0))]> M2).
    set (M4 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg ra0e]> M3).
    set (M5 := <[Regidx (mword_of_int 8 : mword 5) := regval_into_reg s00e]> M4).
    set (M6 := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg s10e]> M5).
    set (M7 := <[Regidx csp_rs1 := regval_into_reg
        (add_vec (M6 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))))]> M6).
    (* the fixed value every mycpu() call returns, by construction *)
    assert (Hm110 : M1 !!! Regidx (mword_of_int 10 : mword 5) = a0v).
    { rewrite /M1 /a0v Hmo_a0 (rget_tp ms). reflexivity. }
    (* normalise pc = ret_tgt to PO+0x1c *)
    iEval (rewrite upd_eq) in "Hpc".
    assert (Hpc1c : ret_pc (add_vec_int P 4)
                    = (mword_of_int (PO + 0x1c) : mword 64)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc1c) in "Hpc".
    (* ---- 0x1c: c.lw a5,120(a0) : a5 := zext32(noff) ---- *)
    iPoseProof (poi_1c with "Htext") as "Hi1c".
    iApply (wp_clw_s_sconf Φ (mword_of_int (PO + 0x1c)) (mword_of_int 15 : mword 5) (mword_of_int 10 : mword 5)
              (mword_of_int 120 : mword 12) M1 av noff false
 ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi1c [Hnoff] [-]").
    { iEval (rgne). iEval (rewrite Hm110). iExact "Hnoff". }
    rewrite wp_next_off.
    iIntros "Hcg Hpc Hnoff".
    iEval (rgne) in "Hnoff".
    iEval (rewrite Hm110) in "Hnoff".
    assert (Hpc1e : add_vec_int (mword_of_int (PO + 0x1c) : mword 64) 2 = mword_of_int (PO + 0x1e))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc1e) in "Hpc".
    (* ---- 0x1e: c.addiw a5,a5,1 : a5 := sext32(noff+1) ---- *)
    iPoseProof (poi_1e with "Htext") as "Hi1e".
    iApply (wp_caddiw_s_sconf Φ (mword_of_int (PO + 0x1e)) (mword_of_int 15 : mword 5) (mword_of_int 1 : mword 6)
              M2 av false ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi1e [-]").
    rewrite wp_next_off.
    iIntros "Hcg Hpc".
    assert (Hpc20 : add_vec_int (mword_of_int (PO + 0x1e) : mword 64) 2 = mword_of_int (PO + 0x20))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc20) in "Hpc".
    (* ---- 0x20: c.sw a5,120(a0) : store noff+1 ---- *)
    assert (Hm310 : M3 !!! Regidx (mword_of_int 10 : mword 5) = a0v).
    { rewrite /M3. rewrite upd_ne; [| vm_compute; discriminate].
      rewrite /M2. rewrite upd_ne; [| vm_compute; discriminate]. exact Hm110. }
    iPoseProof (poi_20 with "Htext") as "Hi20".
    iApply (wp_csw_s_sconf Φ (mword_of_int (PO + 0x20)) (mword_of_int 15 : mword 5) (mword_of_int 10 : mword 5)
              (mword_of_int 120 : mword 12) M3 av noff false
              with "Hcg Hpc Hi20 [Hnoff] [-]").
    { iEval (rgne). iEval (rewrite Hm310). iExact "Hnoff". }
    rewrite wp_next_off.
    iIntros "Hcg Hpc Hnoff".
    assert (Hpc22 : add_vec_int (mword_of_int (PO + 0x20) : mword 64) 2 = mword_of_int (PO + 0x22))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc22) in "Hpc".
    (* ---- 0x22: c.ldsp ra,24(sp) : ra := ra0e ---- *)
    assert (Hcsp3 : M3 !!! Regidx csp_rs1 = spm).
    { rewrite /M3. rewrite upd_ne; [| vm_compute; discriminate].
      rewrite /M2. rewrite upd_ne; [| vm_compute; discriminate].
      exact Hcsp. }
    iPoseProof (poi_22 with "Htext") as "Hi22".
    iApply (wp_cldsp_s_sconf Φ (mword_of_int (PO + 0x22)) (mword_of_int 3 : mword 6) (mword_of_int 1 : mword 5)
              M3 av ra0e false
 ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi22 [Hpp24] [-]").
    { iEval (rewrite Hcsp3). iExact "Hpp24". }
    rewrite wp_next_off.
    iIntros "Hcg Hpc Hpp24".
    assert (Hpc24 : add_vec_int (mword_of_int (PO + 0x22) : mword 64) 2 = mword_of_int (PO + 0x24))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc24) in "Hpc".
    (* ---- 0x24: c.ldsp s0,16(sp) : s0 := s00e ---- *)
    assert (Hcsp4 : M4 !!! Regidx csp_rs1 = spm).
    { rewrite /M4. rewrite upd_ne; [| vm_compute; discriminate]. exact Hcsp3. }
    iPoseProof (poi_24 with "Htext") as "Hi24".
    iApply (wp_cldsp_s_sconf Φ (mword_of_int (PO + 0x24)) (mword_of_int 2 : mword 6) (mword_of_int 8 : mword 5)
              M4 av s00e false
 ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi24 [Hpp16] [-]").
    { iEval (rewrite Hcsp4). iExact "Hpp16". }
    rewrite wp_next_off.
    iIntros "Hcg Hpc Hpp16".
    assert (Hpc26 : add_vec_int (mword_of_int (PO + 0x24) : mword 64) 2 = mword_of_int (PO + 0x26))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc26) in "Hpc".
    (* ---- 0x26: c.ldsp s1,8(sp) : s1 := s10e ---- *)
    assert (Hcsp5 : M5 !!! Regidx csp_rs1 = spm).
    { rewrite /M5. rewrite upd_ne; [| vm_compute; discriminate]. exact Hcsp4. }
    iPoseProof (poi_26 with "Htext") as "Hi26".
    iApply (wp_cldsp_s_sconf Φ (mword_of_int (PO + 0x26)) (mword_of_int 1 : mword 6) (mword_of_int 9 : mword 5)
              M5 av s10e false
 ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi26 [Hpp8] [-]").
    { iEval (rewrite Hcsp5). iExact "Hpp8". }
    rewrite wp_next_off.
    iIntros "Hcg Hpc Hpp8".
    assert (Hpc28 : add_vec_int (mword_of_int (PO + 0x26) : mword 64) 2 = mword_of_int (PO + 0x28))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc28) in "Hpc".
    (* ---- 0x28: c.addi16sp sp,32 -- the frame trade back ---- *)
    assert (Hcsp6 : M6 !!! Regidx csp_rs1 = spm).
    { rewrite /M6. rewrite upd_ne; [| vm_compute; discriminate].
      rewrite /M5. rewrite upd_ne; [| vm_compute; discriminate].
      rewrite /M4. rewrite upd_ne; [| vm_compute; discriminate].
      exact Hcsp3. }
    assert (HM7sp : M7 !!! Regidx csp_rs1 = sp0up).
    { rewrite /M7. rewrite upd_eq. rewrite Hcsp6. reflexivity. }
    assert (Hupc : pa_stk sp0up 4 = spm).
    { unfold sp0up. apply po_up_cancel. }
    assert (Hwv : add_vec (M6 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))) = sp0up).
    { rewrite Hcsp6. reflexivity. }
    assert (Hpop : M6 !!! Regidx csp_rs1
                   = pa_stk (add_vec (M6 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6)))) 4).
    { rewrite Hwv Hcsp6. symmetry. exact Hupc. }
    assert (Hb1u : pa_stk sp0up 1
                    = add_vec spm (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000")))).
    { unfold sp0up, pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb2u : pa_stk sp0up 2
                    = add_vec spm (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000")))).
    { unfold sp0up, pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb3u : pa_stk sp0up 3
                    = add_vec spm (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000")))).
    { unfold sp0up, pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    iEval (rewrite Hcsp3) in "Hpp24".
    iEval (rewrite Hcsp4) in "Hpp16".
    iEval (rewrite Hcsp5) in "Hpp8".
    iEval (rewrite -Hb1u) in "Hpp24".
    iEval (rewrite -Hb2u) in "Hpp16".
    iEval (rewrite -Hb3u) in "Hpp8".
    iEval (rewrite -Hupc) in "Hgap".
    iAssert (stack_own sp0up 4) with "[Hpp24 Hpp16 Hpp8 Hgap]" as "Hframe4".
    { rewrite stack_own_slots. cbn [seq].
      iSplitL "Hpp24"; [by iExists _ |].
      iSplitL "Hpp16"; [by iExists _ |].
      iSplitL "Hpp8"; [by iExists _ |].
      iSplitL "Hgap"; [by iExists _ |].
      done. }
    iEval (rewrite -Hwv) in "Hframe4".
    iPoseProof (poi_28 with "Htext") as "Hi28".
    iApply (wp_caddi16sp_pop_s_sconf Φ (mword_of_int (PO + 0x28)) (mword_of_int 2 : mword 6) M6 av 4 false Hpop
              with "Hcg Hpc Hi28 Hframe4 [-]").
    rewrite wp_next_off.
    iIntros "Hcg Hpc".
    assert (Hpc2a : add_vec_int (mword_of_int (PO + 0x28) : mword 64) 2 = mword_of_int (PO + 0x2a))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc2a) in "Hpc".
    (* ---- 0x2a: c.ret : PC := ra0e (low bit cleared) ---- *)
    assert (Hra7 : M7 !!! Regidx (mword_of_int 1 : mword 5) = ra0e).
    { rewrite /M7. rewrite upd_ne; [| vm_compute; discriminate].
      rewrite /M6. rewrite upd_ne; [| vm_compute; discriminate].
      rewrite /M5. rewrite upd_ne; [| vm_compute; discriminate].
      rewrite /M4. apply upd_eq. }
    iPoseProof (poi_2a with "Htext") as "Hi2a".
    iApply (wp_cret_s_sconf Φ (mword_of_int (PO + 0x2a)) (mword_of_int 1 : mword 5) M7 (av + 4)%nat false
              ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi2a [-]").
    rewrite wp_next_off.
    iIntros "Hcg Hpc".
    iEval (rgne) in "Hpc".
    iEval (rewrite Hra7) in "Hpc".
    (* ---- convert memory back to the postcondition addresses ---- *)
    assert (Hs00v : (<[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int P 4)]> ms) !!! Regidx (mword_of_int 8 : mword 5) = s00)
      by (rewrite upd_ne; [ reflexivity | vm_compute; discriminate ]).
    assert (HM315 : M3 !!! Regidx (mword_of_int 15 : mword 5) = noff_a5).
    { rewrite /M3 upd_eq /M2 upd_eq. reflexivity. }
    iEval (rgne) in "Hnoff".
    iEval (rgne) in "Hnoff".
    iEval (rewrite Hm310 HM315) in "Hnoff".
    iApply ("Hcont" with "Hpc [Hcg] Hnoff").
    iExists M7. iFrame "Hcg". iPureIntro.
    split; [exact Hra7|].
    repeat split.
    - rewrite /M7. rewrite upd_eq.
      rewrite /M6. rewrite upd_ne; [| vm_compute; discriminate].
      rewrite Hcsp5. reflexivity.
    - (* s2 (x18): never written by the epilogue chain nor by mycpu *)
      rewrite /M7. rewrite upd_ne; [| vm_compute; discriminate].
      rewrite /M6. rewrite upd_ne; [| vm_compute; discriminate].
      rewrite /M5. rewrite upd_ne; [| vm_compute; discriminate].
      rewrite /M4. rewrite upd_ne; [| vm_compute; discriminate].
      rewrite /M3. rewrite upd_ne; [| vm_compute; discriminate].
      rewrite /M2. rewrite upd_ne; [| vm_compute; discriminate].
      exact Hs2.
    - (* s3 (x19) *)
      rewrite /M7. rewrite upd_ne; [| vm_compute; discriminate].
      rewrite /M6. rewrite upd_ne; [| vm_compute; discriminate].
      rewrite /M5. rewrite upd_ne; [| vm_compute; discriminate].
      rewrite /M4. rewrite upd_ne; [| vm_compute; discriminate].
      rewrite /M3. rewrite upd_ne; [| vm_compute; discriminate].
      rewrite /M2. rewrite upd_ne; [| vm_compute; discriminate].
      exact Hs3.
    - (* s4 (x20) *)
      rewrite /M7. rewrite upd_ne; [| vm_compute; discriminate].
      rewrite /M6. rewrite upd_ne; [| vm_compute; discriminate].
      rewrite /M5. rewrite upd_ne; [| vm_compute; discriminate].
      rewrite /M4. rewrite upd_ne; [| vm_compute; discriminate].
      rewrite /M3. rewrite upd_ne; [| vm_compute; discriminate].
      rewrite /M2. rewrite upd_ne; [| vm_compute; discriminate].
      exact Hs4.
    - (* s5 (x21) *)
      rewrite /M7. rewrite upd_ne; [| vm_compute; discriminate].
      rewrite /M6. rewrite upd_ne; [| vm_compute; discriminate].
      rewrite /M5. rewrite upd_ne; [| vm_compute; discriminate].
      rewrite /M4. rewrite upd_ne; [| vm_compute; discriminate].
      rewrite /M3. rewrite upd_ne; [| vm_compute; discriminate].
      rewrite /M2. rewrite upd_ne; [| vm_compute; discriminate].
      exact Hs5.
    - (* s6 (x22) *)
      rewrite /M7. rewrite upd_ne; [| vm_compute; discriminate].
      rewrite /M6. rewrite upd_ne; [| vm_compute; discriminate].
      rewrite /M5. rewrite upd_ne; [| vm_compute; discriminate].
      rewrite /M4. rewrite upd_ne; [| vm_compute; discriminate].
      rewrite /M3. rewrite upd_ne; [| vm_compute; discriminate].
      rewrite /M2. rewrite upd_ne; [| vm_compute; discriminate].
      exact Hs6.
    - (* s7 (x23) *)
      rewrite /M7. rewrite upd_ne; [| vm_compute; discriminate].
      rewrite /M6. rewrite upd_ne; [| vm_compute; discriminate].
      rewrite /M5. rewrite upd_ne; [| vm_compute; discriminate].
      rewrite /M4. rewrite upd_ne; [| vm_compute; discriminate].
      rewrite /M3. rewrite upd_ne; [| vm_compute; discriminate].
      rewrite /M2. rewrite upd_ne; [| vm_compute; discriminate].
      exact Hs7.
    - (* s8 (x24) *)
      rewrite /M7. rewrite upd_ne; [| vm_compute; discriminate].
      rewrite /M6. rewrite upd_ne; [| vm_compute; discriminate].
      rewrite /M5. rewrite upd_ne; [| vm_compute; discriminate].
      rewrite /M4. rewrite upd_ne; [| vm_compute; discriminate].
      rewrite /M3. rewrite upd_ne; [| vm_compute; discriminate].
      rewrite /M2. rewrite upd_ne; [| vm_compute; discriminate].
      exact Hs8.
    - (* s9 (x25) *)
      rewrite /M7. rewrite upd_ne; [| vm_compute; discriminate].
      rewrite /M6. rewrite upd_ne; [| vm_compute; discriminate].
      rewrite /M5. rewrite upd_ne; [| vm_compute; discriminate].
      rewrite /M4. rewrite upd_ne; [| vm_compute; discriminate].
      rewrite /M3. rewrite upd_ne; [| vm_compute; discriminate].
      rewrite /M2. rewrite upd_ne; [| vm_compute; discriminate].
      exact Hs9.
    - (* s10 (x26) *)
      rewrite /M7. rewrite upd_ne; [| vm_compute; discriminate].
      rewrite /M6. rewrite upd_ne; [| vm_compute; discriminate].
      rewrite /M5. rewrite upd_ne; [| vm_compute; discriminate].
      rewrite /M4. rewrite upd_ne; [| vm_compute; discriminate].
      rewrite /M3. rewrite upd_ne; [| vm_compute; discriminate].
      rewrite /M2. rewrite upd_ne; [| vm_compute; discriminate].
      exact Hs10.
    - (* s11 (x27) *)
      rewrite /M7. rewrite upd_ne; [| vm_compute; discriminate].
      rewrite /M6. rewrite upd_ne; [| vm_compute; discriminate].
      rewrite /M5. rewrite upd_ne; [| vm_compute; discriminate].
      rewrite /M4. rewrite upd_ne; [| vm_compute; discriminate].
      rewrite /M3. rewrite upd_ne; [| vm_compute; discriminate].
      rewrite /M2. rewrite upd_ne; [| vm_compute; discriminate].
      exact Hs11.
  Qed.

  (* ------------------------------------------------------------------- *)
  (* push_off itself.  BLOCKED (explicit-cpuid port) -- a confirmed,       *)
  (* central-layer resource-accounting gap, not a consumer-side proof     *)
  (* gap.  Summary (full diagnosis in the porting report):                *)
  (*                                                                       *)
  (* At entry index b = true, the disable instruction (PO+0x0a, csrrci)   *)
  (* must go through WpSconfCsr.wp_csrci_sstatus_s_sconf's b = true       *)
  (* branch, whose precondition demands an intr_count k eb resource       *)
  (* SEPARATE from (not extracted out of, then reassembled back into) the *)
  (* sie_cap_gpr m av true p it also needs to pass whole.  But sie_arm    *)
  (* true p already contains BOTH eighths of the kernel-code token: its   *)
  (* own direct ghost conjunct, and, nested inside cpu_hart 0 true p, the *)
  (* other eighth (intr_count 0 true's own copy) -- and cpu_own n eb p C  *)
  (* true supplies NEITHER (cpu_own_on: only the pure fact plus the frame *)
  (* C).  Verified empirically (a scratch lemma, reproduced in the        *)
  (* report) that sie_arm true p alone cannot yield BOTH a reconstructed  *)
  (* sie_arm true p AND a separate intr_count 0 true: extracting the      *)
  (* arm's nested eighth for the leaf's separate Hcnt, and reassembling a *)
  (* valid arm to still pass as Hcg, both want the identical, single      *)
  (* spare eighth.  No third source exists among SpecPushOff.v's two      *)
  (* premises.  The b = false entry is NOT affected (cpu_own already      *)
  (* supplies intr_count directly there, no flip needed) -- the           *)
  (* obstruction is specific to the generic-b prologue reaching the       *)
  (* disable at b = true.                                                 *)
  (*                                                                       *)
  (* The SAME root cause blocks wp_pop_off_sconf's restore branch below   *)
  (* (WpSconfCsr.wp_csrsi_sstatus_x0_s_sconf's b = false branch wants a    *)
  (* caller-supplied cpu_hart 0 true p PRECONDITION -- i.e. an intr_count  *)
  (* 0 true, ghost-valued '1' -- while the caller's sie_cap_gpr is         *)
  (* STILL at b = false, i.e. its tied half is ghost-valued '0'; holding   *)
  (* both simultaneously is a proven contradiction via two chained         *)
  (* ghost_var_agree steps, so no real caller can ever construct that      *)
  (* precondition honestly).  Left unproven per the STOP-leave-it-clean    *)
  (* instruction rather than forcing something. *)
  Lemma wp_push_off_sconf `{CID : CpuId} (Φ : mval -> iProp Σ)
      (m : regfile) (av : nat)
      (n : nat) (eb : bool) (p : mword 64) (C : iProp Σ) (b : bool)
    : wp_push_off_sconf_body Φ m av n eb p C b.
  Proof.
    cbv beta delta [wp_push_off_sconf_body].
    intros caller_ret Hnbound Hav.
  Abort.

  (* ------------------------------------------------------------------- *)
  (* pop_off over the v2 bundle.  ENTRY IS LITERAL [false] (SpecPushOff's *)
  (* own [wp_pop_off_sconf_body]: [cpu_own (S n) eb p C false] pins the    *)
  (* level at [S n >= 1], hence SIE off, throughout the body -- no        *)
  (* generic-[b] prologue, no arm-crossing puzzle: [cpu_own]'s [false]    *)
  (* arm already IS [cpu_hart (S n) eb p], so every intr_count/cpu_hart    *)
  (* piece the leaves want comes straight off it, exactly as pre-port.    *)
  (* Only the LAST instruction (the csrsi restore, when the count fully   *)
  (* unwinds AND the saved base was enabled) can flip to true, which is   *)
  (* exactly why [wp_next]'s index is [bexit] rather than [false] and     *)
  (* why the shared epilogue -- now b-GENERIC in its own right (see       *)
  (* [wp_pop_off_epi_sconf] above) -- is invoked at literal [false] in    *)
  (* the first two branches and at literal [true] in the restore branch,  *)
  (* whose own internal [wp_next true] discharge is simply forwarded as   *)
  (* pop_off's OWN [wp_next bexit] obligation ([bexit = true] there). *)
  Lemma wp_pop_off_sconf `{CID : CpuId} (Φ : mval -> iProp Σ)
      (m : regfile) (av : nat) (n : nat) (eb : bool) (p : mword 64) (C : iProp Σ)
    : wp_pop_off_sconf_body Φ m av n eb p C.
  Proof.
    cbv beta delta [wp_pop_off_sconf_body].
    intros pcE ret_tgt bexit Hav.
    pose (a0v := mycpu_ret cid_word : mword 64).
    pose (noffv := noff_val (S n) : mword 32).
    pose (intenav := intena_val eb : mword 32).
    set (nv1 := sign_extend' 64 (subrange_vec_dec (add_vec (sign_extend' 64 noffv) (sign_extend' 64 (sign_extend' 12 (mword_of_int 63 : mword 6)))) 31 0)).
    set (storeval := (autocast (T := mword) (subrange_vec_dec nv1 (Z.sub (Z.mul 4 8) 1) 0) : mword 32)).
    set (a_noff := add_vec a0v (sign_extend' 64 (mword_of_int 120 : mword 12))).
    set (a_int := add_vec a0v (sign_extend' 64 (mword_of_int 124 : mword 12))).
    pose (sp0 := (m !!! Regidx csp_rs1 : mword 64)).
    set (spd := add_vec sp0 (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6)))).
    set (P0 := <[Regidx csp_rs1 := regval_into_reg spd]> m).
    set (P1 := <[Regidx (mword_of_int 8 : mword 5) := regval_into_reg
        (add_vec (P0 !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm (mword_of_int 4 : mword 8))))]> P0).
    iIntros "Hcg Hcpu Htcp #Htext Hpc Hcont".
    iEval (rewrite cpu_own_off /cpu_hart /cpu_cells) in "Hcpu".
    iDestruct "Hcpu" as "(((%Hbound & Hnoff & Hint & Hproc) & Hcnt) & HC)".
    assert (Hcoup : neq_vec nv1 zero_reg = false <-> n = 0%nat)
      by (apply pop_nv1_zero_iff; exact Hbound).
    assert (Hnoffpos : zopz0zKzJ_s zero_reg (sign_extend' 64 noffv) = false)
      by (apply pop_noff_pos; exact Hbound).
    iDestruct (intr_count_pos_off with "Hcnt") as "[Htok #Havail]".
    iPoseProof (ppi_00 with "Htext") as "Hi00".
    iPoseProof (ppi_02 with "Htext") as "Hi02".
    iPoseProof (ppi_04 with "Htext") as "Hi04".
    iPoseProof (ppi_06 with "Htext") as "Hi06".
    iPoseProof (ppi_08 with "Htext") as "Hi08".
    iPoseProof (ppi_0c with "Htext") as "Hi0c".
    iPoseProof (ppi_10 with "Htext") as "Hi10".
    iPoseProof (ppi_12 with "Htext") as "Hi12".
    iPoseProof (ppi_14 with "Htext") as "Hi14".
    iPoseProof (ppi_16 with "Htext") as "Hi16".
    iPoseProof (ppi_1a with "Htext") as "Hi1a".
    iPoseProof (ppi_1c with "Htext") as "Hi1c".
    iPoseProof (ppi_1e with "Htext") as "Hi1e".
    assert (Hcsp0 : P0 !!! Regidx csp_rs1 = spd) by (rewrite /P0; apply upd_eq).
    assert (Hspd2 : pa_stk sp0 2 = spd).
    { rewrite /spd. unfold pa_stk, add_vec_int. apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    assert (Hpush : add_vec (m !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6))) = pa_stk (m !!! Regidx csp_rs1) 2).
    { unfold pa_stk, add_vec_int. apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    (* ---- 0x00: c.addi sp,-16 -- the frame push ---- *)
    iApply (wp_caddi_sp_push_s_sconf Φ pcE (mword_of_int 48) m av 2 false
              ltac:(lia) Hpush
              with "Hcg Hpc Hi00 [-]").
    rewrite wp_next_off.
    iIntros "Hcg Hframe Hpc".
    assert (Hpp02 : add_vec_int (pcE : mword 64) 2 = mword_of_int (PP + 0x02)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp02) in "Hpc".
    iDestruct (stack_own_2_elim with "Hframe") as (vr8 vr0) "[Hr8 Hr0]".
    assert (Hb1 : pa_stk sp0 1
                   = add_vec spd (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000")))).
    { rewrite /spd. unfold sp0, pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb2 : pa_stk sp0 2
                   = add_vec spd (zero_extend' 64 (concat_vec (mword_of_int 0 : mword 6) ('b"000")))).
    { rewrite /spd. unfold sp0, pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    (* ---- 0x02: c.sdsp ra,8(sp) ---- *)
    iApply (wp_csdsp_s_sconf Φ (mword_of_int (PP + 0x02)) (mword_of_int 1 : mword 6) (mword_of_int 1 : mword 5)
              P0 (av - 2)%nat vr8 false
              with "Hcg Hpc Hi02 [Hr8] [-]").
    { iEval (rewrite Hcsp0 -Hb1). iExact "Hr8". }
    rewrite wp_next_off.
    iIntros "Hcg Hpc Hr8".
    assert (Hpp04 : add_vec_int (mword_of_int (PP + 0x02) : mword 64) 2 = mword_of_int (PP + 0x04)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp04) in "Hpc".
    (* ---- 0x04: c.sdsp s0,0(sp) ---- *)
    iApply (wp_csdsp_s_sconf Φ (mword_of_int (PP + 0x04)) (mword_of_int 0 : mword 6) (mword_of_int 8 : mword 5)
              P0 (av - 2)%nat vr0 false
              with "Hcg Hpc Hi04 [Hr0] [-]").
    { iEval (rewrite Hcsp0 -Hb2). iExact "Hr0". }
    rewrite wp_next_off.
    iIntros "Hcg Hpc Hr0".
    assert (Hpp06 : add_vec_int (mword_of_int (PP + 0x04) : mword 64) 2 = mword_of_int (PP + 0x06)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp06) in "Hpc".
    (* ---- 0x06: c.addi4spn s0,sp,4 ---- *)
    iApply (wp_caddi4spn_s_sconf Φ (mword_of_int (PP + 0x06)) (Cregidx (mword_of_int 0)) (mword_of_int 4 : mword 8) (mword_of_int 8 : mword 5)
              P0 (av - 2)%nat false
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi06 [-]").
    rewrite wp_next_off.
    iIntros "Hcg Hpc".
    assert (Hpp08 : add_vec_int (mword_of_int (PP + 0x06) : mword 64) 2 = mword_of_int (PP + 0x08)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp08) in "Hpc".
    change (<[Regidx (mword_of_int 8 : mword 5) := regval_into_reg
        (add_vec (P0 !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm (mword_of_int 4 : mword 8))))]> P0) with P1.
    (* ---- 0x08: jal ra,mycpu ---- *)
    assert (Hcsp1 : P1 !!! Regidx csp_rs1 = spd)
      by (rewrite /P1 upd_ne; [exact Hcsp0 | vm_compute; discriminate]).
    iApply (Mycpu.wp_call_mycpu_sconf_cs Φ (mword_of_int (PP + 0x08)) (mword_of_int 0xc94 : mword 21) P1 (av - 2)%nat p
 ltac:(apply bv_eq; vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
              ltac:(lia)
              with "Hcg Htext Hpc Hi08 [-]").
    iIntros (mo) "Hcg Hpc %Hmo".
    set (Cr := mo).
    destruct Hmo as [Hcs Hmo_a0].
    destruct Hcs as (HcspC & Hs0C & Hs1C & Hs2C & Hs3C & Hs4C & Hs5C & Hs6C & Hs7C & Hs8C & Hs9C & Hs10C & Hs11C).
    assert (Ha0C : Cr !!! Regidx (mword_of_int 10 : mword 5) = a0v).
    { rewrite /Cr /a0v Hmo_a0 (rget_tp P1). reflexivity. }
    assert (HcspC' : Cr !!! Regidx csp_rs1 = spd) by (rewrite /Cr HcspC; exact Hcsp1).
    iEval (rewrite upd_eq) in "Hpc".
    assert (Hpc0c : ret_pc (add_vec_int (mword_of_int (PP + 0x08) : mword 64) 4)
                    = (mword_of_int (PP + 0x0c) : mword 64)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc0c) in "Hpc".
    (* ---- 0x0c: csrr a5,sstatus -- the interrupts-off sanity check ---- *)
    iApply (wp_csrr_sstatus_s_sconf Φ (mword_of_int (PP + 0x0c)) (mword_of_int 15 : mword 5) Cr (av - 2)%nat false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi0c [-]").
    rewrite wp_next_off.
    iIntros (msr) "%Hmsfr Hhs Hsc Htr Hpc Hfile Harm".
    set (P3 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (sstatus_read msr)]> Cr).
    iDestruct "Harm" as "[Hstk Hrep]".
    (* [b] is literal [false] at this call (pop_off's own ambient index), so
       the leaf's postcondition already delivers [sie_arm false p] directly
       -- no disjunction to refute (the old ghost_var_agree-vs-Htok dance was
       needed only pre-port, when the arm was an internal [A ∨ B]). *)
    iDestruct "Hrep" as "[%HSIEr Hq0]".
    iAssert (sie_cap P3 (av - 2)%nat false p) with "[Hstk Htr Hq0]" as "Hcapsc".
    { iFrame "Hstk Htr". iExact "Hq0". }
    iDestruct (sie_cap_gpr_join with "Hhs Hsc Hcapsc Hfile") as "Hcg".
    assert (Hsst2 : neq_vec (and_vec (sstatus_read msr)
              (sign_extend' 64 (sign_extend' 12 (mword_of_int 2 : mword 6)))) zero_reg = false).
    { apply pop_sstatus_clear_neq. rewrite HSIEr. vm_compute. reflexivity. }
    assert (Hpc10 : add_vec_int (mword_of_int (PP + 0x0c) : mword 64) 4 = mword_of_int (PP + 0x10)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc10) in "Hpc".
    (* ---- 0x10: c.andi a5,2 ---- *)
    iApply (wp_candi_s_sconf Φ (mword_of_int (PP + 0x10)) (mword_of_int 15 : mword 5) (mword_of_int 2 : mword 6)
              P3 (av - 2)%nat false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi10 [-]").
    rewrite wp_next_off.
    iIntros "Hcg Hpc".
    set (P4 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg
        (and_vec (P3 !!! Regidx (mword_of_int 15 : mword 5))
                 (sign_extend' 64 (sign_extend' 12 (mword_of_int 2 : mword 6))))]> P3).
    change (<[Regidx (mword_of_int 15 : mword 5) := regval_into_reg
        (and_vec (P3 !!! Regidx (mword_of_int 15 : mword 5))
                 (sign_extend' 64 (sign_extend' 12 (mword_of_int 2 : mword 6))))]> P3) with P4.
    assert (Hpc12 : add_vec_int (mword_of_int (PP + 0x10) : mword 64) 2 = mword_of_int (PP + 0x12)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc12) in "Hpc".
    (* ---- 0x12: c.bnez a5 (falls: interrupts are off) ---- *)
    assert (Ha5P4 : P4 !!! Regidx (mword_of_int 15 : mword 5)
                     = and_vec (sstatus_read msr) (sign_extend' 64 (sign_extend' 12 (mword_of_int 2 : mword 6)))).
    { rewrite /P4 upd_eq /P3 upd_eq. reflexivity. }
    iApply (wp_cbnez_fall_s_sconf Φ (mword_of_int (PP + 0x12)) (mword_of_int 15 : mword 8) (Cregidx (mword_of_int 7)) (mword_of_int 15 : mword 5)
              P4 (av - 2)%nat false
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
              ltac:(rgne; rewrite Ha5P4; exact Hsst2)
              with "Hcg Hpc Hi12 [-]").
    rewrite wp_next_off.
    iIntros "Hcg Hpc".
    assert (Hpc14 : add_vec_int (mword_of_int (PP + 0x12) : mword 64) 2 = mword_of_int (PP + 0x14)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc14) in "Hpc".
    (* ---- 0x14: c.lw a5,120(a0) : a5 := noff ---- *)
    assert (Ha0P4 : P4 !!! Regidx (mword_of_int 10 : mword 5) = a0v).
    { rewrite /P4 upd_ne; [| vm_compute; discriminate].
      rewrite /P3 upd_ne; [| vm_compute; discriminate].
      exact Ha0C. }
    iApply (wp_clw_s_sconf Φ (mword_of_int (PP + 0x14)) (mword_of_int 15 : mword 5) (mword_of_int 10 : mword 5)
              (mword_of_int 120 : mword 12) P4 (av - 2)%nat noffv false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi14 [Hnoff] [-]").
    { iEval (rgne). iEval (rewrite Ha0P4). iExact "Hnoff". }
    rewrite wp_next_off.
    iIntros "Hcg Hpc Hnoff".
    set (P5 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (sign_extend' 64 noffv)]> P4).
    change (<[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (sign_extend' 64 noffv)]> P4) with P5.
    assert (Hpc16 : add_vec_int (mword_of_int (PP + 0x14) : mword 64) 2 = mword_of_int (PP + 0x16)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc16) in "Hpc".
    (* ---- 0x16: bge x0,a5 (falls: noff >= 1) ---- *)
    assert (Ha5P5 : P5 !!! Regidx (mword_of_int 15 : mword 5) = sign_extend' 64 noffv)
      by (rewrite /P5; apply upd_eq).
    iApply (wp_bge_x0_fall_s_sconf Φ (mword_of_int (PP + 0x16)) (mword_of_int 0x26 : mword 13) (mword_of_int 15 : mword 5)
              P5 (av - 2)%nat false
              ltac:(vm_compute; discriminate)
              ltac:(rgne; rewrite Ha5P5; exact Hnoffpos)
              with "Hcg Hpc Hi16 [-]").
    rewrite wp_next_off.
    iIntros "Hcg Hpc".
    assert (Hpc1a : add_vec_int (mword_of_int (PP + 0x16) : mword 64) 4 = mword_of_int (PP + 0x1a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc1a) in "Hpc".
    (* ---- 0x1a: c.addiw a5,-1 ---- *)
    iApply (wp_caddiw_s_sconf Φ (mword_of_int (PP + 0x1a)) (mword_of_int 15 : mword 5) (mword_of_int 63 : mword 6)
              P5 (av - 2)%nat false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi1a [-]").
    rewrite wp_next_off.
    iIntros "Hcg Hpc".
    set (P6 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg
        (sign_extend' 64 (subrange_vec_dec
           (add_vec (P5 !!! Regidx (mword_of_int 15 : mword 5))
              (sign_extend' 64 (sign_extend' 12 (mword_of_int 63 : mword 6)))) 31 0))]> P5).
    change (<[Regidx (mword_of_int 15 : mword 5) := regval_into_reg
        (sign_extend' 64 (subrange_vec_dec
           (add_vec (P5 !!! Regidx (mword_of_int 15 : mword 5))
              (sign_extend' 64 (sign_extend' 12 (mword_of_int 63 : mword 6)))) 31 0))]> P5) with P6.
    assert (Hpc1c : add_vec_int (mword_of_int (PP + 0x1a) : mword 64) 2 = mword_of_int (PP + 0x1c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc1c) in "Hpc".
    assert (Ha5P6 : P6 !!! Regidx (mword_of_int 15 : mword 5) = nv1).
    { rewrite /P6 upd_eq Ha5P5. reflexivity. }
    (* ---- 0x1c: c.sw a5,120(a0) : store noff-1 ---- *)
    assert (Ha0P6 : P6 !!! Regidx (mword_of_int 10 : mword 5) = a0v).
    { rewrite /P6 upd_ne; [| vm_compute; discriminate].
      rewrite /P5 upd_ne; [| vm_compute; discriminate].
      exact Ha0P4. }
    iApply (wp_csw_s_sconf Φ (mword_of_int (PP + 0x1c)) (mword_of_int 15 : mword 5) (mword_of_int 10 : mword 5)
              (mword_of_int 120 : mword 12) P6 (av - 2)%nat noffv false
              with "Hcg Hpc Hi1c [Hnoff] [-]").
    { iEval (rgne). iEval (rewrite Ha0P6 -Ha0P4). iExact "Hnoff". }
    rewrite wp_next_off.
    iIntros "Hcg Hpc Hnoff".
    iEval (rgne) in "Hnoff".
    iEval (rgne) in "Hnoff".
    iEval (rewrite Ha0P6 Ha5P6) in "Hnoff".
    assert (Hpc1e : add_vec_int (mword_of_int (PP + 0x1c) : mword 64) 2 = mword_of_int (PP + 0x1e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc1e) in "Hpc".
    (* ---- shared epilogue facts ---- *)
    assert (Hra0P : P0 !!! Regidx (mword_of_int 1 : mword 5) = m !!! Regidx (mword_of_int 1 : mword 5))
      by (rewrite /P0 upd_ne; [reflexivity | vm_compute; discriminate]).
    assert (Hs00P : P0 !!! Regidx (mword_of_int 8 : mword 5) = m !!! Regidx (mword_of_int 8 : mword 5))
      by (rewrite /P0 upd_ne; [reflexivity | vm_compute; discriminate]).
    iEval (rgne) in "Hr8". iEval (rewrite Hcsp0 Hra0P) in "Hr8".
    iEval (rgne) in "Hr0". iEval (rewrite Hcsp0 Hs00P) in "Hr0".
    assert (HcspP6 : P6 !!! Regidx csp_rs1 = spd).
    { rewrite /P6 upd_ne; [| vm_compute; discriminate].
      rewrite /P5 upd_ne; [| vm_compute; discriminate].
      rewrite /P4 upd_ne; [| vm_compute; discriminate].
      rewrite /P3 upd_ne; [| vm_compute; discriminate].
      exact HcspC'. }
    assert (Hsp0up : add_vec spd (sign_extend' 64 (sign_extend' 12 (mword_of_int 16 : mword 6))) = sp0).
    { rewrite /spd /sp0 po_addv_assoc.
      assert (HAB : add_vec (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6)))
                            (sign_extend' 64 (sign_extend' 12 (mword_of_int 16 : mword 6))) = mword_of_int 0)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite HAB. apply avi0. }
    (* ---- 0x1e: c.bnez a5 : noff-1 = 0 ? ---- *)
    destruct (neq_vec nv1 zero_reg) eqn:Hnv.
    - (* noff-1 <> 0: TAKEN to the epilogue at 0x28; no restore.
         bexit reduces to [false] here (n = S n' via Hn0, below). *)
      iApply (wp_cbnez_taken_s_sconf Φ (mword_of_int (PP + 0x1e)) (mword_of_int 5 : mword 8) (Cregidx (mword_of_int 7)) (mword_of_int 15 : mword 5)
                P6 (av - 2)%nat false
                ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
                ltac:(rgne; rewrite Ha5P6; exact Hnv)
                ltac:(vm_compute; reflexivity)
                with "Hcg Hpc Hi1e [-]").
      rewrite wp_next_off.
      iNext.
      iIntros "Hcg Hpc".
      assert (Htgt28 : add_vec (mword_of_int (PP + 0x1e) : mword 64)
                 (sign_extend' 64 (sign_extend' 13 (concat_vec (mword_of_int 5 : mword 8) ('b"0")))) = mword_of_int (PP + 0x28))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Htgt28) in "Hpc".
      assert (Hn0 : n <> 0%nat).
      { intro Hz. pose proof (proj2 Hcoup Hz) as HH. congruence. }
      destruct n as [|n']; [ contradiction |].
      assert (Hbexf : bexit = false) by (rewrite /bexit; reflexivity).
      iEval (rewrite Hbexf wp_next_off) in "Hcont".
      iApply (wp_pop_off_epi_sconf Φ P6 (av - 2)%nat
                (m !!! Regidx (mword_of_int 1 : mword 5)) (m !!! Regidx (mword_of_int 8 : mword 5)) false p
                with "Hcg Htext Hpc [Hr8] [Hr0] [-]").
      { iEval (rewrite HcspP6). iExact "Hr8". }
      { iEval (rewrite HcspP6). iExact "Hr0". }
      rewrite wp_next_off.
      iIntros (mf) "Hcg Hpc %Hmf".
      assert (Hav2 : (av - 2 + 2)%nat = av) by lia.
      iEval (rewrite Hav2) in "Hcg".
      subst mf.
      (* still nested: neq nv1 0 = true, so n = S n'; the token rides
         through un-flipped, repacked one level lower. *)
      iApply ("Hcont" with "Hcg [Hnoff Hint Htok Hproc HC] Hpc [%]").
      { (* cpu_own (S n') eb p C false *)
        rewrite /cpu_own /cpu_hart /cpu_cells.
        iSplitL "Hnoff Hint Htok Hproc".
        { iSplitL "Hnoff Hint Hproc".
          { iSplitR.
            { iPureIntro. rewrite Nat2Z.inj_succ in Hbound |- *. lia. }
            iSplitL "Hnoff".
            { assert (Hdec : noff_val (S n') = storeval).
              { symmetry. rewrite /storeval /nv1. change noffv with (noff_val (S (S n'))).
                apply pop_storeval_pred. exact Hbound. }
              iEval (rewrite Hdec). iExact "Hnoff". }
            iSplitL "Hint". { iExact "Hint". }
            iExact "Hproc". }
          destruct eb.
          - iApply (intr_count_pack_S_on with "Htok Havail").
          - iApply (intr_count_pack_S_off with "Htok"). }
        iExact "HC". }
      unfold callee_saved. repeat split.
      + rewrite upd_eq HcspP6 Hsp0up. reflexivity.
      + do 3 (rewrite upd_ne; [| vm_compute; discriminate]).
        rewrite /P6 upd_ne; [| vm_compute; discriminate].
        rewrite /P5 upd_ne; [| vm_compute; discriminate].
        rewrite /P4 upd_ne; [| vm_compute; discriminate].
        rewrite /P3 upd_ne; [| vm_compute; discriminate].
        rewrite /Cr Hs1C.
        rewrite /P1 upd_ne; [| vm_compute; discriminate].
        rewrite /P0 upd_ne; [| vm_compute; discriminate]. reflexivity.
      + do 3 (rewrite upd_ne; [| vm_compute; discriminate]).
        rewrite /P6 upd_ne; [| vm_compute; discriminate].
        rewrite /P5 upd_ne; [| vm_compute; discriminate].
        rewrite /P4 upd_ne; [| vm_compute; discriminate].
        rewrite /P3 upd_ne; [| vm_compute; discriminate].
        rewrite /Cr Hs2C.
        rewrite /P1 upd_ne; [| vm_compute; discriminate].
        rewrite /P0 upd_ne; [| vm_compute; discriminate]. reflexivity.
      + do 3 (rewrite upd_ne; [| vm_compute; discriminate]).
        rewrite /P6 upd_ne; [| vm_compute; discriminate].
        rewrite /P5 upd_ne; [| vm_compute; discriminate].
        rewrite /P4 upd_ne; [| vm_compute; discriminate].
        rewrite /P3 upd_ne; [| vm_compute; discriminate].
        rewrite /Cr Hs3C.
        rewrite /P1 upd_ne; [| vm_compute; discriminate].
        rewrite /P0 upd_ne; [| vm_compute; discriminate]. reflexivity.
      + do 3 (rewrite upd_ne; [| vm_compute; discriminate]).
        rewrite /P6 upd_ne; [| vm_compute; discriminate].
        rewrite /P5 upd_ne; [| vm_compute; discriminate].
        rewrite /P4 upd_ne; [| vm_compute; discriminate].
        rewrite /P3 upd_ne; [| vm_compute; discriminate].
        rewrite /Cr Hs4C.
        rewrite /P1 upd_ne; [| vm_compute; discriminate].
        rewrite /P0 upd_ne; [| vm_compute; discriminate]. reflexivity.
      + do 3 (rewrite upd_ne; [| vm_compute; discriminate]).
        rewrite /P6 upd_ne; [| vm_compute; discriminate].
        rewrite /P5 upd_ne; [| vm_compute; discriminate].
        rewrite /P4 upd_ne; [| vm_compute; discriminate].
        rewrite /P3 upd_ne; [| vm_compute; discriminate].
        rewrite /Cr Hs5C.
        rewrite /P1 upd_ne; [| vm_compute; discriminate].
        rewrite /P0 upd_ne; [| vm_compute; discriminate]. reflexivity.
      + do 3 (rewrite upd_ne; [| vm_compute; discriminate]).
        rewrite /P6 upd_ne; [| vm_compute; discriminate].
        rewrite /P5 upd_ne; [| vm_compute; discriminate].
        rewrite /P4 upd_ne; [| vm_compute; discriminate].
        rewrite /P3 upd_ne; [| vm_compute; discriminate].
        rewrite /Cr Hs6C.
        rewrite /P1 upd_ne; [| vm_compute; discriminate].
        rewrite /P0 upd_ne; [| vm_compute; discriminate]. reflexivity.
      + do 3 (rewrite upd_ne; [| vm_compute; discriminate]).
        rewrite /P6 upd_ne; [| vm_compute; discriminate].
        rewrite /P5 upd_ne; [| vm_compute; discriminate].
        rewrite /P4 upd_ne; [| vm_compute; discriminate].
        rewrite /P3 upd_ne; [| vm_compute; discriminate].
        rewrite /Cr Hs7C.
        rewrite /P1 upd_ne; [| vm_compute; discriminate].
        rewrite /P0 upd_ne; [| vm_compute; discriminate]. reflexivity.
      + do 3 (rewrite upd_ne; [| vm_compute; discriminate]).
        rewrite /P6 upd_ne; [| vm_compute; discriminate].
        rewrite /P5 upd_ne; [| vm_compute; discriminate].
        rewrite /P4 upd_ne; [| vm_compute; discriminate].
        rewrite /P3 upd_ne; [| vm_compute; discriminate].
        rewrite /Cr Hs8C.
        rewrite /P1 upd_ne; [| vm_compute; discriminate].
        rewrite /P0 upd_ne; [| vm_compute; discriminate]. reflexivity.
      + do 3 (rewrite upd_ne; [| vm_compute; discriminate]).
        rewrite /P6 upd_ne; [| vm_compute; discriminate].
        rewrite /P5 upd_ne; [| vm_compute; discriminate].
        rewrite /P4 upd_ne; [| vm_compute; discriminate].
        rewrite /P3 upd_ne; [| vm_compute; discriminate].
        rewrite /Cr Hs9C.
        rewrite /P1 upd_ne; [| vm_compute; discriminate].
        rewrite /P0 upd_ne; [| vm_compute; discriminate]. reflexivity.
      + do 3 (rewrite upd_ne; [| vm_compute; discriminate]).
        rewrite /P6 upd_ne; [| vm_compute; discriminate].
        rewrite /P5 upd_ne; [| vm_compute; discriminate].
        rewrite /P4 upd_ne; [| vm_compute; discriminate].
        rewrite /P3 upd_ne; [| vm_compute; discriminate].
        rewrite /Cr Hs10C.
        rewrite /P1 upd_ne; [| vm_compute; discriminate].
        rewrite /P0 upd_ne; [| vm_compute; discriminate]. reflexivity.
      + do 3 (rewrite upd_ne; [| vm_compute; discriminate]).
        rewrite /P6 upd_ne; [| vm_compute; discriminate].
        rewrite /P5 upd_ne; [| vm_compute; discriminate].
        rewrite /P4 upd_ne; [| vm_compute; discriminate].
        rewrite /P3 upd_ne; [| vm_compute; discriminate].
        rewrite /Cr Hs11C.
        rewrite /P1 upd_ne; [| vm_compute; discriminate].
        rewrite /P0 upd_ne; [| vm_compute; discriminate]. reflexivity.
    - (* noff-1 = 0: FALL to the intena check at 0x20 *)
      iApply (wp_cbnez_fall_s_sconf Φ (mword_of_int (PP + 0x1e)) (mword_of_int 5 : mword 8) (Cregidx (mword_of_int 7)) (mword_of_int 15 : mword 5)
                P6 (av - 2)%nat false
                ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
                ltac:(rgne; rewrite Ha5P6; exact Hnv)
                with "Hcg Hpc Hi1e [-]").
      rewrite wp_next_off.
      iIntros "Hcg Hpc".
      assert (Hpc20 : add_vec_int (mword_of_int (PP + 0x1e) : mword 64) 2 = mword_of_int (PP + 0x20)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpc20) in "Hpc".
      (* ---- 0x20: c.lw a5,124(a0) : a5 := intena ---- *)
      iPoseProof (ppi_20 with "Htext") as "Hi20".
      iPoseProof (ppi_22 with "Htext") as "Hi22".
      iApply (wp_clw_s_sconf Φ (mword_of_int (PP + 0x20)) (mword_of_int 15 : mword 5) (mword_of_int 10 : mword 5)
                (mword_of_int 124 : mword 12) P6 (av - 2)%nat intenav false
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi20 [Hint] [-]").
      { iEval (rgne). iEval (rewrite Ha0P6). iExact "Hint". }
      rewrite wp_next_off.
      iIntros "Hcg Hpc Hint".
      iEval (rgne) in "Hint".
      iEval (rewrite Ha0P6) in "Hint".
      set (P7 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (sign_extend' 64 intenav)]> P6).
      change (<[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (sign_extend' 64 intenav)]> P6) with P7.
      assert (Hpc22 : add_vec_int (mword_of_int (PP + 0x20) : mword 64) 2 = mword_of_int (PP + 0x22)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpc22) in "Hpc".
      assert (Ha5P7 : P7 !!! Regidx (mword_of_int 15 : mword 5) = sign_extend' 64 intenav)
        by (rewrite /P7; apply upd_eq).
      assert (HcspP7 : P7 !!! Regidx csp_rs1 = spd)
        by (rewrite /P7 upd_ne; [exact HcspP6 | vm_compute; discriminate]).
      (* ---- 0x22: c.beqz a5 : intena = 0 ? ---- *)
      destruct (eq_vec (sign_extend' 64 intenav) zero_reg) eqn:Hie2.
      + (* intena = 0: TAKEN to the epilogue; no restore -- bexit = false *)
        assert (HneqF : neq_vec (sign_extend' 64 intenav) zero_reg = false)
          by (unfold neq_vec; rewrite Hie2; reflexivity).
        iApply (wp_cbeqz_taken_s_sconf Φ (mword_of_int (PP + 0x22)) (mword_of_int 3 : mword 8) (Cregidx (mword_of_int 7)) (mword_of_int 15 : mword 5)
                  P7 (av - 2)%nat false
                  ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
                  ltac:(rgne; rewrite Ha5P7; exact Hie2)
                  ltac:(vm_compute; reflexivity)
                  with "Hcg Hpc Hi22 [-]").
        rewrite wp_next_off.
        iNext.
        iIntros "Hcg Hpc".
        assert (Htgt28' : add_vec (mword_of_int (PP + 0x22) : mword 64)
                   (sign_extend' 64 (sign_extend' 13 (concat_vec (mword_of_int 3 : mword 8) ('b"0")))) = mword_of_int (PP + 0x28))
          by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Htgt28') in "Hpc".
        assert (Hn0B : n = 0%nat) by (apply (proj1 Hcoup); unfold neq_vec in *; congruence).
        subst n.
        assert (Hebf : eb = false).
        { assert (Hie2' : eq_vec (sign_extend' 64 (intena_val eb)) zero_reg = true)
            by (change (intena_val eb) with intenav; exact Hie2).
          pose proof (intena_val_zero eb) as HH. rewrite Hie2' in HH.
          destruct eb; [discriminate HH | reflexivity]. }
        subst eb.
        assert (Hbexf : bexit = false) by (rewrite /bexit; reflexivity).
        iEval (rewrite Hbexf wp_next_off) in "Hcont".
        iApply (wp_pop_off_epi_sconf Φ P7 (av - 2)%nat
                  (m !!! Regidx (mword_of_int 1 : mword 5)) (m !!! Regidx (mword_of_int 8 : mword 5)) false p
                  with "Hcg Htext Hpc [Hr8] [Hr0] [-]").
        { iEval (rewrite HcspP7). iExact "Hr8". }
        { iEval (rewrite HcspP7). iExact "Hr0". }
        rewrite wp_next_off.
        iIntros (mf) "Hcg Hpc %Hmf".
        assert (Hav2 : (av - 2 + 2)%nat = av) by lia.
        iEval (rewrite Hav2) in "Hcg".
        subst mf.
        iApply ("Hcont" with "Hcg [Hnoff Hint Htok Hproc HC] Hpc [%]").
        { rewrite /cpu_own /cpu_hart /cpu_cells.
          iSplitL "Hnoff Hint Htok Hproc".
          { iSplitL "Hnoff Hint Hproc".
            { iSplitR. { iPureIntro. change (Z.of_nat 0) with 0%Z. lia. }
              iSplitL "Hnoff".
              { assert (Hdec : noff_val 0 = storeval).
                { symmetry. rewrite /storeval /nv1. change noffv with (noff_val 1).
                  apply pop_storeval_pred. exact Hbound. }
                iEval (rewrite Hdec). iExact "Hnoff". }
              iSplitL "Hint". { iExists intenav. iExact "Hint". }
              iExact "Hproc". }
            rewrite /intr_count. iExact "Htok". }
          iExact "HC". }
        unfold callee_saved. repeat split.
        * rewrite upd_eq HcspP7 Hsp0up. reflexivity.
        * do 3 (rewrite upd_ne; [| vm_compute; discriminate]).
          rewrite /P7 upd_ne; [| vm_compute; discriminate].
          rewrite /P6 upd_ne; [| vm_compute; discriminate].
          rewrite /P5 upd_ne; [| vm_compute; discriminate].
          rewrite /P4 upd_ne; [| vm_compute; discriminate].
          rewrite /P3 upd_ne; [| vm_compute; discriminate].
          rewrite /Cr Hs1C.
          rewrite /P1 upd_ne; [| vm_compute; discriminate].
          rewrite /P0 upd_ne; [| vm_compute; discriminate]. reflexivity.
        * do 3 (rewrite upd_ne; [| vm_compute; discriminate]).
          rewrite /P7 upd_ne; [| vm_compute; discriminate].
          rewrite /P6 upd_ne; [| vm_compute; discriminate].
          rewrite /P5 upd_ne; [| vm_compute; discriminate].
          rewrite /P4 upd_ne; [| vm_compute; discriminate].
          rewrite /P3 upd_ne; [| vm_compute; discriminate].
          rewrite /Cr Hs2C.
          rewrite /P1 upd_ne; [| vm_compute; discriminate].
          rewrite /P0 upd_ne; [| vm_compute; discriminate]. reflexivity.
        * do 3 (rewrite upd_ne; [| vm_compute; discriminate]).
          rewrite /P7 upd_ne; [| vm_compute; discriminate].
          rewrite /P6 upd_ne; [| vm_compute; discriminate].
          rewrite /P5 upd_ne; [| vm_compute; discriminate].
          rewrite /P4 upd_ne; [| vm_compute; discriminate].
          rewrite /P3 upd_ne; [| vm_compute; discriminate].
          rewrite /Cr Hs3C.
          rewrite /P1 upd_ne; [| vm_compute; discriminate].
          rewrite /P0 upd_ne; [| vm_compute; discriminate]. reflexivity.
        * do 3 (rewrite upd_ne; [| vm_compute; discriminate]).
          rewrite /P7 upd_ne; [| vm_compute; discriminate].
          rewrite /P6 upd_ne; [| vm_compute; discriminate].
          rewrite /P5 upd_ne; [| vm_compute; discriminate].
          rewrite /P4 upd_ne; [| vm_compute; discriminate].
          rewrite /P3 upd_ne; [| vm_compute; discriminate].
          rewrite /Cr Hs4C.
          rewrite /P1 upd_ne; [| vm_compute; discriminate].
          rewrite /P0 upd_ne; [| vm_compute; discriminate]. reflexivity.
        * do 3 (rewrite upd_ne; [| vm_compute; discriminate]).
          rewrite /P7 upd_ne; [| vm_compute; discriminate].
          rewrite /P6 upd_ne; [| vm_compute; discriminate].
          rewrite /P5 upd_ne; [| vm_compute; discriminate].
          rewrite /P4 upd_ne; [| vm_compute; discriminate].
          rewrite /P3 upd_ne; [| vm_compute; discriminate].
          rewrite /Cr Hs5C.
          rewrite /P1 upd_ne; [| vm_compute; discriminate].
          rewrite /P0 upd_ne; [| vm_compute; discriminate]. reflexivity.
        * do 3 (rewrite upd_ne; [| vm_compute; discriminate]).
          rewrite /P7 upd_ne; [| vm_compute; discriminate].
          rewrite /P6 upd_ne; [| vm_compute; discriminate].
          rewrite /P5 upd_ne; [| vm_compute; discriminate].
          rewrite /P4 upd_ne; [| vm_compute; discriminate].
          rewrite /P3 upd_ne; [| vm_compute; discriminate].
          rewrite /Cr Hs6C.
          rewrite /P1 upd_ne; [| vm_compute; discriminate].
          rewrite /P0 upd_ne; [| vm_compute; discriminate]. reflexivity.
        * do 3 (rewrite upd_ne; [| vm_compute; discriminate]).
          rewrite /P7 upd_ne; [| vm_compute; discriminate].
          rewrite /P6 upd_ne; [| vm_compute; discriminate].
          rewrite /P5 upd_ne; [| vm_compute; discriminate].
          rewrite /P4 upd_ne; [| vm_compute; discriminate].
          rewrite /P3 upd_ne; [| vm_compute; discriminate].
          rewrite /Cr Hs7C.
          rewrite /P1 upd_ne; [| vm_compute; discriminate].
          rewrite /P0 upd_ne; [| vm_compute; discriminate]. reflexivity.
        * do 3 (rewrite upd_ne; [| vm_compute; discriminate]).
          rewrite /P7 upd_ne; [| vm_compute; discriminate].
          rewrite /P6 upd_ne; [| vm_compute; discriminate].
          rewrite /P5 upd_ne; [| vm_compute; discriminate].
          rewrite /P4 upd_ne; [| vm_compute; discriminate].
          rewrite /P3 upd_ne; [| vm_compute; discriminate].
          rewrite /Cr Hs8C.
          rewrite /P1 upd_ne; [| vm_compute; discriminate].
          rewrite /P0 upd_ne; [| vm_compute; discriminate]. reflexivity.
        * do 3 (rewrite upd_ne; [| vm_compute; discriminate]).
          rewrite /P7 upd_ne; [| vm_compute; discriminate].
          rewrite /P6 upd_ne; [| vm_compute; discriminate].
          rewrite /P5 upd_ne; [| vm_compute; discriminate].
          rewrite /P4 upd_ne; [| vm_compute; discriminate].
          rewrite /P3 upd_ne; [| vm_compute; discriminate].
          rewrite /Cr Hs9C.
          rewrite /P1 upd_ne; [| vm_compute; discriminate].
          rewrite /P0 upd_ne; [| vm_compute; discriminate]. reflexivity.
        * do 3 (rewrite upd_ne; [| vm_compute; discriminate]).
          rewrite /P7 upd_ne; [| vm_compute; discriminate].
          rewrite /P6 upd_ne; [| vm_compute; discriminate].
          rewrite /P5 upd_ne; [| vm_compute; discriminate].
          rewrite /P4 upd_ne; [| vm_compute; discriminate].
          rewrite /P3 upd_ne; [| vm_compute; discriminate].
          rewrite /Cr Hs10C.
          rewrite /P1 upd_ne; [| vm_compute; discriminate].
          rewrite /P0 upd_ne; [| vm_compute; discriminate]. reflexivity.
        * do 3 (rewrite upd_ne; [| vm_compute; discriminate]).
          rewrite /P7 upd_ne; [| vm_compute; discriminate].
          rewrite /P6 upd_ne; [| vm_compute; discriminate].
          rewrite /P5 upd_ne; [| vm_compute; discriminate].
          rewrite /P4 upd_ne; [| vm_compute; discriminate].
          rewrite /P3 upd_ne; [| vm_compute; discriminate].
          rewrite /Cr Hs11C.
          rewrite /P1 upd_ne; [| vm_compute; discriminate].
          rewrite /P0 upd_ne; [| vm_compute; discriminate]. reflexivity.

      + (* intena <> 0: FALL into the restore -- bexit = eb = true here *)
        assert (HneqT : neq_vec (sign_extend' 64 intenav) zero_reg = true)
          by (unfold neq_vec; rewrite Hie2; reflexivity).
        iApply (wp_cbeqz_fall_s_sconf Φ (mword_of_int (PP + 0x22)) (mword_of_int 3 : mword 8) (Cregidx (mword_of_int 7)) (mword_of_int 15 : mword 5)
                  P7 (av - 2)%nat false
                  ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
                  ltac:(rgne; rewrite Ha5P7; exact Hie2)
                  with "Hcg Hpc Hi22 [-]").
        rewrite wp_next_off.
        iIntros "Hcg Hpc".
        assert (Hpc24 : add_vec_int (mword_of_int (PP + 0x22) : mword 64) 2 = mword_of_int (PP + 0x24)) by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hpc24) in "Hpc".
        assert (Hn0C : n = 0%nat).
        { apply (proj1 Hcoup). unfold neq_vec in *. congruence. }
        subst n.
        assert (Hebt : eb = true).
        { assert (Hie2' : eq_vec (sign_extend' 64 (intena_val eb)) zero_reg = false)
            by (change (intena_val eb) with intenav; exact Hie2).
          pose proof (intena_val_zero eb) as HH. rewrite Hie2' in HH.
          destruct eb; [reflexivity | discriminate HH]. }
        subst eb.
        assert (Htcseq : trap_csrs_pay 0 true = trap_csrs) by reflexivity.
        iEval (rewrite Htcseq) in "Htcp".
        (* ---- 0x24: csrsi sstatus,2 (rd = x0) -- the restore.  BLOCKED: this
           is the SAME central-layer gap documented above wp_push_off_sconf.
           WpSconfCsr.wp_csrsi_sstatus_x0_s_sconf's [b = false] branch (the
           real-restore arm) additionally demands a caller-supplied
           [cpu_hart 0 true p] PRECONDITION -- i.e. an [intr_count 0 true],
           ghost-valued '1' -- to park into the freshly-armed [sie_arm true
           p], handed through UNCHANGED (never consumed by the flip itself,
           which only touches [Hhalf]/[Harm]/[Htok]/[Hqi]).  But at the call
           site the caller's own [sie_cap_gpr ... false p] still carries the
           tied half at '0' (the real CSR has not flipped yet), and
           ghost_var agreement across [Hhalf]/[Harm] forces every ghost
           fraction of this name held here to read '0' too -- so a
           [cpu_hart 0 true p] fraction (valued '1') cannot be held
           simultaneously without a provable contradiction.  No real caller
           can construct this precondition honestly; left unproven. *)
  Abort.

End ProofPushOff.

End PushOffProof.
