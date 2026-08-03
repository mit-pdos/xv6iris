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
Require Import WpGprCsrwCommon WpIntenaBits KernelRvcDecode KernelBaseDecode WpPushOffCsr CodeMycpu SpecMycpu CodePushOff CodePopOff.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import CpuOwn.
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
  Lemma wp_pop_off_epi_sconf `{GEN : GenId} `{CID : CpuId} (Φ : mval -> iProp Σ)
      (M : regfile) (av : nat) (ra0e s00e : mword 64) (b : bool) (p : mword 64) :
    let spd := M !!! Regidx csp_rs1 in
    let sp0up := add_vec spd (sign_extend' 64 (sign_extend' 12 (mword_of_int 16 : mword 6))) in
    let ret_tgt := ret_pc ra0e in
    sie_cap_gpr M av b p -∗
    kernel_text -∗ pc_is (mword_of_int (PP + 0x28) : mword 64) -∗
    add_vec spd (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000"))) ↦₈ ra0e -∗
    add_vec spd (zero_extend' 64 (concat_vec (mword_of_int 0 : mword 6) ('b"000"))) ↦₈ s00e -∗
    wp_next b p (fun (CID : CpuId) =>
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
    iIntros (CID1 Hh1) "Hcg Hpc Hp8".
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
    iIntros (CID2 Hh2) "Hcg Hpc Hp0".
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
    iIntros (CID3 Hh3) "Hcg Hpc".
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
    iIntros (CID4 Hh4) "Hcg Hpc".
    iEval (rgne) in "Hpc".
    assert (Hra_final : ret_pc (M6 !!! Regidx (mword_of_int 1 : mword 5)) = ret_tgt)
      by (rewrite HM6ra; reflexivity).
    iEval (rewrite Hra_final) in "Hpc".
    iSpecialize ("Hcont" $! CID4 with "[%]"); [wp_next_chain|].
    iApply ("Hcont" $! M6 with "Hcg Hpc [%]").
    rewrite /M6 /M5 /M4 Hsp5. reflexivity.
  Qed.

  (* ------------------------------------------------------------------- *)
  (* THE b-GENERIC ENTRY SEAM.  push_off is entered at whatever SIE state  *)
  (* its caller had, so its prologue (PO+0x00..0x08) runs at a generic     *)
  (* [b] and the [csrrci] at PO+0x0a is where the arm is dismantled.       *)
  (* [WpSconfCsr]'s flip leaf takes [intr_count_pre b n eb] and hands back *)
  (* [cpu_cells_pay b p]: at [b = true] the counting token and the per-cpu *)
  (* cells are BOTH inside [sie_arm true p] and [cpu_own] is only the pure *)
  (* fact plus the frame [C], so what goes in is that fact and what comes  *)
  (* out is the freed cells; at [b = false] the token goes in off          *)
  (* [cpu_own] and the cells never move.  These three lemmas are the       *)
  (* consumer side of exactly that, with no case split in the proof body.  *)
  (* ------------------------------------------------------------------- *)
  Lemma po_own_split `{GEN : GenId} `{CIDx : CpuId} (k : nat) (ebx : bool)
      (px : mword 64) (Cx : iProp Σ) (bx : bool) :
    cpu_own k ebx px Cx bx -∗
    ⌜ bx = true -> k = 0%nat /\ ebx = true ⌝ ∗
    intr_count_pre bx k ebx ∗
    (if bx then emp else cpu_cells k ebx px) ∗
    Cx.
  Proof.
    destruct bx.
    - iIntros "[%Hk HC]".
      iSplitR; [ iPureIntro; intros _; exact Hk |].
      iSplitR; [ iPureIntro; exact Hk |].
      iSplitR; [ done | iExact "HC" ].
    - iIntros "[[Hcells Hcnt] HC]".
      iSplitR; [ iPureIntro; discriminate |].
      iSplitL "Hcnt"; [ iExact "Hcnt" |].
      iSplitL "Hcells"; [ iExact "Hcells" | iExact "HC" ].
  Qed.

  (* the cells the flip leaf did NOT free (b = false: the caller's own) have
     to cross the flip instruction itself; at [b = true] there are none, and
     at [b = false] the hart is pinned.  Same two-arm argument as
     [CpuOwn.cpu_own_transport]. *)
  Lemma po_cells_transport (CID0 CID1 : CpuId) (k : nat) (ebx : bool)
      (px : mword 64) (bx : bool) :
    (bx = false \/ px = zero_reg -> (CID1 : CPU) = (CID0 : CPU)) ->
    (if bx then emp else cpu_cells (CID := CID0) k ebx px) -∗
    (if bx then emp else cpu_cells (CID := CID1) k ebx px).
  Proof.
    intros Heq. destruct bx.
    - iIntros "H". iExact "H".
    - rewrite (_ : CID1 = CID0); [ iIntros "$" | exact (Heq (or_introl eq_refl)) ].
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
  Lemma wp_push_off_suffix_sconf `{GEN : GenId} `{CID : CpuId} (Φ : mval -> iProp Σ)
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
    iApply wp_next_off_intro.
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
    iApply wp_next_off_intro.
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
    iApply wp_next_off_intro.
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
    iApply wp_next_off_intro.
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
    iApply wp_next_off_intro.
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
    iApply wp_next_off_intro.
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
    iApply wp_next_off_intro.
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
    iApply wp_next_off_intro.
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
  (* push_off itself.  THE ONE FUNCTION WHOSE PROLOGUE IS GENERIC IN [b]: *)
  (* it is entered at whatever SIE state the caller had, so PO+0x00..0x08 *)
  (* each thread a FRESH hart (CID1..CID5) and the [csrrci] at PO+0x0a is *)
  (* where the arm is dismantled.  Everything the prologue holds across   *)
  (* those five steps is either plain memory (the frame slots) or         *)
  (* [cpu_own], kept FOLDED and moved with [cpu_own_transport]: at        *)
  (* [b = true] it names no hart at all (the cells are in [sie_arm]), at  *)
  (* [b = false] the hart cannot move.  At the flip, [po_own_split] hands *)
  (* the leaf what it needs on each arm ([intr_count_pre]) and            *)
  (* an inline [iAssert] puts the cells back together from the caller's   *)
  (* half and the freed [cpu_cells_pay].  From PO+0x0e on, [b] is LITERALLY    *)
  (* false and every [wp_next] collapses by [wp_next_off].                *)
  (* ------------------------------------------------------------------- *)
  Lemma wp_push_off_sconf `{GEN : GenId} `{CID : CpuId} (Φ : mval -> iProp Σ)
      (m : regfile) (av : nat)
      (n : nat) (eb : bool) (p : mword 64) (C : iProp Σ) (b : bool)
    : wp_push_off_sconf_body Φ m av n eb p C b.
  Proof.
    cbv beta delta [wp_push_off_sconf_body].
    intros caller_ret Hnbound Hav.
    assert (Hbound : (Z.of_nat n < 2 ^ 31)%Z) by (clear - Hnbound; lia).
    pose (noff := noff_val n : mword 32).
    pose (sp0 := (m !!! Regidx csp_rs1 : mword 64)).
    set (spd := add_vec sp0 (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6)))).
    set (N0 := <[Regidx csp_rs1 := regval_into_reg spd]> m).
    set (N1 := <[Regidx (mword_of_int 8 : mword 5) := regval_into_reg
        (add_vec (N0 !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm (mword_of_int 8 : mword 8))))]> N0).
    iIntros "Hcg Hown #Htext Hpc Hcont".
    assert (Hb1 : add_vec spd (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000"))) = pa_stk sp0 1).
    { rewrite /spd. unfold pa_stk, add_vec_int. rewrite !pa_stk_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb2 : add_vec spd (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000"))) = pa_stk sp0 2).
    { rewrite /spd. unfold pa_stk, add_vec_int. rewrite !pa_stk_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb3 : add_vec spd (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000"))) = pa_stk sp0 3).
    { rewrite /spd. unfold pa_stk, add_vec_int. rewrite !pa_stk_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hspd4 : pa_stk sp0 4 = spd).
    { rewrite /spd. unfold pa_stk, add_vec_int. apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    assert (Hcsp0 : N0 !!! Regidx csp_rs1 = spd) by (rewrite /N0; apply upd_eq).
    assert (Hpush : add_vec (m !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))) = pa_stk (m !!! Regidx csp_rs1) 4).
    { unfold pa_stk, add_vec_int. apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    (* ---- 0x00: c.addi sp,-32 -- the frame push ---- *)
    iPoseProof (poi_00 with "Htext") as "Hi00".
    iApply (wp_caddi_sp_push_s_sconf Φ (mword_of_int (PO + 0x00)) (mword_of_int 32 : mword 6) m av 4 b
              ltac:(lia) Hpush
              with "Hcg Hpc Hi00 [-]").
    iIntros (CID1 Hh1) "Hcg Hframe Hpc".
    iEval (rewrite stack_own_slots; cbn [seq]) in "Hframe".
    iDestruct "Hframe" as "(S1 & S2 & S3 & S4 & _)".
    iDestruct "S1" as (vr24) "Hr24".
    iDestruct "S2" as (vr16) "Hr16".
    iDestruct "S3" as (vr8) "Hr8".
    iDestruct "S4" as (vgap) "Hgap".
    iEval (rewrite -Hb1) in "Hr24". iEval (rewrite -Hb2) in "Hr16".
    iEval (rewrite -Hb3) in "Hr8".
    assert (Hpp02 : add_vec_int (mword_of_int (PO + 0x00) : mword 64) 2 = mword_of_int (PO + 0x02)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp02) in "Hpc".
    (* ---- 0x02: c.sdsp ra,24(sp) ---- *)
    iPoseProof (poi_02 with "Htext") as "Hi02".
    iApply (wp_csdsp_s_sconf Φ (mword_of_int (PO + 0x02)) (mword_of_int 3 : mword 6) (mword_of_int 1 : mword 5)
              N0 (av - 4)%nat vr24 b
              with "Hcg Hpc Hi02 [Hr24] [-]").
    { iEval (rewrite Hcsp0). iExact "Hr24". }
    iIntros (CID2 Hh2) "Hcg Hpc Hr24".
    assert (Hpp04 : add_vec_int (mword_of_int (PO + 0x02) : mword 64) 2 = mword_of_int (PO + 0x04)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp04) in "Hpc".
    (* ---- 0x04: c.sdsp s0,16(sp) ---- *)
    iPoseProof (poi_04 with "Htext") as "Hi04".
    iApply (wp_csdsp_s_sconf Φ (mword_of_int (PO + 0x04)) (mword_of_int 2 : mword 6) (mword_of_int 8 : mword 5)
              N0 (av - 4)%nat vr16 b
              with "Hcg Hpc Hi04 [Hr16] [-]").
    { iEval (rewrite Hcsp0). iExact "Hr16". }
    iIntros (CID3 Hh3) "Hcg Hpc Hr16".
    assert (Hpp06 : add_vec_int (mword_of_int (PO + 0x04) : mword 64) 2 = mword_of_int (PO + 0x06)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp06) in "Hpc".
    (* ---- 0x06: c.sdsp s1,8(sp) ---- *)
    iPoseProof (poi_06 with "Htext") as "Hi06".
    iApply (wp_csdsp_s_sconf Φ (mword_of_int (PO + 0x06)) (mword_of_int 1 : mword 6) (mword_of_int 9 : mword 5)
              N0 (av - 4)%nat vr8 b
              with "Hcg Hpc Hi06 [Hr8] [-]").
    { iEval (rewrite Hcsp0). iExact "Hr8". }
    iIntros (CID4 Hh4) "Hcg Hpc Hr8".
    assert (Hpp08 : add_vec_int (mword_of_int (PO + 0x06) : mword 64) 2 = mword_of_int (PO + 0x08)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp08) in "Hpc".
    (* ---- 0x08: c.addi4spn s0,sp,32 ---- *)
    iPoseProof (poi_08 with "Htext") as "Hi08".
    iApply (wp_caddi4spn_s_sconf Φ (mword_of_int (PO + 0x08)) (Cregidx (mword_of_int 0)) (mword_of_int 8 : mword 8) (mword_of_int 8 : mword 5)
              N0 (av - 4)%nat b
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi08 [-]").
    iIntros (CID5 Hh5) "Hcg Hpc".
    assert (Hpp0a : add_vec_int (mword_of_int (PO + 0x08) : mword 64) 2 = mword_of_int (PO + 0x0a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp0a) in "Hpc".
    (* ---- 0x0a: csrrci a5,sstatus,2 -- THE FLIP, and the arm seam ---- *)
    iDestruct (cpu_own_transport CID CID5 n eb p C b ltac:(wp_next_chain) with "Hown") as "Hown".
    iDestruct (po_own_split n eb p C b with "Hown") as "(%Hbon & Hcnt & Hcells0 & HC)".
    iPoseProof (poi_0a with "Htext") as "Hi0a".
    iApply (wp_csrci_sstatus_s_sconf Φ (mword_of_int (PO + 0x0a)) (mword_of_int 15 : mword 5) n eb
              N1 (av - 4)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hcnt Hpc Hi0a [-]").
    iIntros (CID6 Hh6 mstatus0) "%Hmsf %Hsie Hcg Hcnt Htcp Hpay Hpc".
    iDestruct (po_cells_transport CID5 CID6 n eb p b ltac:(wp_next_chain) with "Hcells0") as "Hcells0".
    iSpecialize ("Hcont" $! CID6 with "[%]"); [wp_next_chain|].
    (* THE HART IS PINNED AT CID6 FROM HERE ON (push_off never re-enables),
       so drop the entry hart, the five prologue harts and their conditional
       equalities: with exactly one [CpuId] left in context the ambient
       instance -- and hence [cid_word], [cpu_cells], [rget_tp] -- is
       unambiguous, and the rest of the proof reads hart-free. *)
    iAssert (cpu_cells (CID := CID6) n eb p) with "[Hcells0 Hpay]" as "Hcells".
    { destruct b.
      - destruct (Hbon eq_refl) as [Hn0 Heb0]. rewrite Hn0 Heb0.
        iEval (rewrite cpu_cells_pay_on) in "Hpay". iExact "Hpay".
      - iExact "Hcells0". }
    iDestruct "Hcells" as "(_ & Hnoff & Hint & Hproc)".
    (* from here on b is LITERALLY false *)
    pose (a0f := mycpu_ret cid_word : mword 64).
    set (N2 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (sstatus_read mstatus0)]> N1).
    assert (Hpp0e : add_vec_int (mword_of_int (PO + 0x0a) : mword 64) 4 = mword_of_int (PO + 0x0e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp0e) in "Hpc".
    (* ---- 0x0e: c.mv s1,a5 ---- *)
    iPoseProof (poi_0e with "Htext") as "Hi0e".
    iApply (wp_cmv_s_sconf Φ (mword_of_int (PO + 0x0e)) (mword_of_int 9 : mword 5) (mword_of_int 15 : mword 5)
              N2 (av - 4)%nat false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi0e [-]").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc". iEval (rgne) in "Hcg".
    set (N3 := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg
        (add_vec zero_reg (N2 !!! Regidx (mword_of_int 15 : mword 5)))]> N2).
    change (<[Regidx (mword_of_int 9 : mword 5) := regval_into_reg
        (add_vec zero_reg (N2 !!! Regidx (mword_of_int 15 : mword 5)))]> N2) with N3.
    assert (Hpp10 : add_vec_int (mword_of_int (PO + 0x0e) : mword 64) 2 = mword_of_int (PO + 0x10)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp10) in "Hpc".
    (* ---- 0x10: jal ra,mycpu (jimm=0xd06) ---- *)
    assert (Hcsp3n : N3 !!! Regidx csp_rs1 = spd).
    { rewrite /N3. rewrite upd_ne; [| vm_compute; discriminate].
      rewrite /N2. rewrite upd_ne; [| vm_compute; discriminate].
      rewrite /N1. rewrite upd_ne; [| vm_compute; discriminate]. exact Hcsp0. }
    iPoseProof (poi_10 with "Htext") as "Hi10".
    iApply (Mycpu.wp_call_mycpu_sconf_cs Φ (mword_of_int (PO + 0x10)) (mword_of_int 0xd06 : mword 21) N3 (av - 4)%nat p
              ltac:(apply bv_eq; vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
              ltac:(lia)
              with "Hcg Htext Hpc Hi10 [-]").
    iIntros (mo1) "Hcg Hpc %Hmo4".
    set (N4 := mo1).
    destruct Hmo4 as [Hmo4cs Hmo4a0].
    destruct Hmo4cs as (Hcsp4 & Hs0_4 & Hs1_4 & Hs2_4 & Hs3_4 & Hs4_4 & Hs5_4 & Hs6_4 & Hs7_4 & Hs8_4 & Hs9_4 & Hs10_4 & Hs11_4).
    set (N5 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (sign_extend' 64 noff)]> N4).
    assert (Ha0_10 : N4 !!! Regidx (mword_of_int 10 : mword 5) = a0f).
    { rewrite /N4 /a0f Hmo4a0 (rget_tp N3). reflexivity. }
    iEval (rewrite upd_eq) in "Hpc".
    assert (Hpc14 : ret_pc (add_vec_int (mword_of_int (PO + 0x10) : mword 64) 4)
                    = (mword_of_int (PO + 0x14) : mword 64)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc14) in "Hpc".
    (* ---- 0x14: c.lw a5,120(a0) : a5 := noff ---- *)
    iPoseProof (poi_14 with "Htext") as "Hi14".
    iApply (wp_clw_s_sconf Φ (mword_of_int (PO + 0x14)) (mword_of_int 15 : mword 5) (mword_of_int 10 : mword 5)
              (mword_of_int 120 : mword 12) N4 (av - 4)%nat noff false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi14 [Hnoff] [-]").
    { iEval (rgne). iEval (rewrite Ha0_10). iExact "Hnoff". }
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc Hnoff".
    iEval (rgne) in "Hnoff". iEval (rewrite Ha0_10) in "Hnoff".
    assert (Hpp16 : add_vec_int (mword_of_int (PO + 0x14) : mword 64) 2 = mword_of_int (PO + 0x16)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp16) in "Hpc".
    (* ---- 0x16: c.beqz a5, 0x2c ---- *)
    assert (Ha5 : N5 !!! Regidx (mword_of_int 15 : mword 5) = sign_extend' 64 noff) by (rewrite /N5; apply upd_eq).
    assert (Hv1 : N0 !!! Regidx (mword_of_int 1 : mword 5) = m !!! Regidx (mword_of_int 1 : mword 5))
      by (rewrite /N0; rewrite upd_ne; [ reflexivity | vm_compute; discriminate ]).
    assert (Hv8 : N0 !!! Regidx (mword_of_int 8 : mword 5) = m !!! Regidx (mword_of_int 8 : mword 5))
      by (rewrite /N0; rewrite upd_ne; [ reflexivity | vm_compute; discriminate ]).
    assert (Hv9 : N0 !!! Regidx (mword_of_int 9 : mword 5) = m !!! Regidx (mword_of_int 9 : mword 5))
      by (rewrite /N0; rewrite upd_ne; [ reflexivity | vm_compute; discriminate ]).
    assert (HcspN5 : N5 !!! Regidx csp_rs1 = spd).
    { rewrite /N5. rewrite upd_ne; [| vm_compute; discriminate].
      rewrite Hcsp4. exact Hcsp3n. }
    (* convert held memory to clean addresses/values (shared by both arms) *)
    iEval (rgne) in "Hr24". iEval (rewrite Hcsp0 Hv1) in "Hr24".
    iEval (rgne) in "Hr16". iEval (rewrite Hcsp0 Hv8) in "Hr16".
    iEval (rgne) in "Hr8". iEval (rewrite Hcsp0 Hv9) in "Hr8".
    iPoseProof (poi_16 with "Htext") as "Hi16".
    destruct (eq_vec (sign_extend' 64 noff) zero_reg) eqn:Hcond.
    - (* ===== TAKEN arm: noff == 0 ===== *)
      assert (Hcondf : eq_vec (sign_extend' 64 (noff_val n)) zero_reg = true).
      { change (noff_val n) with noff. exact Hcond. }
      assert (Hn0 : n = 0%nat).
      { pose proof (noff_val_zero n Hbound) as HH. rewrite Hcondf in HH.
        symmetry in HH. apply Nat.eqb_eq in HH. exact HH. }
      subst n.
      iDestruct "Hint" as (iv0) "Hintena".
      iApply (wp_cbeqz_taken_s_sconf Φ (mword_of_int (PO + 0x16)) (mword_of_int 11 : mword 8)
                (Cregidx (mword_of_int 7)) (mword_of_int 15 : mword 5) N5 (av - 4)%nat false
                ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
                ltac:(rgne; rewrite Ha5; exact Hcond)
                ltac:(vm_compute; reflexivity)
                with "Hcg Hpc Hi16 [-]").
      iApply wp_next_off_intro.
      iNext.
      iIntros "Hcg Hpc".
      assert (Htgt2c : add_vec (mword_of_int (PO + 0x16) : mword 64)
                 (sign_extend' 64 (sign_extend' 13 (concat_vec (mword_of_int 11 : mword 8) ('b"0")))) = mword_of_int (PO + 0x2c))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Htgt2c) in "Hpc".
      (* ---- 0x2c: jal ra,mycpu (jimm=0xcea) ---- *)
      iPoseProof (poi_2c with "Htext") as "Hi2c".
      iApply (Mycpu.wp_call_mycpu_sconf_cs Φ (mword_of_int (PO + 0x2c)) (mword_of_int 0xcea : mword 21) N5 (av - 4)%nat p
                ltac:(apply bv_eq; vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                ltac:(lia)
                with "Hcg Htext Hpc Hi2c [-]").
      iIntros (mo2) "Hcg Hpc %Hmo6".
      set (N6 := mo2).
      destruct Hmo6 as [Hmo6cs Hmo6a0].
      destruct Hmo6cs as (Hcsp6 & Hs0_6 & Hs1_6 & Hs2_6 & Hs3_6 & Hs4_6 & Hs5_6 & Hs6_6 & Hs7_6 & Hs8_6 & Hs9_6 & Hs10_6 & Hs11_6).
      assert (Ha0_2c : N6 !!! Regidx (mword_of_int 10 : mword 5) = a0f).
      { rewrite /N6 /a0f Hmo6a0 (rget_tp N5). reflexivity. }
      iEval (rewrite upd_eq) in "Hpc".
      assert (Hpc30 : ret_pc (add_vec_int (mword_of_int (PO + 0x2c) : mword 64) 4)
                      = (mword_of_int (PO + 0x30) : mword 64)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpc30) in "Hpc".
      (* ---- 0x30: srli a5,s1,1 ---- *)
      iPoseProof (poi_30 with "Htext") as "Hi30".
      iApply (wp_srli4_s_sconf Φ (mword_of_int (PO + 0x30)) (mword_of_int 15 : mword 5) (mword_of_int 9 : mword 5)
                (mword_of_int 1 : mword 6) N6 (av - 4)%nat false
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi30 [-]").
      iApply wp_next_off_intro.
      iIntros "Hcg Hpc". iEval (rgne) in "Hcg".
      set (N7 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg
          (shift_bits_right (N6 !!! Regidx (mword_of_int 9 : mword 5))
             (subrange_vec_dec (mword_of_int 1 : mword 6) (Z.sub log2_xlen 1) 0))]> N6).
      change (<[Regidx (mword_of_int 15 : mword 5) := regval_into_reg
          (shift_bits_right (N6 !!! Regidx (mword_of_int 9 : mword 5))
             (subrange_vec_dec (mword_of_int 1 : mword 6) (Z.sub log2_xlen 1) 0))]> N6) with N7.
      assert (Hpc34 : add_vec_int (mword_of_int (PO + 0x30) : mword 64) 4 = mword_of_int (PO + 0x34)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpc34) in "Hpc".
      (* ---- 0x34: andi a5,a5,1 ---- *)
      iPoseProof (poi_34 with "Htext") as "Hi34".
      iApply (wp_candi_s_sconf Φ (mword_of_int (PO + 0x34)) (mword_of_int 15 : mword 5) (mword_of_int 1 : mword 6)
                N7 (av - 4)%nat false
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi34 [-]").
      iApply wp_next_off_intro.
      iIntros "Hcg Hpc". iEval (rgne) in "Hcg".
      set (N8 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg
          (and_vec (N7 !!! Regidx (mword_of_int 15 : mword 5))
             (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6))))]> N7).
      change (<[Regidx (mword_of_int 15 : mword 5) := regval_into_reg
          (and_vec (N7 !!! Regidx (mword_of_int 15 : mword 5))
             (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6))))]> N7) with N8.
      assert (Hpc36 : add_vec_int (mword_of_int (PO + 0x34) : mword 64) 2 = mword_of_int (PO + 0x36)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpc36) in "Hpc".
      assert (Hsv32 : trunc32 (rget N8 (mword_of_int 15 : mword 5)) = po_intena_val mstatus0).
      { rgne. rewrite /N8 upd_eq /N7 upd_eq.
        rewrite Hs1_6 /N5 upd_ne; [| vm_compute; discriminate].
        rewrite Hs1_4 /N3 upd_eq /N2 upd_eq.
        rewrite add_vec_zero_l. reflexivity. }
      (* ---- 0x36: c.sw a5,124(a0) : store intena ---- *)
      assert (Hintaddr : N8 !!! Regidx (mword_of_int 10 : mword 5) = a0f).
      { rewrite /N8. rewrite upd_ne; [| vm_compute; discriminate].
        rewrite /N7. rewrite upd_ne; [| vm_compute; discriminate]. exact Ha0_2c. }
      iPoseProof (poi_36 with "Htext") as "Hi36".
      iApply (wp_csw_s_sconf Φ (mword_of_int (PO + 0x36)) (mword_of_int 15 : mword 5) (mword_of_int 10 : mword 5)
                (mword_of_int 124 : mword 12) N8 (av - 4)%nat iv0 false
                with "Hcg Hpc Hi36 [Hintena] [-]").
      { iEval (rgne). iEval (rewrite Hintaddr). iExact "Hintena". }
      iApply wp_next_off_intro.
      iIntros "Hcg Hpc Hintena".
      iEval (rgne) in "Hintena". iEval (rewrite Hintaddr) in "Hintena".
      iEval (rewrite Hsv32) in "Hintena".
      assert (Hpc38 : add_vec_int (mword_of_int (PO + 0x36) : mword 64) 2 = mword_of_int (PO + 0x38)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpc38) in "Hpc".
      (* ---- 0x38: c.j 0xbd8 ---- *)
      iPoseProof (poi_38 with "Htext") as "Hi38".
      iApply (wp_cj_s_sconf Φ (mword_of_int (PO + 0x38)) (sign_extend' 21 (concat_vec (mword_of_int 2032 : mword 11) ('b"0")))
                N8 (av - 4)%nat false
                ltac:(vm_compute; reflexivity)
                with "Hcg Hpc Hi38 [-]").
      iApply wp_next_off_intro.
      iNext.
      iIntros "Hcg Hpc".
      assert (Htgt18t : add_vec (mword_of_int (PO + 0x38) : mword 64)
                 (sign_extend' 64 (sign_extend' 21 (concat_vec (mword_of_int 2032 : mword 11) ('b"0")))) = mword_of_int (PO + 0x18))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Htgt18t) in "Hpc".
      assert (HcspN8 : N8 !!! Regidx csp_rs1 = spd).
      { rewrite /N8. rewrite upd_ne; [| vm_compute; discriminate].
        rewrite /N7. rewrite upd_ne; [| vm_compute; discriminate].
        rewrite Hcsp6. exact HcspN5. }
      (* ---- apply the suffix with ms = N8 ---- *)
      iApply (wp_push_off_suffix_sconf Φ N8 (av - 4)%nat noff
                (m !!! Regidx (mword_of_int 1 : mword 5)) (m !!! Regidx (mword_of_int 8 : mword 5)) (m !!! Regidx (mword_of_int 9 : mword 5)) vgap p
                ltac:(lia)
                with "Hcg Htext Hpc [Hnoff] [Hr24] [Hr16] [Hr8] [Hgap] [-]").
      { iExact "Hnoff". }
      { iEval (rewrite HcspN8). iExact "Hr24". }
      { iEval (rewrite HcspN8). iExact "Hr16". }
      { iEval (rewrite HcspN8). iExact "Hr8". }
      { iEval (rewrite HcspN8 -Hspd4). iExact "Hgap". }
      iIntros "Hpc Hmfin Hnoff".
      iDestruct "Hmfin" as (mfin) "(Hcg & %Hp)".
      destruct Hp as (Hra & Hs0 & Hs1 & Hsp & Hs2 & Hs3 & Hs4 & Hs5 & Hs6 & Hs7 & Hs8 & Hs9 & Hs10 & Hs11).
      assert (Hav4 : (av - 4 + 4)%nat = av) by lia.
      iEval (rewrite Hav4) in "Hcg".
      iApply ("Hcont" $! mstatus0 mfin with "[%] Hcg [Hnoff Hintena Hcnt Hproc HC] Htcp Hpc [%]").
      { exact Hmsf. }
      { (* cpu_own (S 0) eb p C false *)
        rewrite /cpu_own /cpu_hart /cpu_cells.
        iSplitL "Hnoff Hintena Hcnt Hproc".
        { iSplitL "Hnoff Hintena Hproc".
          { iSplitR. { iPureIntro. change (Z.of_nat (S 0)) with 1%Z. lia. }
            iSplitL "Hnoff".
            { assert (Hstore1 : (autocast (T := mword) (subrange_vec_dec (sign_extend' 64 (subrange_vec_dec (add_vec (sign_extend' 64 noff) (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6)))) 31 0)) (Z.sub (Z.mul 4 8) 1) 0) : mword 32) = noff_val (S 0)).
              { change noff with (noff_val 0). apply push_storeval_succ. change (Z.of_nat 0) with 0%Z. lia. }
              iEval (rewrite Hstore1) in "Hnoff". iExact "Hnoff". }
            iSplitL "Hintena".
            { assert (Hival : intena_val eb = po_intena_val mstatus0).
              { symmetry. apply po_intena_val_bridge. apply Hsie. reflexivity. }
              iEval (rewrite Hival). iExact "Hintena". }
            iExact "Hproc". }
          iExact "Hcnt". }
        iExact "HC". }
      { unfold callee_saved. repeat split.
      - (* sp *)
        rewrite Hsp HcspN8 /spd /sp0 po_addv_assoc.
        assert (HAB : add_vec (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6)))
                              (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))) = mword_of_int 0)
          by (apply bv_eq; vm_compute; reflexivity).
        rewrite HAB. apply avi0.
      - (* s0 *) exact Hs0.
      - (* s1 *) exact Hs1.
      - (* s2 *)
        rewrite Hs2.
        rewrite /N8 upd_ne; [| vm_compute; discriminate].
        rewrite /N7 upd_ne; [| vm_compute; discriminate].
        rewrite Hs2_6.
        rewrite /N5 upd_ne; [| vm_compute; discriminate].
        rewrite Hs2_4.
        rewrite /N3 upd_ne; [| vm_compute; discriminate].
        rewrite /N2 upd_ne; [| vm_compute; discriminate].
        rewrite /N1 upd_ne; [| vm_compute; discriminate].
        rewrite /N0 upd_ne; [| vm_compute; discriminate].
        reflexivity.
      - (* s3 *)
        rewrite Hs3.
        rewrite /N8 upd_ne; [| vm_compute; discriminate].
        rewrite /N7 upd_ne; [| vm_compute; discriminate].
        rewrite Hs3_6.
        rewrite /N5 upd_ne; [| vm_compute; discriminate].
        rewrite Hs3_4.
        rewrite /N3 upd_ne; [| vm_compute; discriminate].
        rewrite /N2 upd_ne; [| vm_compute; discriminate].
        rewrite /N1 upd_ne; [| vm_compute; discriminate].
        rewrite /N0 upd_ne; [| vm_compute; discriminate].
        reflexivity.
      - (* s4 *)
        rewrite Hs4.
        rewrite /N8 upd_ne; [| vm_compute; discriminate].
        rewrite /N7 upd_ne; [| vm_compute; discriminate].
        rewrite Hs4_6.
        rewrite /N5 upd_ne; [| vm_compute; discriminate].
        rewrite Hs4_4.
        rewrite /N3 upd_ne; [| vm_compute; discriminate].
        rewrite /N2 upd_ne; [| vm_compute; discriminate].
        rewrite /N1 upd_ne; [| vm_compute; discriminate].
        rewrite /N0 upd_ne; [| vm_compute; discriminate].
        reflexivity.
      - (* s5 *)
        rewrite Hs5.
        rewrite /N8 upd_ne; [| vm_compute; discriminate].
        rewrite /N7 upd_ne; [| vm_compute; discriminate].
        rewrite Hs5_6.
        rewrite /N5 upd_ne; [| vm_compute; discriminate].
        rewrite Hs5_4.
        rewrite /N3 upd_ne; [| vm_compute; discriminate].
        rewrite /N2 upd_ne; [| vm_compute; discriminate].
        rewrite /N1 upd_ne; [| vm_compute; discriminate].
        rewrite /N0 upd_ne; [| vm_compute; discriminate].
        reflexivity.
      - (* s6 *)
        rewrite Hs6.
        rewrite /N8 upd_ne; [| vm_compute; discriminate].
        rewrite /N7 upd_ne; [| vm_compute; discriminate].
        rewrite Hs6_6.
        rewrite /N5 upd_ne; [| vm_compute; discriminate].
        rewrite Hs6_4.
        rewrite /N3 upd_ne; [| vm_compute; discriminate].
        rewrite /N2 upd_ne; [| vm_compute; discriminate].
        rewrite /N1 upd_ne; [| vm_compute; discriminate].
        rewrite /N0 upd_ne; [| vm_compute; discriminate].
        reflexivity.
      - (* s7 *)
        rewrite Hs7.
        rewrite /N8 upd_ne; [| vm_compute; discriminate].
        rewrite /N7 upd_ne; [| vm_compute; discriminate].
        rewrite Hs7_6.
        rewrite /N5 upd_ne; [| vm_compute; discriminate].
        rewrite Hs7_4.
        rewrite /N3 upd_ne; [| vm_compute; discriminate].
        rewrite /N2 upd_ne; [| vm_compute; discriminate].
        rewrite /N1 upd_ne; [| vm_compute; discriminate].
        rewrite /N0 upd_ne; [| vm_compute; discriminate].
        reflexivity.
      - (* s8 *)
        rewrite Hs8.
        rewrite /N8 upd_ne; [| vm_compute; discriminate].
        rewrite /N7 upd_ne; [| vm_compute; discriminate].
        rewrite Hs8_6.
        rewrite /N5 upd_ne; [| vm_compute; discriminate].
        rewrite Hs8_4.
        rewrite /N3 upd_ne; [| vm_compute; discriminate].
        rewrite /N2 upd_ne; [| vm_compute; discriminate].
        rewrite /N1 upd_ne; [| vm_compute; discriminate].
        rewrite /N0 upd_ne; [| vm_compute; discriminate].
        reflexivity.
      - (* s9 *)
        rewrite Hs9.
        rewrite /N8 upd_ne; [| vm_compute; discriminate].
        rewrite /N7 upd_ne; [| vm_compute; discriminate].
        rewrite Hs9_6.
        rewrite /N5 upd_ne; [| vm_compute; discriminate].
        rewrite Hs9_4.
        rewrite /N3 upd_ne; [| vm_compute; discriminate].
        rewrite /N2 upd_ne; [| vm_compute; discriminate].
        rewrite /N1 upd_ne; [| vm_compute; discriminate].
        rewrite /N0 upd_ne; [| vm_compute; discriminate].
        reflexivity.
      - (* s10 *)
        rewrite Hs10.
        rewrite /N8 upd_ne; [| vm_compute; discriminate].
        rewrite /N7 upd_ne; [| vm_compute; discriminate].
        rewrite Hs10_6.
        rewrite /N5 upd_ne; [| vm_compute; discriminate].
        rewrite Hs10_4.
        rewrite /N3 upd_ne; [| vm_compute; discriminate].
        rewrite /N2 upd_ne; [| vm_compute; discriminate].
        rewrite /N1 upd_ne; [| vm_compute; discriminate].
        rewrite /N0 upd_ne; [| vm_compute; discriminate].
        reflexivity.
      - (* s11 *)
        rewrite Hs11.
        rewrite /N8 upd_ne; [| vm_compute; discriminate].
        rewrite /N7 upd_ne; [| vm_compute; discriminate].
        rewrite Hs11_6.
        rewrite /N5 upd_ne; [| vm_compute; discriminate].
        rewrite Hs11_4.
        rewrite /N3 upd_ne; [| vm_compute; discriminate].
        rewrite /N2 upd_ne; [| vm_compute; discriminate].
        rewrite /N1 upd_ne; [| vm_compute; discriminate].
        rewrite /N0 upd_ne; [| vm_compute; discriminate].
        reflexivity. }
    - (* ===== FALL arm: noff <> 0 ===== *)
      destruct n as [|n'].
      { exfalso. pose proof (noff_val_zero 0 Hbound) as HH.
        change (noff_val 0) with noff in HH. rewrite Hcond in HH. discriminate HH. }
      iRename "Hint" into "Hintena".
      iApply (wp_cbeqz_fall_s_sconf Φ (mword_of_int (PO + 0x16)) (mword_of_int 11 : mword 8)
                (Cregidx (mword_of_int 7)) (mword_of_int 15 : mword 5) N5 (av - 4)%nat false
                ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
                ltac:(rgne; rewrite Ha5; exact Hcond)
                with "Hcg Hpc Hi16 [-]").
      iApply wp_next_off_intro.
      iIntros "Hcg Hpc".
      assert (Hpc18 : add_vec_int (mword_of_int (PO + 0x16) : mword 64) 2 = mword_of_int (PO + 0x18)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpc18) in "Hpc".
      (* ---- apply the suffix with ms = N5 ---- *)
      iApply (wp_push_off_suffix_sconf Φ N5 (av - 4)%nat noff
                (m !!! Regidx (mword_of_int 1 : mword 5)) (m !!! Regidx (mword_of_int 8 : mword 5)) (m !!! Regidx (mword_of_int 9 : mword 5)) vgap p
                ltac:(lia)
                with "Hcg Htext Hpc [Hnoff] [Hr24] [Hr16] [Hr8] [Hgap] [-]").
      { iExact "Hnoff". }
      { iEval (rewrite HcspN5). iExact "Hr24". }
      { iEval (rewrite HcspN5). iExact "Hr16". }
      { iEval (rewrite HcspN5). iExact "Hr8". }
      { iEval (rewrite HcspN5 -Hspd4). iExact "Hgap". }
      iIntros "Hpc Hmfin Hnoff".
      iDestruct "Hmfin" as (mfin) "(Hcg & %Hp)".
      destruct Hp as (Hra & Hs0 & Hs1 & Hsp & Hs2 & Hs3 & Hs4 & Hs5 & Hs6 & Hs7 & Hs8 & Hs9 & Hs10 & Hs11).
      assert (Hav4 : (av - 4 + 4)%nat = av) by lia.
      iEval (rewrite Hav4) in "Hcg".
      iApply ("Hcont" $! mstatus0 mfin with "[%] Hcg [Hnoff Hintena Hcnt Hproc HC] Htcp Hpc [%]").
      { exact Hmsf. }
      { (* cpu_own (S (S n')) eb p C false *)
        rewrite /cpu_own /cpu_hart /cpu_cells.
        iSplitL "Hnoff Hintena Hcnt Hproc".
        { iSplitL "Hnoff Hintena Hproc".
          { iSplitR. { iPureIntro. rewrite Nat2Z.inj_succ in Hbound |- *. lia. }
            iSplitL "Hnoff".
            { assert (Hstoref : (autocast (T := mword) (subrange_vec_dec (sign_extend' 64 (subrange_vec_dec (add_vec (sign_extend' 64 noff) (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6)))) 31 0)) (Z.sub (Z.mul 4 8) 1) 0) : mword 32) = noff_val (S (S n'))).
              { change noff with (noff_val (S n')). apply push_storeval_succ. exact Hnbound. }
              iEval (rewrite Hstoref) in "Hnoff". iExact "Hnoff". }
            iSplitL "Hintena". { iExact "Hintena". }
            iExact "Hproc". }
          iExact "Hcnt". }
        iExact "HC". }
      { unfold callee_saved. repeat split.
      - (* sp *)
        rewrite Hsp HcspN5 /spd /sp0 po_addv_assoc.
        assert (HAB : add_vec (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6)))
                              (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))) = mword_of_int 0)
          by (apply bv_eq; vm_compute; reflexivity).
        rewrite HAB. apply avi0.
      - (* s0 *) exact Hs0.
      - (* s1 *) exact Hs1.
      - (* s2 *)
        rewrite Hs2.
        rewrite /N5 upd_ne; [| vm_compute; discriminate].
        rewrite Hs2_4.
        rewrite /N3 upd_ne; [| vm_compute; discriminate].
        rewrite /N2 upd_ne; [| vm_compute; discriminate].
        rewrite /N1 upd_ne; [| vm_compute; discriminate].
        rewrite /N0 upd_ne; [| vm_compute; discriminate].
        reflexivity.
      - (* s3 *)
        rewrite Hs3.
        rewrite /N5 upd_ne; [| vm_compute; discriminate].
        rewrite Hs3_4.
        rewrite /N3 upd_ne; [| vm_compute; discriminate].
        rewrite /N2 upd_ne; [| vm_compute; discriminate].
        rewrite /N1 upd_ne; [| vm_compute; discriminate].
        rewrite /N0 upd_ne; [| vm_compute; discriminate].
        reflexivity.
      - (* s4 *)
        rewrite Hs4.
        rewrite /N5 upd_ne; [| vm_compute; discriminate].
        rewrite Hs4_4.
        rewrite /N3 upd_ne; [| vm_compute; discriminate].
        rewrite /N2 upd_ne; [| vm_compute; discriminate].
        rewrite /N1 upd_ne; [| vm_compute; discriminate].
        rewrite /N0 upd_ne; [| vm_compute; discriminate].
        reflexivity.
      - (* s5 *)
        rewrite Hs5.
        rewrite /N5 upd_ne; [| vm_compute; discriminate].
        rewrite Hs5_4.
        rewrite /N3 upd_ne; [| vm_compute; discriminate].
        rewrite /N2 upd_ne; [| vm_compute; discriminate].
        rewrite /N1 upd_ne; [| vm_compute; discriminate].
        rewrite /N0 upd_ne; [| vm_compute; discriminate].
        reflexivity.
      - (* s6 *)
        rewrite Hs6.
        rewrite /N5 upd_ne; [| vm_compute; discriminate].
        rewrite Hs6_4.
        rewrite /N3 upd_ne; [| vm_compute; discriminate].
        rewrite /N2 upd_ne; [| vm_compute; discriminate].
        rewrite /N1 upd_ne; [| vm_compute; discriminate].
        rewrite /N0 upd_ne; [| vm_compute; discriminate].
        reflexivity.
      - (* s7 *)
        rewrite Hs7.
        rewrite /N5 upd_ne; [| vm_compute; discriminate].
        rewrite Hs7_4.
        rewrite /N3 upd_ne; [| vm_compute; discriminate].
        rewrite /N2 upd_ne; [| vm_compute; discriminate].
        rewrite /N1 upd_ne; [| vm_compute; discriminate].
        rewrite /N0 upd_ne; [| vm_compute; discriminate].
        reflexivity.
      - (* s8 *)
        rewrite Hs8.
        rewrite /N5 upd_ne; [| vm_compute; discriminate].
        rewrite Hs8_4.
        rewrite /N3 upd_ne; [| vm_compute; discriminate].
        rewrite /N2 upd_ne; [| vm_compute; discriminate].
        rewrite /N1 upd_ne; [| vm_compute; discriminate].
        rewrite /N0 upd_ne; [| vm_compute; discriminate].
        reflexivity.
      - (* s9 *)
        rewrite Hs9.
        rewrite /N5 upd_ne; [| vm_compute; discriminate].
        rewrite Hs9_4.
        rewrite /N3 upd_ne; [| vm_compute; discriminate].
        rewrite /N2 upd_ne; [| vm_compute; discriminate].
        rewrite /N1 upd_ne; [| vm_compute; discriminate].
        rewrite /N0 upd_ne; [| vm_compute; discriminate].
        reflexivity.
      - (* s10 *)
        rewrite Hs10.
        rewrite /N5 upd_ne; [| vm_compute; discriminate].
        rewrite Hs10_4.
        rewrite /N3 upd_ne; [| vm_compute; discriminate].
        rewrite /N2 upd_ne; [| vm_compute; discriminate].
        rewrite /N1 upd_ne; [| vm_compute; discriminate].
        rewrite /N0 upd_ne; [| vm_compute; discriminate].
        reflexivity.
      - (* s11 *)
        rewrite Hs11.
        rewrite /N5 upd_ne; [| vm_compute; discriminate].
        rewrite Hs11_4.
        rewrite /N3 upd_ne; [| vm_compute; discriminate].
        rewrite /N2 upd_ne; [| vm_compute; discriminate].
        rewrite /N1 upd_ne; [| vm_compute; discriminate].
        rewrite /N0 upd_ne; [| vm_compute; discriminate].
        reflexivity. }
  Qed.

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
  Lemma wp_pop_off_sconf `{GEN : GenId} `{CID : CpuId} (Φ : mval -> iProp Σ)
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
    iApply wp_next_off_intro.
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
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc Hr8".
    assert (Hpp04 : add_vec_int (mword_of_int (PP + 0x02) : mword 64) 2 = mword_of_int (PP + 0x04)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp04) in "Hpc".
    (* ---- 0x04: c.sdsp s0,0(sp) ---- *)
    iApply (wp_csdsp_s_sconf Φ (mword_of_int (PP + 0x04)) (mword_of_int 0 : mword 6) (mword_of_int 8 : mword 5)
              P0 (av - 2)%nat vr0 false
              with "Hcg Hpc Hi04 [Hr0] [-]").
    { iEval (rewrite Hcsp0 -Hb2). iExact "Hr0". }
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc Hr0".
    assert (Hpp06 : add_vec_int (mword_of_int (PP + 0x04) : mword 64) 2 = mword_of_int (PP + 0x06)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp06) in "Hpc".
    (* ---- 0x06: c.addi4spn s0,sp,4 ---- *)
    iApply (wp_caddi4spn_s_sconf Φ (mword_of_int (PP + 0x06)) (Cregidx (mword_of_int 0)) (mword_of_int 4 : mword 8) (mword_of_int 8 : mword 5)
              P0 (av - 2)%nat false
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi06 [-]").
    iApply wp_next_off_intro.
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
    iApply wp_next_off_intro.
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
    iApply wp_next_off_intro.
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
    iApply wp_next_off_intro.
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
    iApply wp_next_off_intro.
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
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    assert (Hpc1a : add_vec_int (mword_of_int (PP + 0x16) : mword 64) 4 = mword_of_int (PP + 0x1a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc1a) in "Hpc".
    (* ---- 0x1a: c.addiw a5,-1 ---- *)
    iApply (wp_caddiw_s_sconf Φ (mword_of_int (PP + 0x1a)) (mword_of_int 15 : mword 5) (mword_of_int 63 : mword 6)
              P5 (av - 2)%nat false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi1a [-]").
    iApply wp_next_off_intro.
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
    iApply wp_next_off_intro.
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
      iApply wp_next_off_intro.
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
      iApply wp_next_off_intro.
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
      iApply wp_next_off_intro.
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
      iApply wp_next_off_intro.
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
        iApply wp_next_off_intro.
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
        iApply wp_next_off_intro.
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
        iApply wp_next_off_intro.
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
        (* ---- 0x24: csrsi sstatus,2 (rd = x0) -- THE RESTORE, and the
           other half of the arm seam.  The pieces go IN: the counting
           token (level 0 + the persistent handler-avail = [intr_count 1
           true]), the trap CSRs the level-0/enabled-base boundary owes,
           and the per-cpu CELLS -- and the leaf rebuilds [sie_arm true p]
           whole around them, minting the count eighth at '1' itself.  What
           the caller keeps is its frame [C] and the pure fact, i.e.
           [cpu_own 0 true p C true]. ---- *)
        iPoseProof (ppi_24 with "Htext") as "Hi24".
        assert (Hdec : noff_val 0 = storeval).
        { symmetry. rewrite /storeval /nv1. change noffv with (noff_val 1).
          apply pop_storeval_pred. exact Hbound. }
        iApply (wp_csrsi_sstatus_x0_s_sconf Φ (mword_of_int (PP + 0x24)) P7 (av - 2)%nat false
                  with "Hcg [Htok] Htcp [Hnoff Hint Hproc] Hpc Hi24 [-]").
        { iApply (intr_count_pack_S_on 0 with "Htok Havail"). }
        { rewrite /cpu_cells.
          iSplitR. { iPureIntro. change (Z.of_nat 0) with 0%Z. lia. }
          iSplitL "Hnoff". { iEval (rewrite Hdec). iExact "Hnoff". }
          iSplitL "Hint". { iExists intenav. iExact "Hint". }
          iExact "Hproc". }
        iApply wp_next_off_intro.
        iIntros (msi) "%Hmsfi Hcg Hpc".
        assert (Hpc28 : add_vec_int (mword_of_int (PP + 0x24) : mword 64) 4 = mword_of_int (PP + 0x28)) by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hpc28) in "Hpc".
        (* the exit index is [bexit] = [eb] = true: the epilogue below runs
           with interrupts ENABLED, so it is invoked at literal [true] and
           its own [wp_next true] obligation IS pop_off's. *)
        assert (Hbext : bexit = true) by (rewrite /bexit; reflexivity).
        iEval (rewrite Hbext) in "Hcont".
        iApply (wp_pop_off_epi_sconf Φ P7 (av - 2)%nat
                  (m !!! Regidx (mword_of_int 1 : mword 5)) (m !!! Regidx (mword_of_int 8 : mword 5)) true p
                  with "Hcg Htext Hpc [Hr8] [Hr0] [-]").
        { iEval (rewrite HcspP7). iExact "Hr8". }
        { iEval (rewrite HcspP7). iExact "Hr0". }
        iIntros (CIDe Hse mf) "Hcg Hpc %Hmf".
        assert (Hav2 : (av - 2 + 2)%nat = av) by lia.
        iEval (rewrite Hav2) in "Hcg".
        subst mf.
        iSpecialize ("Hcont" $! CIDe with "[%]"); [wp_next_chain|].
        iApply ("Hcont" with "Hcg [HC] Hpc [%]").
        { iApply (cpu_own_on_intro with "HC"). }
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
  Qed.

End ProofPushOff.

End PushOffProof.
