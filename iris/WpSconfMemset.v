(* WpSconfMemset.v: the memset byte-fill loop over the SIE-agnostic v2
   bundle.  memset runs OUTSIDE the interrupt-disabled region (kfree
   calls it before acquire, kalloc after release), so it must be
   SIE-agnostic — interrupts absorbed by the funnel during the fill.
   It threads sconf + sie_cap (NO intr_count: the fill never touches
   the disable nesting).  Fuel induction over the remaining byte count
   (the packaged bne-taken leaf hands the step's later out, stripped by
   iNext against the fuel IH — bounded loop, not iLöb). *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvModelBytes RiscvLang RiscvPtsto RiscvExtras.
Require Import RegFile.
Require Import WpGpr InstrBytes WpMmodeLeafBase.
Require Import SmodeCore.
Require Import KptTree.
Require Import StackOwn KernelText.
Require Import IntrDefs.
Require Import IntrDefs.
Require Import VcGen.
Require Import WpSconfAlu WpSconfMem WpSconfBtype WpSconfCtl.
Require Import WpMemsetS.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SpecMemsetParts.
Import Defs.


(* the epilogue +16 cancels a pa_stk 2 re-anchor (closed offsets). *)
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

Module MemsetProof : MEMSET.

Section WpSconfMemset.
  Context `{!riscvGS Σ, !sieG Σ}.
  Context `{CID : CpuId}.

  (* the memset store leaf's [pa = add_vec cur (sext 0)] equals the
     buffer's [ms_pa cur] (both are just cur). *)
  Local Lemma ms_pa_sb_pa (cur : mword 64) :
    ms_pa cur = add_vec cur (sign_extend' 64 (mword_of_int 0 : mword 12)).
  Proof.
    unfold ms_pa, ms_a8.
    change (0 * 1)%Z with 0%Z. rewrite avi0. rewrite zero_extend'_id.
    rewrite subrange_id. rewrite sign_extend'_id. reflexivity.
  Qed.

  Local Lemma trunc8_nth0 (v : mword 64) : trunc8 v = nth_byte (trunc8 v) 0.
  Proof.
    apply bv_eq. rewrite nth_byte_unsigned.
    change (Z.of_N (8 * N.of_nat 0)) with 0%Z. rewrite Z.shiftr_0_r.
    symmetry. apply Z.mod_small.
    pose proof (bv_unsigned_in_range _ (trunc8 v)) as [Hlo Hhi].
    split; [ exact Hlo |].
    eapply Z.lt_le_trans; [ exact Hhi |].
    unfold bv_modulus. change (2 ^ Z.of_N 8)%Z with 256%Z.
    change (2 ^ 8)%Z with 256%Z. apply Z.le_refl.
  Qed.

  Lemma wp_memset_loop_sconf (γ : gname) (root_ppn : mword 44) (Φ : mval -> iProp Σ)
      (N : nat) (p e cval : mword 64) (ra1 ra4 ra5 : mword 5) (imm_bne : mword 13)
      (olds : nat -> bv 8) (n : nat)
    : wp_memset_loop_sconf_body γ root_ppn Φ N p e cval ra1 ra4 ra5 imm_bne olds n.
  Proof.
    cbv beta delta [wp_memset_loop_sconf_body].
    intros pc0 pc4 pc6 cbyte Hra1 Hra4 Hra5 Hback Hal0
      Hincr Hcmp Hra4ne Hra1ne Hra5sp Hext0 Hext4 Hext6.
    induction rem as [|rem' IH]; intros off m Hoff Hrem Hcur Hm4 Hm1;
      [ exfalso; lia | ].
    iIntros "Hsc Hhs Hcg Htlbinv
             #Htext Hpc Hbuf Hcont".
    iPoseProof (Hext0 with "Htext") as "Hi0".
    iPoseProof (Hext4 with "Htext") as "Hi4".
    iPoseProof (Hext6 with "Htext") as "Hi6".
    (* off < N, and the current byte is offset off *)
    assert (HoffN : (off < N)%nat) by lia.
    (* peel the head byte of the pending buffer *)
    rewrite (seq_cons off rem').
    rewrite big_sepL_cons.
    iDestruct "Hbuf" as "[Hb0 Hbuf]".
    (* --- 0xce0: sb a1, 0(a5) : fill byte [off] --- *)
    iApply (wp_sb_s_sconf γ root_ppn Φ pc0 ra1 ra5 (mword_of_int 0) m n (olds off)
              with "Hsc Hhs Hcg Htlbinv Hpc Hi0 [Hb0]").
    { rewrite Hcur. rewrite -ms_pa_sb_pa. iExact "Hb0". }
    iIntros "Hhs Hsc Hcg Htlbinv Hpc Hb0".
    (* --- 0xce4: c.addi a5, a5, 1 : a5 := a5 + 1 --- *)
    iApply (wp_caddi_s_sconf γ root_ppn Φ pc4 ra5 (mword_of_int 1) m n
              Hra5 Hra5sp
              with "Hsc Hhs Hcg Htlbinv [Hpc] Hi4 [-]").
    { unfold pc4. iExact "Hpc". }
    iIntros "Hhs Hsc Hcg Htlbinv Hpc".
    (* the new a5 value = ms_addr p (S off) *)
    set (m' := <[Regidx ra5 := regval_into_reg
          (add_vec (m !!! Regidx ra5) (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6))))]> m).
    assert (Hm'a5 : m' !!! Regidx ra5 = ms_addr p (S off)).
    { unfold m'. rewrite upd_eq. unfold regval_into_reg. rewrite Hcur.
      change (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6))) with ms_incr1.
      apply Hincr. }
    assert (Hm'a4 : m' !!! Regidx ra4 = e).
    { unfold m'. rewrite upd_ne; [ exact Hm4 | exact Hra4ne ]. }
    assert (Hm'a1 : m' !!! Regidx ra1 = cval).
    { unfold m'. rewrite upd_ne; [ exact Hm1 | exact Hra1ne ]. }
    (* --- 0xce6: bne a5, a4, ce0 --- *)
    destruct rem' as [|rem''].
    - (* last iteration: S off = N, bne falls through to 0xcea *)
      assert (HSN : (S off = N)%nat) by lia.
      iApply (wp_bne_fall_s_sconf γ root_ppn Φ pc6 imm_bne ra4 ra5 m' n
                Hra5 Hra4
                ltac:(rewrite Hm'a5 Hm'a4; rewrite (Hcmp off HoffN); rewrite HSN Nat.eqb_refl; reflexivity)
                with "Hsc Hhs Hcg Htlbinv [Hpc] Hi6 [-]").
      { unfold pc6. iExact "Hpc". }
      iIntros "Hhs Hsc Hcg Htlbinv Hpc".
      assert (Hspeq : m' !!! Regidx csp_rs1
                      = <[Regidx ra5 := regval_into_reg (ms_addr p N)]> m !!! Regidx csp_rs1).
      { unfold m'.
        rewrite (upd_ne _ (Regidx ra5) (Regidx csp_rs1));
          [| intro HH; apply Hra5sp; congruence].
        rewrite (upd_ne _ (Regidx ra5) (Regidx csp_rs1));
          [| intro HH; apply Hra5sp; congruence].
        reflexivity. }
      iDestruct (sie_cap_gpr_split with "Hcg") as "[Hcap Hfile]".
      iDestruct (sie_cap_retarget γ root_ppn m'
                   (<[Regidx ra5 := regval_into_reg (ms_addr p N)]> m) n Hspeq
                   with "Hcap") as "Hcap".
      iAssert (gpr_file (<[Regidx ra5 := regval_into_reg (ms_addr p N)]> m)) with "[Hfile]" as "Hfile".
      { (* gpr_file m' = <[ra5 := ms_addr p N]> m *)
        rewrite HSN in Hm'a5. unfold m'.
        replace (ms_addr p N) with
          (add_vec (m !!! Regidx ra5) (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6)))).
        2:{ change (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6))) with ms_incr1.
            rewrite Hcur. rewrite Hincr. rewrite HSN. reflexivity. }
        iExact "Hfile". }
      iDestruct (sie_cap_gpr_join with "Hcap Hfile") as "Hcg".
      iApply ("Hcont" with "Hhs Hsc Hcg Htlbinv Hpc [Hb0 Hbuf]").
      (* buffer: seq off 1 = [off], the single filled byte *)
      cbn [seq]. rewrite big_sepL_cons.
      iSplitL "Hb0"; [ iEval (rewrite -ms_pa_sb_pa trunc8_nth0 Hcur Hm1) in "Hb0"; iExact "Hb0" | done ].
    - (* more iterations: S off < N, bne taken back to the loop head pc0 *)
      assert (HSN : (S off < N)%nat) by lia.
      iApply (wp_bne_taken_s_sconf γ root_ppn Φ pc6 imm_bne ra4 ra5 m' n
                Hra5 Hra4
                ltac:(rewrite Hm'a5 Hm'a4; rewrite (Hcmp off HoffN);
                      replace (Nat.eqb (S off) N) with false by (symmetry; apply Nat.eqb_neq; lia); reflexivity)
                ltac:(rewrite Hback; exact Hal0)
                with "Hsc Hhs Hcg Htlbinv [Hpc] Hi6 [-]").
      { unfold pc6. iExact "Hpc". }
      iNext.
      iIntros "Hhs Hsc Hcg Htlbinv Hpc".
      rewrite Hback.
      iApply (IH (S off) m' ltac:(lia) ltac:(lia) Hm'a5 Hm'a4 Hm'a1
                with "Hsc Hhs Hcg Htlbinv Htext Hpc [Hbuf] [Hb0 Hcont]").
      + iExact "Hbuf".
      + (* recombine: the just-filled byte [off] + IH's continuation gives seq off (S(S rem'')) filled *)
        iIntros "Hhs Hsc Hcg Htlbinv Hpc Hbuf'".
        assert (Hmeq : <[Regidx ra5 := regval_into_reg (ms_addr p N)]> m'
                     = <[Regidx ra5 := regval_into_reg (ms_addr p N)]> m)
          by (unfold m'; apply upd_upd).
        iEval (rewrite Hmeq) in "Hcg".
        iApply ("Hcont" with "Hhs Hsc Hcg Htlbinv Hpc [Hb0 Hbuf']").
        change (seq off (S (S rem''))) with (off :: seq (S off) (S rem'')).
        rewrite big_sepL_cons.
        iSplitL "Hb0"; [ iEval (rewrite -ms_pa_sb_pa trunc8_nth0 Hcur Hm1) in "Hb0"; iExact "Hb0" | iExact "Hbuf'" ].
  Qed.

  Lemma wp_memset_suffix_sconf (γ : gname) (root_ppn : mword 44) (Φ : mval -> iProp Σ)
      (M : regfile) (n : nat) (ra0e s00e : mword 64)
    : wp_memset_suffix_sconf_body γ root_ppn Φ M n ra0e s00e.
  Proof.
    cbv beta delta [wp_memset_suffix_sconf_body].
    intros spd sp0up ret_tgt Hal0.
    set (M4 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg ra0e]> M).
    set (M5 := <[Regidx (mword_of_int 8 : mword 5) := regval_into_reg s00e]> M4).
    set (M6 := <[Regidx csp_rs1 := regval_into_reg
        (add_vec (M5 !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 16 : mword 6))))]> M5).
    iIntros "Hsc Hhs Hcg Htlbinv Hi28 Hi2a Hi2c Hi2e Hpc Hp8 Hp0 Hcont".
    (* ---- 0x28: c.ldsp ra,8(sp) ---- *)
    iApply (wp_cldsp_s_sconf γ root_ppn Φ (mword_of_int (MS + 0x1e)) (mword_of_int 1 : mword 6) (mword_of_int 1 : mword 5)
              M n ra0e
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hsc Hhs Hcg Htlbinv Hpc Hi28 Hp8 [-]").
    iIntros "Hhs Hsc Hcg Htlbinv Hpc Hp8".
    assert (Hpc2a : add_vec_int (mword_of_int (MS + 0x1e) : mword 64) 2 = mword_of_int (MS + 0x20))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc2a) in "Hpc".
    change (<[Regidx (mword_of_int 1 : mword 5) := regval_into_reg ra0e]> M) with M4.
    (* ---- 0x2a: c.ldsp s0,0(sp) ---- *)
    assert (Hsp4 : M4 !!! Regidx csp_rs1 = spd)
      by (rewrite /M4 upd_ne; [reflexivity | vm_compute; discriminate]).
    iApply (wp_cldsp_s_sconf γ root_ppn Φ (mword_of_int (MS + 0x20)) (mword_of_int 0 : mword 6) (mword_of_int 8 : mword 5)
              M4 n s00e
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hsc Hhs Hcg Htlbinv Hpc Hi2a [Hp0] [-]").
    { iEval (rewrite Hsp4). iExact "Hp0". }
    iIntros "Hhs Hsc Hcg Htlbinv Hpc Hp0".
    assert (Hpc2c : add_vec_int (mword_of_int (MS + 0x20) : mword 64) 2 = mword_of_int (MS + 0x22))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc2c) in "Hpc".
    change (<[Regidx (mword_of_int 8 : mword 5) := regval_into_reg s00e]> M4) with M5.
    (* ---- 0x2c: c.addi sp,16 -- the frame trade back ---- *)
    assert (Hsp5 : M5 !!! Regidx csp_rs1 = spd)
      by (rewrite /M5 upd_ne; [exact Hsp4 | vm_compute; discriminate]).
    assert (Hupc : pa_stk sp0up 2 = spd).
    { unfold sp0up. apply po_up_cancel16. }
    assert (Hwv : add_vec (M5 !!! Regidx csp_rs1)
                    (sign_extend' 64 (sign_extend' 12 (mword_of_int 16 : mword 6))) = sp0up).
    { rewrite Hsp5. reflexivity. }
    assert (Hpop : M5 !!! Regidx csp_rs1
                   = pa_stk (add_vec (M5 !!! Regidx csp_rs1)
                       (sign_extend' 64 (sign_extend' 12 (mword_of_int 16 : mword 6)))) 2).
    { rewrite Hwv Hupc. exact Hsp5. }
    assert (Hb1u : pa_stk sp0up 1
                    = add_vec spd (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000")))).
    { unfold sp0up, pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb2u : pa_stk sp0up 2
                    = add_vec spd (zero_extend' 64 (concat_vec (mword_of_int 0 : mword 6) ('b"000")))).
    { unfold sp0up, pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    iApply (wp_caddi_sp_pop_s_sconf γ root_ppn Φ (mword_of_int (MS + 0x22)) (mword_of_int 16 : mword 6) M5
              n 2 Hpop
              with "Hsc Hhs Hcg Htlbinv Hpc Hi2c [Hp8 Hp0] [-]").
    { iEval (rewrite Hwv).
      iApply (stack_own_2_intro with "[Hp8] [Hp0]").
      - iEval (rewrite Hb1u). iExact "Hp8".
      - iEval (rewrite Hb2u -Hsp4). iExact "Hp0". }
    iIntros "Hhs Hsc Hcg Htlbinv Hpc".
    assert (Hpc2e : add_vec_int (mword_of_int (MS + 0x22) : mword 64) 2 = mword_of_int (MS + 0x24))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc2e) in "Hpc".
    change (<[Regidx csp_rs1 := regval_into_reg
        (add_vec (M5 !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 16 : mword 6))))]> M5) with M6.
    (* ---- 0x2e: c.ret ---- *)
    assert (HM6ra : M6 !!! Regidx (mword_of_int 1 : mword 5) = ra0e).
    { rewrite /M6 upd_ne; [| vm_compute; discriminate].
      rewrite /M5 upd_ne; [| vm_compute; discriminate].
      rewrite /M4. apply upd_eq. }
    assert (Hal0' : eq_vec (access_vec_dec (update_vec_dec (add_vec (M6 !!! Regidx (mword_of_int 1 : mword 5)) (sign_extend' 64 (zeros' 12))) 0 ('b"0")) 0) ('b"0") = true)
      by (rewrite HM6ra; exact Hal0).
    iApply (wp_cret_s_sconf γ root_ppn Φ (mword_of_int (MS + 0x24)) (mword_of_int 1 : mword 5) M6 (n + 2)%nat
              ltac:(vm_compute; discriminate) Hal0'
              with "Hsc Hhs Hcg Htlbinv Hpc Hi2e [-]").
    iIntros "Hhs Hsc Hcg Htlbinv Hpc".
    assert (Hra_final : update_vec_dec (add_vec (M6 !!! Regidx (mword_of_int 1 : mword 5)) (sign_extend' 64 (zeros' 12))) 0 ('b"0") = ret_tgt)
      by (rewrite HM6ra; reflexivity).
    iEval (rewrite Hra_final) in "Hpc".
    iApply ("Hcont" $! M6 with "Hhs Hsc Hcg Htlbinv Hpc [%]").
    rewrite /M6 /M5 /M4 Hsp5. reflexivity.
  Qed.


  (* =================================================================== *)
  (*  memset PREFIX over sconf (memset+0x00..+0x10): the 2-slot frame      *)
  (*  alloc (c.addi sp,-16, a push trading 2 off the avail count), the two *)
  (*  c.sdsp saves into the freed frame cells, c.addi4spn s0, the n<>0     *)
  (*  c.beqz fall-through, and the a4 end-pointer setup.  Hands the two     *)
  (*  full frame cells (ra0/s0) out to the loop.                            *)
  (* =================================================================== *)
  Lemma wp_memset_prefix_sconf (γ : gname) (root_ppn : mword 44) (Φ : mval -> iProp Σ)
      (m0 : regfile) (n : nat)
      (imm_entry shamt_l shamt_r : mword 6) (nzimm_s0 imm8_beqz : mword 8)
      (wval_add : mword 64)
    : wp_memset_prefix_sconf_body γ root_ppn Φ m0 n imm_entry shamt_l shamt_r nzimm_s0 imm8_beqz wval_add.
  Proof.
    cbv beta delta [wp_memset_prefix_sconf_body].
    intros ra_idx s0_idx a0_idx a2_idx a4_idx a5_idx pcE sp0 sp' pa_ra pa_s0
      ra0 s00 m1 m2 m3 m4 m5 m6 Hn2 Hsp' Hn0 Hvalue_add.
    iIntros "Hsc Hhs Hcg Htlbinv Hpc Hi00 Hi02 Hi04 Hi06 Hi08 Hi0a Hi0c Hi0e Hi10 Hcont".
    assert (Hcsp1 : m1 !!! Regidx csp_rs1 = sp') by (apply upd_eq).
    (* ---- 0x00: c.addi sp,-16 -- the frame push ---- *)
    iApply (wp_caddi_sp_push_s_sconf γ root_ppn Φ pcE imm_entry m0 n 2 Hn2 Hsp'
              with "Hsc Hhs Hcg Htlbinv Hpc Hi00 [-]").
    iIntros "Hhs Hsc Hcg Hframe Htlbinv Hpc".
    assert (Hpp02 : add_vec_int (pcE : mword 64) 2 = mword_of_int (MS + 0x02)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp02) in "Hpc".
    iDestruct (stack_own_2_elim with "Hframe") as (vr8 vs0) "[Hbra Hbs0]".
    assert (Hpa1 : add_vec (m1 !!! Regidx csp_rs1) (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000"))) = pa_stk sp0 1).
    { rewrite Hcsp1 Hsp'. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hpa2 : add_vec (m1 !!! Regidx csp_rs1) (zero_extend' 64 (concat_vec (mword_of_int 0 : mword 6) ('b"000"))) = pa_stk sp0 2).
    { rewrite Hcsp1 Hsp'. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    iEval (rewrite -Hpa1) in "Hbra".
    iEval (rewrite -Hpa2) in "Hbs0".
    (* ---- 0x02: c.sdsp ra,8(sp) ---- *)
    iApply (wp_csdsp_s_sconf γ root_ppn Φ (mword_of_int (MS + 0x02)) (mword_of_int 1 : mword 6) ra_idx m1 (n - 2)%nat vr8
              with "Hsc Hhs Hcg Htlbinv Hpc Hi02 Hbra [-]").
    iIntros "Hhs Hsc Hcg Htlbinv Hpc Hbra".
    assert (Hpp04 : add_vec_int (mword_of_int (MS + 0x02) : mword 64) 2 = mword_of_int (MS + 0x04)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp04) in "Hpc".
    (* ---- 0x04: c.sdsp s0,0(sp) ---- *)
    iApply (wp_csdsp_s_sconf γ root_ppn Φ (mword_of_int (MS + 0x04)) (mword_of_int 0 : mword 6) s0_idx m1 (n - 2)%nat vs0
              with "Hsc Hhs Hcg Htlbinv Hpc Hi04 Hbs0 [-]").
    iIntros "Hhs Hsc Hcg Htlbinv Hpc Hbs0".
    assert (Hpp06 : add_vec_int (mword_of_int (MS + 0x04) : mword 64) 2 = mword_of_int (MS + 0x06)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp06) in "Hpc".
    (* the saved values: ra0/s00 *)
    assert (Hra0v : m1 !!! Regidx ra_idx = ra0)
      by (unfold m1, ra0; rewrite upd_ne; [reflexivity | vm_compute; discriminate]).
    assert (Hs00v : m1 !!! Regidx s0_idx = s00)
      by (unfold m1, s00; rewrite upd_ne; [reflexivity | vm_compute; discriminate]).
    (* ---- 0x06: c.addi4spn s0,sp,16 ---- *)
    iApply (wp_caddi4spn_s_sconf γ root_ppn Φ (mword_of_int (MS + 0x06)) (Cregidx (mword_of_int 0)) nzimm_s0 s0_idx m1 (n - 2)%nat
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hsc Hhs Hcg Htlbinv Hpc Hi06 [-]").
    iIntros "Hhs Hsc Hcg Htlbinv Hpc".
    assert (Hpp08 : add_vec_int (mword_of_int (MS + 0x06) : mword 64) 2 = mword_of_int (MS + 0x08)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp08) in "Hpc".
    change (<[Regidx s0_idx := regval_into_reg (add_vec (m1 !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm nzimm_s0)))]> m1) with m2.
    (* ---- 0x08: c.beqz a2,cea : n<>0, fall through ---- *)
    assert (Hn0' : eq_vec (m2 !!! Regidx a2_idx) zero_reg = false).
    { unfold m2, m1, a2_idx. rewrite upd_ne; [| vm_compute; discriminate].
      rewrite upd_ne; [| vm_compute; discriminate]. exact Hn0. }
    iApply (wp_cbeqz_fall_s_sconf γ root_ppn Φ (mword_of_int (MS + 0x08)) imm8_beqz (Cregidx (mword_of_int 4)) a2_idx m2 (n - 2)%nat
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) Hn0'
              with "Hsc Hhs Hcg Htlbinv Hpc Hi08 [-]").
    iIntros "Hhs Hsc Hcg Htlbinv Hpc".
    assert (Hpp0a : add_vec_int (mword_of_int (MS + 0x08) : mword 64) 2 = mword_of_int (MS + 0x0a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp0a) in "Hpc".
    (* ---- 0x0a: c.mv a5,a0 ---- *)
    iApply (wp_cmv_s_sconf γ root_ppn Φ (mword_of_int (MS + 0x0a)) a5_idx a0_idx m2 (n - 2)%nat
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hsc Hhs Hcg Htlbinv Hpc Hi0a [-]").
    iIntros "Hhs Hsc Hcg Htlbinv Hpc".
    assert (Hpp0c : add_vec_int (mword_of_int (MS + 0x0a) : mword 64) 2 = mword_of_int (MS + 0x0c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp0c) in "Hpc".
    change (<[Regidx a5_idx := regval_into_reg (add_vec zero_reg (m2 !!! Regidx a0_idx))]> m2) with m3.
    (* ---- 0x0c: c.slli a2,shamt_l ---- *)
    iApply (wp_cslli_s_sconf γ root_ppn Φ (mword_of_int (MS + 0x0c)) (Regidx a2_idx) a2_idx shamt_l m3 (n - 2)%nat
              eq_refl ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hsc Hhs Hcg Htlbinv Hpc Hi0c [-]").
    iIntros "Hhs Hsc Hcg Htlbinv Hpc".
    assert (Hpp0e : add_vec_int (mword_of_int (MS + 0x0c) : mword 64) 2 = mword_of_int (MS + 0x0e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp0e) in "Hpc".
    change (<[Regidx a2_idx := regval_into_reg (shift_bits_left (m3 !!! Regidx a2_idx) (subrange_vec_dec shamt_l (Z.sub log2_xlen 1) 0))]> m3) with m4.
    (* ---- 0x0e: c.srli a2,shamt_r ---- *)
    iApply (wp_csrli_s_sconf γ root_ppn Φ (mword_of_int (MS + 0x0e)) (Cregidx (mword_of_int 4)) a2_idx shamt_r m4 (n - 2)%nat
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hsc Hhs Hcg Htlbinv Hpc Hi0e [-]").
    iIntros "Hhs Hsc Hcg Htlbinv Hpc".
    assert (Hpp10 : add_vec_int (mword_of_int (MS + 0x0e) : mword 64) 2 = mword_of_int (MS + 0x10)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp10) in "Hpc".
    change (<[Regidx a2_idx := regval_into_reg (shift_bits_right (m4 !!! Regidx a2_idx) (subrange_vec_dec shamt_r (Z.sub log2_xlen 1) 0))]> m4) with m5.
    (* ---- 0x10: add a4,a2,a0 (end pointer) ---- *)
    iApply (wp_add_s_sconf γ root_ppn Φ (mword_of_int (MS + 0x10)) a4_idx a2_idx a0_idx wval_add m5 (n - 2)%nat
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) Hvalue_add
              with "Hsc Hhs Hcg Htlbinv Hpc Hi10 [-]").
    iIntros "Hhs Hsc Hcg Htlbinv Hpc".
    assert (Hpp14 : add_vec_int (mword_of_int (MS + 0x10) : mword 64) 4 = add_vec_int (pcE : mword 64) 20) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp14) in "Hpc".
    change (<[Regidx a4_idx := regval_into_reg wval_add]> m5) with m6.
    (* frame cells hold ra0/s00 at pa_ra/pa_s0 (via Hcsp1: m1!!!csp = sp') *)
    iEval (rewrite Hcsp1 Hra0v) in "Hbra".
    iEval (rewrite Hcsp1 Hs00v) in "Hbs0".
    iApply ("Hcont" with "Hsc Hhs Hcg Htlbinv Hpc Hbra Hbs0").
  Qed.

End WpSconfMemset.

End MemsetProof.

