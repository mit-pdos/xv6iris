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
Import Defs.

Notation MS := KernelSyms.memset.

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
      (olds : nat -> bv 8) :
    let pc0 := mword_of_int (KernelSyms.memset + 0x14) in
    let pc4 := add_vec_int pc0 4 in
    let pc6 := add_vec_int pc0 6 in
    let cbyte := nth_byte (autocast (T := mword) (subrange_vec_dec cval (Z.sub (Z.mul 1 8) 1) 0) : mword 8) 0 in
    (* register indices distinct from x0 *)
    uint ra1 <> 0 -> uint ra4 <> 0 -> uint ra5 <> 0 ->
    (* fetch: TLB slot 5 + geometry for each of the three instructions *)
    (* bne target = loop top pc0; only 2-alignment is needed (the C extension
       legalizes the bit1 = 1 target in the relocated image). *)
    add_vec pc6 (sign_extend' 64 imm_bne) = pc0 ->
    eq_vec (access_vec_dec pc0 0) ('b"0") = true ->
    (* store geometry (svpn := svpn_of a8) is derived internally at [wp_sb_s_pt]. *)
    (* pointer arithmetic: c.addi advances offset; bne compares a5+1 vs a4=e *)
    (forall j : nat, add_vec (ms_addr p j) ms_incr1 = ms_addr p (S j)) ->
    (forall j : nat, (j < N)%nat -> neq_vec (ms_addr p (S j)) e = negb (Nat.eqb (S j) N)) ->
    (* register indices of a1/a4 are distinct from a5 (so c.addi a5 leaves them) *)
    Regidx ra4 <> Regidx ra5 -> Regidx ra1 <> Regidx ra5 ->
    ra5 <> csp_rs1 ->
    (* the three loop instructions, fetched fresh each iteration from kernel_text *)
    (⊢ kernel_text -∗ instr pc0 false (STORE (mword_of_int 0, Regidx ra1, Regidx ra5, 1))) ->
    (⊢ kernel_text -∗ instr pc4 true (ITYPE (sign_extend' 12 (mword_of_int 1 : mword 6), Regidx ra5, Regidx ra5, ADDI))) ->
    (⊢ kernel_text -∗ instr pc6 false (BTYPE (imm_bne, Regidx ra4, Regidx ra5, BNE))) ->
    forall (rem off : nat) (m : gmap regidx (mword 64)),
    (off + rem = N)%nat -> (1 <= rem)%nat ->
    m !!! Regidx ra5 = ms_addr p off ->
    m !!! Regidx ra4 = e ->
    m !!! Regidx ra1 = cval ->
    sconf γ -∗
    hart_state ↦ᵣ HART_ACTIVE tt -∗
    sie_cap γ root_ppn m -∗
    tlb_inv_pt root_ppn -∗
    kernel_text -∗
    pc_is pc0 -∗ gpr_file m -∗
    ([∗ list] j ∈ seq off rem, (ms_pa (ms_addr p j)) ↦ₘ olds j) -∗
    ( hart_state ↦ᵣ HART_ACTIVE tt -∗
      sconf γ -∗
      sie_cap γ root_ppn (<[Regidx ra5 := regval_into_reg (ms_addr p N)]> m) -∗
      tlb_inv_pt root_ppn -∗
      pc_is (add_vec_int pc6 4) -∗
      gpr_file (<[Regidx ra5 := regval_into_reg (ms_addr p N)]> m) -∗
      ([∗ list] j ∈ seq off rem, (ms_pa (ms_addr p j)) ↦ₘ cbyte) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    intros pc0 pc4 pc6 cbyte Hra1 Hra4 Hra5 Hback Hal0
      Hincr Hcmp Hra4ne Hra1ne Hra5sp Hext0 Hext4 Hext6.
    induction rem as [|rem' IH]; intros off m Hoff Hrem Hcur Hm4 Hm1;
      [ exfalso; lia | ].
    iIntros "Hsc Hhs Hcap Htlbinv
             #Htext Hpc Hfile Hbuf Hcont".
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
    iApply (wp_sb_s_sconf γ root_ppn Φ pc0 ra1 ra5 (mword_of_int 0) m (olds off)
              with "Hsc Hhs Hcap Htlbinv Hpc Hfile Hi0 [Hb0]").
    { rewrite Hcur. rewrite -ms_pa_sb_pa. iExact "Hb0". }
    iIntros "Hhs Hsc Hcap Htlbinv Hpc Hfile Hb0".
    (* --- 0xce4: c.addi a5, a5, 1 : a5 := a5 + 1 --- *)
    iApply (wp_caddi_s_sconf γ root_ppn Φ pc4 ra5 (mword_of_int 1) m
              Hra5 Hra5sp
              with "Hsc Hhs Hcap Htlbinv [Hpc] Hfile Hi4 [-]").
    { unfold pc4. iExact "Hpc". }
    iIntros "Hhs Hsc Hcap Htlbinv Hpc Hfile".
    (* the new a5 value = ms_addr p (S off) *)
    set (m' := <[Regidx ra5 := regval_into_reg
          (add_vec (m !!! Regidx ra5) (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6))))]> m).
    assert (Hm'a5 : m' !!! Regidx ra5 = ms_addr p (S off)).
    { unfold m'. rewrite lookup_total_insert. unfold regval_into_reg. rewrite Hcur.
      change (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6))) with ms_incr1.
      apply Hincr. }
    assert (Hm'a4 : m' !!! Regidx ra4 = e).
    { unfold m'. rewrite lookup_total_insert_ne; [ exact Hm4 | exact (not_eq_sym Hra4ne) ]. }
    assert (Hm'a1 : m' !!! Regidx ra1 = cval).
    { unfold m'. rewrite lookup_total_insert_ne; [ exact Hm1 | exact (not_eq_sym Hra1ne) ]. }
    (* --- 0xce6: bne a5, a4, ce0 --- *)
    destruct rem' as [|rem''].
    - (* last iteration: S off = N, bne falls through to 0xcea *)
      assert (HSN : (S off = N)%nat) by lia.
      iApply (wp_bne_fall_s_sconf γ root_ppn Φ pc6 imm_bne ra4 ra5 m'
                Hra5 Hra4
                ltac:(rewrite Hm'a5 Hm'a4; rewrite (Hcmp off HoffN); rewrite HSN Nat.eqb_refl; reflexivity)
                with "Hsc Hhs Hcap Htlbinv [Hpc] Hfile Hi6 [-]").
      { unfold pc6. iExact "Hpc". }
      iIntros "Hhs Hsc Hcap Htlbinv Hpc Hfile".
      assert (Hspeq : m' !!! Regidx csp_rs1
                      = <[Regidx ra5 := regval_into_reg (ms_addr p N)]> m !!! Regidx csp_rs1).
      { unfold m'.
        rewrite (lookup_total_insert_ne _ (Regidx ra5) (Regidx csp_rs1));
          [| intro HH; apply Hra5sp; congruence].
        rewrite (lookup_total_insert_ne _ (Regidx ra5) (Regidx csp_rs1));
          [| intro HH; apply Hra5sp; congruence].
        reflexivity. }
      iDestruct (sie_cap_retarget γ root_ppn m'
                   (<[Regidx ra5 := regval_into_reg (ms_addr p N)]> m) Hspeq
                   with "Hcap") as "Hcap".
      iApply ("Hcont" with "Hhs Hsc Hcap Htlbinv Hpc [Hfile] [Hb0 Hbuf]").
      + (* gpr_file m' = <[ra5 := ms_addr p N]> m *)
        rewrite HSN in Hm'a5. unfold m'.
        replace (ms_addr p N) with
          (add_vec (m !!! Regidx ra5) (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6)))).
        2:{ change (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6))) with ms_incr1.
            rewrite Hcur. rewrite Hincr. rewrite HSN. reflexivity. }
        iExact "Hfile".
      + (* buffer: seq off 1 = [off], the single filled byte *)
        cbn [seq]. rewrite big_sepL_cons.
        iSplitL "Hb0"; [ iEval (rewrite -ms_pa_sb_pa trunc8_nth0 Hcur Hm1) in "Hb0"; iExact "Hb0" | done ].
    - (* more iterations: S off < N, bne taken back to the loop head pc0 *)
      assert (HSN : (S off < N)%nat) by lia.
      iApply (wp_bne_taken_s_sconf γ root_ppn Φ pc6 imm_bne ra4 ra5 m'
                Hra5 Hra4
                ltac:(rewrite Hm'a5 Hm'a4; rewrite (Hcmp off HoffN);
                      replace (Nat.eqb (S off) N) with false by (symmetry; apply Nat.eqb_neq; lia); reflexivity)
                ltac:(rewrite Hback; exact Hal0)
                with "Hsc Hhs Hcap Htlbinv [Hpc] Hfile Hi6 [-]").
      { unfold pc6. iExact "Hpc". }
      iNext.
      iIntros "Hhs Hsc Hcap Htlbinv Hpc Hfile".
      rewrite Hback.
      iApply (IH (S off) m' ltac:(lia) ltac:(lia) Hm'a5 Hm'a4 Hm'a1
                with "Hsc Hhs Hcap Htlbinv Htext Hpc Hfile [Hbuf] [Hb0 Hcont]").
      + iExact "Hbuf".
      + (* recombine: the just-filled byte [off] + IH's continuation gives seq off (S(S rem'')) filled *)
        iIntros "Hhs Hsc Hcap Htlbinv Hpc Hfile Hbuf'".
        assert (Hmeq : <[Regidx ra5 := regval_into_reg (ms_addr p N)]> m'
                     = <[Regidx ra5 := regval_into_reg (ms_addr p N)]> m)
          by (unfold m'; apply insert_insert).
        iEval (rewrite Hmeq) in "Hfile".
        iEval (rewrite Hmeq) in "Hcap".
        iApply ("Hcont" with "Hhs Hsc Hcap Htlbinv Hpc Hfile [Hb0 Hbuf']").
        change (seq off (S (S rem''))) with (off :: seq (S off) (S rem'')).
        rewrite big_sepL_cons.
        iSplitL "Hb0"; [ iEval (rewrite -ms_pa_sb_pa trunc8_nth0 Hcur Hm1) in "Hb0"; iExact "Hb0" | iExact "Hbuf'" ].
  Qed.

  Lemma wp_memset_suffix_sconf (γ : gname) (root_ppn : mword 44) (Φ : mval -> iProp Σ)
      (M : gmap regidx (mword 64)) (ra0e s00e : mword 64) :
    let spd := M !!! Regidx csp_rs1 in
    let sp0up := add_vec spd (sign_extend' 64 (sign_extend' 12 (mword_of_int 16 : mword 6))) in
    let ret_tgt := update_vec_dec (add_vec ra0e (sign_extend' 64 (zeros' 12))) 0 ('b"0") in
    eq_vec (access_vec_dec ret_tgt 0) ('b"0") = true ->
    sconf γ -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
    sie_cap γ root_ppn M -∗ tlb_inv_pt root_ppn -∗
    instr (mword_of_int (MS + 0x1e) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), sp, Regidx (mword_of_int 1 : mword 5), false, 8)) -∗
    instr (mword_of_int (MS + 0x20) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), sp, Regidx (mword_of_int 8 : mword 5), false, 8)) -∗
    instr (mword_of_int (MS + 0x22) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 16 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)) -∗
    instr (mword_of_int (MS + 0x24) : mword 64) true (JALR (zeros' 12, Regidx (mword_of_int 1 : mword 5), zreg)) -∗
    pc_is (mword_of_int (MS + 0x1e) : mword 64) -∗ gpr_file M -∗
    add_vec spd (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000"))) ↦₈ ra0e -∗
    add_vec spd (zero_extend' 64 (concat_vec (mword_of_int 0 : mword 6) ('b"000"))) ↦₈ s00e -∗
    ( ∀ mf,
      hart_state ↦ᵣ HART_ACTIVE tt -∗ sconf γ -∗
      sie_cap γ root_ppn mf -∗ tlb_inv_pt root_ppn -∗
      pc_is ret_tgt -∗ gpr_file mf -∗
      ⌜ mf = <[Regidx csp_rs1 := regval_into_reg sp0up]>
             (<[Regidx (mword_of_int 8 : mword 5) := regval_into_reg s00e]>
              (<[Regidx (mword_of_int 1 : mword 5) := regval_into_reg ra0e]> M)) ⌝ -∗
      stack_own (pa_stk sp0up kv_frame_slots) 2 -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    intros spd sp0up ret_tgt Hal0.
    set (M4 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg ra0e]> M).
    set (M5 := <[Regidx (mword_of_int 8 : mword 5) := regval_into_reg s00e]> M4).
    set (M6 := <[Regidx csp_rs1 := regval_into_reg
        (add_vec (M5 !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 16 : mword 6))))]> M5).
    iIntros "Hsc Hhs Hcap Htlbinv Hi28 Hi2a Hi2c Hi2e Hpc Hfile Hp8 Hp0 Hcont".
    (* ---- 0x28: c.ldsp ra,8(sp) ---- *)
    iApply (wp_cldsp_s_sconf γ root_ppn Φ (mword_of_int (MS + 0x1e)) (mword_of_int 1 : mword 6) (mword_of_int 1 : mword 5)
              M ra0e
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hsc Hhs Hcap Htlbinv Hpc Hfile Hi28 Hp8 [-]").
    iIntros "Hhs Hsc Hcap Htlbinv Hpc Hfile Hp8".
    assert (Hpc2a : add_vec_int (mword_of_int (MS + 0x1e) : mword 64) 2 = mword_of_int (MS + 0x20))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc2a) in "Hpc".
    change (<[Regidx (mword_of_int 1 : mword 5) := regval_into_reg ra0e]> M) with M4.
    (* ---- 0x2a: c.ldsp s0,0(sp) ---- *)
    assert (Hsp4 : M4 !!! Regidx csp_rs1 = spd)
      by (rewrite /M4 lookup_total_insert_ne; [reflexivity | vm_compute; discriminate]).
    iApply (wp_cldsp_s_sconf γ root_ppn Φ (mword_of_int (MS + 0x20)) (mword_of_int 0 : mword 6) (mword_of_int 8 : mword 5)
              M4 s00e
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hsc Hhs Hcap Htlbinv Hpc Hfile Hi2a [Hp0] [-]").
    { iEval (rewrite Hsp4). iExact "Hp0". }
    iIntros "Hhs Hsc Hcap Htlbinv Hpc Hfile Hp0".
    assert (Hpc2c : add_vec_int (mword_of_int (MS + 0x20) : mword 64) 2 = mword_of_int (MS + 0x22))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc2c) in "Hpc".
    change (<[Regidx (mword_of_int 8 : mword 5) := regval_into_reg s00e]> M4) with M5.
    (* ---- 0x2c: c.addi sp,16 -- the frame trade back ---- *)
    assert (Hsp5 : M5 !!! Regidx csp_rs1 = spd)
      by (rewrite /M5 lookup_total_insert_ne; [exact Hsp4 | vm_compute; discriminate]).
    assert (HM6sp : M6 !!! Regidx csp_rs1 = sp0up).
    { rewrite /M6 lookup_total_insert Hsp5. reflexivity. }
    assert (Hupc : pa_stk sp0up 2 = spd).
    { unfold sp0up. apply po_up_cancel16. }
    assert (Hup : M5 !!! Regidx csp_rs1 = pa_stk (M6 !!! Regidx csp_rs1) 2).
    { rewrite Hsp5 HM6sp Hupc. reflexivity. }
    assert (Hb1u : pa_stk sp0up 1
                    = add_vec spd (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000")))).
    { unfold sp0up, pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb2u : pa_stk sp0up 2
                    = add_vec spd (zero_extend' 64 (concat_vec (mword_of_int 0 : mword 6) ('b"000")))).
    { unfold sp0up, pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    iApply (wp_caddi_sp_s_sconf γ root_ppn Φ (mword_of_int (MS + 0x22)) (mword_of_int 16 : mword 6) M5
              (stack_own (pa_stk sp0up kv_frame_slots) 2)
              with "Hsc Hhs Hcap Htlbinv Hpc Hfile Hi2c [Hp8 Hp0] [-]").
    { iIntros "Hcap".
      iAssert (stack_own (M6 !!! Regidx csp_rs1) 2) with "[Hp8 Hp0]" as "Hframe".
      { rewrite HM6sp.
        iApply (stack_own_2_intro with "[Hp8] [Hp0]").
        - iEval (rewrite Hb1u). iExact "Hp8".
        - iEval (rewrite Hb2u -Hsp4). iExact "Hp0". }
      iDestruct (sie_cap_move_up γ root_ppn M5 M6 2 Hup with "Hframe Hcap") as "[Hcap Hdeep]".
      iEval (rewrite HM6sp) in "Hdeep". iFrame "Hcap Hdeep". }
    iIntros "Hhs Hsc Hcap Hdeep Htlbinv Hpc Hfile".
    assert (Hpc2e : add_vec_int (mword_of_int (MS + 0x22) : mword 64) 2 = mword_of_int (MS + 0x24))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc2e) in "Hpc".
    change (<[Regidx csp_rs1 := regval_into_reg
        (add_vec (M5 !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 16 : mword 6))))]> M5) with M6.
    (* ---- 0x2e: c.ret ---- *)
    assert (HM6ra : M6 !!! Regidx (mword_of_int 1 : mword 5) = ra0e).
    { rewrite /M6 lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /M5 lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /M4. apply lookup_total_insert. }
    assert (Hal0' : eq_vec (access_vec_dec (update_vec_dec (add_vec (M6 !!! Regidx (mword_of_int 1 : mword 5)) (sign_extend' 64 (zeros' 12))) 0 ('b"0")) 0) ('b"0") = true)
      by (rewrite HM6ra; exact Hal0).
    iApply (wp_cret_s_sconf γ root_ppn Φ (mword_of_int (MS + 0x24)) (mword_of_int 1 : mword 5) M6
              ltac:(vm_compute; discriminate) Hal0'
              with "Hsc Hhs Hcap Htlbinv Hpc Hfile Hi2e [-]").
    iIntros "Hhs Hsc Hcap Htlbinv Hpc Hfile".
    assert (Hra_final : update_vec_dec (add_vec (M6 !!! Regidx (mword_of_int 1 : mword 5)) (sign_extend' 64 (zeros' 12))) 0 ('b"0") = ret_tgt)
      by (rewrite HM6ra; reflexivity).
    iEval (rewrite Hra_final) in "Hpc".
    iApply ("Hcont" $! M6 with "Hhs Hsc Hcap Htlbinv Hpc Hfile [%] Hdeep").
    rewrite /M6 /M5 /M4 Hsp5. reflexivity.
  Qed.


  (* =================================================================== *)
  (*  memset PREFIX over sconf (memset+0x00..+0x10): the 2-slot frame      *)
  (*  alloc (c.addi sp,-16 traded via sie_cap_move_down 2), the two        *)
  (*  c.sdsp saves into the freed frame cells, c.addi4spn s0, the n<>0     *)
  (*  c.beqz fall-through, and the a4 end-pointer setup.  Threads deep-2    *)
  (*  custody in, hands the two full frame cells (ra0/s0) out to the loop.  *)
  (* =================================================================== *)
  Lemma wp_memset_prefix_sconf (γ : gname) (root_ppn : mword 44) (Φ : mval -> iProp Σ)
      (m0 : gmap regidx (mword 64))
      (imm_entry shamt_l shamt_r : mword 6) (nzimm_s0 imm8_beqz : mword 8)
      (wval_add : mword 64) :
    let ra_idx : mword 5 := mword_of_int 1 in
    let s0_idx : mword 5 := mword_of_int 8 in
    let a0_idx : mword 5 := mword_of_int 10 in
    let a2_idx : mword 5 := mword_of_int 12 in
    let a4_idx : mword 5 := mword_of_int 14 in
    let a5_idx : mword 5 := mword_of_int 15 in
    let pcE := mword_of_int MS in
    let sp0 := m0 !!! Regidx csp_rs1 in
    let sp' := add_vec sp0 (sign_extend' 64 (sign_extend' 12 imm_entry)) in
    let pa_ra := add_vec sp' (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000"))) in
    let pa_s0 := add_vec sp' (zero_extend' 64 (concat_vec (mword_of_int 0 : mword 6) ('b"000"))) in
    let ra0 := m0 !!! Regidx ra_idx in
    let s00 := m0 !!! Regidx s0_idx in
    let m1 := <[Regidx csp_rs1 := regval_into_reg sp']> m0 in
    let m2 := <[Regidx s0_idx := regval_into_reg (add_vec (m1 !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm nzimm_s0)))]> m1 in
    let m3 := <[Regidx a5_idx := regval_into_reg (add_vec zero_reg (m2 !!! Regidx a0_idx))]> m2 in
    let m4 := <[Regidx a2_idx := regval_into_reg (shift_bits_left (m3 !!! Regidx a2_idx) (subrange_vec_dec shamt_l (Z.sub log2_xlen 1) 0))]> m3 in
    let m5 := <[Regidx a2_idx := regval_into_reg (shift_bits_right (m4 !!! Regidx a2_idx) (subrange_vec_dec shamt_r (Z.sub log2_xlen 1) 0))]> m4 in
    let m6 := <[Regidx a4_idx := regval_into_reg wval_add]> m5 in
    sp' = pa_stk sp0 2 ->
    eq_vec (m0 !!! Regidx a2_idx) zero_reg = false ->
    add_vec (m5 !!! Regidx a2_idx) (m5 !!! Regidx a0_idx) = wval_add ->
    sconf γ -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
    sie_cap γ root_ppn m0 -∗ tlb_inv_pt root_ppn -∗
    pc_is pcE -∗ gpr_file m0 -∗
    instr pcE true (ITYPE (sign_extend' 12 imm_entry, Regidx csp_rs1, Regidx csp_rs1, ADDI)) -∗
    instr (add_vec_int pcE 2) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), Regidx ra_idx, sp, 8)) -∗
    instr (add_vec_int pcE 4) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), Regidx s0_idx, sp, 8)) -∗
    instr (add_vec_int pcE 6) true (ITYPE (caddi4spn_imm nzimm_s0, sp, Regidx s0_idx, ADDI)) -∗
    instr (add_vec_int pcE 8) true (BTYPE (sign_extend' 13 (concat_vec imm8_beqz ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 4)), BEQ)) -∗
    instr (add_vec_int pcE 10) true (RTYPE (Regidx a0_idx, zreg, Regidx a5_idx, ADD)) -∗
    instr (add_vec_int pcE 12) true (SHIFTIOP (shamt_l, Regidx a2_idx, Regidx a2_idx, SLLI)) -∗
    instr (add_vec_int pcE 14) true (SHIFTIOP (shamt_r, Regidx a2_idx, Regidx a2_idx, SRLI)) -∗
    instr (add_vec_int pcE 16) false (RTYPE (Regidx a0_idx, Regidx a2_idx, Regidx a4_idx, ADD)) -∗
    stack_own (pa_stk sp0 kv_frame_slots) 2 -∗
    ( sconf γ -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
      sie_cap γ root_ppn m6 -∗ tlb_inv_pt root_ppn -∗
      pc_is (add_vec_int pcE 20) -∗ gpr_file m6 -∗
      pa_ra ↦₈ ra0 -∗ pa_s0 ↦₈ s00 -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    intros ra_idx s0_idx a0_idx a2_idx a4_idx a5_idx pcE sp0 sp' pa_ra pa_s0
      ra0 s00 m1 m2 m3 m4 m5 m6 Hsp' Hn0 Hvalue_add.
    iIntros "Hsc Hhs Hcap Htlbinv Hpc Hfile Hi00 Hi02 Hi04 Hi06 Hi08 Hi0a Hi0c Hi0e Hi10 Hdeep Hcont".
    assert (Hcsp1 : m1 !!! Regidx csp_rs1 = sp') by (apply lookup_total_insert).
    assert (Hsp1 : m1 !!! Regidx csp_rs1 = pa_stk (m0 !!! Regidx csp_rs1) 2)
      by (rewrite Hcsp1; exact Hsp').
    (* ---- 0x00: c.addi sp,-16 -- the frame trade ---- *)
    iApply (wp_caddi_sp_s_sconf γ root_ppn Φ pcE imm_entry m0 (stack_own sp0 2)
              with "Hsc Hhs Hcap Htlbinv Hpc Hfile Hi00 [Hdeep] [-]").
    { iIntros "Hcap".
      iDestruct (sie_cap_move_down γ root_ppn m0 m1 2 Hsp1 with "Hdeep Hcap") as "[Hcap Hframe]".
      iFrame "Hcap Hframe". }
    iIntros "Hhs Hsc Hcap Hframe Htlbinv Hpc Hfile".
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
    iApply (wp_csdsp_s_sconf γ root_ppn Φ (mword_of_int (MS + 0x02)) (mword_of_int 1 : mword 6) ra_idx m1 vr8
              with "Hsc Hhs Hcap Htlbinv Hpc Hfile Hi02 Hbra [-]").
    iIntros "Hhs Hsc Hcap Htlbinv Hpc Hfile Hbra".
    assert (Hpp04 : add_vec_int (mword_of_int (MS + 0x02) : mword 64) 2 = mword_of_int (MS + 0x04)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp04) in "Hpc".
    (* ---- 0x04: c.sdsp s0,0(sp) ---- *)
    iApply (wp_csdsp_s_sconf γ root_ppn Φ (mword_of_int (MS + 0x04)) (mword_of_int 0 : mword 6) s0_idx m1 vs0
              with "Hsc Hhs Hcap Htlbinv Hpc Hfile Hi04 Hbs0 [-]").
    iIntros "Hhs Hsc Hcap Htlbinv Hpc Hfile Hbs0".
    assert (Hpp06 : add_vec_int (mword_of_int (MS + 0x04) : mword 64) 2 = mword_of_int (MS + 0x06)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp06) in "Hpc".
    (* the saved values: ra0/s00 *)
    assert (Hra0v : m1 !!! Regidx ra_idx = ra0)
      by (unfold m1, ra0; rewrite lookup_total_insert_ne; [reflexivity | vm_compute; discriminate]).
    assert (Hs00v : m1 !!! Regidx s0_idx = s00)
      by (unfold m1, s00; rewrite lookup_total_insert_ne; [reflexivity | vm_compute; discriminate]).
    (* ---- 0x06: c.addi4spn s0,sp,16 ---- *)
    iApply (wp_caddi4spn_s_sconf γ root_ppn Φ (mword_of_int (MS + 0x06)) (Cregidx (mword_of_int 0)) nzimm_s0 s0_idx m1
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hsc Hhs Hcap Htlbinv Hpc Hfile Hi06 [-]").
    iIntros "Hhs Hsc Hcap Htlbinv Hpc Hfile".
    assert (Hpp08 : add_vec_int (mword_of_int (MS + 0x06) : mword 64) 2 = mword_of_int (MS + 0x08)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp08) in "Hpc".
    change (<[Regidx s0_idx := regval_into_reg (add_vec (m1 !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm nzimm_s0)))]> m1) with m2.
    (* ---- 0x08: c.beqz a2,cea : n<>0, fall through ---- *)
    assert (Hn0' : eq_vec (m2 !!! Regidx a2_idx) zero_reg = false).
    { unfold m2, m1, a2_idx. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite lookup_total_insert_ne; [| vm_compute; discriminate]. exact Hn0. }
    iApply (wp_cbeqz_fall_s_sconf γ root_ppn Φ (mword_of_int (MS + 0x08)) imm8_beqz (Cregidx (mword_of_int 4)) a2_idx m2
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) Hn0'
              with "Hsc Hhs Hcap Htlbinv Hpc Hfile Hi08 [-]").
    iIntros "Hhs Hsc Hcap Htlbinv Hpc Hfile".
    assert (Hpp0a : add_vec_int (mword_of_int (MS + 0x08) : mword 64) 2 = mword_of_int (MS + 0x0a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp0a) in "Hpc".
    (* ---- 0x0a: c.mv a5,a0 ---- *)
    iApply (wp_cmv_s_sconf γ root_ppn Φ (mword_of_int (MS + 0x0a)) a5_idx a0_idx m2
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hsc Hhs Hcap Htlbinv Hpc Hfile Hi0a [-]").
    iIntros "Hhs Hsc Hcap Htlbinv Hpc Hfile".
    assert (Hpp0c : add_vec_int (mword_of_int (MS + 0x0a) : mword 64) 2 = mword_of_int (MS + 0x0c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp0c) in "Hpc".
    change (<[Regidx a5_idx := regval_into_reg (add_vec zero_reg (m2 !!! Regidx a0_idx))]> m2) with m3.
    (* ---- 0x0c: c.slli a2,shamt_l ---- *)
    iApply (wp_cslli_s_sconf γ root_ppn Φ (mword_of_int (MS + 0x0c)) (Regidx a2_idx) a2_idx shamt_l m3
              eq_refl ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hsc Hhs Hcap Htlbinv Hpc Hfile Hi0c [-]").
    iIntros "Hhs Hsc Hcap Htlbinv Hpc Hfile".
    assert (Hpp0e : add_vec_int (mword_of_int (MS + 0x0c) : mword 64) 2 = mword_of_int (MS + 0x0e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp0e) in "Hpc".
    change (<[Regidx a2_idx := regval_into_reg (shift_bits_left (m3 !!! Regidx a2_idx) (subrange_vec_dec shamt_l (Z.sub log2_xlen 1) 0))]> m3) with m4.
    (* ---- 0x0e: c.srli a2,shamt_r ---- *)
    iApply (wp_csrli_s_sconf γ root_ppn Φ (mword_of_int (MS + 0x0e)) (Cregidx (mword_of_int 4)) a2_idx shamt_r m4
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hsc Hhs Hcap Htlbinv Hpc Hfile Hi0e [-]").
    iIntros "Hhs Hsc Hcap Htlbinv Hpc Hfile".
    assert (Hpp10 : add_vec_int (mword_of_int (MS + 0x0e) : mword 64) 2 = mword_of_int (MS + 0x10)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp10) in "Hpc".
    change (<[Regidx a2_idx := regval_into_reg (shift_bits_right (m4 !!! Regidx a2_idx) (subrange_vec_dec shamt_r (Z.sub log2_xlen 1) 0))]> m4) with m5.
    (* ---- 0x10: add a4,a2,a0 (end pointer) ---- *)
    iApply (wp_add_s_sconf γ root_ppn Φ (mword_of_int (MS + 0x10)) a4_idx a2_idx a0_idx wval_add m5
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) Hvalue_add
              with "Hsc Hhs Hcap Htlbinv Hpc Hfile Hi10 [-]").
    iIntros "Hhs Hsc Hcap Htlbinv Hpc Hfile".
    assert (Hpp14 : add_vec_int (mword_of_int (MS + 0x10) : mword 64) 4 = add_vec_int (pcE : mword 64) 20) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp14) in "Hpc".
    change (<[Regidx a4_idx := regval_into_reg wval_add]> m5) with m6.
    (* frame cells hold ra0/s00 at pa_ra/pa_s0 (via Hcsp1: m1!!!csp = sp') *)
    iEval (rewrite Hcsp1 Hra0v) in "Hbra".
    iEval (rewrite Hcsp1 Hs00v) in "Hbs0".
    iApply ("Hcont" with "Hsc Hhs Hcap Htlbinv Hpc Hfile Hbra Hbs0").
  Qed.

End WpSconfMemset.

