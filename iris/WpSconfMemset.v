(* WpSconfMemset.v: the memset byte-fill loop over the SIE-agnostic v2
   bundle.  memset runs OUTSIDE the interrupt-disabled region (kfree
   calls it before acquire, kalloc after release), so it must be
   SIE-agnostic — interrupts absorbed by the funnel during the fill.
   It threads sconf + sie_cap (NO intr_count: the fill never touches
   the disable nesting).  Fuel induction over the remaining byte count
   (the packaged bne-taken leaf hands the step's later out, stripped by
   iNext against the fuel IH — bounded loop, not iLöb). *)
Require Import WpSmodeLeafBase.
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvModelBytes RiscvLang RiscvPtsto RiscvExec RiscvTryStep RiscvFetchExec RiscvExtras.
Require Import WpLoad WpLeafCommon WpGpr MinstretInv InstrBytes WpMmodeLeafBase.
Require Import SmodePte PtAdBits Pt4kWalk CommonWalk PtTree PtTreeAdue KptPt.
Require Import SmodeCore WpSmodeGpr.
Require Import KptTree SmodeCorePt WpSmodePtLeaves SRegime.
Require Import StackOwn CalleeSaved WpSmodeSret AlignBits KernelText.
Require Import IntrDefs WpIntrInv WpSmodeIntr.
Require Import WpSconfAlu WpSconfMem WpSconfBtype.
Require Import WpMemsetS.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Import Defs.

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

End WpSconfMemset.
