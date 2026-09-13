(* ProofPrputc.v -- the whole-function WP for xv6's prputc() over the
   SIE-agnostic sconf world.

     static void prputc(int c) { uartputc_sync(1, c); }

   Eleven instructions: the standard 16-byte / 2-slot frame, [c.mv a1,a0]
   (the byte becomes uartputc_sync's SECOND argument), [c.li a0,1] (the port
   index) and one [jal].  Structurally it is [ProofConsputc.v]'s non-BACKSPACE
   arm with no test in front of it, so there is no join and no shared
   epilogue: the whole thing is one straight line.

   WHAT IT OWES, AND WHAT IT DOES NOT.  The contract ([SpecPrputc.v]) promises
   nothing about the bytes, because nothing tracks the second port's wire --
   the owner's ruling, recorded there and in
   claude-notes/projects/xv6-bump-163d39b.md.  uartputc_sync's own contract
   still threads a [UartTxInv.uart_sent_sub], so this proof MINTS the empty
   one out of nothing ([uart_sent_sub_nil_free]: [◯ML []] is the unit of the
   mono-list RA) and DROPS what comes back.  That single [iMod] is the whole
   of the trace bookkeeping that printk's cone used to carry from here up.

   THE CALLEE'S CONTRACT IS TAKEN AS AN INLINE HYPOTHESIS, not as
   [SpecUartPutc.wp_uartputc_sconf_body i ...].  The port-indexed spelling of
   that contract is a sibling lane's change and its argument ORDER is not this
   proof's business: writing the premises out here keeps the body independent
   of it, and leaves [LinkPrputc.v] as the one file that has to match.  The
   premises below are exactly what a port-generic uartputc_sync gives at
   [Uart1]: a0 pinned to [UartsFields.uart_index Uart1], the port's own
   invariant (NOT the console bundle [dev_inv]), the .data word its MMIO base
   is loaded from, and the port's transmit lock. *)
From Stdlib Require Import ZArith Bool Lia List String.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_var gen_heap invariants.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import RiscvLang RiscvPtsto.
Require Import RegFile InstrBytes WpMmodeLeafBase.
Require Import RiscvExtras.
Require Import StackOwn CalleeSaved KernelText.
Require Import KernelRvcDecode.
Require Import WpSconfAlu WpSconfMem WpSconfCtl WpSconfBtype WpSmodeIntr.
Require Import DevModel.
Require Import UartsFields.
Require Import DiskPtsto WpUart.
Require Import IntrDefs HartTp WpNext.
Require Import LockRank.
Require Import CpuOwn.
Require Import UartTxInv.
Require Import CodePrputc.
Require Import SpecUartPutc SpecPrputc.
From Kernel Require KernelInstrs.
From Kernel Require KernelSyms.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Require Import TsoCtx.
Local Open Scope Z_scope.
Import Defs.

(* clean-context (mword-free) nat bounds, so [lia] never sees a bv.
   [prputc_stack = 20] = its own 2-slot frame over uartputc_sync's 18. *)
Lemma pp_cap_bounds (K : nat) : (20 <= K)%nat -> (2 <= K)%nat /\ (18 <= K - 2)%nat.
Proof. lia. Qed.

Lemma pp_nk (K : nat) : (2 <= K)%nat -> ((K - 2) + 2)%nat = K.
Proof. lia. Qed.

Section ProofPrputc.
  Context `{!riscvGS Σ, !xv6G Σ}.
  Context `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}.

  Context {kt : ktier}.
  Ltac reg_neq :=
    lazymatch goal with
    | |- ?a <> ?b => tryif unify a b then fail else (vm_compute; discriminate)
    end.

  Local Notation ra_idx := (mword_of_int 1 : mword 5).
  Local Notation s0_idx := (mword_of_int 8 : mword 5).
  Local Notation a0_idx := (mword_of_int 10 : mword 5).
  Local Notation a1_idx := (mword_of_int 11 : mword 5).

  (* [CID0] is its OWN binder: by the time the proof reaches the call it may
     have migrated hart (generic [b]), so the callee's contract must be
     instantiable at whichever hart that turns out to be -- the same rule as
     [ProofConsputc.v]'s [wp_uartputc]. *)
  Hypothesis wp_uartputc :
    forall `{CID0 : CpuId} (γl1 : gname) (γ1 : uart_names)
      (m0 : regfile) (K : nat) (n : nat) (eb : bool) (b : bool) (p : mword 64)
      (lks : gset string),
      (18 <= K)%nat ->
      m0 !!! Regidx a0_idx = (mword_of_int (uart_index Uart1) : mword 64) ->
      (Z.of_nat n + 1 < 2 ^ 31)%Z ->
      locks_below lks "uart1" ->
      sie_cap_gpr kt m0 K b p -∗
      cpu_own n eb p b lks -∗
      kernel_text -∗
      pc_is (mword_of_int KernelSyms.uartputc_sync : mword 64) -∗
      uart_inv Uart1 γ1 -∗
      uart_base_word Uart1 -∗
      is_txlock_at Uart1 γl1 γ1 -∗
      uart_sent_sub γ1 [] -∗
      wp_next (CID0 := CID0) b p (fun (CID : CpuId) =>
        ∀ mf : regfile,
        sie_cap_gpr kt mf K b p -∗
        cpu_own n eb p b lks -∗
        pc_is (ret_pc (m0 !!! Regidx ra_idx)) -∗
        ⌜ callee_saved m0 mf /\ mf !!! Regidx ra_idx = m0 !!! Regidx ra_idx ⌝ -∗
        WP (Loop : expr riscv_lang)) -∗
      WP (Loop : expr riscv_lang).

  Lemma wp_prputc_sconf_gen
      (m : regfile) (K : nat) (n : nat) (eb : bool) (b : bool) (p : mword 64)
      (lks : gset string)
    : wp_prputc_sconf_body kt m K n eb b p lks.
  Proof.
    cbv beta delta [wp_prputc_sconf_body].
    intros ra_i pcE ra0 ret_tgt HK Hn Hbelow.
    assert (HK20 : (20 <= K)%nat) by (exact HK).
    pose proof (pp_cap_bounds K HK20) as (Hc2 & HK18).
    iIntros "Hcg Hcpu #Htext Hpc #Henv Hcont".
    iDestruct "Henv" as (γl1 γ1) "(#Huinv & #Htxl & #Hbase)".
    (* THE EMPTY TRACE CLAIM, MINTED FROM NOTHING.  uartputc_sync wants a
       [uart_sent_sub] to extend; this cone has none to give and none to
       report, so it takes the unit of the mono-list RA. *)
    iApply fupd_wp.
    iMod (uart_sent_sub_nil_free γ1) as "#Hsub".
    iModIntro.
    (* frame-cell address facts (2-slot frame: ra @ slot 1, s0 @ slot 2) *)
    assert (Hpush : add_vec (m !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6))) = pa_stk (m !!! Regidx csp_rs1) 2).
    { unfold pa_stk, add_vec_int. apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    assert (Hb1 : add_vec (add_vec (m !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6)))) (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000"))) = pa_stk (m !!! Regidx csp_rs1) 1).
    { unfold pa_stk, add_vec_int. rewrite !pa_stk_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb2 : add_vec (add_vec (m !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6)))) (zero_extend' 64 (concat_vec (mword_of_int 0 : mword 6) ('b"000"))) = pa_stk (m !!! Regidx csp_rs1) 2).
    { unfold pa_stk, add_vec_int. rewrite !pa_stk_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    (* ===== PROLOGUE (0x00..0x06) ===== *)
    iApply (wp_caddi_sp_push_s_sconf (mword_of_int KernelSyms.prputc) (mword_of_int 48 : mword 6) m K 2 b Hc2 Hpush
              with "Hcg Hpc []").
    { iApply (ppc_00 with "Htext"). }
    iIntros (CID1 Hs1) "Hcg Hframe Hpc".
    set (W1 := <[Regidx csp_rs1 := regval_into_reg
        (add_vec (m !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6))))]> m).
    iEval (rewrite (stack_own_slots (KTR := kt)); cbn [seq]) in "Hframe".
    iDestruct "Hframe" as "(S1 & S2 & _)".
    iDestruct "S1" as (v1) "Hc1". iDestruct "S2" as (v2) "Hc2".
    assert (HspW1 : W1 !!! Regidx csp_rs1 = add_vec (m !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6)))) by (rewrite /W1 upd_eq; reflexivity).
    assert (Hp02 : add_vec_int (mword_of_int KernelSyms.prputc : mword 64) 2 = mword_of_int (KernelSyms.prputc + 0x02)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp02) in "Hpc".
    (* +0x02 sd ra,8(sp) -> slot 1 *)
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.prputc + 0x02)) (mword_of_int 1 : mword 6) ra_idx
              W1 (K - 2)%nat v1 b with "Hcg Hpc [] [Hc1]").
    { iApply (ppc_02 with "Htext"). }
    { iEval (rewrite HspW1 Hb1). iExact "Hc1". }
    iIntros (CID2 Hs2) "Hcg Hpc Hc1".
    assert (HW1r1 : forall (CID' : CpuId), rget (CID := CID') W1 ra_idx = m !!! Regidx ra_idx)
      by (intros CID'; rgne; rewrite /W1 upd_ne; [reflexivity | reg_neq]).
    iEval (rewrite HspW1 Hb1 HW1r1) in "Hc1".
    assert (Hp04 : add_vec_int (mword_of_int (KernelSyms.prputc + 0x02) : mword 64) 2 = mword_of_int (KernelSyms.prputc + 0x04)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp04) in "Hpc".
    (* +0x04 sd s0,0(sp) -> slot 2 *)
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.prputc + 0x04)) (mword_of_int 0 : mword 6) s0_idx
              W1 (K - 2)%nat v2 b with "Hcg Hpc [] [Hc2]").
    { iApply (ppc_04 with "Htext"). }
    { iEval (rewrite HspW1 Hb2). iExact "Hc2". }
    iIntros (CID3 Hs3) "Hcg Hpc Hc2".
    assert (HW1r8 : forall (CID' : CpuId), rget (CID := CID') W1 s0_idx = m !!! Regidx s0_idx)
      by (intros CID'; rgne; rewrite /W1 upd_ne; [reflexivity | reg_neq]).
    iEval (rewrite HspW1 Hb2 HW1r8) in "Hc2".
    assert (Hp06 : add_vec_int (mword_of_int (KernelSyms.prputc + 0x04) : mword 64) 2 = mword_of_int (KernelSyms.prputc + 0x06)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp06) in "Hpc".
    (* +0x06 addi s0,sp,16 (value unused; s0 reloaded at the epilogue) *)
    iApply (wp_caddi4spn_s_sconf (mword_of_int (KernelSyms.prputc + 0x06)) (Cregidx (mword_of_int 0)) (mword_of_int 4 : mword 8) s0_idx
              W1 (K - 2)%nat b ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc []").
    { iApply (ppc_06 with "Htext"). }
    iIntros (CID4 Hs4) "Hcg Hpc".
    set (W2 := <[Regidx s0_idx := regval_into_reg (add_vec (W1 !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm (mword_of_int 4 : mword 8))))]> W1).
    assert (Hp08 : add_vec_int (mword_of_int (KernelSyms.prputc + 0x06) : mword 64) 2 = mword_of_int (KernelSyms.prputc + 0x08)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp08) in "Hpc".
    (* ===== the two argument moves (0x08..0x0a) ===== *)
    (* +0x08 c.mv a1,a0 : the byte becomes uartputc_sync's SECOND argument *)
    assert (Hrg08 : rget (CID := CID4) W2 a0_idx = W2 !!! Regidx a0_idx)
      by (rgne; reflexivity).
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.prputc + 0x08)) a1_idx a0_idx
              W2 (K - 2)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc []").
    { iApply (ppc_08 with "Htext"). }
    iIntros (CID5 Hs5) "Hcg Hpc".
    iEval (rewrite Hrg08) in "Hcg".
    set (T1 := <[Regidx a1_idx := regval_into_reg (add_vec zero_reg (W2 !!! Regidx a0_idx))]> W2).
    assert (Hp0a : add_vec_int (mword_of_int (KernelSyms.prputc + 0x08) : mword 64) 2 = mword_of_int (KernelSyms.prputc + 0x0a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp0a) in "Hpc".
    (* +0x0a c.li a0,1 : THE PORT INDEX -- [uart_index Uart1] *)
    iApply (wp_cli_s_sconf (mword_of_int (KernelSyms.prputc + 0x0a)) a0_idx (mword_of_int 1 : mword 6)
              (mword_of_int 1 : mword 64) T1 (K - 2)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc []").
    { iApply (ppc_0a with "Htext"). }
    iIntros (CID6 Hs6) "Hcg Hpc".
    set (T2 := <[Regidx a0_idx := regval_into_reg (mword_of_int 1 : mword 64)]> T1).
    assert (Hp0c : add_vec_int (mword_of_int (KernelSyms.prputc + 0x0a) : mword 64) 2 = mword_of_int (KernelSyms.prputc + 0x0c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp0c) in "Hpc".
    (* +0x0c jal uartputc_sync *)
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.prputc + 0x0c)) ra_idx (mword_of_int 1320 : mword 21)
              T2 (K - 2)%nat b ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc []").
    { iApply (ppc_0c with "Htext"). }
    iIntros (CID7 Hs7) "Hcg Hpc".
    set (T3 := <[Regidx ra_idx := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.prputc + 0x0c) : mword 64) 4)]> T2).
    assert (Htgtu : add_vec (mword_of_int (KernelSyms.prputc + 0x0c) : mword 64) (sign_extend' 64 (mword_of_int 1320 : mword 21)) = mword_of_int KernelSyms.uartputc_sync) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgtu) in "Hpc".
    (* a0 IS the port index at the call: the [c.li] set it and the [jal]
       writes only ra. *)
    assert (HT3a0 : T3 !!! Regidx a0_idx = (mword_of_int (uart_index Uart1) : mword 64)).
    { rewrite /T3 upd_ne; [| reg_neq]. rewrite /T2 upd_eq.
      unfold uart_index. reflexivity. }
    iDestruct (cpu_own_transport CID CID7 n eb p b ltac:(wp_next_chain) with "Hcpu") as "Hcpu".
    iApply (wp_uartputc (CID0 := CID7) γl1 γ1 T3 (K - 2)%nat n eb b p lks
              HK18 HT3a0 Hn Hbelow
              with "Hcg Hcpu Htext Hpc Huinv Hbase Htxl Hsub").
    iIntros (CID8 Hs8 mf) "Hcg Hcpu Hpc %Hcs".
    destruct Hcs as [Hcs Hra].
    assert (Hret : ret_pc (T3 !!! Regidx ra_idx) = mword_of_int (KernelSyms.prputc + 0x10)).
    { rewrite /T3 upd_eq. unfold ret_pc. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite Hret) in "Hpc".
    (* the call's callee-saved hop, composed back to the entry map: the
       prologue and the two argument moves touch sp, s0, a1, a0 and ra, so
       every callee-saved index other than sp and s0 survives. *)
    assert (Hthread0 : forall c : mword 5, is_cs_idx c = true ->
              mf !!! Regidx c = W2 !!! Regidx c).
    { intros c Hc.
      pose proof (is_cs_idx_true_neq ra_idx c ltac:(vm_compute; reflexivity) Hc) as N1.
      pose proof (is_cs_idx_true_neq a0_idx c ltac:(vm_compute; reflexivity) Hc) as Na0.
      pose proof (is_cs_idx_true_neq a1_idx c ltac:(vm_compute; reflexivity) Hc) as Na1.
      rewrite (callee_saved_lookup Hcs c Hc).
      rewrite /T3 upd_ne; [| congruence].
      rewrite /T2 upd_ne; [| congruence].
      rewrite /T1 upd_ne; [reflexivity | congruence]. }
    assert (HW2sp : W2 !!! Regidx csp_rs1 = add_vec (m !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6)))).
    { rewrite /W2 upd_ne; [| reg_neq]. exact HspW1. }
    assert (HW2cs : forall c : mword 5, is_cs_idx c = true -> c <> csp_rs1 -> c <> s0_idx ->
              W2 !!! Regidx c = m !!! Regidx c).
    { intros c Hc Nsp N8.
      rewrite /W2 upd_ne; [| congruence].
      rewrite /W1 upd_ne; [reflexivity | congruence]. }
    assert (Hmfsp : mf !!! Regidx csp_rs1 = add_vec (m !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6)))).
    { rewrite (Hthread0 csp_rs1 ltac:(vm_compute; reflexivity)). exact HW2sp. }
    assert (Hthread : forall c : mword 5, is_cs_idx c = true -> c <> csp_rs1 -> c <> s0_idx ->
              mf !!! Regidx c = m !!! Regidx c).
    { intros c Hc Nsp N8. rewrite (Hthread0 c Hc). exact (HW2cs c Hc Nsp N8). }
    (* ===== EPILOGUE (0x10 .. 0x16) ===== *)
    assert (Hbe1 : add_vec (mf !!! Regidx csp_rs1) (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000"))) = pa_stk (m !!! Regidx csp_rs1) 1).
    { rewrite Hmfsp. exact Hb1. }
    assert (Hbe2 : add_vec (mf !!! Regidx csp_rs1) (zero_extend' 64 (concat_vec (mword_of_int 0 : mword 6) ('b"000"))) = pa_stk (m !!! Regidx csp_rs1) 2).
    { rewrite Hmfsp. exact Hb2. }
    (* +0x10 ld ra,8(sp) *)
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.prputc + 0x10)) (mword_of_int 1 : mword 6) ra_idx
              mf (K - 2)%nat (m !!! Regidx ra_idx) b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc [] [Hc1]").
    { iApply (ppc_10 with "Htext"). }
    { iEval (rewrite Hbe1). iExact "Hc1". }
    iIntros (CID9 Hs9) "Hcg Hpc Hc1". iEval (rewrite Hbe1) in "Hc1".
    set (E1 := <[Regidx ra_idx := regval_into_reg (m !!! Regidx ra_idx)]> mf).
    assert (HE1sp : E1 !!! Regidx csp_rs1 = add_vec (m !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6))))
      by (rewrite /E1 upd_ne; [exact Hmfsp | reg_neq]).
    assert (Hp12 : add_vec_int (mword_of_int (KernelSyms.prputc + 0x10) : mword 64) 2 = mword_of_int (KernelSyms.prputc + 0x12)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp12) in "Hpc".
    (* +0x12 ld s0,0(sp) *)
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.prputc + 0x12)) (mword_of_int 0 : mword 6) s0_idx
              E1 (K - 2)%nat (m !!! Regidx s0_idx) b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc [] [Hc2]").
    { iApply (ppc_12 with "Htext"). }
    { iEval (rewrite HE1sp Hb2). iExact "Hc2". }
    iIntros (CID10 Hs10) "Hcg Hpc Hc2". iEval (rewrite HE1sp Hb2) in "Hc2".
    set (E2 := <[Regidx s0_idx := regval_into_reg (m !!! Regidx s0_idx)]> E1).
    assert (HE2sp : E2 !!! Regidx csp_rs1 = add_vec (m !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6))))
      by (rewrite /E2 upd_ne; [exact HE1sp | reg_neq]).
    assert (Hp14 : add_vec_int (mword_of_int (KernelSyms.prputc + 0x12) : mword 64) 2 = mword_of_int (KernelSyms.prputc + 0x14)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp14) in "Hpc".
    (* +0x14 addi sp,sp,16 : the frame pop *)
    assert (Hwv : add_vec (E2 !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 16 : mword 6))) = m !!! Regidx csp_rs1).
    { rewrite HE2sp. apply frame_cancel_16. }
    assert (Hpop : E2 !!! Regidx csp_rs1 = pa_stk (add_vec (E2 !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 16 : mword 6)))) 2).
    { rewrite Hwv. rewrite HE2sp. exact Hpush. }
    iAssert (stack_own (KTR := kt) (m !!! Regidx csp_rs1) 2) with "[Hc1 Hc2]" as "Hframe".
    { rewrite (stack_own_slots (KTR := kt)); cbn [seq].
      iSplitL "Hc1". { iExists (m !!! Regidx ra_idx). iExact "Hc1". }
      iSplitL "Hc2". { iExists (m !!! Regidx s0_idx). iExact "Hc2". }
      done. }
    iEval (rewrite -Hwv) in "Hframe".
    iApply (wp_caddi_sp_pop_s_sconf (mword_of_int (KernelSyms.prputc + 0x14)) (mword_of_int 16 : mword 6)
              E2 (K - 2)%nat 2 b Hpop with "Hcg Hpc [] Hframe").
    { iApply (ppc_14 with "Htext"). }
    iIntros (CID11 Hs11) "Hcg Hpc".
    set (E3 := <[Regidx csp_rs1 := regval_into_reg (add_vec (E2 !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 16 : mword 6))))]> E2).
    iEval (rewrite (pp_nk K Hc2)) in "Hcg".
    assert (Hp16 : add_vec_int (mword_of_int (KernelSyms.prputc + 0x14) : mword 64) 2 = mword_of_int (KernelSyms.prputc + 0x16)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp16) in "Hpc".
    (* +0x16 ret *)
    assert (HE3ra : E3 !!! Regidx ra_idx = m !!! Regidx ra_idx).
    { rewrite /E3 upd_ne; [| reg_neq]. rewrite /E2 upd_ne; [| reg_neq]. rewrite /E1 upd_eq. reflexivity. }
    assert (Hrt : forall (CID' : CpuId), ret_pc (rget (CID := CID') E3 ra_idx) = ret_pc (m !!! Regidx ra_idx))
      by (intros CID'; rgne; rewrite HE3ra; reflexivity).
    iApply (wp_cret_s_sconf (mword_of_int (KernelSyms.prputc + 0x16)) ra_idx E3 K b
              ltac:(vm_compute; discriminate) with "Hcg Hpc []").
    { iApply (ppc_16 with "Htext"). }
    iIntros (CID12 Hs12) "Hcg Hpc". iEval (rewrite Hrt) in "Hpc".
    iDestruct (cpu_own_transport CID8 CID12 n eb p b ltac:(wp_next_chain) with "Hcpu") as "Hcpu".
    iSpecialize ("Hcont" $! CID12 with "[%]"); [wp_next_chain|].
    iApply ("Hcont" $! E3 with "Hcg Hcpu Hpc [%]").
    split; [| exact HE3ra ].
    assert (HthreadE : forall c : mword 5, is_cs_idx c = true ->
              c <> csp_rs1 -> c <> s0_idx -> E3 !!! Regidx c = m !!! Regidx c).
    { intros c Hc Nsp N8.
      pose proof (is_cs_idx_true_neq ra_idx c ltac:(vm_compute; reflexivity) Hc) as N1.
      rewrite /E3 upd_ne; [| congruence].
      rewrite /E2 upd_ne; [| congruence].
      rewrite /E1 upd_ne; [| congruence].
      exact (Hthread c Hc Nsp N8). }
    unfold callee_saved.
    split. { rewrite /E3 upd_eq. exact Hwv. }
    split. { rewrite /E3 upd_ne; [| reg_neq]. rewrite /E2 upd_eq; reflexivity. }
    repeat split; apply HthreadE; vm_compute; first [reflexivity | discriminate].
  Qed.

End ProofPrputc.
