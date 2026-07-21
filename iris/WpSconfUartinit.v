(* WpSconfUartinit.v -- the whole-function WP for xv6's uartinit() over the
   SIE-agnostic sconf world.  uartinit() programs the 16550 (7 MMIO byte
   writes to UART0) then initlock(&tx_lock,"uart").  It runs BEFORE dev_inv is
   allocated, so it owns the raw [uart_frag] half (via the frag store leaf
   Uart.wp_sb_uart_frag_s_sconf) rather than dev_inv + a transmitter token.

   Straight-line, 16-byte frame, one jal sub-call (initlock).  Structurally a
   clone of WpSconfKinit with the freerange/lock-invariant tail replaced by
   returning initlock's raw outputs, and the seven device stores inserted. *)
From Stdlib Require Import Eqdep_dec ZArith Lia List.
From stdpp Require Import gmap list list_monad bitvector.definitions bitvector.tactics.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import excl.
From iris.base_logic.lib Require Import ghost_var gen_heap invariants own.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto.
Require Import RegFile.
Require Import WpGpr InstrBytes WpMmodeLeafBase WpAuipc.
Require Import SmodeCore.
Require Import KptTree.
Require Import StackOwn CalleeSaved.
Require Import KernelText KernelDataInv.
Require Import WpLock.
Require Import DevModel WpUart.
Require Import IntrDefs WpSmodeIntr.
Require Import IntrDefs.
Require Import WpSconfAlu WpSconfMem WpSconfCtl.
Require Import WpInitlock SpecInitlock.
Require Import SpecUart.
Require Import WpUartinitDecode.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SpecUartinit.
Local Open Scope Z_scope.
Import Defs.

(* x0 is pinned to [zero_reg] by the gpr_file (its entry owns only the pure
   value-zero fact).  Extract it while keeping the capability. *)
Lemma sie_cap_gpr_x0 `{!riscvGS Σ, !sieG Σ} `{CID : CpuId} (γ : gname) (root_ppn : mword 44) (m : regfile) (n : nat) :
  sie_cap_gpr γ root_ppn m n ⊢ ⌜ m !!! Regidx (mword_of_int 0 : mword 5) = zero_reg ⌝.
Proof.
  iIntros "Hcg".
  iDestruct (sie_cap_gpr_split with "Hcg") as "[_ Hfile]".
  iDestruct (gpr_file_lookup_acc _ (Regidx (mword_of_int 0 : mword 5)) with "Hfile") as "[Hpt _]".
  unfold gpr_pt.
  replace (uint (mword_of_int 0 : mword 5) =? 0) with true by (vm_compute; reflexivity).
  iDestruct "Hpt" as %H. iPureIntro. rewrite rf_lookup. exact H.
Qed.

Module UartinitProof (Uart : UART) (Initlock : INITLOCK) : UARTINIT.

Section WpSconfUartinit.
  Context `{!riscvGS Σ, !sieG Σ}.
  Context `{CID : CpuId}.

  Notation UI := KernelSyms.uartinit.

  Lemma wp_uartinit_sconf (γ : gname) (root_ppn : mword 44) (Φ : mval -> iProp Σ)
      (m : regfile) (K : nat) (u0 : uart_state) (vlock : bv 32) (vname vcpu : bv 64)
    : wp_uartinit_sconf_body γ root_ppn Φ m K u0 vlock vname vcpu.
  Proof.
    cbv beta delta [wp_uartinit_sconf_body].
    intros pcE ret_tgt lk c_name c_cpu HK Hretm.
    set (sp0 := m !!! Regidx csp_rs1).
    set (spr := add_vec sp0 (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6)))).
    iIntros "Hsc Hhs Hcg Htlbinv #Htext #Hkdata Hpc Huf Hlock Hname Hcpu Hcont".
    iDestruct (sie_cap_gpr_x0 with "Hcg") as %Hx0.
    (* the "uart" string literal, read out of the kernel's data image *)
    assert (Huart : forall j b, cstring_bytes "uart"%string !! j = Some b ->
                      KernelData.kernel_data !! (0x80007030 + Z.of_nat j)%Z = Some b).
    { intros j b Hj.
      do 5 (destruct j as [|j];
            [vm_compute in Hj; injection Hj as <-; vm_compute; reflexivity |]);
      vm_compute in Hj; discriminate. }
    iPoseProof (kernel_data_string 0x80007030 "uart"%string _ eq_refl Huart
                  with "Hkdata") as "#Hstr".
    (* pc-advance helper facts *)
    assert (Hspr2 : spr = pa_stk sp0 2).
    { unfold spr, pa_stk, add_vec_int. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb1 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000"))) = pa_stk sp0 1).
    { unfold spr, sp0, pa_stk, add_vec_int. rewrite pa_stk_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb2 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 0 : mword 6) ('b"000"))) = pa_stk sp0 2).
    { unfold spr, sp0, pa_stk, add_vec_int. rewrite pa_stk_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    iPoseProof (uii_00 with "Htext") as "Hi00".
    iPoseProof (uii_02 with "Htext") as "Hi02".
    iPoseProof (uii_04 with "Htext") as "Hi04".
    iPoseProof (uii_06 with "Htext") as "Hi06".
    iPoseProof (uii_08 with "Htext") as "Hi08".
    iPoseProof (uii_0c with "Htext") as "Hi0c".
    iPoseProof (uii_10 with "Htext") as "Hi10".
    iPoseProof (uii_14 with "Htext") as "Hi14".
    iPoseProof (uii_18 with "Htext") as "Hi18".
    iPoseProof (uii_1c with "Htext") as "Hi1c".
    iPoseProof (uii_1e with "Htext") as "Hi1e".
    iPoseProof (uii_22 with "Htext") as "Hi22".
    iPoseProof (uii_26 with "Htext") as "Hi26".
    iPoseProof (uii_2a with "Htext") as "Hi2a".
    iPoseProof (uii_2e with "Htext") as "Hi2e".
    iPoseProof (uii_30 with "Htext") as "Hi30".
    iPoseProof (uii_32 with "Htext") as "Hi32".
    iPoseProof (uii_36 with "Htext") as "Hi36".
    iPoseProof (uii_3a with "Htext") as "Hi3a".
    iPoseProof (uii_3e with "Htext") as "Hi3e".
    iPoseProof (uii_42 with "Htext") as "Hi42".
    iPoseProof (uii_46 with "Htext") as "Hi46".
    iPoseProof (uii_4a with "Htext") as "Hi4a".
    iPoseProof (uii_4e with "Htext") as "Hi4e".
    iPoseProof (uii_50 with "Htext") as "Hi50".
    iPoseProof (uii_52 with "Htext") as "Hi52".
    iPoseProof (uii_54 with "Htext") as "Hi54".
    (* ===== PROLOGUE 0x00..0x06: 2-slot frame + save ra/s0 ===== *)
    set (R1 := <[Regidx csp_rs1 := regval_into_reg (add_vec sp0 (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6))))]> m).
    assert (Hspm : m !!! Regidx csp_rs1 = sp0) by reflexivity.
    assert (Hpush : add_vec (m !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6))) = pa_stk (m !!! Regidx csp_rs1) 2).
    { unfold pa_stk, add_vec_int. apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    iApply (wp_caddi_sp_push_s_sconf γ root_ppn Φ pcE (mword_of_int 48 : mword 6) m K 2 ltac:(lia) Hpush
              with "Hsc Hhs Hcg Htlbinv Hpc Hi00 [-]").
    iIntros "Hhs Hsc Hcg Hframe Htlbinv Hpc".
    iEval (rewrite Hspm) in "Hframe".
    change (<[Regidx csp_rs1 := regval_into_reg (add_vec sp0 (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6))))]> m) with R1.
    assert (HspR1 : R1 !!! Regidx csp_rs1 = spr) by (rewrite /R1 upd_eq; reflexivity).
    iEval (rewrite stack_own_slots; cbn [seq]) in "Hframe".
    iDestruct "Hframe" as "(S1 & S2 & _)".
    iDestruct "S1" as (vra0) "Hras". iDestruct "S2" as (vs00) "Hs0s".
    assert (Hpp02 : add_vec_int (pcE : mword 64) 2 = mword_of_int (UI + 0x02)) by (unfold pcE; apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp02) in "Hpc".
    (* +0x02 c.sdsp ra,8(sp) *)
    iApply (wp_csdsp_s_sconf γ root_ppn Φ (mword_of_int (UI + 0x02)) (mword_of_int 1 : mword 6) (mword_of_int 1 : mword 5)
              R1 (K - 2)%nat vra0 with "Hsc Hhs Hcg Htlbinv Hpc Hi02 [Hras] [-]").
    { iEval (rewrite HspR1 Hb1). iExact "Hras". }
    iIntros "Hhs Hsc Hcg Htlbinv Hpc Hras".
    iEval (rewrite HspR1 Hb1) in "Hras".
    assert (Hrav : R1 !!! Regidx (mword_of_int 1 : mword 5) = m !!! Regidx (mword_of_int 1 : mword 5))
      by (rewrite /R1 upd_ne; [reflexivity | vm_compute; discriminate]).
    iEval (rewrite Hrav) in "Hras".
    assert (Hpp04 : add_vec_int (mword_of_int (UI + 0x02) : mword 64) 2 = mword_of_int (UI + 0x04)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp04) in "Hpc".
    (* +0x04 c.sdsp s0,0(sp) *)
    iApply (wp_csdsp_s_sconf γ root_ppn Φ (mword_of_int (UI + 0x04)) (mword_of_int 0 : mword 6) (mword_of_int 8 : mword 5)
              R1 (K - 2)%nat vs00 with "Hsc Hhs Hcg Htlbinv Hpc Hi04 [Hs0s] [-]").
    { iEval (rewrite HspR1 Hb2). iExact "Hs0s". }
    iIntros "Hhs Hsc Hcg Htlbinv Hpc Hs0s".
    iEval (rewrite HspR1 Hb2) in "Hs0s".
    assert (Hs0v : R1 !!! Regidx (mword_of_int 8 : mword 5) = m !!! Regidx (mword_of_int 8 : mword 5))
      by (rewrite /R1 upd_ne; [reflexivity | vm_compute; discriminate]).
    iEval (rewrite Hs0v) in "Hs0s".
    assert (Hpp06 : add_vec_int (mword_of_int (UI + 0x04) : mword 64) 2 = mword_of_int (UI + 0x06)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp06) in "Hpc".
    (* +0x06 c.addi4spn s0,sp,16 *)
    iApply (wp_caddi4spn_s_sconf γ root_ppn Φ (mword_of_int (UI + 0x06)) (Cregidx (mword_of_int 0)) (mword_of_int 4 : mword 8) (mword_of_int 8 : mword 5)
              R1 (K - 2)%nat ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hsc Hhs Hcg Htlbinv Hpc Hi06 [-]").
    iIntros "Hhs Hsc Hcg Htlbinv Hpc".
    set (R2 := <[Regidx (mword_of_int 8 : mword 5) := regval_into_reg (add_vec (R1 !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm (mword_of_int 4 : mword 8))))]> R1).
    assert (Hpp08 : add_vec_int (mword_of_int (UI + 0x06) : mword 64) 2 = mword_of_int (UI + 0x08)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp08) in "Hpc".
    (* ===== BODY: address setup + 7 device stores ===== *)
    (* +0x08 lui a5,0x10000 *)
    iApply (wp_lui_s_sconf γ root_ppn Φ (mword_of_int (UI + 0x08)) (mword_of_int 15 : mword 5) (mword_of_int 0x10000 : mword 20)
              (luival (mword_of_int 0x10000 : mword 20)) R2 (K - 2)%nat ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) eq_refl
              with "Hsc Hhs Hcg Htlbinv Hpc Hi08 [-]").
    iIntros "Hhs Hsc Hcg Htlbinv Hpc".
    set (R3 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (luival (mword_of_int 0x10000 : mword 20))]> R2).
    assert (HR3a5 : R3 !!! Regidx (mword_of_int 15 : mword 5) = uart_pa 0)
      by (rewrite /R3 upd_eq; unfold uart_pa, uart_base; apply bv_eq; vm_compute; reflexivity).
    assert (HR3x0 : R3 !!! Regidx (mword_of_int 0 : mword 5) = zero_reg).
    { rewrite /R3 upd_ne; [| vm_compute; discriminate].
      rewrite /R2 upd_ne; [| vm_compute; discriminate].
      rewrite /R1 upd_ne; [exact Hx0 | vm_compute; discriminate]. }
    assert (Hpp0c : add_vec_int (mword_of_int (UI + 0x08) : mword 64) 4 = mword_of_int (UI + 0x0c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp0c) in "Hpc".
    (* +0x0c sb zero,1(a5) : off 1, byte from x0 (=0); result discarded downstream *)
    set (b1 := autocast (T := mword) (subrange_vec_dec (R3 !!! Regidx (mword_of_int 0 : mword 5)) (Z.sub (Z.mul 1 8) 1) 0) : mword 8).
    set (u1 := if uart_dlab u0
               then UartState (u_rx u0) (u_tx u0) (u_out u0) (u_ier u0) (u_lcr u0) (u_fcr u0) (u_dll u0) b1
               else UartState (u_rx u0) (u_tx u0) (u_out u0) b1 (u_lcr u0) (u_fcr u0) (u_dll u0) (u_dlm u0)).
    assert (Hw1 : uart_write u0 1 b1 = Some u1).
    { unfold u1, uart_write. destruct (uart_dlab u0); reflexivity. }
    iApply (Uart.wp_sb_uart_frag_s_sconf γ root_ppn 1 Φ (mword_of_int (UI + 0x0c)) false (mword_of_int 0 : mword 5) (mword_of_int 15 : mword 5) (mword_of_int 1 : mword 12)
              R3 (K - 2)%nat u0 u1
              ltac:(unfold uart_size; lia)
              Hw1
              ltac:(rewrite HR3a5; vm_compute; reflexivity)
              ltac:(rewrite HR3a5; apply bv_eq; vm_compute; reflexivity)
              ltac:(rewrite HR3a5; apply bv_eq; vm_compute; reflexivity)
              ltac:(rewrite HR3a5; apply bv_eq; vm_compute; reflexivity)
              with "Hsc Hhs Hcg Htlbinv Hpc Hi0c Huf [-]").
    iIntros "Hhs Hsc Hcg Htlbinv Hpc Huf".
    assert (Hpp10 : add_vec_int (mword_of_int (UI + 0x0c) : mword 64) 4 = mword_of_int (UI + 0x10)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp10) in "Hpc".
    (* +0x10 lui a4,0x10000 *)
    iApply (wp_lui_s_sconf γ root_ppn Φ (mword_of_int (UI + 0x10)) (mword_of_int 14 : mword 5) (mword_of_int 0x10000 : mword 20)
              (luival (mword_of_int 0x10000 : mword 20)) R3 (K - 2)%nat ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) eq_refl
              with "Hsc Hhs Hcg Htlbinv Hpc Hi10 [-]").
    iIntros "Hhs Hsc Hcg Htlbinv Hpc".
    set (R4 := <[Regidx (mword_of_int 14 : mword 5) := regval_into_reg (luival (mword_of_int 0x10000 : mword 20))]> R3).
    assert (HR4a4 : R4 !!! Regidx (mword_of_int 14 : mword 5) = uart_pa 0)
      by (rewrite /R4 upd_eq; unfold uart_pa, uart_base; apply bv_eq; vm_compute; reflexivity).
    assert (HR4x0 : R4 !!! Regidx (mword_of_int 0 : mword 5) = zero_reg)
      by (rewrite /R4 upd_ne; [exact HR3x0 | vm_compute; discriminate]).
    assert (Hpp14 : add_vec_int (mword_of_int (UI + 0x10) : mword 64) 4 = mword_of_int (UI + 0x14)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp14) in "Hpc".
    (* +0x14 li a3,-128 (addi a3,zero,-128) *)
    iApply (wp_addi4_s_sconf γ root_ppn Φ (mword_of_int (UI + 0x14)) (mword_of_int 13 : mword 5) (mword_of_int 0 : mword 5) (mword_of_int 3968 : mword 12)
              R4 (K - 2)%nat ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hsc Hhs Hcg Htlbinv Hpc Hi14 [-]").
    iIntros "Hhs Hsc Hcg Htlbinv Hpc".
    set (R5 := <[Regidx (mword_of_int 13 : mword 5) := regval_into_reg (add_vec (R4 !!! Regidx (mword_of_int 0 : mword 5)) (sign_extend' 64 (mword_of_int 3968 : mword 12)))]> R4).
    assert (HR5a4 : R5 !!! Regidx (mword_of_int 14 : mword 5) = uart_pa 0)
      by (rewrite /R5 upd_ne; [exact HR4a4 | vm_compute; discriminate]).
    assert (Hpp18 : add_vec_int (mword_of_int (UI + 0x14) : mword 64) 4 = mword_of_int (UI + 0x18)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp18) in "Hpc".
    (* +0x18 sb a3,3(a4) : off3 -> lcr := 0x80, dlab on *)
    set (u2 := UartState (u_rx u1) (u_tx u1) (u_out u1) (u_ier u1) (Z_to_bv 8 128) (u_fcr u1) (u_dll u1) (u_dlm u1)).
    assert (Hw2 : uart_write u1 3 (autocast (T := mword) (subrange_vec_dec (R5 !!! Regidx (mword_of_int 13 : mword 5)) (Z.sub (Z.mul 1 8) 1) 0) : mword 8) = Some u2).
    { assert (Hb : (autocast (T := mword) (subrange_vec_dec (R5 !!! Regidx (mword_of_int 13 : mword 5)) (Z.sub (Z.mul 1 8) 1) 0) : mword 8) = Z_to_bv 8 128).
      { rewrite /R5 upd_eq HR4x0. apply bv_eq; vm_compute; reflexivity. }
      rewrite Hb. unfold u2, uart_write. reflexivity. }
    iApply (Uart.wp_sb_uart_frag_s_sconf γ root_ppn 3 Φ (mword_of_int (UI + 0x18)) false (mword_of_int 13 : mword 5) (mword_of_int 14 : mword 5) (mword_of_int 3 : mword 12)
              R5 (K - 2)%nat u1 u2
              ltac:(unfold uart_size; lia) Hw2
              ltac:(rewrite HR5a4; vm_compute; reflexivity)
              ltac:(rewrite HR5a4; apply bv_eq; vm_compute; reflexivity)
              ltac:(rewrite HR5a4; apply bv_eq; vm_compute; reflexivity)
              ltac:(rewrite HR5a4; apply bv_eq; vm_compute; reflexivity)
              with "Hsc Hhs Hcg Htlbinv Hpc Hi18 Huf [-]").
    iIntros "Hhs Hsc Hcg Htlbinv Hpc Huf".
    assert (Hpp1c : add_vec_int (mword_of_int (UI + 0x18) : mword 64) 4 = mword_of_int (UI + 0x1c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp1c) in "Hpc".
    (* +0x1c c.li a3,3 *)
    iApply (wp_cli_s_sconf γ root_ppn Φ (mword_of_int (UI + 0x1c)) (mword_of_int 13 : mword 5) (mword_of_int 3 : mword 6) (mword_of_int 3 : mword 64)
              R5 (K - 2)%nat ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) ltac:(vm_compute; reflexivity)
              with "Hsc Hhs Hcg Htlbinv Hpc Hi1c [-]").
    iIntros "Hhs Hsc Hcg Htlbinv Hpc".
    set (R6 := <[Regidx (mword_of_int 13 : mword 5) := regval_into_reg (mword_of_int 3 : mword 64)]> R5).
    assert (Hpp1e : add_vec_int (mword_of_int (UI + 0x1c) : mword 64) 2 = mword_of_int (UI + 0x1e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp1e) in "Hpc".
    (* +0x1e lui a2,0x10000 *)
    iApply (wp_lui_s_sconf γ root_ppn Φ (mword_of_int (UI + 0x1e)) (mword_of_int 12 : mword 5) (mword_of_int 0x10000 : mword 20)
              (luival (mword_of_int 0x10000 : mword 20)) R6 (K - 2)%nat ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) eq_refl
              with "Hsc Hhs Hcg Htlbinv Hpc Hi1e [-]").
    iIntros "Hhs Hsc Hcg Htlbinv Hpc".
    set (R7 := <[Regidx (mword_of_int 12 : mword 5) := regval_into_reg (luival (mword_of_int 0x10000 : mword 20))]> R6).
    assert (HR7a2 : R7 !!! Regidx (mword_of_int 12 : mword 5) = uart_pa 0)
      by (rewrite /R7 upd_eq; unfold uart_pa, uart_base; apply bv_eq; vm_compute; reflexivity).
    assert (HR7a5 : R7 !!! Regidx (mword_of_int 15 : mword 5) = uart_pa 0).
    { rewrite /R7 upd_ne; [| vm_compute; discriminate].
      rewrite /R6 upd_ne; [| vm_compute; discriminate].
      rewrite /R5 upd_ne; [| vm_compute; discriminate].
      rewrite /R4 upd_ne; [exact HR3a5 | vm_compute; discriminate]. }
    assert (HR7a4 : R7 !!! Regidx (mword_of_int 14 : mword 5) = uart_pa 0).
    { rewrite /R7 upd_ne; [| vm_compute; discriminate].
      rewrite /R6 upd_ne; [| vm_compute; discriminate].
      rewrite /R5 upd_ne; [exact HR4a4 | vm_compute; discriminate]. }
    assert (HR7a3 : R7 !!! Regidx (mword_of_int 13 : mword 5) = mword_of_int 3).
    { rewrite /R7 upd_ne; [| vm_compute; discriminate].
      rewrite /R6 upd_eq; reflexivity. }
    assert (HR7x0 : R7 !!! Regidx (mword_of_int 0 : mword 5) = zero_reg).
    { rewrite /R7 upd_ne; [| vm_compute; discriminate].
      rewrite /R6 upd_ne; [| vm_compute; discriminate].
      rewrite /R5 upd_ne; [| vm_compute; discriminate].
      rewrite /R4 upd_ne; [exact HR3x0 | vm_compute; discriminate]. }
    assert (Hpp22 : add_vec_int (mword_of_int (UI + 0x1e) : mword 64) 4 = mword_of_int (UI + 0x22)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp22) in "Hpc".
    (* +0x22 sb a3,0(a2) : off0 dlab-on -> dll := 3 *)
    set (u3 := UartState (u_rx u2) (u_tx u2) (u_out u2) (u_ier u2) (u_lcr u2) (u_fcr u2) (Z_to_bv 8 3) (u_dlm u2)).
    assert (Hw3 : uart_write u2 0 (autocast (T := mword) (subrange_vec_dec (R7 !!! Regidx (mword_of_int 13 : mword 5)) (Z.sub (Z.mul 1 8) 1) 0) : mword 8) = Some u3).
    { assert (Hb : (autocast (T := mword) (subrange_vec_dec (R7 !!! Regidx (mword_of_int 13 : mword 5)) (Z.sub (Z.mul 1 8) 1) 0) : mword 8) = Z_to_bv 8 3).
      { rewrite HR7a3. apply bv_eq; vm_compute; reflexivity. }
      rewrite Hb. unfold u3, uart_write. reflexivity. }
    iApply (Uart.wp_sb_uart_frag_s_sconf γ root_ppn 0 Φ (mword_of_int (UI + 0x22)) false (mword_of_int 13 : mword 5) (mword_of_int 12 : mword 5) (mword_of_int 0 : mword 12)
              R7 (K - 2)%nat u2 u3
              ltac:(unfold uart_size; lia) Hw3
              ltac:(rewrite HR7a2; vm_compute; reflexivity)
              ltac:(rewrite HR7a2; apply bv_eq; vm_compute; reflexivity)
              ltac:(rewrite HR7a2; apply bv_eq; vm_compute; reflexivity)
              ltac:(rewrite HR7a2; apply bv_eq; vm_compute; reflexivity)
              with "Hsc Hhs Hcg Htlbinv Hpc Hi22 Huf [-]").
    iIntros "Hhs Hsc Hcg Htlbinv Hpc Huf".
    assert (Hpp26 : add_vec_int (mword_of_int (UI + 0x22) : mword 64) 4 = mword_of_int (UI + 0x26)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp26) in "Hpc".
    (* +0x26 sb zero,1(a5) : off1 dlab-on -> dlm := 0 (x0) *)
    set (b4 := autocast (T := mword) (subrange_vec_dec (R7 !!! Regidx (mword_of_int 0 : mword 5)) (Z.sub (Z.mul 1 8) 1) 0) : mword 8).
    set (u4 := UartState (u_rx u3) (u_tx u3) (u_out u3) (u_ier u3) (u_lcr u3) (u_fcr u3) (u_dll u3) b4).
    assert (Hw4 : uart_write u3 1 b4 = Some u4).
    { unfold u4, uart_write. reflexivity. }
    iApply (Uart.wp_sb_uart_frag_s_sconf γ root_ppn 1 Φ (mword_of_int (UI + 0x26)) false (mword_of_int 0 : mword 5) (mword_of_int 15 : mword 5) (mword_of_int 1 : mword 12)
              R7 (K - 2)%nat u3 u4
              ltac:(unfold uart_size; lia) Hw4
              ltac:(rewrite HR7a5; vm_compute; reflexivity)
              ltac:(rewrite HR7a5; apply bv_eq; vm_compute; reflexivity)
              ltac:(rewrite HR7a5; apply bv_eq; vm_compute; reflexivity)
              ltac:(rewrite HR7a5; apply bv_eq; vm_compute; reflexivity)
              with "Hsc Hhs Hcg Htlbinv Hpc Hi26 Huf [-]").
    iIntros "Hhs Hsc Hcg Htlbinv Hpc Huf".
    assert (Hpp2a : add_vec_int (mword_of_int (UI + 0x26) : mword 64) 4 = mword_of_int (UI + 0x2a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp2a) in "Hpc".
    (* +0x2a sb a3,3(a4) : off3 -> lcr := 3, dlab off *)
    set (u5 := UartState (u_rx u4) (u_tx u4) (u_out u4) (u_ier u4) (Z_to_bv 8 3) (u_fcr u4) (u_dll u4) (u_dlm u4)).
    assert (Hw5 : uart_write u4 3 (autocast (T := mword) (subrange_vec_dec (R7 !!! Regidx (mword_of_int 13 : mword 5)) (Z.sub (Z.mul 1 8) 1) 0) : mword 8) = Some u5).
    { assert (Hb : (autocast (T := mword) (subrange_vec_dec (R7 !!! Regidx (mword_of_int 13 : mword 5)) (Z.sub (Z.mul 1 8) 1) 0) : mword 8) = Z_to_bv 8 3).
      { rewrite HR7a3. apply bv_eq; vm_compute; reflexivity. }
      rewrite Hb. unfold u5, uart_write. reflexivity. }
    iApply (Uart.wp_sb_uart_frag_s_sconf γ root_ppn 3 Φ (mword_of_int (UI + 0x2a)) false (mword_of_int 13 : mword 5) (mword_of_int 14 : mword 5) (mword_of_int 3 : mword 12)
              R7 (K - 2)%nat u4 u5
              ltac:(unfold uart_size; lia) Hw5
              ltac:(rewrite HR7a4; vm_compute; reflexivity)
              ltac:(rewrite HR7a4; apply bv_eq; vm_compute; reflexivity)
              ltac:(rewrite HR7a4; apply bv_eq; vm_compute; reflexivity)
              ltac:(rewrite HR7a4; apply bv_eq; vm_compute; reflexivity)
              with "Hsc Hhs Hcg Htlbinv Hpc Hi2a Huf [-]").
    iIntros "Hhs Hsc Hcg Htlbinv Hpc Huf".
    assert (Hpp2e : add_vec_int (mword_of_int (UI + 0x2a) : mword 64) 4 = mword_of_int (UI + 0x2e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp2e) in "Hpc".
    (* +0x2e c.mv a4,a2 *)
    iApply (wp_cmv_s_sconf γ root_ppn Φ (mword_of_int (UI + 0x2e)) (mword_of_int 14 : mword 5) (mword_of_int 12 : mword 5)
              R7 (K - 2)%nat ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hsc Hhs Hcg Htlbinv Hpc Hi2e [-]").
    iIntros "Hhs Hsc Hcg Htlbinv Hpc".
    set (R8 := <[Regidx (mword_of_int 14 : mword 5) := regval_into_reg (add_vec zero_reg (R7 !!! Regidx (mword_of_int 12 : mword 5)))]> R7).
    assert (HR8a4 : R8 !!! Regidx (mword_of_int 14 : mword 5) = uart_pa 0).
    { rewrite /R8 upd_eq. rewrite HR7a2. apply bv_eq; vm_compute; reflexivity. }
    assert (Hpp30 : add_vec_int (mword_of_int (UI + 0x2e) : mword 64) 2 = mword_of_int (UI + 0x30)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp30) in "Hpc".
    (* +0x30 c.li a2,7 *)
    iApply (wp_cli_s_sconf γ root_ppn Φ (mword_of_int (UI + 0x30)) (mword_of_int 12 : mword 5) (mword_of_int 7 : mword 6) (mword_of_int 7 : mword 64)
              R8 (K - 2)%nat ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) ltac:(vm_compute; reflexivity)
              with "Hsc Hhs Hcg Htlbinv Hpc Hi30 [-]").
    iIntros "Hhs Hsc Hcg Htlbinv Hpc".
    set (R9 := <[Regidx (mword_of_int 12 : mword 5) := regval_into_reg (mword_of_int 7 : mword 64)]> R8).
    assert (HR9a4 : R9 !!! Regidx (mword_of_int 14 : mword 5) = uart_pa 0)
      by (rewrite /R9 upd_ne; [exact HR8a4 | vm_compute; discriminate]).
    assert (HR9a5 : R9 !!! Regidx (mword_of_int 15 : mword 5) = uart_pa 0).
    { rewrite /R9 upd_ne; [| vm_compute; discriminate].
      rewrite /R8 upd_ne; [exact HR7a5 | vm_compute; discriminate]. }
    assert (HR9a2 : R9 !!! Regidx (mword_of_int 12 : mword 5) = mword_of_int 7)
      by (rewrite /R9 upd_eq; reflexivity).
    assert (HR9a3 : R9 !!! Regidx (mword_of_int 13 : mword 5) = mword_of_int 3).
    { rewrite /R9 upd_ne; [| vm_compute; discriminate].
      rewrite /R8 upd_ne; [exact HR7a3 | vm_compute; discriminate]. }
    assert (Hpp32 : add_vec_int (mword_of_int (UI + 0x30) : mword 64) 2 = mword_of_int (UI + 0x32)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp32) in "Hpc".
    (* +0x32 sb a2,2(a4) : off2 -> fcr := 7, clear rx/tx FIFOs *)
    set (u6 := UartState [] [] (u_out u5) (u_ier u5) (u_lcr u5) (Z_to_bv 8 7) (u_dll u5) (u_dlm u5)).
    assert (Hw6 : uart_write u5 2 (autocast (T := mword) (subrange_vec_dec (R9 !!! Regidx (mword_of_int 12 : mword 5)) (Z.sub (Z.mul 1 8) 1) 0) : mword 8) = Some u6).
    { assert (Hb : (autocast (T := mword) (subrange_vec_dec (R9 !!! Regidx (mword_of_int 12 : mword 5)) (Z.sub (Z.mul 1 8) 1) 0) : mword 8) = Z_to_bv 8 7).
      { rewrite HR9a2. apply bv_eq; vm_compute; reflexivity. }
      rewrite Hb. unfold u6, uart_write. reflexivity. }
    iApply (Uart.wp_sb_uart_frag_s_sconf γ root_ppn 2 Φ (mword_of_int (UI + 0x32)) false (mword_of_int 12 : mword 5) (mword_of_int 14 : mword 5) (mword_of_int 2 : mword 12)
              R9 (K - 2)%nat u5 u6
              ltac:(unfold uart_size; lia) Hw6
              ltac:(rewrite HR9a4; vm_compute; reflexivity)
              ltac:(rewrite HR9a4; apply bv_eq; vm_compute; reflexivity)
              ltac:(rewrite HR9a4; apply bv_eq; vm_compute; reflexivity)
              ltac:(rewrite HR9a4; apply bv_eq; vm_compute; reflexivity)
              with "Hsc Hhs Hcg Htlbinv Hpc Hi32 Huf [-]").
    iIntros "Hhs Hsc Hcg Htlbinv Hpc Huf".
    assert (Hpp36 : add_vec_int (mword_of_int (UI + 0x32) : mword 64) 4 = mword_of_int (UI + 0x36)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp36) in "Hpc".
    (* +0x36 sb a3,1(a5) : off1 dlab-off -> ier := 3 *)
    set (u7 := UartState (u_rx u6) (u_tx u6) (u_out u6) (Z_to_bv 8 3) (u_lcr u6) (u_fcr u6) (u_dll u6) (u_dlm u6)).
    assert (Hw7 : uart_write u6 1 (autocast (T := mword) (subrange_vec_dec (R9 !!! Regidx (mword_of_int 13 : mword 5)) (Z.sub (Z.mul 1 8) 1) 0) : mword 8) = Some u7).
    { assert (Hb : (autocast (T := mword) (subrange_vec_dec (R9 !!! Regidx (mword_of_int 13 : mword 5)) (Z.sub (Z.mul 1 8) 1) 0) : mword 8) = Z_to_bv 8 3).
      { rewrite HR9a3. apply bv_eq; vm_compute; reflexivity. }
      rewrite Hb. unfold u7, uart_write. reflexivity. }
    iApply (Uart.wp_sb_uart_frag_s_sconf γ root_ppn 1 Φ (mword_of_int (UI + 0x36)) false (mword_of_int 13 : mword 5) (mword_of_int 15 : mword 5) (mword_of_int 1 : mword 12)
              R9 (K - 2)%nat u6 u7
              ltac:(unfold uart_size; lia) Hw7
              ltac:(rewrite HR9a5; vm_compute; reflexivity)
              ltac:(rewrite HR9a5; apply bv_eq; vm_compute; reflexivity)
              ltac:(rewrite HR9a5; apply bv_eq; vm_compute; reflexivity)
              ltac:(rewrite HR9a5; apply bv_eq; vm_compute; reflexivity)
              with "Hsc Hhs Hcg Htlbinv Hpc Hi36 Huf [-]").
    iIntros "Hhs Hsc Hcg Htlbinv Hpc Huf".
    (* device programming done; u7 = uartinit_post u0 *)
    assert (Hb4v : b4 = Z_to_bv 8 0).
    { unfold b4. rewrite HR7x0. apply bv_eq; vm_compute; reflexivity. }
    assert (Hfin : u7 = uartinit_post u0).
    { unfold u7, u6, u5, u4, u3, u2, u1, uartinit_post.
      rewrite Hb4v.
      cbn [u_rx u_tx u_out u_ier u_lcr u_fcr u_dll u_dlm].
      destruct (uart_dlab u0); reflexivity. }
    iEval (rewrite Hfin) in "Huf".
    (* carry the saved-slot cells + register facts through *)
    assert (HR9sp : R9 !!! Regidx csp_rs1 = spr).
    { rewrite /R9 upd_ne; [| vm_compute; discriminate].
      rewrite /R8 upd_ne; [| vm_compute; discriminate].
      rewrite /R7 upd_ne; [| vm_compute; discriminate].
      rewrite /R6 upd_ne; [| vm_compute; discriminate].
      rewrite /R5 upd_ne; [| vm_compute; discriminate].
      rewrite /R4 upd_ne; [| vm_compute; discriminate].
      rewrite /R3 upd_ne; [| vm_compute; discriminate].
      rewrite /R2 upd_ne; [exact HspR1 | vm_compute; discriminate]. }
    assert (Hpp3a : add_vec_int (mword_of_int (UI + 0x36) : mword 64) 4 = mword_of_int (UI + 0x3a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp3a) in "Hpc".
    (* ===== args: a1 = "uart", a0 = &tx_lock (0x3a..0x46) ===== *)
    (* +0x3a auipc a1,0x6 *)
    iApply (wp_auipc_s_sconf γ root_ppn Φ (mword_of_int (UI + 0x3a)) (mword_of_int 11 : mword 5) (mword_of_int 6 : mword 20)
              R9 (K - 2)%nat ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hsc Hhs Hcg Htlbinv Hpc Hi3a [-]").
    iIntros "Hhs Hsc Hcg Htlbinv Hpc".
    set (R10 := <[Regidx (mword_of_int 11 : mword 5) := regval_into_reg (add_vec (mword_of_int (UI + 0x3a) : mword 64) (auipc_off (mword_of_int 6 : mword 20)))]> R9).
    assert (Hpp3e : add_vec_int (mword_of_int (UI + 0x3a) : mword 64) 4 = mword_of_int (UI + 0x3e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp3e) in "Hpc".
    (* +0x3e addi a1,a1,1904 *)
    iApply (wp_addi4_s_sconf γ root_ppn Φ (mword_of_int (UI + 0x3e)) (mword_of_int 11 : mword 5) (mword_of_int 11 : mword 5) (mword_of_int 1904 : mword 12)
              R10 (K - 2)%nat ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hsc Hhs Hcg Htlbinv Hpc Hi3e [-]").
    iIntros "Hhs Hsc Hcg Htlbinv Hpc".
    set (R11 := <[Regidx (mword_of_int 11 : mword 5) := regval_into_reg (add_vec (R10 !!! Regidx (mword_of_int 11 : mword 5)) (sign_extend' 64 (mword_of_int 1904 : mword 12)))]> R10).
    (* a1 now holds &"uart" -- the string initlock is about to store *)
    assert (HR11a1 : R11 !!! Regidx (mword_of_int 11 : mword 5) = (mword_of_int 0x80007030 : mword 64)).
    { rewrite /R11 upd_eq. rewrite /R10 upd_eq. apply bv_eq; vm_compute; reflexivity. }
    assert (Hpp42 : add_vec_int (mword_of_int (UI + 0x3e) : mword 64) 4 = mword_of_int (UI + 0x42)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp42) in "Hpc".
    (* +0x42 auipc a0,0x12 *)
    iApply (wp_auipc_s_sconf γ root_ppn Φ (mword_of_int (UI + 0x42)) (mword_of_int 10 : mword 5) (mword_of_int 18 : mword 20)
              R11 (K - 2)%nat ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hsc Hhs Hcg Htlbinv Hpc Hi42 [-]").
    iIntros "Hhs Hsc Hcg Htlbinv Hpc".
    set (R12 := <[Regidx (mword_of_int 10 : mword 5) := regval_into_reg (add_vec (mword_of_int (UI + 0x42) : mword 64) (auipc_off (mword_of_int 18 : mword 20)))]> R11).
    assert (Hpp46 : add_vec_int (mword_of_int (UI + 0x42) : mword 64) 4 = mword_of_int (UI + 0x46)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp46) in "Hpc".
    (* +0x46 addi a0,a0,2632  (a0 := &tx_lock = lk) *)
    iApply (wp_addi4_s_sconf γ root_ppn Φ (mword_of_int (UI + 0x46)) (mword_of_int 10 : mword 5) (mword_of_int 10 : mword 5) (mword_of_int 2632 : mword 12)
              R12 (K - 2)%nat ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hsc Hhs Hcg Htlbinv Hpc Hi46 [-]").
    iIntros "Hhs Hsc Hcg Htlbinv Hpc".
    set (R13 := <[Regidx (mword_of_int 10 : mword 5) := regval_into_reg (add_vec (R12 !!! Regidx (mword_of_int 10 : mword 5)) (sign_extend' 64 (mword_of_int 2632 : mword 12)))]> R12).
    assert (HR13a0 : R13 !!! Regidx (mword_of_int 10 : mword 5) = lk).
    { rewrite /R13 upd_eq. rewrite /R12 upd_eq. unfold lk. apply bv_eq; vm_compute; reflexivity. }
    assert (HR13sp : R13 !!! Regidx csp_rs1 = spr).
    { rewrite /R13 upd_ne; [| vm_compute; discriminate].
      rewrite /R12 upd_ne; [| vm_compute; discriminate].
      rewrite /R11 upd_ne; [| vm_compute; discriminate].
      rewrite /R10 upd_ne; [exact HR9sp | vm_compute; discriminate]. }
    assert (Hpp4a : add_vec_int (mword_of_int (UI + 0x46) : mword 64) 4 = mword_of_int (UI + 0x4a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp4a) in "Hpc".
    (* ===== jal initlock (0x4a) ===== *)
    iApply (wp_jal_s_sconf γ root_ppn Φ (mword_of_int (UI + 0x4a)) (mword_of_int 1 : mword 5) (mword_of_int 696 : mword 21)
              R13 (K - 2)%nat ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) ltac:(vm_compute; reflexivity)
              with "Hsc Hhs Hcg Htlbinv Hpc Hi4a [-]").
    iIntros "Hhs Hsc Hcg Htlbinv Hpc".
    set (R14 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (UI + 0x4a) : mword 64) 4)]> R13).
    assert (Htgtil : add_vec (mword_of_int (UI + 0x4a) : mword 64) (sign_extend' 64 (mword_of_int 696 : mword 21)) = mword_of_int KernelSyms.initlock) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgtil) in "Hpc".
    assert (HR14a0 : R14 !!! Regidx (mword_of_int 10 : mword 5) = lk)
      by (rewrite /R14 upd_ne; [exact HR13a0 | vm_compute; discriminate]).
    assert (HR14a1 : R14 !!! Regidx (mword_of_int 11 : mword 5) = (mword_of_int 0x80007030 : mword 64)).
    { rewrite /R14 upd_ne; [| vm_compute; discriminate].
      rewrite /R13 upd_ne; [| vm_compute; discriminate].
      rewrite /R12 upd_ne; [exact HR11a1 | vm_compute; discriminate]. }
    assert (HR14sp : R14 !!! Regidx csp_rs1 = spr)
      by (rewrite /R14 upd_ne; [exact HR13sp | vm_compute; discriminate]).
    assert (HR14ra : R14 !!! Regidx (mword_of_int 1 : mword 5) = add_vec_int (mword_of_int (UI + 0x4a) : mword 64) 4)
      by (rewrite /R14; apply upd_eq).
    (* initlock(&tx_lock,"uart"): owns lk's 3 fields, returns them init'd *)
    iApply (Initlock.wp_initlock_sconf γ root_ppn Φ R14 vlock vname vcpu "uart"%string (K - 2)
              ltac:(lia)
              ltac:(rewrite HR14ra; vm_compute; reflexivity)
              with "Hsc Hhs Hcg Htlbinv Htext Hpc [] [Hlock] [Hname] [Hcpu]").
    { iEval (rewrite HR14a1). iExact "Hstr". }
    { iEval (rewrite HR14a0). iExact "Hlock". }
    { iEval (rewrite HR14a0). iExact "Hname". }
    { iEval (rewrite HR14a0). iExact "Hcpu". }
    iIntros (mil) "Hsc Hhs Hcg Htlbinv Hpc %Hilcs Hlock Hlname Hcpu".
    iEval (rewrite HR14a0) in "Hlock". iEval (rewrite HR14a0) in "Hlname". iEval (rewrite HR14a0) in "Hcpu".
    assert (Hpcil : update_vec_dec (add_vec (R14 !!! Regidx (mword_of_int 1 : mword 5)) (sign_extend' 64 (zeros' 12))) 0 ('b"0") = mword_of_int (UI + 0x4e)).
    { rewrite HR14ra. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite Hpcil) in "Hpc".
    pose proof Hilcs as Hilcs_full. unfold callee_saved in Hilcs.
    destruct Hilcs as (Hilsp & Hiltp & Hils0 & Hils1 & Hils2 & Hils3 & Hils4 & Hils5 & Hils6 & Hils7 & Hils8 & Hils9 & Hils10 & Hils11).
    assert (Hmilsp : mil !!! Regidx csp_rs1 = spr) by (rewrite Hilsp; exact HR14sp).
    (* ===== EPILOGUE 0x4e..0x54: restore ra/s0, pop frame, ret ===== *)
    (* +0x4e c.ldsp ra,8(sp) *)
    iApply (wp_cldsp_s_sconf γ root_ppn Φ (mword_of_int (UI + 0x4e)) (mword_of_int 1 : mword 6) (mword_of_int 1 : mword 5)
              mil (K - 2)%nat (m !!! Regidx (mword_of_int 1 : mword 5)) (dqm:=DfracOwn 1)
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hsc Hhs Hcg Htlbinv Hpc Hi4e [Hras] [-]").
    { iEval (rewrite -Hb1 -Hmilsp) in "Hras". iExact "Hras". }
    iIntros "Hhs Hsc Hcg Htlbinv Hpc Hras".
    iEval (rewrite Hmilsp Hb1) in "Hras".
    set (E1 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 1 : mword 5))]> mil).
    assert (HE1sp : E1 !!! Regidx csp_rs1 = spr) by (rewrite /E1 upd_ne; [exact Hmilsp | vm_compute; discriminate]).
    assert (Hpp50 : add_vec_int (mword_of_int (UI + 0x4e) : mword 64) 2 = mword_of_int (UI + 0x50)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp50) in "Hpc".
    (* +0x50 c.ldsp s0,0(sp) *)
    iApply (wp_cldsp_s_sconf γ root_ppn Φ (mword_of_int (UI + 0x50)) (mword_of_int 0 : mword 6) (mword_of_int 8 : mword 5)
              E1 (K - 2)%nat (m !!! Regidx (mword_of_int 8 : mword 5)) (dqm:=DfracOwn 1)
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hsc Hhs Hcg Htlbinv Hpc Hi50 [Hs0s] [-]").
    { iEval (rewrite -Hb2 -HE1sp) in "Hs0s". iExact "Hs0s". }
    iIntros "Hhs Hsc Hcg Htlbinv Hpc Hs0s".
    iEval (rewrite HE1sp Hb2) in "Hs0s".
    set (E2 := <[Regidx (mword_of_int 8 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 8 : mword 5))]> E1).
    assert (HE2sp : E2 !!! Regidx csp_rs1 = spr) by (rewrite /E2 upd_ne; [exact HE1sp | vm_compute; discriminate]).
    assert (Hpp52 : add_vec_int (mword_of_int (UI + 0x50) : mword 64) 2 = mword_of_int (UI + 0x52)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp52) in "Hpc".
    (* +0x52 c.addi sp,16 : pop frame *)
    set (E3 := <[Regidx csp_rs1 := regval_into_reg (add_vec (E2 !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 16 : mword 6))))]> E2).
    assert (HE3csp : E3 !!! Regidx csp_rs1 = sp0).
    { rewrite /E3 upd_eq. rewrite HE2sp. unfold regval_into_reg, spr, sp0.
      apply initlock_sp_cancel. }
    assert (Hwv : add_vec (E2 !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 16 : mword 6))) = sp0).
    { rewrite -HE3csp /E3 upd_eq. reflexivity. }
    assert (Hpop : E2 !!! Regidx csp_rs1
                   = pa_stk (add_vec (E2 !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 16 : mword 6)))) 2).
    { rewrite Hwv HE2sp. exact Hspr2. }
    iAssert (stack_own sp0 2) with "[Hras Hs0s]" as "Hframe".
    { rewrite stack_own_slots. cbn [seq].
      iSplitL "Hras"; [iExists _; iExact "Hras"|].
      iSplitL "Hs0s"; [iExists _; iExact "Hs0s"|]. done. }
    iEval (rewrite -Hwv) in "Hframe".
    iApply (wp_caddi_sp_pop_s_sconf γ root_ppn Φ (mword_of_int (UI + 0x52)) (mword_of_int 16 : mword 6) E2 (K - 2)%nat 2 Hpop
              with "Hsc Hhs Hcg Htlbinv Hpc Hi52 Hframe [-]").
    iIntros "Hhs Hsc Hcg Htlbinv Hpc".
    assert (Hnk : ((K - 2) + 2)%nat = K) by lia.
    iEval (rewrite Hnk) in "Hcg".
    change (<[Regidx csp_rs1 := regval_into_reg (add_vec (E2 !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 16 : mword 6))))]> E2) with E3.
    assert (Hpp54 : add_vec_int (mword_of_int (UI + 0x52) : mword 64) 2 = mword_of_int (UI + 0x54)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp54) in "Hpc".
    (* +0x54 c.ret *)
    assert (HE3ra : E3 !!! Regidx (mword_of_int 1 : mword 5) = m !!! Regidx (mword_of_int 1 : mword 5)).
    { rewrite /E3 upd_ne; [| vm_compute; discriminate].
      rewrite /E2 upd_ne; [| vm_compute; discriminate].
      rewrite /E1 upd_eq; reflexivity. }
    assert (Hretaligned : eq_vec (access_vec_dec (update_vec_dec (add_vec (E3 !!! Regidx (mword_of_int 1 : mword 5)) (sign_extend' 64 (zeros' 12))) 0 ('b"0")) 0) ('b"0") = true)
      by (rewrite HE3ra; exact Hretm).
    iApply (wp_cret_s_sconf γ root_ppn Φ (mword_of_int (UI + 0x54)) (mword_of_int 1 : mword 5) E3 K
              ltac:(vm_compute; discriminate) Hretaligned
              with "Hsc Hhs Hcg Htlbinv Hpc Hi54 [-]").
    iIntros "Hhs Hsc Hcg Htlbinv Hpc".
    assert (Hretf : update_vec_dec (add_vec (E3 !!! Regidx (mword_of_int 1 : mword 5)) (sign_extend' 64 (zeros' 12))) 0 ('b"0") = ret_tgt)
      by (rewrite HE3ra; reflexivity).
    iEval (rewrite Hretf) in "Hpc".
    (* callee_saved m E3 *)
    assert (Hthread : forall c : mword 5, is_cs_idx c = true ->
              c <> mword_of_int 1 -> c <> csp_rs1 -> c <> mword_of_int 8 ->
              E3 !!! Regidx c = m !!! Regidx c).
    { intros c Hc N1 Nsp N8.
      pose proof (is_cs_idx_true_neq (mword_of_int 10 : mword 5) c ltac:(vm_compute; reflexivity) Hc) as Na0.
      pose proof (is_cs_idx_true_neq (mword_of_int 11 : mword 5) c ltac:(vm_compute; reflexivity) Hc) as Na1.
      pose proof (is_cs_idx_true_neq (mword_of_int 12 : mword 5) c ltac:(vm_compute; reflexivity) Hc) as Na2.
      pose proof (is_cs_idx_true_neq (mword_of_int 13 : mword 5) c ltac:(vm_compute; reflexivity) Hc) as Na3.
      pose proof (is_cs_idx_true_neq (mword_of_int 14 : mword 5) c ltac:(vm_compute; reflexivity) Hc) as Na4.
      pose proof (is_cs_idx_true_neq (mword_of_int 15 : mword 5) c ltac:(vm_compute; reflexivity) Hc) as Na5.
      rewrite /E3 upd_ne; [| congruence].
      rewrite /E2 upd_ne; [| congruence].
      rewrite /E1 upd_ne; [| congruence].
      rewrite (callee_saved_lookup Hilcs_full c Hc).
      rewrite /R14 upd_ne; [| congruence].
      rewrite /R13 upd_ne; [| congruence].
      rewrite /R12 upd_ne; [| congruence].
      rewrite /R11 upd_ne; [| congruence].
      rewrite /R10 upd_ne; [| congruence].
      rewrite /R9 upd_ne; [| congruence].
      rewrite /R8 upd_ne; [| congruence].
      rewrite /R7 upd_ne; [| congruence].
      rewrite /R6 upd_ne; [| congruence].
      rewrite /R5 upd_ne; [| congruence].
      rewrite /R4 upd_ne; [| congruence].
      rewrite /R3 upd_ne; [| congruence].
      rewrite /R2 upd_ne; [| congruence].
      rewrite /R1 upd_ne; [reflexivity | congruence]. }
    iApply ("Hcont" $! E3 with "Hsc Hhs Hcg Htlbinv Hpc [%] Huf Hlock Hlname Hcpu").
    unfold callee_saved.
    split. { rewrite HE3csp. reflexivity. }
    split. { apply Hthread; vm_compute; first [reflexivity | discriminate]. }
    split. { rewrite /E3 upd_ne; [| vm_compute; discriminate].
             rewrite /E2 upd_eq; reflexivity. }
    repeat split; apply Hthread; vm_compute; first [reflexivity | discriminate].
  Qed.

End WpSconfUartinit.
End UartinitProof.
