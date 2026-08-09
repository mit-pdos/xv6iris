(* ProofUartinit.v -- the whole-function WP for xv6's uartinit() over the
   SIE-agnostic sconf world.  uartinit() programs the 16550 (7 MMIO byte
   writes to UART0) then initlock(&tx_lock,"uart").

   Straight-line, 16-byte frame, one jal sub-call (initlock).  Structurally a
   clone of ProofKinit with the freerange/lock-invariant tail replaced by
   returning initlock's raw outputs, and the seven device stores inserted.

   THE SEVEN STORES RUN UNDER THE TIME-0 UART INVARIANT.  The UART thread is a
   top-level thread from step 0, so [uart_frag] can never sit raw in a CPU's
   precondition; each store therefore goes through the invariant-borrowing
   accessor leaf [Uart.wp_sb_uart_uinv_s_sconf], which opens [uart_inv] across
   its own step and asks the caller for a GHOST STEP -- a wand that, given the
   [uart_write] equation and the invariant's four ghost halves at [u], returns
   them at [u'].  What travels through those wands is the pair the caller
   threads: the exclusive transmitter token [uart_tx_own γd l] and the UNFROZEN
   DLAB half.  Per offset:

     off 1 (IER / DLM), off 0 with DLAB set (DLL) -- pure config, nothing
       tracked moves ([uart_write_1_stable] / [uart_write_0_dlab_stable], and
       [uart_ghosts_stable] closes the wand).  The DLL write needs to know it
       is NOT a THR push, which is exactly what the caller's DLAB half says.
     off 3 (LCR) -- DLAB moves, and only DLAB: the wand re-agrees BOTH halves
       at the new bit ([ui_lcr_step], over [WpUart.uart_dlab_update]).
     off 2 (FCR = 0x07) -- bits 1|2 clear both FIFOs.  The rx clear is
       ghost-invisible; the tx clear would SHRINK the accepted trace, except
       that the token pins [uart_acc u = l] and the carried [uart_out_lb l]
       says [l] is already transmitted, so [uart_tx_empty_of_out] leaves the
       FIFO empty and the clear shrinks nothing ([ui_tx_empty], the same
       argument uartputc_sync's poll uses).

   After the final LCR write the caller half is at [false], so
   [uart_dlab_freeze] mints the persistent [uart_dlab_off] -- uartinit's
   output, and the reason the freeze no longer lives in
   [uart_ghosts_alloc]. *)
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
Require Import WpMmodeLeafBase.
Require Import RiscvExtras.
Require Import SmodeCore.
Require Import StackOwn CalleeSaved.
Require Import KernelDataInv.
Require Import DevModel WpUart.
Require Import IntrDefs WpSmodeIntr.
Require Import IntrDefs HartTp WpNext.
Require Import WpSconfAlu WpSconfMem WpSconfCtl.
Require Import WpLock.
Require Import SpecInitlock.
Require Import SpecUart.
Require Import CodeUartinit.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SpecUartinit.
Require Import KernelRvcDecode.
Local Open Scope Z_scope.
Import Defs.

Module UartinitProof (Uart : UART) (Initlock : INITLOCK) : UARTINIT.

Section ProofUartinit.
  Context `{!riscvGS Σ, !sieG Σ}.
  Context `{!uartGhostG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.


  (* ------------------------------------------------------------------- *)
  (*  The three readings of the invariant's ghost bundle that the seven   *)
  (*  ghost steps below need.  Each is stated over [uart_ghosts] rather   *)
  (*  than its components, because that is the form the accessor leaf     *)
  (*  hands out.                                                          *)
  (* ------------------------------------------------------------------- *)

  (* "DLAB is what my half says it is" -- what makes the DLL/DLM writes
     provably divisor-latch writes rather than THR pushes. *)
  Lemma ui_dlab_of_ghosts (gd : uart_names) (u : uart_state) (dq : dfrac) (b : bool) :
    uart_ghosts gd u -∗ uart_dlab_is gd dq b -∗ ⌜ uart_dlab u = b ⌝.
  Proof.
    iIntros "(_ & _ & _ & Hdl) Hb".
    iApply (uart_dlab_agree with "Hdl Hb").
  Qed.

  (* "the tx FIFO is empty" -- from the token (the accepted trace is exactly
     [l]) plus the carried lower bound (all of [l] has been transmitted). *)
  Lemma ui_tx_empty (gd : uart_names) (u : uart_state) (l : list (bv 8)) :
    uart_ghosts gd u -∗ uart_tx_own gd l -∗ uart_out_lb gd l -∗ ⌜ u_tx u = [] ⌝.
  Proof.
    iIntros "(_ & Ho & Ht & _) Hown Hlb".
    iDestruct (uart_tx_own_agree with "Ht Hown") as %Hacc.
    iDestruct (uart_out_prefix with "Ho Hlb") as %Hpre.
    iPureIntro. exact (uart_tx_empty_of_out u l Hacc Hpre).
  Qed.

  (* the LCR write's ghost step: acc/out are untouched, DLAB moves, and moving
     it consumes and returns BOTH halves. *)
  Lemma ui_lcr_step (gd : uart_names) (u u' : uart_state) (b : bool) :
    uart_acc u' = uart_acc u -> u_out u' = u_out u ->
    uart_ghosts gd u -∗ uart_dlab_is gd (DfracOwn (1/2)) b ==∗
    uart_ghosts gd u' ∗ uart_dlab_is gd (DfracOwn (1/2)) (uart_dlab u').
  Proof.
    iIntros (Ha Ho) "(Hs & Hout & Ht & Hdl) Hb".
    iMod (uart_dlab_update gd u u' b with "Hdl Hb") as "[Hdl' Hb']".
    iModIntro. iSplitL "Hs Hout Ht Hdl'"; [| iExact "Hb'"].
    rewrite /uart_ghosts.
    iDestruct (uart_sent_auth_stable _ u u' Ha with "Hs") as "$".
    iDestruct (uart_out_auth_stable _ u u' Ho with "Hout") as "$".
    iDestruct (uart_tx_auth_stable _ u u' Ha with "Ht") as "$".
    iExact "Hdl'".
  Qed.

  Lemma wp_uartinit_sconf (γd : uart_names)
      (m : regfile) (K : nat) (l : list (bv 8)) (b0 : bool)
      (vlock : bv 32) (vname vcpu : bv 64) (p : mword 64)
    : wp_uartinit_sconf_body γd m K l b0 vlock vname vcpu p.
  Proof.
    cbv beta delta [wp_uartinit_sconf_body].
    intros pcE ret_tgt lk c_name c_cpu HK.
    set (sp0 := m !!! Regidx csp_rs1).
    set (spr := add_vec sp0 (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6)))).
    iIntros "Hcg #Htext #Hkdata Hpc #Huinv Htx #Hlb #Hsent Hdlab Hlock Hname Hcpu Hcont".
    iDestruct (sie_cap_gpr_x0 m K false p (mword_of_int 0 : mword 5) ltac:(vm_compute; reflexivity)
                 with "Hcg") as "[%Hx0 Hcg]".
    (* the "uart" string literal, read out of the kernel's data image *)
    assert (Huart : forall j bt, cstring_bytes "uart"%string !! j = Some bt ->
                      KernelData.kernel_data !! (0x80007030 + Z.of_nat j)%Z = Some bt).
    { intros j bt Hj.
      do 5 (destruct j as [|j];
            [vm_compute in Hj; injection Hj as <-; vm_compute; reflexivity |]);
      vm_compute in Hj; discriminate. }
    iPoseProof (kernel_data_string 0x80007030 "uart"%string _ eq_refl ltac:(unfold text_end; lia) Huart
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
    iApply (wp_caddi_sp_push_s_sconf pcE (mword_of_int 48 : mword 6) m K 2 false ltac:(lia) Hpush
              with "Hcg Hpc Hi00 [-]").
    iApply wp_next_off_intro.
    iIntros "Hcg Hframe Hpc".
    iEval (rewrite Hspm) in "Hframe".
    change (<[Regidx csp_rs1 := regval_into_reg (add_vec sp0 (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6))))]> m) with R1.
    assert (HspR1 : R1 !!! Regidx csp_rs1 = spr) by (rewrite /R1 upd_eq; reflexivity).
    iEval (rewrite stack_own_slots; cbn [seq]) in "Hframe".
    iDestruct "Hframe" as "(S1 & S2 & _)".
    iDestruct "S1" as (vra0) "Hras". iDestruct "S2" as (vs00) "Hs0s".
    assert (Hpp02 : add_vec_int (pcE : mword 64) 2 = mword_of_int (KernelSyms.uartinit + 0x02)) by (unfold pcE; apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp02) in "Hpc".
    (* +0x02 c.sdsp ra,8(sp) *)
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.uartinit + 0x02)) (mword_of_int 1 : mword 6) (mword_of_int 1 : mword 5)
              R1 (K - 2)%nat vra0 false with "Hcg Hpc Hi02 [Hras] [-]").
    { iEval (rewrite HspR1 Hb1). iExact "Hras". }
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc Hras".
    iEval (rewrite HspR1 Hb1) in "Hras".
    assert (Hrav : forall (CID' : CpuId), rget (CID := CID') R1 (mword_of_int 1 : mword 5) = m !!! Regidx (mword_of_int 1 : mword 5))
      by (intros CID'; rgne; rewrite /R1 upd_ne; [reflexivity | vm_compute; discriminate]).
    iEval (rewrite Hrav) in "Hras".
    assert (Hpp04 : add_vec_int (mword_of_int (KernelSyms.uartinit + 0x02) : mword 64) 2 = mword_of_int (KernelSyms.uartinit + 0x04)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp04) in "Hpc".
    (* +0x04 c.sdsp s0,0(sp) *)
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.uartinit + 0x04)) (mword_of_int 0 : mword 6) (mword_of_int 8 : mword 5)
              R1 (K - 2)%nat vs00 false with "Hcg Hpc Hi04 [Hs0s] [-]").
    { iEval (rewrite HspR1 Hb2). iExact "Hs0s". }
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc Hs0s".
    iEval (rewrite HspR1 Hb2) in "Hs0s".
    assert (Hs0v : forall (CID' : CpuId), rget (CID := CID') R1 (mword_of_int 8 : mword 5) = m !!! Regidx (mword_of_int 8 : mword 5))
      by (intros CID'; rgne; rewrite /R1 upd_ne; [reflexivity | vm_compute; discriminate]).
    iEval (rewrite Hs0v) in "Hs0s".
    assert (Hpp06 : add_vec_int (mword_of_int (KernelSyms.uartinit + 0x04) : mword 64) 2 = mword_of_int (KernelSyms.uartinit + 0x06)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp06) in "Hpc".
    (* +0x06 c.addi4spn s0,sp,16 *)
    iApply (wp_caddi4spn_s_sconf (mword_of_int (KernelSyms.uartinit + 0x06)) (Cregidx (mword_of_int 0)) (mword_of_int 4 : mword 8) (mword_of_int 8 : mword 5)
              R1 (K - 2)%nat false ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi06 [-]").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    set (R2 := <[Regidx (mword_of_int 8 : mword 5) := regval_into_reg (add_vec (R1 !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm (mword_of_int 4 : mword 8))))]> R1).
    assert (Hpp08 : add_vec_int (mword_of_int (KernelSyms.uartinit + 0x06) : mword 64) 2 = mword_of_int (KernelSyms.uartinit + 0x08)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp08) in "Hpc".
    (* ===== BODY: address setup + 7 device stores ===== *)
    (* +0x08 lui a5,0x10000 *)
    iApply (wp_lui_s_sconf (mword_of_int (KernelSyms.uartinit + 0x08)) (mword_of_int 15 : mword 5) (mword_of_int 0x10000 : mword 20)
              (luival (mword_of_int 0x10000 : mword 20)) R2 (K - 2)%nat false ltac:(vm_compute; discriminate) ltac:(rdok) eq_refl
              with "Hcg Hpc Hi08 [-]").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    set (R3 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (luival (mword_of_int 0x10000 : mword 20))]> R2).
    assert (HR3a5 : R3 !!! Regidx (mword_of_int 15 : mword 5) = uart_pa 0)
      by (rewrite /R3 upd_eq; unfold uart_pa, uart_base; apply bv_eq; vm_compute; reflexivity).
    assert (HR3x0 : R3 !!! Regidx (mword_of_int 0 : mword 5) = zero_reg).
    { rewrite /R3 upd_ne; [| vm_compute; discriminate].
      rewrite /R2 upd_ne; [| vm_compute; discriminate].
      rewrite /R1 upd_ne; [exact Hx0 | vm_compute; discriminate]. }
    assert (Hpp0c : add_vec_int (mword_of_int (KernelSyms.uartinit + 0x08) : mword 64) 4 = mword_of_int (KernelSyms.uartinit + 0x0c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp0c) in "Hpc".
    (* +0x0c sb zero,1(a5) : IER <- 0.  Offset 1 is IER (or DLM under DLAB);
       either way nothing tracked moves, so the tokens pass straight through. *)
    iApply (Uart.wp_sb_uart_uinv_s_sconf (CID:=CID) γd 1 (mword_of_int (KernelSyms.uartinit + 0x0c)) false (mword_of_int 0 : mword 5) (mword_of_int 15 : mword 5) (mword_of_int 1 : mword 12)
              R3 (K - 2)%nat
              (uart_tx_own γd l ∗ uart_dlab_is γd (DfracOwn (1/2)) b0)%I
              (uart_tx_own γd l ∗ uart_dlab_is γd (DfracOwn (1/2)) b0)%I
              false p
              ltac:(unfold uart_size; lia)
              ltac:(rgne; rewrite HR3a5; vm_compute; reflexivity)
              ltac:(rgne; rewrite HR3a5; apply bv_eq; vm_compute; reflexivity)
              ltac:(rgne; rewrite HR3a5; apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc Hi0c Huinv [$Htx $Hdlab] [] [-]").
    { iIntros (uu uu') "%Hw Hg [Ht Hd]".
      destruct (uart_write_1_stable uu _ uu' Hw) as (Ha & Ho & Hdb).
      iModIntro. iSplitL "Hg";
        [ iApply (uart_ghosts_stable γd uu uu' Ha Ho Hdb with "Hg") | iFrame "Ht Hd" ]. }
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc [Htx Hdlab]".
    assert (Hpp10 : add_vec_int (mword_of_int (KernelSyms.uartinit + 0x0c) : mword 64) 4 = mword_of_int (KernelSyms.uartinit + 0x10)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp10) in "Hpc".
    (* +0x10 lui a4,0x10000 *)
    iApply (wp_lui_s_sconf (mword_of_int (KernelSyms.uartinit + 0x10)) (mword_of_int 14 : mword 5) (mword_of_int 0x10000 : mword 20)
              (luival (mword_of_int 0x10000 : mword 20)) R3 (K - 2)%nat false ltac:(vm_compute; discriminate) ltac:(rdok) eq_refl
              with "Hcg Hpc Hi10 [-]").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    set (R4 := <[Regidx (mword_of_int 14 : mword 5) := regval_into_reg (luival (mword_of_int 0x10000 : mword 20))]> R3).
    assert (HR4a4 : R4 !!! Regidx (mword_of_int 14 : mword 5) = uart_pa 0)
      by (rewrite /R4 upd_eq; unfold uart_pa, uart_base; apply bv_eq; vm_compute; reflexivity).
    assert (HR4x0 : R4 !!! Regidx (mword_of_int 0 : mword 5) = zero_reg)
      by (rewrite /R4 upd_ne; [exact HR3x0 | vm_compute; discriminate]).
    assert (Hpp14 : add_vec_int (mword_of_int (KernelSyms.uartinit + 0x10) : mword 64) 4 = mword_of_int (KernelSyms.uartinit + 0x14)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp14) in "Hpc".
    (* +0x14 li a3,-128 (addi a3,zero,-128) *)
    iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.uartinit + 0x14)) (mword_of_int 13 : mword 5) (mword_of_int 0 : mword 5) (mword_of_int 3968 : mword 12)
              R4 (K - 2)%nat false ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi14 [-]").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    set (R5 := <[Regidx (mword_of_int 13 : mword 5) := regval_into_reg (add_vec (rget R4 (mword_of_int 0 : mword 5)) (sign_extend' 64 (mword_of_int 3968 : mword 12)))]> R4).
    assert (HR5a4 : R5 !!! Regidx (mword_of_int 14 : mword 5) = uart_pa 0)
      by (rewrite /R5 upd_ne; [exact HR4a4 | vm_compute; discriminate]).
    assert (Hpp18 : add_vec_int (mword_of_int (KernelSyms.uartinit + 0x14) : mword 64) 4 = mword_of_int (KernelSyms.uartinit + 0x18)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp18) in "Hpc".
    (* +0x18 sb a3,3(a4) : LCR <- 0x80 -- DLAB ON.  The one write in the
       sequence that moves a tracked quantity: both DLAB halves step to
       [true] together, acc/out are untouched. *)
    assert (Hblcr1 : (autocast (T := mword) (subrange_vec_dec (R5 !!! Regidx (mword_of_int 13 : mword 5)) (Z.sub (Z.mul 1 8) 1) 0) : mword 8) = Z_to_bv 8 128).
    { rewrite /R5 upd_eq. rgne. rewrite HR4x0. apply bv_eq; vm_compute; reflexivity. }
    iApply (Uart.wp_sb_uart_uinv_s_sconf (CID:=CID) γd 3 (mword_of_int (KernelSyms.uartinit + 0x18)) false (mword_of_int 13 : mword 5) (mword_of_int 14 : mword 5) (mword_of_int 3 : mword 12)
              R5 (K - 2)%nat
              (uart_tx_own γd l ∗ uart_dlab_is γd (DfracOwn (1/2)) b0)%I
              (uart_tx_own γd l ∗ uart_dlab_is γd (DfracOwn (1/2)) true)%I
              false p
              ltac:(unfold uart_size; lia)
              ltac:(rgne; rewrite HR5a4; vm_compute; reflexivity)
              ltac:(rgne; rewrite HR5a4; apply bv_eq; vm_compute; reflexivity)
              ltac:(rgne; rewrite HR5a4; apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc Hi18 Huinv [$Htx $Hdlab] [] [-]").
    { iIntros (uu uu') "%Hw Hg [Ht Hd]".
      destruct (uart_write_3_stable uu _ uu' Hw) as (Ha & Ho & Hdb).
      assert (Hdt : uart_dlab uu' = true)
        by (rewrite Hdb Hblcr1; vm_compute; reflexivity).
      iMod (ui_lcr_step γd uu uu' b0 Ha Ho with "Hg Hd") as "[Hg' Hd']".
      iEval (rewrite Hdt) in "Hd'".
      iModIntro. iSplitL "Hg'"; [ iExact "Hg'" | iFrame "Ht Hd'" ]. }
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc [Htx Hdlab]".
    assert (Hpp1c : add_vec_int (mword_of_int (KernelSyms.uartinit + 0x18) : mword 64) 4 = mword_of_int (KernelSyms.uartinit + 0x1c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp1c) in "Hpc".
    (* +0x1c c.li a3,3 *)
    iApply (wp_cli_s_sconf (mword_of_int (KernelSyms.uartinit + 0x1c)) (mword_of_int 13 : mword 5) (mword_of_int 3 : mword 6) (mword_of_int 3 : mword 64)
              R5 (K - 2)%nat false ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi1c [-]").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    set (R6 := <[Regidx (mword_of_int 13 : mword 5) := regval_into_reg (mword_of_int 3 : mword 64)]> R5).
    assert (Hpp1e : add_vec_int (mword_of_int (KernelSyms.uartinit + 0x1c) : mword 64) 2 = mword_of_int (KernelSyms.uartinit + 0x1e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp1e) in "Hpc".
    (* +0x1e lui a2,0x10000 *)
    iApply (wp_lui_s_sconf (mword_of_int (KernelSyms.uartinit + 0x1e)) (mword_of_int 12 : mword 5) (mword_of_int 0x10000 : mword 20)
              (luival (mword_of_int 0x10000 : mword 20)) R6 (K - 2)%nat false ltac:(vm_compute; discriminate) ltac:(rdok) eq_refl
              with "Hcg Hpc Hi1e [-]").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
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
    assert (Hpp22 : add_vec_int (mword_of_int (KernelSyms.uartinit + 0x1e) : mword 64) 4 = mword_of_int (KernelSyms.uartinit + 0x22)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp22) in "Hpc".
    (* +0x22 sb a3,0(a2) : DLL <- 3.  Offset 0 is the divisor latch, not THR --
       and it is the caller's DLAB half that says so. *)
    iApply (Uart.wp_sb_uart_uinv_s_sconf (CID:=CID) γd 0 (mword_of_int (KernelSyms.uartinit + 0x22)) false (mword_of_int 13 : mword 5) (mword_of_int 12 : mword 5) (mword_of_int 0 : mword 12)
              R7 (K - 2)%nat
              (uart_tx_own γd l ∗ uart_dlab_is γd (DfracOwn (1/2)) true)%I
              (uart_tx_own γd l ∗ uart_dlab_is γd (DfracOwn (1/2)) true)%I
              false p
              ltac:(unfold uart_size; lia)
              ltac:(rgne; rewrite HR7a2; vm_compute; reflexivity)
              ltac:(rgne; rewrite HR7a2; apply bv_eq; vm_compute; reflexivity)
              ltac:(rgne; rewrite HR7a2; apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc Hi22 Huinv [$Htx $Hdlab] [] [-]").
    { iIntros (uu uu') "%Hw Hg [Ht Hd]".
      iDestruct (ui_dlab_of_ghosts γd uu (DfracOwn (1/2)) true with "Hg Hd") as %Hdu.
      destruct (uart_write_0_dlab_stable uu _ uu' Hdu Hw) as (Ha & Ho & Hdb).
      iModIntro. iSplitL "Hg";
        [ iApply (uart_ghosts_stable γd uu uu' Ha Ho Hdb with "Hg") | iFrame "Ht Hd" ]. }
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc [Htx Hdlab]".
    assert (Hpp26 : add_vec_int (mword_of_int (KernelSyms.uartinit + 0x22) : mword 64) 4 = mword_of_int (KernelSyms.uartinit + 0x26)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp26) in "Hpc".
    (* +0x26 sb zero,1(a5) : DLM <- 0.  Offset 1 again -- stable at either DLAB. *)
    iApply (Uart.wp_sb_uart_uinv_s_sconf (CID:=CID) γd 1 (mword_of_int (KernelSyms.uartinit + 0x26)) false (mword_of_int 0 : mword 5) (mword_of_int 15 : mword 5) (mword_of_int 1 : mword 12)
              R7 (K - 2)%nat
              (uart_tx_own γd l ∗ uart_dlab_is γd (DfracOwn (1/2)) true)%I
              (uart_tx_own γd l ∗ uart_dlab_is γd (DfracOwn (1/2)) true)%I
              false p
              ltac:(unfold uart_size; lia)
              ltac:(rgne; rewrite HR7a5; vm_compute; reflexivity)
              ltac:(rgne; rewrite HR7a5; apply bv_eq; vm_compute; reflexivity)
              ltac:(rgne; rewrite HR7a5; apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc Hi26 Huinv [$Htx $Hdlab] [] [-]").
    { iIntros (uu uu') "%Hw Hg [Ht Hd]".
      destruct (uart_write_1_stable uu _ uu' Hw) as (Ha & Ho & Hdb).
      iModIntro. iSplitL "Hg";
        [ iApply (uart_ghosts_stable γd uu uu' Ha Ho Hdb with "Hg") | iFrame "Ht Hd" ]. }
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc [Htx Hdlab]".
    assert (Hpp2a : add_vec_int (mword_of_int (KernelSyms.uartinit + 0x26) : mword 64) 4 = mword_of_int (KernelSyms.uartinit + 0x2a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp2a) in "Hpc".
    (* +0x2a sb a3,3(a4) : LCR <- 0x03 -- 8N1, DLAB OFF.  Both halves step to
       [false]; from here the half is freezable. *)
    assert (Hblcr2 : (autocast (T := mword) (subrange_vec_dec (R7 !!! Regidx (mword_of_int 13 : mword 5)) (Z.sub (Z.mul 1 8) 1) 0) : mword 8) = Z_to_bv 8 3).
    { rewrite HR7a3. apply bv_eq; vm_compute; reflexivity. }
    iApply (Uart.wp_sb_uart_uinv_s_sconf (CID:=CID) γd 3 (mword_of_int (KernelSyms.uartinit + 0x2a)) false (mword_of_int 13 : mword 5) (mword_of_int 14 : mword 5) (mword_of_int 3 : mword 12)
              R7 (K - 2)%nat
              (uart_tx_own γd l ∗ uart_dlab_is γd (DfracOwn (1/2)) true)%I
              (uart_tx_own γd l ∗ uart_dlab_is γd (DfracOwn (1/2)) false)%I
              false p
              ltac:(unfold uart_size; lia)
              ltac:(rgne; rewrite HR7a4; vm_compute; reflexivity)
              ltac:(rgne; rewrite HR7a4; apply bv_eq; vm_compute; reflexivity)
              ltac:(rgne; rewrite HR7a4; apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc Hi2a Huinv [$Htx $Hdlab] [] [-]").
    { iIntros (uu uu') "%Hw Hg [Ht Hd]".
      destruct (uart_write_3_stable uu _ uu' Hw) as (Ha & Ho & Hdb).
      assert (Hdt : uart_dlab uu' = false)
        by (rewrite Hdb Hblcr2; vm_compute; reflexivity).
      iMod (ui_lcr_step γd uu uu' true Ha Ho with "Hg Hd") as "[Hg' Hd']".
      iEval (rewrite Hdt) in "Hd'".
      iModIntro. iSplitL "Hg'"; [ iExact "Hg'" | iFrame "Ht Hd'" ]. }
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc [Htx Hdlab]".
    assert (Hpp2e : add_vec_int (mword_of_int (KernelSyms.uartinit + 0x2a) : mword 64) 4 = mword_of_int (KernelSyms.uartinit + 0x2e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp2e) in "Hpc".
    (* +0x2e c.mv a4,a2 *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.uartinit + 0x2e)) (mword_of_int 14 : mword 5) (mword_of_int 12 : mword 5)
              R7 (K - 2)%nat false ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi2e [-]").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    set (R8 := <[Regidx (mword_of_int 14 : mword 5) := regval_into_reg (add_vec zero_reg (rget R7 (mword_of_int 12 : mword 5)))]> R7).
    assert (HR8a4 : R8 !!! Regidx (mword_of_int 14 : mword 5) = uart_pa 0).
    { rewrite /R8 upd_eq. rgne. rewrite HR7a2. apply bv_eq; vm_compute; reflexivity. }
    assert (Hpp30 : add_vec_int (mword_of_int (KernelSyms.uartinit + 0x2e) : mword 64) 2 = mword_of_int (KernelSyms.uartinit + 0x30)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp30) in "Hpc".
    (* +0x30 c.li a2,7 *)
    iApply (wp_cli_s_sconf (mword_of_int (KernelSyms.uartinit + 0x30)) (mword_of_int 12 : mword 5) (mword_of_int 7 : mword 6) (mword_of_int 7 : mword 64)
              R8 (K - 2)%nat false ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi30 [-]").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
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
    assert (Hpp32 : add_vec_int (mword_of_int (KernelSyms.uartinit + 0x30) : mword 64) 2 = mword_of_int (KernelSyms.uartinit + 0x32)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp32) in "Hpc".
    (* +0x32 sb a2,2(a4) : FCR <- 0x07 -- enable + CLEAR BOTH FIFOS.  The tx
       clear is the write the invariant would forbid; the token plus the
       carried [uart_out_lb] prove the FIFO already empty, so it shrinks
       nothing. *)
    iApply (Uart.wp_sb_uart_uinv_s_sconf (CID:=CID) γd 2 (mword_of_int (KernelSyms.uartinit + 0x32)) false (mword_of_int 12 : mword 5) (mword_of_int 14 : mword 5) (mword_of_int 2 : mword 12)
              R9 (K - 2)%nat
              (uart_tx_own γd l ∗ uart_dlab_is γd (DfracOwn (1/2)) false)%I
              (uart_tx_own γd l ∗ uart_dlab_is γd (DfracOwn (1/2)) false)%I
              false p
              ltac:(unfold uart_size; lia)
              ltac:(rgne; rewrite HR9a4; vm_compute; reflexivity)
              ltac:(rgne; rewrite HR9a4; apply bv_eq; vm_compute; reflexivity)
              ltac:(rgne; rewrite HR9a4; apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc Hi32 Huinv [$Htx $Hdlab] [] [-]").
    { iIntros (uu uu') "%Hw Hg [Ht Hd]".
      iDestruct (ui_tx_empty γd uu l with "Hg Ht Hlb") as %Htxe.
      destruct (uart_write_2_stable uu _ uu' Htxe Hw) as (Ha & Ho & Hdb).
      iModIntro. iSplitL "Hg";
        [ iApply (uart_ghosts_stable γd uu uu' Ha Ho Hdb with "Hg") | iFrame "Ht Hd" ]. }
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc [Htx Hdlab]".
    assert (Hpp36 : add_vec_int (mword_of_int (KernelSyms.uartinit + 0x32) : mword 64) 4 = mword_of_int (KernelSyms.uartinit + 0x36)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp36) in "Hpc".
    (* +0x36 sb a3,1(a5) : IER <- 3 -- enable tx/rx interrupts.  Offset 1
       again, stable. *)
    iApply (Uart.wp_sb_uart_uinv_s_sconf (CID:=CID) γd 1 (mword_of_int (KernelSyms.uartinit + 0x36)) false (mword_of_int 13 : mword 5) (mword_of_int 15 : mword 5) (mword_of_int 1 : mword 12)
              R9 (K - 2)%nat
              (uart_tx_own γd l ∗ uart_dlab_is γd (DfracOwn (1/2)) false)%I
              (uart_tx_own γd l ∗ uart_dlab_is γd (DfracOwn (1/2)) false)%I
              false p
              ltac:(unfold uart_size; lia)
              ltac:(rgne; rewrite HR9a5; vm_compute; reflexivity)
              ltac:(rgne; rewrite HR9a5; apply bv_eq; vm_compute; reflexivity)
              ltac:(rgne; rewrite HR9a5; apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc Hi36 Huinv [$Htx $Hdlab] [] [-]").
    { iIntros (uu uu') "%Hw Hg [Ht Hd]".
      destruct (uart_write_1_stable uu _ uu' Hw) as (Ha & Ho & Hdb).
      iModIntro. iSplitL "Hg";
        [ iApply (uart_ghosts_stable γd uu uu' Ha Ho Hdb with "Hg") | iFrame "Ht Hd" ]. }
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc [Htx Hdlab]".
    (* Device programming done, and DLAB is off for good: freeze the caller
       half into the persistent [uart_dlab_off], which is what every later
       THR writer (uartputc_sync) needs to know offset 0 really is THR. *)
    iMod (uart_dlab_freeze γd with "Hdlab") as "#Hdoff".
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
    assert (Hpp3a : add_vec_int (mword_of_int (KernelSyms.uartinit + 0x36) : mword 64) 4 = mword_of_int (KernelSyms.uartinit + 0x3a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp3a) in "Hpc".
    (* ===== args: a1 = "uart", a0 = &tx_lock (0x3a..0x46) ===== *)
    (* +0x3a auipc a1,0x6 *)
    iApply (wp_auipc_s_sconf (mword_of_int (KernelSyms.uartinit + 0x3a)) (mword_of_int 11 : mword 5) (mword_of_int 6 : mword 20)
              R9 (K - 2)%nat false ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi3a [-]").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    set (R10 := <[Regidx (mword_of_int 11 : mword 5) := regval_into_reg (add_vec (mword_of_int (KernelSyms.uartinit + 0x3a) : mword 64) (auipc_off (mword_of_int 6 : mword 20)))]> R9).
    assert (Hpp3e : add_vec_int (mword_of_int (KernelSyms.uartinit + 0x3a) : mword 64) 4 = mword_of_int (KernelSyms.uartinit + 0x3e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp3e) in "Hpc".
    (* +0x3e addi a1,a1,1904 *)
    iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.uartinit + 0x3e)) (mword_of_int 11 : mword 5) (mword_of_int 11 : mword 5) (mword_of_int 1904 : mword 12)
              R10 (K - 2)%nat false ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi3e [-]").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    set (R11 := <[Regidx (mword_of_int 11 : mword 5) := regval_into_reg (add_vec (rget R10 (mword_of_int 11 : mword 5)) (sign_extend' 64 (mword_of_int 1904 : mword 12)))]> R10).
    (* a1 now holds &"uart" -- the string initlock is about to store *)
    assert (HR11a1 : R11 !!! Regidx (mword_of_int 11 : mword 5) = (mword_of_int 0x80007030 : mword 64)).
    { rewrite /R11 upd_eq. rgne. rewrite /R10 upd_eq. apply bv_eq; vm_compute; reflexivity. }
    assert (Hpp42 : add_vec_int (mword_of_int (KernelSyms.uartinit + 0x3e) : mword 64) 4 = mword_of_int (KernelSyms.uartinit + 0x42)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp42) in "Hpc".
    (* +0x42 auipc a0,0x12 *)
    iApply (wp_auipc_s_sconf (mword_of_int (KernelSyms.uartinit + 0x42)) (mword_of_int 10 : mword 5) (mword_of_int 18 : mword 20)
              R11 (K - 2)%nat false ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi42 [-]").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    set (R12 := <[Regidx (mword_of_int 10 : mword 5) := regval_into_reg (add_vec (mword_of_int (KernelSyms.uartinit + 0x42) : mword 64) (auipc_off (mword_of_int 18 : mword 20)))]> R11).
    assert (Hpp46 : add_vec_int (mword_of_int (KernelSyms.uartinit + 0x42) : mword 64) 4 = mword_of_int (KernelSyms.uartinit + 0x46)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp46) in "Hpc".
    (* +0x46 addi a0,a0,2632  (a0 := &tx_lock = lk) *)
    iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.uartinit + 0x46)) (mword_of_int 10 : mword 5) (mword_of_int 10 : mword 5) (mword_of_int 2632 : mword 12)
              R12 (K - 2)%nat false ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi46 [-]").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    set (R13 := <[Regidx (mword_of_int 10 : mword 5) := regval_into_reg (add_vec (rget R12 (mword_of_int 10 : mword 5)) (sign_extend' 64 (mword_of_int 2632 : mword 12)))]> R12).
    assert (HR13a0 : R13 !!! Regidx (mword_of_int 10 : mword 5) = lk).
    { rewrite /R13 upd_eq. rgne. rewrite /R12 upd_eq. unfold lk. apply bv_eq; vm_compute; reflexivity. }
    assert (HR13sp : R13 !!! Regidx csp_rs1 = spr).
    { rewrite /R13 upd_ne; [| vm_compute; discriminate].
      rewrite /R12 upd_ne; [| vm_compute; discriminate].
      rewrite /R11 upd_ne; [| vm_compute; discriminate].
      rewrite /R10 upd_ne; [exact HR9sp | vm_compute; discriminate]. }
    assert (Hpp4a : add_vec_int (mword_of_int (KernelSyms.uartinit + 0x46) : mword 64) 4 = mword_of_int (KernelSyms.uartinit + 0x4a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp4a) in "Hpc".
    (* ===== jal initlock (0x4a) ===== *)
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.uartinit + 0x4a)) (mword_of_int 1 : mword 5) (mword_of_int 696 : mword 21)
              R13 (K - 2)%nat false ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi4a [-]").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    set (R14 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.uartinit + 0x4a) : mword 64) 4)]> R13).
    assert (Htgtil : add_vec (mword_of_int (KernelSyms.uartinit + 0x4a) : mword 64) (sign_extend' 64 (mword_of_int 696 : mword 21)) = mword_of_int KernelSyms.initlock) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgtil) in "Hpc".
    assert (HR14a0 : R14 !!! Regidx (mword_of_int 10 : mword 5) = lk)
      by (rewrite /R14 upd_ne; [exact HR13a0 | vm_compute; discriminate]).
    assert (HR14a1 : R14 !!! Regidx (mword_of_int 11 : mword 5) = (mword_of_int 0x80007030 : mword 64)).
    { rewrite /R14 upd_ne; [| vm_compute; discriminate].
      rewrite /R13 upd_ne; [| vm_compute; discriminate].
      rewrite /R12 upd_ne; [exact HR11a1 | vm_compute; discriminate]. }
    assert (HR14sp : R14 !!! Regidx csp_rs1 = spr)
      by (rewrite /R14 upd_ne; [exact HR13sp | vm_compute; discriminate]).
    assert (HR14ra : R14 !!! Regidx (mword_of_int 1 : mword 5) = add_vec_int (mword_of_int (KernelSyms.uartinit + 0x4a) : mword 64) 4)
      by (rewrite /R14; apply upd_eq).
    (* initlock(&tx_lock,"uart"): owns lk's 3 fields, returns them init'd *)
    iApply (Initlock.wp_initlock_sconf R14 vlock vname vcpu "uart"%string (K - 2) false p
              ltac:(lia)
              with "Hcg Htext Hpc [] [Hlock] [Hname] [Hcpu]").
    { iEval (rewrite HR14a1). iExact "Hstr". }
    { iEval (rewrite HR14a0). iExact "Hlock". }
    { iEval (rewrite HR14a0). iExact "Hname". }
    { iEval (rewrite HR14a0). iExact "Hcpu". }
    iApply wp_next_off_intro.
    iIntros (mil) "Hcg Hpc %Hilcs Hlock Hlname Hcpu".
    iEval (rewrite HR14a0) in "Hlock". iEval (rewrite HR14a0 HR14a1) in "Hlname". iEval (rewrite HR14a0) in "Hcpu".
    iMod (lock_name_intro with "Hstr Hlname") as "#Hlnm".
    assert (Hpcil : ret_pc (R14 !!! Regidx (mword_of_int 1 : mword 5)) = mword_of_int (KernelSyms.uartinit + 0x4e)).
    { rewrite HR14ra. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite Hpcil) in "Hpc".
    pose proof Hilcs as Hilcs_full. unfold callee_saved in Hilcs.
    destruct Hilcs as (Hilsp & Hils0 & Hils1 & Hils2 & Hils3 & Hils4 & Hils5 & Hils6 & Hils7 & Hils8 & Hils9 & Hils10 & Hils11).
    assert (Hmilsp : mil !!! Regidx csp_rs1 = spr) by (rewrite Hilsp; exact HR14sp).
    (* ===== EPILOGUE 0x4e..0x54: restore ra/s0, pop frame, ret ===== *)
    (* +0x4e c.ldsp ra,8(sp) *)
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.uartinit + 0x4e)) (mword_of_int 1 : mword 6) (mword_of_int 1 : mword 5)
              mil (K - 2)%nat (m !!! Regidx (mword_of_int 1 : mword 5)) false (dqm:=DfracOwn 1)
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi4e [Hras] [-]").
    { iEval (rewrite -Hb1 -Hmilsp) in "Hras". iExact "Hras". }
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc Hras".
    iEval (rewrite Hmilsp Hb1) in "Hras".
    set (E1 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 1 : mword 5))]> mil).
    assert (HE1sp : E1 !!! Regidx csp_rs1 = spr) by (rewrite /E1 upd_ne; [exact Hmilsp | vm_compute; discriminate]).
    assert (Hpp50 : add_vec_int (mword_of_int (KernelSyms.uartinit + 0x4e) : mword 64) 2 = mword_of_int (KernelSyms.uartinit + 0x50)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp50) in "Hpc".
    (* +0x50 c.ldsp s0,0(sp) *)
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.uartinit + 0x50)) (mword_of_int 0 : mword 6) (mword_of_int 8 : mword 5)
              E1 (K - 2)%nat (m !!! Regidx (mword_of_int 8 : mword 5)) false (dqm:=DfracOwn 1)
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi50 [Hs0s] [-]").
    { iEval (rewrite -Hb2 -HE1sp) in "Hs0s". iExact "Hs0s". }
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc Hs0s".
    iEval (rewrite HE1sp Hb2) in "Hs0s".
    set (E2 := <[Regidx (mword_of_int 8 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 8 : mword 5))]> E1).
    assert (HE2sp : E2 !!! Regidx csp_rs1 = spr) by (rewrite /E2 upd_ne; [exact HE1sp | vm_compute; discriminate]).
    assert (Hpp52 : add_vec_int (mword_of_int (KernelSyms.uartinit + 0x50) : mword 64) 2 = mword_of_int (KernelSyms.uartinit + 0x52)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp52) in "Hpc".
    (* +0x52 c.addi sp,16 : pop frame *)
    set (E3 := <[Regidx csp_rs1 := regval_into_reg (add_vec (E2 !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 16 : mword 6))))]> E2).
    assert (HE3csp : E3 !!! Regidx csp_rs1 = sp0).
    { rewrite /E3 upd_eq. rewrite HE2sp. unfold regval_into_reg, spr, sp0.
      apply frame_cancel_16. }
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
    iApply (wp_caddi_sp_pop_s_sconf (mword_of_int (KernelSyms.uartinit + 0x52)) (mword_of_int 16 : mword 6) E2 (K - 2)%nat 2 false Hpop
              with "Hcg Hpc Hi52 Hframe [-]").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    assert (Hnk : ((K - 2) + 2)%nat = K) by lia.
    iEval (rewrite Hnk) in "Hcg".
    change (<[Regidx csp_rs1 := regval_into_reg (add_vec (E2 !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 16 : mword 6))))]> E2) with E3.
    assert (Hpp54 : add_vec_int (mword_of_int (KernelSyms.uartinit + 0x52) : mword 64) 2 = mword_of_int (KernelSyms.uartinit + 0x54)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp54) in "Hpc".
    (* +0x54 c.ret *)
    assert (HE3ra : E3 !!! Regidx (mword_of_int 1 : mword 5) = m !!! Regidx (mword_of_int 1 : mword 5)).
    { rewrite /E3 upd_ne; [| vm_compute; discriminate].
      rewrite /E2 upd_ne; [| vm_compute; discriminate].
      rewrite /E1 upd_eq; reflexivity. }
    iApply (wp_cret_s_sconf (mword_of_int (KernelSyms.uartinit + 0x54)) (mword_of_int 1 : mword 5) E3 K false
              ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi54 [-]").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    assert (Hretf : forall (CID' : CpuId), ret_pc (rget (CID := CID') E3 (mword_of_int 1 : mword 5)) = ret_tgt)
      by (intros CID'; rgne; rewrite HE3ra; reflexivity).
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
    iApply ("Hcont" $! E3 with "Hcg Hpc [%] Htx Hsent Hdoff Hlock Hlnm Hcpu").
    unfold callee_saved.
    split. { rewrite HE3csp. reflexivity. }
    split. { rewrite /E3 upd_ne; [| vm_compute; discriminate].
             rewrite /E2 upd_eq; reflexivity. }
    repeat split; apply Hthread; vm_compute; first [reflexivity | discriminate].
  Qed.

End ProofUartinit.
End UartinitProof.
