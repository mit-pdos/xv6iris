(* ProofUartinitone.v -- the whole-function WP for xv6's uartinitone() over
   the SIE-agnostic sconf world.  uartinitone() programs ONE 16550: 7 MMIO
   byte writes to the port its argument names, and NOTHING ELSE, then
   [initlock(&u->tx_lock, name)].

   Straight-line, 16-byte frame, ONE sub-call.  [uartinit] is two calls to it
   (ProofUartinit).

   THE ADDRESS IS LOADED, AND THAT IS THE WHOLE DIFFERENCE FROM THE OLD
   SINGLE-PORT uartinit.  Every [WriteReg(u, reg, v)] compiles to
   [ld a5,0(a0); sb …,reg(a5)], so the store leaf's base register holds the
   `.data` word [uarts[i].base] rather than a [lui] constant.  What turns
   that into [uart_pa i off] is [SpecUartPutc.uart_base_word i], the
   persistent VA-tier snapshot the boot chain mints; the load itself is the
   ordinary RAM leaf [WpSconfMem.wp_cld_s_sconf] at [DfracDiscarded].  The
   seventh write additionally reads [u->rx] ([UartTxInv.uart_rx_word i]) and
   runs [snez]/[addi] on it, so the IER byte is 3 at the console and 2 at
   the other port -- but nothing in the proof depends on WHICH, because
   offset 1 is stable at every byte ([uart_write_1_stable]).

   THE PROOF IS PORT-GENERIC.  [i] stays symbolic all the way through; the
   only places it is case-split are the closed address/geometry equations,
   each one line of [destruct i; …].  The device leaf is the port-indexed
   [SpecUart.wp_sb_uart_uinv_s_sconf_at], which opens [uart_inv i].

   THE STACK BUDGET IS 2 + 2.  uartinitone's own frame is two slots
   ([addi sp,sp,-16]); [SpecInitlock] asks [(2 <= av)] of what it is handed,
   and what it is handed is [K - 2].

   THE SEVEN STORES RUN UNDER THE TIME-0 UART INVARIANT.  The UART thread is
   a top-level thread from step 0, so [uart_frag] can never sit raw in a
   CPU's precondition; each store goes through the invariant-borrowing
   accessor leaf, which opens [uart_inv i] across its own step and asks the
   caller for a GHOST STEP.  What travels through those wands is the pair
   the caller threads: the exclusive transmitter token [uart_tx_own γd l]
   and the UNFROZEN DLAB half.  Per offset:

     off 1 (IER / DLM), off 0 with DLAB set (DLL) -- pure config, nothing
       tracked moves ([uart_write_1_stable] / [uart_write_0_dlab_stable]).
     off 3 (LCR) -- DLAB moves, and only DLAB ([ui_lcr_step]).
     off 2 (FCR = 0x07) -- bits 1|2 clear both FIFOs.  The rx clear is paid
       for with the receive token; the tx clear would SHRINK the accepted
       trace, except that the token pins [uart_acc u = l] and the carried
       [uart_out_lb l] says [l] is already transmitted, so
       [uart_tx_empty_of_out] leaves the FIFO empty and the clear shrinks
       nothing ([ui_tx_empty]).

   After the final LCR write the caller half is at [false], so
   [uart_dlab_freeze] mints the persistent [uart_dlab_off] -- this
   function's output, at this port. *)
From Stdlib Require Import Eqdep_dec ZArith Lia List String.
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
Require Import StackOwn CalleeSaved.
Require Import KernelDataInv.
Require Import DevModel WpUart.
Require Import ObsTrace.   (* [uart_write_wire]: no MMIO write drives SOUT *)
Require Import PowerBoot.   (* [pa_of_z] *)
Require Import UartsFields.
Require Import WpSmodeIntr.
Require Import IntrDefs HartTp WpNext.
Require Import WpSconfAlu WpSconfMem WpSconfCtl.
Require Import WpLock.
Require Import UartTxInv.
Require Import SpecProcinit.
Require Import SpecUart.
Require Import SpecUartPutc.
Require Import SpecInitlock.
Require Import CodeUartinitone.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SpecUartinitone.
Require Import KernelRvcDecode.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Require Import TsoCtx.
Local Open Scope Z_scope.
Import Defs.

Notation UIO := KernelSyms.uartinitone (only parsing).

Module UartinitoneProof (Uart : UART) (Initlock : INITLOCK) : UARTINITONE.

Section ProofUartinitone.
  Context `{!riscvGS Σ, !xv6G Σ}.
  Context `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}.

  (* ------------------------------------------------------------------- *)
  (*  The three readings of the invariant's ghost bundle the seven ghost  *)
  (*  steps below need.  Each is stated over [uart_ghosts] rather than    *)
  (*  its components, because that is the form the accessor leaf hands    *)
  (*  out.                                                                *)
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

  Lemma wp_uartinitone_sconf (i : uart_id) (γd : uart_names)
      (nm : string) (nm_addr : mword 64)
      (m : regfile) (K : nat) (l : list (bv 8)) (b0 : bool) (k : nat)
      (hl : option (list mobs)) (p : mword 64)
    : wp_uartinitone_sconf_body i γd nm nm_addr m K l b0 k hl p.
  Proof.
    cbv beta delta [wp_uartinitone_sconf_body].
    intros pcE ret_tgt HK Ha0 Ha1.
    set (sp0 := m !!! Regidx csp_rs1).
    set (spr := add_vec sp0 (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6)))).
    iIntros "Hcg #Htext Hpc #Hbase #Hrx #Hnm #Huinv Htx #Hlb #Hsent Htok Hdlab Hraw Hcont".
    iDestruct "Hraw" as (vtlock vtname vtcpu) "(Hf1 & Hf2 & Hf3)".
    iDestruct (sie_cap_gpr_x0 m K false p (mword_of_int 0 : mword 5) ltac:(vm_compute; reflexivity)
                 with "Hcg") as "[%Hx0 Hcg]".
    (* ---- the two field addresses, off the ONE argument in a0 ---- *)
    assert (Hea0 : add_vec (mword_of_int (uart_elt i) : mword 64)
                     (sign_extend' 64 (mword_of_int 0 : mword 12))
                   = pa_of_z (uart_f_base i))
      by (destruct i; apply bv_eq; vm_compute; reflexivity).
    assert (Hea8 : add_vec (mword_of_int (uart_elt i) : mword 64)
                     (sign_extend' 64 (mword_of_int 8 : mword 12))
                   = pa_of_z (uart_f_rx i))
      by (destruct i; apply bv_eq; vm_compute; reflexivity).
    (* the LOADED base word IS the port's MMIO window base *)
    assert (Hbw : (Z_to_bv 64 (uart_base i) : mword 64) = uart_pa i 0)
      by (destruct i; apply bv_eq; vm_compute; reflexivity).
    (* pc-advance helper facts *)
    assert (Hspr2 : spr = pa_stk sp0 2).
    { unfold spr, pa_stk, add_vec_int. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb1s : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000"))) = pa_stk sp0 1).
    { unfold spr, sp0, pa_stk, add_vec_int. rewrite pa_stk_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb2s : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 0 : mword 6) ('b"000"))) = pa_stk sp0 2).
    { unfold spr, sp0, pa_stk, add_vec_int. rewrite pa_stk_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    (* ===== PROLOGUE 0x00..0x06 ===== *)
    set (R1 := <[Regidx csp_rs1 := regval_into_reg (add_vec sp0 (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6))))]> m).
    assert (Hspm : m !!! Regidx csp_rs1 = sp0) by reflexivity.
    assert (Hpush : add_vec (m !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6))) = pa_stk (m !!! Regidx csp_rs1) 2).
    { unfold pa_stk, add_vec_int. apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    iApply (wp_caddi_sp_push_s_sconf pcE (mword_of_int 48 : mword 6) m K 2 false ltac:(lia) Hpush
              with "Hcg Hpc []").
    { iApply (uio_00 with "Htext"). }
    iApply wp_next_off_intro.
    iIntros "Hcg Hframe Hpc".
    iEval (rewrite Hspm) in "Hframe".
    change (<[Regidx csp_rs1 := regval_into_reg (add_vec sp0 (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6))))]> m) with R1.
    assert (HspR1 : R1 !!! Regidx csp_rs1 = spr) by (rewrite /R1 upd_eq; reflexivity).
    iEval (rewrite (stack_own_slots (KTR := KT0)); cbn [seq]) in "Hframe".
    iDestruct "Hframe" as "(S1 & S2 & _)".
    iDestruct "S1" as (vra0) "Hras". iDestruct "S2" as (vs00) "Hs0s".
    assert (Hpp02 : add_vec_int (pcE : mword 64) 2 = mword_of_int (UIO + 0x02)) by (unfold pcE; apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp02) in "Hpc".
    (* +0x02 c.sdsp ra,8(sp) *)
    iApply (wp_csdsp_s_sconf (mword_of_int (UIO + 0x02)) (mword_of_int 1 : mword 6) (mword_of_int 1 : mword 5)
              R1 (K - 2)%nat vra0 false with "Hcg Hpc [] [Hras]").
    { iApply (uio_02 with "Htext"). }
    { iEval (rewrite HspR1 Hb1s). iExact "Hras". }
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc Hras".
    iEval (rewrite HspR1 Hb1s) in "Hras".
    assert (Hrav : forall (CID' : CpuId), rget (CID := CID') R1 (mword_of_int 1 : mword 5) = m !!! Regidx (mword_of_int 1 : mword 5))
      by (intros CID'; rgne; rewrite /R1 upd_ne; [reflexivity | vm_compute; discriminate]).
    iEval (rewrite Hrav) in "Hras".
    assert (Hpp04 : add_vec_int (mword_of_int (UIO + 0x02) : mword 64) 2 = mword_of_int (UIO + 0x04)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp04) in "Hpc".
    (* +0x04 c.sdsp s0,0(sp) *)
    iApply (wp_csdsp_s_sconf (mword_of_int (UIO + 0x04)) (mword_of_int 0 : mword 6) (mword_of_int 8 : mword 5)
              R1 (K - 2)%nat vs00 false with "Hcg Hpc [] [Hs0s]").
    { iApply (uio_04 with "Htext"). }
    { iEval (rewrite HspR1 Hb2s). iExact "Hs0s". }
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc Hs0s".
    iEval (rewrite HspR1 Hb2s) in "Hs0s".
    assert (Hs0v : forall (CID' : CpuId), rget (CID := CID') R1 (mword_of_int 8 : mword 5) = m !!! Regidx (mword_of_int 8 : mword 5))
      by (intros CID'; rgne; rewrite /R1 upd_ne; [reflexivity | vm_compute; discriminate]).
    iEval (rewrite Hs0v) in "Hs0s".
    assert (Hpp06 : add_vec_int (mword_of_int (UIO + 0x04) : mword 64) 2 = mword_of_int (UIO + 0x06)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp06) in "Hpc".
    (* +0x06 c.addi4spn s0,sp,16 *)
    iApply (wp_caddi4spn_s_sconf (mword_of_int (UIO + 0x06)) (Cregidx (mword_of_int 0)) (mword_of_int 4 : mword 8) (mword_of_int 8 : mword 5)
              R1 (K - 2)%nat false ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc []").
    { iApply (uio_06 with "Htext"). }
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    set (R2 := <[Regidx (mword_of_int 8 : mword 5) := regval_into_reg (add_vec (R1 !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm (mword_of_int 4 : mword 8))))]> R1).
    assert (HR2sp : R2 !!! Regidx csp_rs1 = spr)
      by (rewrite /R2 upd_ne; [exact HspR1 | vm_compute; discriminate]).
    assert (HR2a0 : R2 !!! Regidx (mword_of_int 10 : mword 5) = mword_of_int (uart_elt i)).
    { rewrite /R2 upd_ne; [| vm_compute; discriminate].
      rewrite /R1 upd_ne; [exact Ha0 | vm_compute; discriminate]. }
    assert (HR2a1 : R2 !!! Regidx (mword_of_int 11 : mword 5) = nm_addr).
    { rewrite /R2 upd_ne; [| vm_compute; discriminate].
      rewrite /R1 upd_ne; [exact Ha1 | vm_compute; discriminate]. }
    assert (HR2x0 : R2 !!! Regidx (mword_of_int 0 : mword 5) = zero_reg).
    { rewrite /R2 upd_ne; [| vm_compute; discriminate].
      rewrite /R1 upd_ne; [exact Hx0 | vm_compute; discriminate]. }
    assert (Hpp08 : add_vec_int (mword_of_int (UIO + 0x06) : mword 64) 2 = mword_of_int (UIO + 0x08)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp08) in "Hpc".
    (* ---- the seven WriteRegs.  Each is [c.ld <r>,0(a0)] then [sb …]. ---- *)
    (* +0x08 c.ld a5,0(a0) *)
    iApply (wp_cld_s_sconf (ktd := KT0) (mword_of_int (UIO + 0x08)) (mword_of_int 15 : mword 5) (mword_of_int 10 : mword 5)
              (mword_of_int 0 : mword 12) R2 (K - 2)%nat (Z_to_bv 64 (uart_base i)) false (dqm:=DfracDiscarded)
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc [] [Hbase]").
    { iApply (uio_08 with "Htext"). }
    { rgne. rewrite HR2a0 Hea0. iExact "Hbase". }
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc _".
    set (L1 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (Z_to_bv 64 (uart_base i) : mword 64)]> R2).
    assert (HL1a5 : L1 !!! Regidx (mword_of_int 15 : mword 5) = uart_pa i 0)
      by (rewrite /L1 upd_eq; exact Hbw).
    assert (HL1a0 : L1 !!! Regidx (mword_of_int 10 : mword 5) = mword_of_int (uart_elt i))
      by (rewrite /L1 upd_ne; [exact HR2a0 | vm_compute; discriminate]).
    assert (HL1x0 : L1 !!! Regidx (mword_of_int 0 : mword 5) = zero_reg)
      by (rewrite /L1 upd_ne; [exact HR2x0 | vm_compute; discriminate]).
    assert (Hpp0a : add_vec_int (mword_of_int (UIO + 0x08) : mword 64) 2 = mword_of_int (UIO + 0x0a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp0a) in "Hpc".
    (* +0x0a sb zero,1(a5) : IER <- 0 *)
    iApply (Uart.wp_sb_uart_uinv_s_sconf_at KT0 i (CID:=CID) γd 1 (mword_of_int (UIO + 0x0a)) false (mword_of_int 0 : mword 5) (mword_of_int 15 : mword 5) (mword_of_int 1 : mword 12)
              L1 (K - 2)%nat
              (uart_tx_own γd l ∗ uart_dlab_is γd (DfracOwn (1/2)) b0)%I
              (uart_tx_own γd l ∗ uart_dlab_is γd (DfracOwn (1/2)) b0)%I
              false p
              ltac:(unfold uart_size; lia)
              ltac:(rgne; rewrite HL1a5; destruct i; vm_compute; reflexivity)
              ltac:(rgne; rewrite HL1a5; destruct i; apply bv_eq; vm_compute; reflexivity)
              ltac:(rgne; rewrite HL1a5; destruct i; apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc [] Huinv [$Htx $Hdlab] []").
    { iApply (uio_0a with "Htext"). }
    { iIntros (uu uu') "%Hw Hg Hcol [Ht Hd]".
      destruct (uart_write_1_stable uu _ uu' Hw) as (Ha & Ho & Hdb).
      destruct (uart_write_rx_stable uu 1 _ uu' ltac:(lia) ltac:(lia) Hw)
        as [Hrxe Hlbe].
      iModIntro. iSplitL "Hg";
        [ iApply (uart_ghosts_stable γd uu uu' Ha Ho Hdb with "Hg") |].
      iSplitL "Hcol";
        [ iApply (uart_colE_stable i γd uu uu' Hrxe Hlbe
             ltac:(exact (uart_write_wire _ _ _ _ Hw)) Ho with "Hcol")
        | iFrame "Ht Hd" ]. }
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc [Htx Hdlab]".
    assert (Hpp0e : add_vec_int (mword_of_int (UIO + 0x0a) : mword 64) 4 = mword_of_int (UIO + 0x0e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp0e) in "Hpc".
    (* +0x0e c.ld a5,0(a0) *)
    iApply (wp_cld_s_sconf (ktd := KT0) (mword_of_int (UIO + 0x0e)) (mword_of_int 15 : mword 5) (mword_of_int 10 : mword 5)
              (mword_of_int 0 : mword 12) L1 (K - 2)%nat (Z_to_bv 64 (uart_base i)) false (dqm:=DfracDiscarded)
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc [] [Hbase]").
    { iApply (uio_0e with "Htext"). }
    { rgne. rewrite HL1a0 Hea0. iExact "Hbase". }
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc _".
    set (L2 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (Z_to_bv 64 (uart_base i) : mword 64)]> L1).
    assert (HL2a5 : L2 !!! Regidx (mword_of_int 15 : mword 5) = uart_pa i 0)
      by (rewrite /L2 upd_eq; exact Hbw).
    assert (HL2a0 : L2 !!! Regidx (mword_of_int 10 : mword 5) = mword_of_int (uart_elt i))
      by (rewrite /L2 upd_ne; [exact HL1a0 | vm_compute; discriminate]).
    assert (HL2x0 : L2 !!! Regidx (mword_of_int 0 : mword 5) = zero_reg)
      by (rewrite /L2 upd_ne; [exact HL1x0 | vm_compute; discriminate]).
    assert (Hpp10 : add_vec_int (mword_of_int (UIO + 0x0e) : mword 64) 2 = mword_of_int (UIO + 0x10)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp10) in "Hpc".
    (* +0x10 li a4,-128 *)
    iApply (wp_addi4_s_sconf (mword_of_int (UIO + 0x10)) (mword_of_int 14 : mword 5) (mword_of_int 0 : mword 5) (mword_of_int 3968 : mword 12)
              L2 (K - 2)%nat false ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc []").
    { iApply (uio_10 with "Htext"). }
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (L3 := <[Regidx (mword_of_int 14 : mword 5) := regval_into_reg (add_vec (L2 !!! Regidx (mword_of_int 0 : mword 5)) (sign_extend' 64 (mword_of_int 3968 : mword 12)))]> L2).
    assert (HL3a5 : L3 !!! Regidx (mword_of_int 15 : mword 5) = uart_pa i 0)
      by (rewrite /L3 upd_ne; [exact HL2a5 | vm_compute; discriminate]).
    assert (HL3a0 : L3 !!! Regidx (mword_of_int 10 : mword 5) = mword_of_int (uart_elt i))
      by (rewrite /L3 upd_ne; [exact HL2a0 | vm_compute; discriminate]).
    assert (HL3x0 : L3 !!! Regidx (mword_of_int 0 : mword 5) = zero_reg)
      by (rewrite /L3 upd_ne; [exact HL2x0 | vm_compute; discriminate]).
    assert (Hpp14 : add_vec_int (mword_of_int (UIO + 0x10) : mword 64) 4 = mword_of_int (UIO + 0x14)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp14) in "Hpc".
    (* +0x14 sb a4,3(a5) : LCR <- 0x80 -- DLAB ON *)
    assert (Hblcr1 : (autocast (T := mword) (subrange_vec_dec (L3 !!! Regidx (mword_of_int 14 : mword 5)) (Z.sub (Z.mul 1 8) 1) 0) : mword 8) = Z_to_bv 8 128).
    { rewrite /L3 upd_eq. rewrite HL2x0. apply bv_eq; vm_compute; reflexivity. }
    iApply (Uart.wp_sb_uart_uinv_s_sconf_at KT0 i (CID:=CID) γd 3 (mword_of_int (UIO + 0x14)) false (mword_of_int 14 : mword 5) (mword_of_int 15 : mword 5) (mword_of_int 3 : mword 12)
              L3 (K - 2)%nat
              (uart_tx_own γd l ∗ uart_dlab_is γd (DfracOwn (1/2)) b0)%I
              (uart_tx_own γd l ∗ uart_dlab_is γd (DfracOwn (1/2)) true)%I
              false p
              ltac:(unfold uart_size; lia)
              ltac:(rgne; rewrite HL3a5; destruct i; vm_compute; reflexivity)
              ltac:(rgne; rewrite HL3a5; destruct i; apply bv_eq; vm_compute; reflexivity)
              ltac:(rgne; rewrite HL3a5; destruct i; apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc [] Huinv [$Htx $Hdlab] []").
    { iApply (uio_14 with "Htext"). }
    { iIntros (uu uu') "%Hw Hg Hcol [Ht Hd]".
      destruct (uart_write_3_stable uu _ uu' Hw) as (Ha & Ho & Hdb).
      destruct (uart_write_rx_stable uu 3 _ uu' ltac:(lia) ltac:(lia) Hw)
        as [Hrxe Hlbe].
      assert (Hdt : uart_dlab uu' = true)
        by (rewrite Hdb Hblcr1; vm_compute; reflexivity).
      iMod (ui_lcr_step γd uu uu' b0 Ha Ho with "Hg Hd") as "[Hg' Hd']".
      iEval (rewrite Hdt) in "Hd'".
      iModIntro. iSplitL "Hg'"; [ iExact "Hg'" |].
      iSplitL "Hcol";
        [ iApply (uart_colE_stable i γd uu uu' Hrxe Hlbe
             ltac:(exact (uart_write_wire _ _ _ _ Hw)) Ho with "Hcol")
        | iFrame "Ht Hd'" ]. }
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc [Htx Hdlab]".
    assert (Hpp18 : add_vec_int (mword_of_int (UIO + 0x14) : mword 64) 4 = mword_of_int (UIO + 0x18)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp18) in "Hpc".
    (* +0x18 c.ld a4,0(a0) *)
    iApply (wp_cld_s_sconf (ktd := KT0) (mword_of_int (UIO + 0x18)) (mword_of_int 14 : mword 5) (mword_of_int 10 : mword 5)
              (mword_of_int 0 : mword 12) L3 (K - 2)%nat (Z_to_bv 64 (uart_base i)) false (dqm:=DfracDiscarded)
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc [] [Hbase]").
    { iApply (uio_18 with "Htext"). }
    { rgne. rewrite HL3a0 Hea0. iExact "Hbase". }
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc _".
    set (L4 := <[Regidx (mword_of_int 14 : mword 5) := regval_into_reg (Z_to_bv 64 (uart_base i) : mword 64)]> L3).
    assert (HL4a4 : L4 !!! Regidx (mword_of_int 14 : mword 5) = uart_pa i 0)
      by (rewrite /L4 upd_eq; exact Hbw).
    assert (HL4a0 : L4 !!! Regidx (mword_of_int 10 : mword 5) = mword_of_int (uart_elt i))
      by (rewrite /L4 upd_ne; [exact HL3a0 | vm_compute; discriminate]).
    assert (HL4x0 : L4 !!! Regidx (mword_of_int 0 : mword 5) = zero_reg)
      by (rewrite /L4 upd_ne; [exact HL3x0 | vm_compute; discriminate]).
    assert (Hpp1a : add_vec_int (mword_of_int (UIO + 0x18) : mword 64) 2 = mword_of_int (UIO + 0x1a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp1a) in "Hpc".
    (* +0x1a c.li a5,3 *)
    iApply (wp_cli_s_sconf (mword_of_int (UIO + 0x1a)) (mword_of_int 15 : mword 5) (mword_of_int 3 : mword 6) (mword_of_int 3 : mword 64)
              L4 (K - 2)%nat false ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc []").
    { iApply (uio_1a with "Htext"). }
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    set (L5 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (mword_of_int 3 : mword 64)]> L4).
    assert (HL5a4 : L5 !!! Regidx (mword_of_int 14 : mword 5) = uart_pa i 0)
      by (rewrite /L5 upd_ne; [exact HL4a4 | vm_compute; discriminate]).
    assert (HL5a0 : L5 !!! Regidx (mword_of_int 10 : mword 5) = mword_of_int (uart_elt i))
      by (rewrite /L5 upd_ne; [exact HL4a0 | vm_compute; discriminate]).
    assert (HL5a5 : L5 !!! Regidx (mword_of_int 15 : mword 5) = mword_of_int 3)
      by (rewrite /L5 upd_eq; reflexivity).
    assert (HL5x0 : L5 !!! Regidx (mword_of_int 0 : mword 5) = zero_reg)
      by (rewrite /L5 upd_ne; [exact HL4x0 | vm_compute; discriminate]).
    assert (Hpp1c : add_vec_int (mword_of_int (UIO + 0x1a) : mword 64) 2 = mword_of_int (UIO + 0x1c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp1c) in "Hpc".
    (* +0x1c sb a5,0(a4) : DLL <- 3, and offset 0 is the divisor latch
       because the caller's DLAB half says DLAB is set *)
    iApply (Uart.wp_sb_uart_uinv_s_sconf_at KT0 i (CID:=CID) γd 0 (mword_of_int (UIO + 0x1c)) false (mword_of_int 15 : mword 5) (mword_of_int 14 : mword 5) (mword_of_int 0 : mword 12)
              L5 (K - 2)%nat
              (uart_tx_own γd l ∗ uart_dlab_is γd (DfracOwn (1/2)) true)%I
              (uart_tx_own γd l ∗ uart_dlab_is γd (DfracOwn (1/2)) true)%I
              false p
              ltac:(unfold uart_size; lia)
              ltac:(rgne; rewrite HL5a4; destruct i; vm_compute; reflexivity)
              ltac:(rgne; rewrite HL5a4; destruct i; apply bv_eq; vm_compute; reflexivity)
              ltac:(rgne; rewrite HL5a4; destruct i; apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc [] Huinv [$Htx $Hdlab] []").
    { iApply (uio_1c with "Htext"). }
    { iIntros (uu uu') "%Hw Hg Hcol [Ht Hd]".
      iDestruct (ui_dlab_of_ghosts γd uu (DfracOwn (1/2)) true with "Hg Hd") as %Hdu.
      destruct (uart_write_0_dlab_stable uu _ uu' Hdu Hw) as (Ha & Ho & Hdb).
      destruct (uart_write_rx_stable uu 0 _ uu' ltac:(lia) ltac:(lia) Hw)
        as [Hrxe Hlbe].
      iModIntro. iSplitL "Hg";
        [ iApply (uart_ghosts_stable γd uu uu' Ha Ho Hdb with "Hg") |].
      iSplitL "Hcol";
        [ iApply (uart_colE_stable i γd uu uu' Hrxe Hlbe
             ltac:(exact (uart_write_wire _ _ _ _ Hw)) Ho with "Hcol")
        | iFrame "Ht Hd" ]. }
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc [Htx Hdlab]".
    assert (Hpp20 : add_vec_int (mword_of_int (UIO + 0x1c) : mword 64) 4 = mword_of_int (UIO + 0x20)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp20) in "Hpc".
    (* +0x20 c.ld a4,0(a0) *)
    iApply (wp_cld_s_sconf (ktd := KT0) (mword_of_int (UIO + 0x20)) (mword_of_int 14 : mword 5) (mword_of_int 10 : mword 5)
              (mword_of_int 0 : mword 12) L5 (K - 2)%nat (Z_to_bv 64 (uart_base i)) false (dqm:=DfracDiscarded)
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc [] [Hbase]").
    { iApply (uio_20 with "Htext"). }
    { rgne. rewrite HL5a0 Hea0. iExact "Hbase". }
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc _".
    set (L6 := <[Regidx (mword_of_int 14 : mword 5) := regval_into_reg (Z_to_bv 64 (uart_base i) : mword 64)]> L5).
    assert (HL6a4 : L6 !!! Regidx (mword_of_int 14 : mword 5) = uart_pa i 0)
      by (rewrite /L6 upd_eq; exact Hbw).
    assert (HL6a0 : L6 !!! Regidx (mword_of_int 10 : mword 5) = mword_of_int (uart_elt i))
      by (rewrite /L6 upd_ne; [exact HL5a0 | vm_compute; discriminate]).
    assert (HL6a5 : L6 !!! Regidx (mword_of_int 15 : mword 5) = mword_of_int 3)
      by (rewrite /L6 upd_ne; [exact HL5a5 | vm_compute; discriminate]).
    assert (HL6x0 : L6 !!! Regidx (mword_of_int 0 : mword 5) = zero_reg)
      by (rewrite /L6 upd_ne; [exact HL5x0 | vm_compute; discriminate]).
    assert (Hpp22 : add_vec_int (mword_of_int (UIO + 0x20) : mword 64) 2 = mword_of_int (UIO + 0x22)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp22) in "Hpc".
    (* +0x22 sb zero,1(a4) : DLM <- 0 *)
    iApply (Uart.wp_sb_uart_uinv_s_sconf_at KT0 i (CID:=CID) γd 1 (mword_of_int (UIO + 0x22)) false (mword_of_int 0 : mword 5) (mword_of_int 14 : mword 5) (mword_of_int 1 : mword 12)
              L6 (K - 2)%nat
              (uart_tx_own γd l ∗ uart_dlab_is γd (DfracOwn (1/2)) true)%I
              (uart_tx_own γd l ∗ uart_dlab_is γd (DfracOwn (1/2)) true)%I
              false p
              ltac:(unfold uart_size; lia)
              ltac:(rgne; rewrite HL6a4; destruct i; vm_compute; reflexivity)
              ltac:(rgne; rewrite HL6a4; destruct i; apply bv_eq; vm_compute; reflexivity)
              ltac:(rgne; rewrite HL6a4; destruct i; apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc [] Huinv [$Htx $Hdlab] []").
    { iApply (uio_22 with "Htext"). }
    { iIntros (uu uu') "%Hw Hg Hcol [Ht Hd]".
      destruct (uart_write_1_stable uu _ uu' Hw) as (Ha & Ho & Hdb).
      destruct (uart_write_rx_stable uu 1 _ uu' ltac:(lia) ltac:(lia) Hw)
        as [Hrxe Hlbe].
      iModIntro. iSplitL "Hg";
        [ iApply (uart_ghosts_stable γd uu uu' Ha Ho Hdb with "Hg") |].
      iSplitL "Hcol";
        [ iApply (uart_colE_stable i γd uu uu' Hrxe Hlbe
             ltac:(exact (uart_write_wire _ _ _ _ Hw)) Ho with "Hcol")
        | iFrame "Ht Hd" ]. }
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc [Htx Hdlab]".
    assert (Hpp26 : add_vec_int (mword_of_int (UIO + 0x22) : mword 64) 4 = mword_of_int (UIO + 0x26)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp26) in "Hpc".
    (* +0x26 c.ld a4,0(a0) *)
    iApply (wp_cld_s_sconf (ktd := KT0) (mword_of_int (UIO + 0x26)) (mword_of_int 14 : mword 5) (mword_of_int 10 : mword 5)
              (mword_of_int 0 : mword 12) L6 (K - 2)%nat (Z_to_bv 64 (uart_base i)) false (dqm:=DfracDiscarded)
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc [] [Hbase]").
    { iApply (uio_26 with "Htext"). }
    { rgne. rewrite HL6a0 Hea0. iExact "Hbase". }
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc _".
    set (L7 := <[Regidx (mword_of_int 14 : mword 5) := regval_into_reg (Z_to_bv 64 (uart_base i) : mword 64)]> L6).
    assert (HL7a4 : L7 !!! Regidx (mword_of_int 14 : mword 5) = uart_pa i 0)
      by (rewrite /L7 upd_eq; exact Hbw).
    assert (HL7a0 : L7 !!! Regidx (mword_of_int 10 : mword 5) = mword_of_int (uart_elt i))
      by (rewrite /L7 upd_ne; [exact HL6a0 | vm_compute; discriminate]).
    assert (HL7a5 : L7 !!! Regidx (mword_of_int 15 : mword 5) = mword_of_int 3)
      by (rewrite /L7 upd_ne; [exact HL6a5 | vm_compute; discriminate]).
    assert (HL7x0 : L7 !!! Regidx (mword_of_int 0 : mword 5) = zero_reg)
      by (rewrite /L7 upd_ne; [exact HL6x0 | vm_compute; discriminate]).
    assert (Hpp28 : add_vec_int (mword_of_int (UIO + 0x26) : mword 64) 2 = mword_of_int (UIO + 0x28)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp28) in "Hpc".
    (* +0x28 sb a5,3(a4) : LCR <- 0x03 -- 8N1, DLAB OFF *)
    assert (Hblcr2 : (autocast (T := mword) (subrange_vec_dec (L7 !!! Regidx (mword_of_int 15 : mword 5)) (Z.sub (Z.mul 1 8) 1) 0) : mword 8) = Z_to_bv 8 3).
    { rewrite HL7a5. apply bv_eq; vm_compute; reflexivity. }
    iApply (Uart.wp_sb_uart_uinv_s_sconf_at KT0 i (CID:=CID) γd 3 (mword_of_int (UIO + 0x28)) false (mword_of_int 15 : mword 5) (mword_of_int 14 : mword 5) (mword_of_int 3 : mword 12)
              L7 (K - 2)%nat
              (uart_tx_own γd l ∗ uart_dlab_is γd (DfracOwn (1/2)) true)%I
              (uart_tx_own γd l ∗ uart_dlab_is γd (DfracOwn (1/2)) false)%I
              false p
              ltac:(unfold uart_size; lia)
              ltac:(rgne; rewrite HL7a4; destruct i; vm_compute; reflexivity)
              ltac:(rgne; rewrite HL7a4; destruct i; apply bv_eq; vm_compute; reflexivity)
              ltac:(rgne; rewrite HL7a4; destruct i; apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc [] Huinv [$Htx $Hdlab] []").
    { iApply (uio_28 with "Htext"). }
    { iIntros (uu uu') "%Hw Hg Hcol [Ht Hd]".
      destruct (uart_write_3_stable uu _ uu' Hw) as (Ha & Ho & Hdb).
      destruct (uart_write_rx_stable uu 3 _ uu' ltac:(lia) ltac:(lia) Hw)
        as [Hrxe Hlbe].
      assert (Hdt : uart_dlab uu' = false)
        by (rewrite Hdb Hblcr2; vm_compute; reflexivity).
      iMod (ui_lcr_step γd uu uu' true Ha Ho with "Hg Hd") as "[Hg' Hd']".
      iEval (rewrite Hdt) in "Hd'".
      iModIntro. iSplitL "Hg'"; [ iExact "Hg'" |].
      iSplitL "Hcol";
        [ iApply (uart_colE_stable i γd uu uu' Hrxe Hlbe
             ltac:(exact (uart_write_wire _ _ _ _ Hw)) Ho with "Hcol")
        | iFrame "Ht Hd'" ]. }
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc [Htx Hdlab]".
    assert (Hpp2c : add_vec_int (mword_of_int (UIO + 0x28) : mword 64) 4 = mword_of_int (UIO + 0x2c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp2c) in "Hpc".
    (* +0x2c c.ld a5,0(a0) *)
    iApply (wp_cld_s_sconf (ktd := KT0) (mword_of_int (UIO + 0x2c)) (mword_of_int 15 : mword 5) (mword_of_int 10 : mword 5)
              (mword_of_int 0 : mword 12) L7 (K - 2)%nat (Z_to_bv 64 (uart_base i)) false (dqm:=DfracDiscarded)
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc [] [Hbase]").
    { iApply (uio_2c with "Htext"). }
    { rgne. rewrite HL7a0 Hea0. iExact "Hbase". }
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc _".
    set (L8 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (Z_to_bv 64 (uart_base i) : mword 64)]> L7).
    assert (HL8a5 : L8 !!! Regidx (mword_of_int 15 : mword 5) = uart_pa i 0)
      by (rewrite /L8 upd_eq; exact Hbw).
    assert (HL8a0 : L8 !!! Regidx (mword_of_int 10 : mword 5) = mword_of_int (uart_elt i))
      by (rewrite /L8 upd_ne; [exact HL7a0 | vm_compute; discriminate]).
    assert (HL8x0 : L8 !!! Regidx (mword_of_int 0 : mword 5) = zero_reg)
      by (rewrite /L8 upd_ne; [exact HL7x0 | vm_compute; discriminate]).
    assert (Hpp2e : add_vec_int (mword_of_int (UIO + 0x2c) : mword 64) 2 = mword_of_int (UIO + 0x2e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp2e) in "Hpc".
    (* +0x2e c.li a4,7 *)
    iApply (wp_cli_s_sconf (mword_of_int (UIO + 0x2e)) (mword_of_int 14 : mword 5) (mword_of_int 7 : mword 6) (mword_of_int 7 : mword 64)
              L8 (K - 2)%nat false ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc []").
    { iApply (uio_2e with "Htext"). }
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    set (L9 := <[Regidx (mword_of_int 14 : mword 5) := regval_into_reg (mword_of_int 7 : mword 64)]> L8).
    assert (HL9a5 : L9 !!! Regidx (mword_of_int 15 : mword 5) = uart_pa i 0)
      by (rewrite /L9 upd_ne; [exact HL8a5 | vm_compute; discriminate]).
    assert (HL9a0 : L9 !!! Regidx (mword_of_int 10 : mword 5) = mword_of_int (uart_elt i))
      by (rewrite /L9 upd_ne; [exact HL8a0 | vm_compute; discriminate]).
    assert (HL9x0 : L9 !!! Regidx (mword_of_int 0 : mword 5) = zero_reg)
      by (rewrite /L9 upd_ne; [exact HL8x0 | vm_compute; discriminate]).
    assert (Hpp30 : add_vec_int (mword_of_int (UIO + 0x2e) : mword 64) 2 = mword_of_int (UIO + 0x30)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp30) in "Hpc".
    (* +0x30 sb a4,2(a5) : FCR <- 0x07 -- enable + CLEAR BOTH FIFOS *)
    iApply (Uart.wp_sb_uart_uinv_s_sconf_at KT0 i (CID:=CID) γd 2 (mword_of_int (UIO + 0x30)) false (mword_of_int 14 : mword 5) (mword_of_int 15 : mword 5) (mword_of_int 2 : mword 12)
              L9 (K - 2)%nat
              (uart_tx_own γd l ∗ uart_dlab_is γd (DfracOwn (1/2)) false ∗
                 uart_rx_tok γd k hl)%I
              (uart_tx_own γd l ∗ uart_dlab_is γd (DfracOwn (1/2)) false ∗
                 ∃ (k' : nat) (hl' : option (list mobs)),
                   uart_rx_tok γd k' hl')%I
              false p
              ltac:(unfold uart_size; lia)
              ltac:(rgne; rewrite HL9a5; destruct i; vm_compute; reflexivity)
              ltac:(rgne; rewrite HL9a5; destruct i; apply bv_eq; vm_compute; reflexivity)
              ltac:(rgne; rewrite HL9a5; destruct i; apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc [] Huinv [$Htx $Hdlab $Htok] []").
    { iApply (uio_30 with "Htext"). }
    { (* THE RECEIVE FLUSH.  FCR = 0x07 sets bit 1, so the receive FIFO is
         emptied outright: this is a pop of everything, and it is why
         uartinitone takes the receive token at all. *)
      iIntros (uu uu') "%Hw Hg Hcol (Ht & Hd & Htok)".
      iDestruct (ui_tx_empty γd uu l with "Hg Ht Hlb") as %Htxe.
      destruct (uart_write_2_stable uu _ uu' Htxe Hw) as (Ha & Ho & Hdb).
      destruct (uart_write_fcr_rx uu _ uu' Hw) as [Hrxe Hlbe].
      match type of Hrxe with
      | u_rx uu' = (if ?cl then [] else _) => destruct cl eqn:Hclr
      end.
      + iMod (uart_colE_flush i γd uu uu' k hl Hrxe Hlbe
                ltac:(exact (uart_write_wire _ _ _ _ Hw)) Ho with "Hcol Htok")
          as "[Hcol Htok]".
        iModIntro. iSplitL "Hg";
          [ iApply (uart_ghosts_stable γd uu uu' Ha Ho Hdb with "Hg") |].
        iFrame "Hcol Ht Hd Htok".
      + iDestruct (uart_colE_stable i γd uu uu' Hrxe Hlbe
             ltac:(exact (uart_write_wire _ _ _ _ Hw)) Ho with "Hcol") as "Hcol".
        iModIntro. iSplitL "Hg";
          [ iApply (uart_ghosts_stable γd uu uu' Ha Ho Hdb with "Hg") |].
        iFrame "Hcol Ht Hd". iExists k, hl. iExact "Htok". }
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc (Htx & Hdlab & Htok)".
    assert (Hpp34 : add_vec_int (mword_of_int (UIO + 0x30) : mword 64) 4 = mword_of_int (UIO + 0x34)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp34) in "Hpc".
    (* ---- the seventh write's OPERAND: [u->rx ? 3 : 2] ---- *)
    (* +0x34 c.ld a5,8(a0) : a5 := u->rx *)
    iApply (wp_cld_s_sconf (ktd := KT0) (mword_of_int (UIO + 0x34)) (mword_of_int 15 : mword 5) (mword_of_int 10 : mword 5)
              (mword_of_int 8 : mword 12) L9 (K - 2)%nat (Z_to_bv 64 (uart_rx_hook i)) false (dqm:=DfracDiscarded)
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc [] [Hrx]").
    { iApply (uio_34 with "Htext"). }
    { rgne. rewrite HL9a0 Hea8. iExact "Hrx". }
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc _".
    set (L10 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (Z_to_bv 64 (uart_rx_hook i) : mword 64)]> L9).
    assert (HL10a0 : L10 !!! Regidx (mword_of_int 10 : mword 5) = mword_of_int (uart_elt i))
      by (rewrite /L10 upd_ne; [exact HL9a0 | vm_compute; discriminate]).
    assert (HL10x0 : L10 !!! Regidx (mword_of_int 0 : mword 5) = zero_reg)
      by (rewrite /L10 upd_ne; [exact HL9x0 | vm_compute; discriminate]).
    assert (Hpp36 : add_vec_int (mword_of_int (UIO + 0x34) : mword 64) 2 = mword_of_int (UIO + 0x36)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp36) in "Hpc".
    (* +0x36 snez a5,a5 (= sltu a5,zero,a5).  The RESULT IS NOT NAMED: the
       IER byte differs between the two ports (3 at the console, 2 at the
       other), and offset 1 is stable at either ([uart_write_1_stable]), so
       the walk carries the value symbolically. *)
    iApply (wp_sltu_s_sconf (mword_of_int (UIO + 0x36)) (mword_of_int 15 : mword 5) (mword_of_int 0 : mword 5) (mword_of_int 15 : mword 5)
              (zero_extend' 64 (bool_to_bit (zopz0zI_u (L10 !!! Regidx (mword_of_int 0 : mword 5)) (L10 !!! Regidx (mword_of_int 15 : mword 5)))))
              L10 (K - 2)%nat false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(repeat rgne; reflexivity)
              with "Hcg Hpc []").
    { iApply (uio_36 with "Htext"). }
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    set (L11 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (zero_extend' 64 (bool_to_bit (zopz0zI_u (L10 !!! Regidx (mword_of_int 0 : mword 5)) (L10 !!! Regidx (mword_of_int 15 : mword 5)))))]> L10).
    assert (HL11a0 : L11 !!! Regidx (mword_of_int 10 : mword 5) = mword_of_int (uart_elt i))
      by (rewrite /L11 upd_ne; [exact HL10a0 | vm_compute; discriminate]).
    assert (Hpp3a : add_vec_int (mword_of_int (UIO + 0x36) : mword 64) 4 = mword_of_int (UIO + 0x3a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp3a) in "Hpc".
    (* +0x3a c.addi a5,a5,2 *)
    iApply (wp_caddi_s_sconf (mword_of_int (UIO + 0x3a)) (mword_of_int 15 : mword 5) (mword_of_int 2 : mword 6)
              L11 (K - 2)%nat false ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc []").
    { iApply (uio_3a with "Htext"). }
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (L12 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (add_vec (L11 !!! Regidx (mword_of_int 15 : mword 5)) (sign_extend' 64 (sign_extend' 12 (mword_of_int 2 : mword 6))))]> L11).
    assert (HL12a0 : L12 !!! Regidx (mword_of_int 10 : mword 5) = mword_of_int (uart_elt i))
      by (rewrite /L12 upd_ne; [exact HL11a0 | vm_compute; discriminate]).
    assert (Hpp3c : add_vec_int (mword_of_int (UIO + 0x3a) : mword 64) 2 = mword_of_int (UIO + 0x3c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp3c) in "Hpc".
    (* +0x3c c.ld a4,0(a0) *)
    iApply (wp_cld_s_sconf (ktd := KT0) (mword_of_int (UIO + 0x3c)) (mword_of_int 14 : mword 5) (mword_of_int 10 : mword 5)
              (mword_of_int 0 : mword 12) L12 (K - 2)%nat (Z_to_bv 64 (uart_base i)) false (dqm:=DfracDiscarded)
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc [] [Hbase]").
    { iApply (uio_3c with "Htext"). }
    { rgne. rewrite HL12a0 Hea0. iExact "Hbase". }
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc _".
    set (L13 := <[Regidx (mword_of_int 14 : mword 5) := regval_into_reg (Z_to_bv 64 (uart_base i) : mword 64)]> L12).
    assert (HL13a4 : L13 !!! Regidx (mword_of_int 14 : mword 5) = uart_pa i 0)
      by (rewrite /L13 upd_eq; exact Hbw).
    assert (HL13a0 : L13 !!! Regidx (mword_of_int 10 : mword 5) = mword_of_int (uart_elt i))
      by (rewrite /L13 upd_ne; [exact HL12a0 | vm_compute; discriminate]).
    assert (Hpp3e : add_vec_int (mword_of_int (UIO + 0x3c) : mword 64) 2 = mword_of_int (UIO + 0x3e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp3e) in "Hpc".
    (* +0x3e sb a5,1(a4) : IER <- tx | (rx ? 1 : 0) *)
    iApply (Uart.wp_sb_uart_uinv_s_sconf_at KT0 i (CID:=CID) γd 1 (mword_of_int (UIO + 0x3e)) false (mword_of_int 15 : mword 5) (mword_of_int 14 : mword 5) (mword_of_int 1 : mword 12)
              L13 (K - 2)%nat
              (uart_tx_own γd l ∗ uart_dlab_is γd (DfracOwn (1/2)) false)%I
              (uart_tx_own γd l ∗ uart_dlab_is γd (DfracOwn (1/2)) false)%I
              false p
              ltac:(unfold uart_size; lia)
              ltac:(rgne; rewrite HL13a4; destruct i; vm_compute; reflexivity)
              ltac:(rgne; rewrite HL13a4; destruct i; apply bv_eq; vm_compute; reflexivity)
              ltac:(rgne; rewrite HL13a4; destruct i; apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc [] Huinv [$Htx $Hdlab] []").
    { iApply (uio_3e with "Htext"). }
    { iIntros (uu uu') "%Hw Hg Hcol [Ht Hd]".
      destruct (uart_write_1_stable uu _ uu' Hw) as (Ha & Ho & Hdb).
      destruct (uart_write_rx_stable uu 1 _ uu' ltac:(lia) ltac:(lia) Hw)
        as [Hrxe Hlbe].
      iModIntro. iSplitL "Hg";
        [ iApply (uart_ghosts_stable γd uu uu' Ha Ho Hdb with "Hg") |].
      iSplitL "Hcol";
        [ iApply (uart_colE_stable i γd uu uu' Hrxe Hlbe
             ltac:(exact (uart_write_wire _ _ _ _ Hw)) Ho with "Hcol")
        | iFrame "Ht Hd" ]. }
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc [Htx Hdlab]".
    (* Device programming done, and DLAB is off for good. *)
    iMod (uart_dlab_freeze γd with "Hdlab") as "#Hdoff".
    (* carry the saved-slot cells + register facts through *)
    assert (HL13sp : L13 !!! Regidx csp_rs1 = spr).
    { rewrite /L13 upd_ne; [| vm_compute; discriminate].
      rewrite /L12 upd_ne; [| vm_compute; discriminate].
      rewrite /L11 upd_ne; [| vm_compute; discriminate].
      rewrite /L10 upd_ne; [| vm_compute; discriminate].
      rewrite /L9 upd_ne; [| vm_compute; discriminate].
      rewrite /L8 upd_ne; [| vm_compute; discriminate].
      rewrite /L7 upd_ne; [| vm_compute; discriminate].
      rewrite /L6 upd_ne; [| vm_compute; discriminate].
      rewrite /L5 upd_ne; [| vm_compute; discriminate].
      rewrite /L4 upd_ne; [| vm_compute; discriminate].
      rewrite /L3 upd_ne; [| vm_compute; discriminate].
      rewrite /L2 upd_ne; [| vm_compute; discriminate].
      rewrite /L1 upd_ne; [exact HR2sp | vm_compute; discriminate]. }
    assert (HL13a1 : L13 !!! Regidx (mword_of_int 11 : mword 5) = nm_addr).
    { rewrite /L13 upd_ne; [| vm_compute; discriminate].
      rewrite /L12 upd_ne; [| vm_compute; discriminate].
      rewrite /L11 upd_ne; [| vm_compute; discriminate].
      rewrite /L10 upd_ne; [| vm_compute; discriminate].
      rewrite /L9 upd_ne; [| vm_compute; discriminate].
      rewrite /L8 upd_ne; [| vm_compute; discriminate].
      rewrite /L7 upd_ne; [| vm_compute; discriminate].
      rewrite /L6 upd_ne; [| vm_compute; discriminate].
      rewrite /L5 upd_ne; [| vm_compute; discriminate].
      rewrite /L4 upd_ne; [| vm_compute; discriminate].
      rewrite /L3 upd_ne; [| vm_compute; discriminate].
      rewrite /L2 upd_ne; [| vm_compute; discriminate].
      rewrite /L1 upd_ne; [exact HR2a1 | vm_compute; discriminate]. }
    assert (Hpp42 : add_vec_int (mword_of_int (UIO + 0x3e) : mword 64) 4 = mword_of_int (UIO + 0x42)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp42) in "Hpc".
    (* ===== 0x42..0x44: a0 := &u->tx_lock, then jal initlock ===== *)
    (* +0x42 c.addi a0,a0,16 *)
    iApply (wp_caddi_s_sconf (mword_of_int (UIO + 0x42)) (mword_of_int 10 : mword 5) (mword_of_int 16 : mword 6)
              L13 (K - 2)%nat false ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc []").
    { iApply (uio_42 with "Htext"). }
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (A1 := <[Regidx (mword_of_int 10 : mword 5) := regval_into_reg (add_vec (L13 !!! Regidx (mword_of_int 10 : mword 5)) (sign_extend' 64 (sign_extend' 12 (mword_of_int 16 : mword 6))))]> L13).
    assert (HA1a0 : A1 !!! Regidx (mword_of_int 10 : mword 5) = a_tx_lock_at i).
    { rewrite /A1 upd_eq. rewrite HL13a0. rewrite /a_tx_lock_at.
      destruct i; apply bv_eq; vm_compute; reflexivity. }
    assert (HA1a1 : A1 !!! Regidx (mword_of_int 11 : mword 5) = nm_addr)
      by (rewrite /A1 upd_ne; [exact HL13a1 | vm_compute; discriminate]).
    assert (HA1sp : A1 !!! Regidx csp_rs1 = spr)
      by (rewrite /A1 upd_ne; [exact HL13sp | vm_compute; discriminate]).
    assert (Hpp44 : add_vec_int (mword_of_int (UIO + 0x42) : mword 64) 2 = mword_of_int (UIO + 0x44)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp44) in "Hpc".
    (* +0x44 jal ra,initlock *)
    iApply (wp_jal_s_sconf (mword_of_int (UIO + 0x44)) (mword_of_int 1 : mword 5) (mword_of_int 766 : mword 21)
              A1 (K - 2)%nat false ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(vm_compute; reflexivity)
              with "Hcg Hpc []").
    { iApply (uio_44 with "Htext"). }
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    set (A2 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (UIO + 0x44) : mword 64) 4)]> A1).
    assert (Htgtil : add_vec (mword_of_int (UIO + 0x44) : mword 64) (sign_extend' 64 (mword_of_int 766 : mword 21)) = mword_of_int KernelSyms.initlock)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgtil) in "Hpc".
    assert (HA2a0 : A2 !!! Regidx (mword_of_int 10 : mword 5) = a_tx_lock_at i)
      by (rewrite /A2 upd_ne; [exact HA1a0 | vm_compute; discriminate]).
    assert (HA2a1 : A2 !!! Regidx (mword_of_int 11 : mword 5) = nm_addr)
      by (rewrite /A2 upd_ne; [exact HA1a1 | vm_compute; discriminate]).
    assert (HA2sp : A2 !!! Regidx csp_rs1 = spr)
      by (rewrite /A2 upd_ne; [exact HA1sp | vm_compute; discriminate]).
    assert (HA2ra : A2 !!! Regidx (mword_of_int 1 : mword 5) = mword_of_int (UIO + 0x48))
      by (rewrite /A2 upd_eq; apply bv_eq; vm_compute; reflexivity).
    (* ---- initlock(&u->tx_lock, name) ---- *)
    iApply (Initlock.wp_initlock_sconf KT0 A2
              vtlock vtname vtcpu nm (K - 2)%nat false p
              ltac:(lia)
              with "Hcg Htext Hpc [] [Hf1] [Hf2] [Hf3]").
    { iEval (rewrite HA2a1). iExact "Hnm". }
    { iEval (rewrite HA2a0). iExact "Hf1". }
    { iEval (rewrite HA2a0). iExact "Hf2". }
    { iEval (rewrite HA2a0). iExact "Hf3". }
    iApply wp_next_off_intro.
    iIntros (mil) "Hcg Hpc %Hilcs Hg1 Hg2 Hg3".
    iEval (rewrite HA2a0) in "Hg1".
    iEval (rewrite HA2a0 HA2a1) in "Hg2".
    iMod (lock_name_intro with "Hnm Hg2") as "#Hnmp".
    iEval (rewrite HA2a0) in "Hg3".
    iAssert (lk_fresh (a_tx_lock_at i) nm) with "[Hg1 Hg3]" as "Hfresh".
    { rewrite /lk_fresh. iSplitL "Hg1"; [iExact "Hg1" |].
      iSplitR; [iExact "Hnmp" | iExact "Hg3"]. }
    assert (Hpcsl : ret_pc (A2 !!! Regidx (mword_of_int 1 : mword 5)) = mword_of_int (UIO + 0x48)).
    { rewrite HA2ra. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite Hpcsl) in "Hpc".
    assert (Hmilsp : mil !!! Regidx csp_rs1 = spr)
      by (rewrite (callee_saved_lookup Hilcs csp_rs1 ltac:(vm_compute; reflexivity)); exact HA2sp).
    (* ===== EPILOGUE 0x48..0x4e ===== *)
    (* +0x48 c.ldsp ra,8(sp) *)
    iApply (wp_cldsp_s_sconf (mword_of_int (UIO + 0x48)) (mword_of_int 1 : mword 6) (mword_of_int 1 : mword 5)
              mil (K - 2)%nat (m !!! Regidx (mword_of_int 1 : mword 5)) false (dqm:=DfracOwn 1)
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc [] [Hras]").
    { iApply (uio_48 with "Htext"). }
    { iEval (rewrite -Hb1s -Hmilsp) in "Hras". iExact "Hras". }
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc Hras".
    iEval (rewrite Hmilsp Hb1s) in "Hras".
    set (E1 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 1 : mword 5))]> mil).
    assert (HE1sp : E1 !!! Regidx csp_rs1 = spr) by (rewrite /E1 upd_ne; [exact Hmilsp | vm_compute; discriminate]).
    assert (Hpp4a : add_vec_int (mword_of_int (UIO + 0x48) : mword 64) 2 = mword_of_int (UIO + 0x4a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp4a) in "Hpc".
    (* +0x4a c.ldsp s0,0(sp) *)
    iApply (wp_cldsp_s_sconf (mword_of_int (UIO + 0x4a)) (mword_of_int 0 : mword 6) (mword_of_int 8 : mword 5)
              E1 (K - 2)%nat (m !!! Regidx (mword_of_int 8 : mword 5)) false (dqm:=DfracOwn 1)
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc [] [Hs0s]").
    { iApply (uio_4a with "Htext"). }
    { iEval (rewrite -Hb2s -HE1sp) in "Hs0s". iExact "Hs0s". }
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc Hs0s".
    iEval (rewrite HE1sp Hb2s) in "Hs0s".
    set (E2 := <[Regidx (mword_of_int 8 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 8 : mword 5))]> E1).
    assert (HE2sp : E2 !!! Regidx csp_rs1 = spr) by (rewrite /E2 upd_ne; [exact HE1sp | vm_compute; discriminate]).
    assert (Hpp4c : add_vec_int (mword_of_int (UIO + 0x4a) : mword 64) 2 = mword_of_int (UIO + 0x4c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp4c) in "Hpc".
    (* +0x4c c.addi sp,16 : pop frame *)
    set (E3 := <[Regidx csp_rs1 := regval_into_reg (add_vec (E2 !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 16 : mword 6))))]> E2).
    assert (HE3csp : E3 !!! Regidx csp_rs1 = sp0).
    { rewrite /E3 upd_eq. rewrite HE2sp. unfold regval_into_reg, spr, sp0.
      apply frame_cancel_16. }
    assert (Hwv : add_vec (E2 !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 16 : mword 6))) = sp0).
    { rewrite -HE3csp /E3 upd_eq. reflexivity. }
    assert (Hpop : E2 !!! Regidx csp_rs1
                   = pa_stk (add_vec (E2 !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 16 : mword 6)))) 2).
    { rewrite Hwv HE2sp. exact Hspr2. }
    iAssert (stack_own (KTR := KT0) sp0 2) with "[Hras Hs0s]" as "Hframe".
    { rewrite (stack_own_slots (KTR := KT0)). cbn [seq].
      iSplitL "Hras"; [iExists _; iExact "Hras"|].
      iSplitL "Hs0s"; [iExists _; iExact "Hs0s"|]. done. }
    iEval (rewrite -Hwv) in "Hframe".
    iApply (wp_caddi_sp_pop_s_sconf (mword_of_int (UIO + 0x4c)) (mword_of_int 16 : mword 6) E2 (K - 2)%nat 2 false Hpop
              with "Hcg Hpc [] Hframe").
    { iApply (uio_4c with "Htext"). }
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    assert (Hnk : ((K - 2) + 2)%nat = K) by lia.
    iEval (rewrite Hnk) in "Hcg".
    change (<[Regidx csp_rs1 := regval_into_reg (add_vec (E2 !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 16 : mword 6))))]> E2) with E3.
    assert (Hpp4e : add_vec_int (mword_of_int (UIO + 0x4c) : mword 64) 2 = mword_of_int (UIO + 0x4e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp4e) in "Hpc".
    (* +0x4e c.ret *)
    assert (HE3ra : E3 !!! Regidx (mword_of_int 1 : mword 5) = m !!! Regidx (mword_of_int 1 : mword 5)).
    { rewrite /E3 upd_ne; [| vm_compute; discriminate].
      rewrite /E2 upd_ne; [| vm_compute; discriminate].
      rewrite /E1 upd_eq; reflexivity. }
    iApply (wp_cret_s_sconf (mword_of_int (UIO + 0x4e)) (mword_of_int 1 : mword 5) E3 K false
              ltac:(vm_compute; discriminate)
              with "Hcg Hpc []").
    { iApply (uio_4e with "Htext"). }
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
      pose proof (is_cs_idx_true_neq (mword_of_int 14 : mword 5) c ltac:(vm_compute; reflexivity) Hc) as Na4.
      pose proof (is_cs_idx_true_neq (mword_of_int 15 : mword 5) c ltac:(vm_compute; reflexivity) Hc) as Na5.
      rewrite /E3 upd_ne; [| congruence].
      rewrite /E2 upd_ne; [| congruence].
      rewrite /E1 upd_ne; [| congruence].
      rewrite (callee_saved_lookup Hilcs c Hc).
      rewrite /A2 upd_ne; [| congruence].
      rewrite /A1 upd_ne; [| congruence].
      rewrite /L13 upd_ne; [| congruence].
      rewrite /L12 upd_ne; [| congruence].
      rewrite /L11 upd_ne; [| congruence].
      rewrite /L10 upd_ne; [| congruence].
      rewrite /L9 upd_ne; [| congruence].
      rewrite /L8 upd_ne; [| congruence].
      rewrite /L7 upd_ne; [| congruence].
      rewrite /L6 upd_ne; [| congruence].
      rewrite /L5 upd_ne; [| congruence].
      rewrite /L4 upd_ne; [| congruence].
      rewrite /L3 upd_ne; [| congruence].
      rewrite /L2 upd_ne; [| congruence].
      rewrite /L1 upd_ne; [| congruence].
      rewrite /R2 upd_ne; [| congruence].
      rewrite /R1 upd_ne; [reflexivity | congruence]. }
    iApply ("Hcont" $! E3 with "Hcg Hpc [%] Htx Hsent Htok Hdoff Hfresh").
    unfold callee_saved.
    split. { rewrite HE3csp. reflexivity. }
    split. { rewrite /E3 upd_ne; [| vm_compute; discriminate].
             rewrite /E2 upd_eq; reflexivity. }
    repeat split; apply Hthread; vm_compute; first [reflexivity | discriminate].
  Qed.

End ProofUartinitone.
End UartinitoneProof.
